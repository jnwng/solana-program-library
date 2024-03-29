//! SPL Account Compression is an on-chain program that exposes an interface to manipulating SPL ConcurrentMerkleTrees
//!
//! A buffer of proof-like changelogs is stored on-chain that allow multiple proof-based writes to succeed within the same slot.
//! This is accomplished by fast-forwarding out-of-date (or possibly invalid) proofs based on information stored in the changelogs.
//! See a copy of the whitepaper [here](https://drive.google.com/file/d/1BOpa5OFmara50fTvL0VIVYjtg-qzHCVc/view)
//!
//! To circumvent proof size restrictions stemming from Solana transaction size restrictions,
//! SPL Account Compression also provides the ability to cache the upper most leaves of the
//! concurrent merkle tree. This is called the "canopy", and is stored at the end of the
//! ConcurrentMerkleTreeAccount. More information can be found in the initialization instruction
//! documentation.
//!
//! While SPL ConcurrentMerkleTrees can generically store arbitrary information,
//! one exemplified use-case is the [Bubblegum](https://github.com/metaplex-foundation/metaplex-program-library/tree/master/bubblegum) contract,
//! which uses SPL-Compression to store encoded information about NFTs.
//! The use of SPL-Compression within Bubblegum allows for:
//! - up to 1 billion NFTs to be stored in a single account on-chain (>10,000x decrease in on-chain cost)
//! - up to 2048 concurrent updates per slot
//!
//! Operationally, SPL ConcurrentMerkleTrees **must** be supplemented by off-chain indexers to cache information
//! about leafs and to power an API that can supply up-to-date proofs to allow updates to the tree.
//! All modifications to SPL ConcurrentMerkleTrees are settled on the Solana ledger via instructions against the SPL Compression contract.
//! A production-ready indexer (Plerkle) can be found in the [Metaplex program library](https://github.com/metaplex-foundation/digital-asset-validator-plugin)

use anchor_lang::{
    prelude::*,
    solana_program::sysvar::{clock::Clock, rent::Rent},
};
use borsh::{BorshDeserialize, BorshSerialize};
pub mod canopy;
pub mod error;
pub mod events;
#[macro_use]
pub mod macros;
mod noop;
pub mod state;
pub mod zero_copy;

pub use crate::noop::{wrap_application_data_v1, Noop};

use crate::canopy::{fill_in_proof_from_canopy, update_canopy};
pub use crate::error::AccountCompressionError;
pub use crate::events::{AccountCompressionEvent, ChangeLogEvent};
use crate::noop::wrap_event;
use crate::state::{
    merkle_tree_get_size, ConcurrentMerkleTreeHeader, CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1,
};
use crate::zero_copy::ZeroCopy;
use anchor_lang::solana_program::{
    program::invoke, system_instruction::create_account, system_program,
};

/// Exported for Anchor / Solita
pub use spl_concurrent_merkle_tree::{
    concurrent_merkle_tree::ConcurrentMerkleTree, error::ConcurrentMerkleTreeError, node::Node,
};

declare_id!("cmtDvXumGCrqC1Age74AVPhSRVXJMd8PJS91L8KbNCK");

/// Context for initializing a new SPL ConcurrentMerkleTree
#[derive(Accounts)]
pub struct Initialize<'info> {
    #[account(zero)]
    /// CHECK: This account will be zeroed out, and the size will be validated
    pub merkle_tree: UncheckedAccount<'info>,

    /// Authority that controls write-access to the tree
    /// Typically a program, e.g., the Bubblegum contract validates that leaves are valid NFTs.
    pub authority: Signer<'info>,

    /// Program used to emit changelogs as cpi instruction data.
    pub noop: Program<'info, Noop>,
}

/// Context for filling a proof buffer
#[derive(Accounts)]
pub struct FillProofBuffer<'info> {
    /// Proof Buffer
    pub payer: Signer<'info>,
    pub proof_buffer: Signer<'info>,
    pub system_program: Program<'info, System>,
}

/// Context for closing a proof buffer
#[derive(Accounts)]
pub struct CloseProofBuffer<'info> {
    /// Proof Buffer
    pub payer: Signer<'info>,
    pub proof_buffer: Signer<'info>,
}

/// Context for initializing a new SPL ConcurrentMerkleTree
#[derive(Accounts)]
pub struct InitializeWithRoot<'info> {
    #[account(zero)]
    /// CHECK: This account will be zeroed out, and the size will be validated
    pub merkle_tree: UncheckedAccount<'info>,

    /// Authority that controls write-access to the tree
    /// Typically a program, e.g., the Bubblegum contract validates that leaves are valid NFTs.
    pub authority: Signer<'info>,

    /// Program used to emit changelogs as cpi instruction data.
    pub noop: Program<'info, Noop>,

    /// Proof Buffer - Optional
    pub proof_buffer: Option<UncheckedAccount<'info>>,
}

/// Context for inserting, appending, or replacing a leaf in the tree
///
/// Modification instructions also require the proof to the leaf to be provided
/// as 32-byte nodes via "remaining accounts".
#[derive(Accounts)]
pub struct Modify<'info> {
    #[account(mut)]
    /// CHECK: This account is validated in the instruction
    pub merkle_tree: UncheckedAccount<'info>,

    /// Authority that controls write-access to the tree
    /// Typically a program, e.g., the Bubblegum contract validates that leaves are valid NFTs.
    pub authority: Signer<'info>,

    /// Program used to emit changelogs as cpi instruction data.
    pub noop: Program<'info, Noop>,
}

/// Context for validating a provided proof against the SPL ConcurrentMerkleTree.
/// Throws an error if provided proof is invalid.
#[derive(Accounts)]
pub struct VerifyLeaf<'info> {
    /// CHECK: This account is validated in the instruction
    pub merkle_tree: UncheckedAccount<'info>,
}

/// Context for transferring `authority`
#[derive(Accounts)]
pub struct TransferAuthority<'info> {
    #[account(mut)]
    /// CHECK: This account is validated in the instruction
    pub merkle_tree: UncheckedAccount<'info>,

    /// Authority that controls write-access to the tree
    /// Typically a program, e.g., the Bubblegum contract validates that leaves are valid NFTs.
    pub authority: Signer<'info>,
}

/// Context for closing a tree
#[derive(Accounts)]
pub struct CloseTree<'info> {
    #[account(mut)]
    /// CHECK: This account is validated in the instruction
    pub merkle_tree: AccountInfo<'info>,

    /// Authority that controls write-access to the tree
    pub authority: Signer<'info>,

    /// CHECK: Recipient of funds after
    #[account(mut)]
    pub recipient: AccountInfo<'info>,
}

#[program]
pub mod spl_account_compression {
    use self::state::ProofBufferHeader;

    use super::*;

    /// Creates a new merkle tree with maximum leaf capacity of `power(2, max_depth)`
    /// and a minimum concurrency limit of `max_buffer_size`.
    ///
    /// Concurrency limit represents the # of replace instructions that can be successfully
    /// executed with proofs dated for the same root. For example, a maximum buffer size of 1024
    /// means that a minimum of 1024 replaces can be executed before a new proof must be
    /// generated for the next replace instruction.
    ///
    /// Concurrency limit should be determined by empirically testing the demand for
    /// state built on top of SPL Compression.
    ///
    /// For instructions on enabling the canopy, see [canopy].
    pub fn init_empty_merkle_tree(
        ctx: Context<Initialize>,
        max_depth: u32,
        max_buffer_size: u32,
    ) -> Result<()> {
        require_eq!(
            *ctx.accounts.merkle_tree.owner,
            crate::id(),
            AccountCompressionError::IncorrectAccountOwner
        );
        let mut merkle_tree_bytes = ctx.accounts.merkle_tree.try_borrow_mut_data()?;

        let (mut header_bytes, rest) =
            merkle_tree_bytes.split_at_mut(CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1);

        let mut header = ConcurrentMerkleTreeHeader::try_from_slice(header_bytes)?;
        header.initialize(
            max_depth,
            max_buffer_size,
            &ctx.accounts.authority.key(),
            Clock::get()?.slot,
        );
        header.serialize(&mut header_bytes)?;
        let merkle_tree_size = merkle_tree_get_size(&header)?;
        let (tree_bytes, canopy_bytes) = rest.split_at_mut(merkle_tree_size);
        let id = ctx.accounts.merkle_tree.key();
        let change_log_event = merkle_tree_apply_fn_mut!(header, id, tree_bytes, initialize,)?;
        wrap_event(
            &AccountCompressionEvent::ChangeLog(*change_log_event),
            &ctx.accounts.noop,
        )?;
        update_canopy(canopy_bytes, header.get_max_depth(), None)
    }

    /// For extremley large trees that cannot be initialized with root in a single transaction,
    /// this allows a user to fill a buffer of proofs that can be used to initialize the tree with roots.
    /// Any tree that you cant make a proof in the space of 1024 - (size of the init_with_root instruction) should use this instruction.
    /// Without proofs that instruction is 208 bytes + the manifest url size. Assuming this url will be around 25/30 bytes, this instruction will be 238 bytes.
    /// In that example, you would need to be able to make a proof in 786 bytes. Which is 786/32 = 24.5. So you would be able to make a tree of depth 24 maximum.
    /// The CMT allows for a maximum depth of 30, so this instruction is necessary for trees of depth 25-30.
    pub fn fill_proof_buffer(
        ctx: Context<FillProofBuffer>,
        max_depth: u32,
        partial_proof: Vec<u8>,
        index: u32,
    ) -> Result<()> {
        if partial_proof.len() % 32 != 0 || partial_proof.is_empty() {
            return Err(AccountCompressionError::InvalidProofBuffer.into());
        }
        let buffer: &mut [u8] = &mut *ctx.accounts.proof_buffer.try_borrow_mut_data()?;
        let len = buffer.len();
        let account_owner = ctx.accounts.proof_buffer.owner;
        let mut header = if len == 0 {
            if index != 0 {
                return Err(AccountCompressionError::ProofIndexOutOfBounds.into());
            }
            if account_owner != &system_program::id() {
                return Err(AccountCompressionError::IncorrectAccountOwner.into());
            }
            let space = (max_depth * 32) + 40;
            let lamports = Rent::get()?.minimum_balance(space as usize);
            let create_ix = create_account(
                &ctx.accounts.payer.key,
                &ctx.accounts.proof_buffer.key,
                lamports,
                space as u64,
                &crate::id(),
            );
            invoke(
                &create_ix,
                &[
                    ctx.accounts.payer.to_account_info(),
                    ctx.accounts.proof_buffer.to_account_info(),
                    ctx.accounts.system_program.to_account_info(),
                ],
            )?;
            ProofBufferHeader {
                owner: ctx.accounts.payer.key.key(),
                remaining_depth: max_depth,
                max_depth,
            }
        } else {
            let (header, _) = buffer.split_at_mut(40);
            *ProofBufferHeader::load_mut_bytes(header)?
        };
        if ctx.accounts.payer.key.as_ref() != header.owner.as_ref() {
            return Err(AccountCompressionError::InvalidProofBufferOwner.into());
        }
        if header.max_depth != max_depth {
            return Err(AccountCompressionError::ProofIndexOutOfBounds.into());
        }
        let offset = 40 + (index * 32) as usize;
        let segments: Vec<&[u8]> = partial_proof.chunks(32).collect();
        for proof in segments.iter() {
            buffer[offset..40 + ((offset + 1) * 32)].copy_from_slice(proof);
        }
        let new_remaining = header.remaining_depth - index;
        //set remaining
        header.remaining_depth = new_remaining;
        Ok(())
    }

    /// Closes the proof buffer account
    pub fn close_proof_buffer(ctx: Context<CloseProofBuffer>) -> Result<()> {
        let data = ctx.accounts.proof_buffer.try_borrow_data()?;
        let (owner, _) = data.split_at(32);
        if owner != ctx.accounts.payer.key.as_ref() {
            return Err(AccountCompressionError::InvalidProofBufferOwner.into());
        }
        let proof_lamports = ctx.accounts.proof_buffer.get_lamports();
        ctx.accounts.proof_buffer.sub_lamports(proof_lamports)?;
        ctx.accounts.payer.add_lamports(proof_lamports)?;
        Ok(())
    }

    // Creates a new merkle tree with an existing root in the buffer.
    // The indexers for the specific tree use case are in charge of handling the indexing or shadow indexing of the tree.
    // Shadow indexing is a technique that allows for the indexing of a tree incrementally with update operations.
    pub fn init_merkle_tree_with_root(
        ctx: Context<InitializeWithRoot>,
        max_depth: u32,
        max_buffer_size: u32,
        root: [u8; 32],
        leaf_index: u32,
        leaf: [u8; 32], // the last leaf in the tree
        manifest_url: String,
    ) -> Result<()> {
        require_eq!(
            *ctx.accounts.merkle_tree.owner,
            crate::id(),
            AccountCompressionError::IncorrectAccountOwner
        );
        let mut merkle_tree_bytes: std::cell::RefMut<'_, &mut [u8]> =
            ctx.accounts.merkle_tree.try_borrow_mut_data()?;

        let proof: Vec<[u8; 32]> = if let Some(proof_buffer_account) = &ctx.accounts.proof_buffer {
            let mut proof_buffer = proof_buffer_account.try_borrow_mut_data()?;
            let (_, proof_bytes) = proof_buffer.split_at_mut(8);
            //if len is not a multiple of 32 then return error
            if proof_bytes.len() % 32 != 0 {
                return Err(AccountCompressionError::InvalidProofBuffer.into());
            }

            let proof_lamports = proof_buffer_account.get_lamports();
            proof_buffer_account.sub_lamports(proof_lamports)?;
            ctx.accounts.authority.add_lamports(proof_lamports)?;
            proof_bytes
                .chunks_exact(32)
                .map(|c| c.try_into().unwrap())
                .collect()
        } else {
            ctx.remaining_accounts
                .into_iter()
                .map(|a| a.key().to_bytes())
                .collect()
        };
        assert_eq!(proof.len(), max_depth as usize);
        let (mut header_bytes, rest) =
            merkle_tree_bytes.split_at_mut(CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1);
        let mut header = ConcurrentMerkleTreeHeader::try_from_slice(&header_bytes)?;
        header.initialize(
            max_depth,
            max_buffer_size,
            &ctx.accounts.authority.key(),
            Clock::get()?.slot,
        );
        header.serialize(&mut header_bytes)?;
        let merkle_tree_size = merkle_tree_get_size(&header)?;
        let (tree_bytes, canopy_bytes) = rest.split_at_mut(merkle_tree_size);
        let id = ctx.accounts.merkle_tree.key();
        let change_log_event = merkle_tree_apply_fn_mut!(
            header,
            id,
            tree_bytes,
            initialize_with_root,
            root,
            leaf,
            &proof,
            leaf_index
        )?;
        update_canopy(canopy_bytes, header.get_max_depth(), Some(&change_log_event))?;
        wrap_event(
            &AccountCompressionEvent::InitWithRoot(*change_log_event, manifest_url),
            &ctx.accounts.noop,
        )
    }

    /// Executes an instruction that overwrites a leaf node.
    /// Composing programs should check that the data hashed into previous_leaf
    /// matches the authority information necessary to execute this instruction.
    pub fn replace_leaf(
        ctx: Context<Modify>,
        root: [u8; 32],
        previous_leaf: [u8; 32],
        new_leaf: [u8; 32],
        index: u32,
    ) -> Result<()> {
        require_eq!(
            *ctx.accounts.merkle_tree.owner,
            crate::id(),
            AccountCompressionError::IncorrectAccountOwner
        );
        let mut merkle_tree_bytes = ctx.accounts.merkle_tree.try_borrow_mut_data()?;
        let (header_bytes, rest) =
            merkle_tree_bytes.split_at_mut(CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1);

        let header = ConcurrentMerkleTreeHeader::try_from_slice(header_bytes)?;
        header.assert_valid_authority(&ctx.accounts.authority.key())?;
        header.assert_valid_leaf_index(index)?;

        let merkle_tree_size = merkle_tree_get_size(&header)?;
        let (tree_bytes, canopy_bytes) = rest.split_at_mut(merkle_tree_size);

        let mut proof = vec![];
        for node in ctx.remaining_accounts.iter() {
            proof.push(node.key().to_bytes());
        }
        fill_in_proof_from_canopy(canopy_bytes, header.get_max_depth(), index, &mut proof)?;
        let id = ctx.accounts.merkle_tree.key();
        // A call is made to ConcurrentMerkleTree::set_leaf(root, previous_leaf, new_leaf, proof, index)
        let change_log_event = merkle_tree_apply_fn_mut!(
            header,
            id,
            tree_bytes,
            set_leaf,
            root,
            previous_leaf,
            new_leaf,
            &proof,
            index,
        )?;
        update_canopy(
            canopy_bytes,
            header.get_max_depth(),
            Some(&change_log_event),
        )?;
        wrap_event(
            &AccountCompressionEvent::ChangeLog(*change_log_event),
            &ctx.accounts.noop,
        )
    }

    /// Transfers `authority`.
    /// Requires `authority` to sign
    pub fn transfer_authority(
        ctx: Context<TransferAuthority>,
        new_authority: Pubkey,
    ) -> Result<()> {
        require_eq!(
            *ctx.accounts.merkle_tree.owner,
            crate::id(),
            AccountCompressionError::IncorrectAccountOwner
        );
        let mut merkle_tree_bytes = ctx.accounts.merkle_tree.try_borrow_mut_data()?;
        let (mut header_bytes, _) =
            merkle_tree_bytes.split_at_mut(CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1);

        let mut header = ConcurrentMerkleTreeHeader::try_from_slice(header_bytes)?;
        header.assert_valid_authority(&ctx.accounts.authority.key())?;

        header.set_new_authority(&new_authority);
        header.serialize(&mut header_bytes)?;

        Ok(())
    }

    /// Verifies a provided proof and leaf.
    /// If invalid, throws an error.
    pub fn verify_leaf(
        ctx: Context<VerifyLeaf>,
        root: [u8; 32],
        leaf: [u8; 32],
        index: u32,
    ) -> Result<()> {
        require_eq!(
            *ctx.accounts.merkle_tree.owner,
            crate::id(),
            AccountCompressionError::IncorrectAccountOwner
        );
        let merkle_tree_bytes = ctx.accounts.merkle_tree.try_borrow_data()?;
        let (header_bytes, rest) =
            merkle_tree_bytes.split_at(CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1);

        let header = ConcurrentMerkleTreeHeader::try_from_slice(header_bytes)?;
        header.assert_valid()?;
        header.assert_valid_leaf_index(index)?;

        let merkle_tree_size = merkle_tree_get_size(&header)?;
        let (tree_bytes, canopy_bytes) = rest.split_at(merkle_tree_size);

        let mut proof = vec![];
        for node in ctx.remaining_accounts.iter() {
            proof.push(node.key().to_bytes());
        }
        fill_in_proof_from_canopy(canopy_bytes, header.get_max_depth(), index, &mut proof)?;
        let id = ctx.accounts.merkle_tree.key();

        merkle_tree_apply_fn!(header, id, tree_bytes, prove_leaf, root, leaf, &proof, index)?;
        Ok(())
    }

    /// This instruction allows the tree's `authority` to append a new leaf to the tree
    /// without having to supply a proof.
    ///
    /// Learn more about SPL
    /// ConcurrentMerkleTree
    /// [here](https://github.com/solana-labs/solana-program-library/tree/master/libraries/concurrent-merkle-tree)
    pub fn append(ctx: Context<Modify>, leaf: [u8; 32]) -> Result<()> {
        require_eq!(
            *ctx.accounts.merkle_tree.owner,
            crate::id(),
            AccountCompressionError::IncorrectAccountOwner
        );
        let mut merkle_tree_bytes = ctx.accounts.merkle_tree.try_borrow_mut_data()?;
        let (header_bytes, rest) =
            merkle_tree_bytes.split_at_mut(CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1);

        let header = ConcurrentMerkleTreeHeader::try_from_slice(header_bytes)?;
        header.assert_valid_authority(&ctx.accounts.authority.key())?;

        let id = ctx.accounts.merkle_tree.key();
        let merkle_tree_size = merkle_tree_get_size(&header)?;
        let (tree_bytes, canopy_bytes) = rest.split_at_mut(merkle_tree_size);
        let change_log_event = merkle_tree_apply_fn_mut!(header, id, tree_bytes, append, leaf)?;
        update_canopy(
            canopy_bytes,
            header.get_max_depth(),
            Some(&change_log_event),
        )?;
        wrap_event(
            &AccountCompressionEvent::ChangeLog(*change_log_event),
            &ctx.accounts.noop,
        )
    }

    /// This instruction takes a proof, and will attempt to write the given leaf
    /// to the specified index in the tree. If the insert operation fails, the leaf will be `append`-ed
    /// to the tree.
    /// It is up to the indexer to parse the final location of the leaf from the emitted changelog.
    pub fn insert_or_append(
        ctx: Context<Modify>,
        root: [u8; 32],
        leaf: [u8; 32],
        index: u32,
    ) -> Result<()> {
        require_eq!(
            *ctx.accounts.merkle_tree.owner,
            crate::id(),
            AccountCompressionError::IncorrectAccountOwner
        );
        let mut merkle_tree_bytes = ctx.accounts.merkle_tree.try_borrow_mut_data()?;
        let (header_bytes, rest) =
            merkle_tree_bytes.split_at_mut(CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1);

        let header = ConcurrentMerkleTreeHeader::try_from_slice(header_bytes)?;
        header.assert_valid_authority(&ctx.accounts.authority.key())?;
        header.assert_valid_leaf_index(index)?;

        let merkle_tree_size = merkle_tree_get_size(&header)?;
        let (tree_bytes, canopy_bytes) = rest.split_at_mut(merkle_tree_size);

        let mut proof = vec![];
        for node in ctx.remaining_accounts.iter() {
            proof.push(node.key().to_bytes());
        }
        fill_in_proof_from_canopy(canopy_bytes, header.get_max_depth(), index, &mut proof)?;
        // A call is made to ConcurrentMerkleTree::fill_empty_or_append
        let id = ctx.accounts.merkle_tree.key();
        let change_log_event = merkle_tree_apply_fn_mut!(
            header,
            id,
            tree_bytes,
            fill_empty_or_append,
            root,
            leaf,
            &proof,
            index,
        )?;
        update_canopy(
            canopy_bytes,
            header.get_max_depth(),
            Some(&change_log_event),
        )?;
        wrap_event(
            &AccountCompressionEvent::ChangeLog(*change_log_event),
            &ctx.accounts.noop,
        )
    }

    pub fn close_empty_tree(ctx: Context<CloseTree>) -> Result<()> {
        require_eq!(
            *ctx.accounts.merkle_tree.owner,
            crate::id(),
            AccountCompressionError::IncorrectAccountOwner
        );
        let mut merkle_tree_bytes = ctx.accounts.merkle_tree.try_borrow_mut_data()?;
        let (header_bytes, rest) =
            merkle_tree_bytes.split_at_mut(CONCURRENT_MERKLE_TREE_HEADER_SIZE_V1);

        let header = ConcurrentMerkleTreeHeader::try_from_slice(header_bytes)?;
        header.assert_valid_authority(&ctx.accounts.authority.key())?;

        let merkle_tree_size = merkle_tree_get_size(&header)?;
        let (tree_bytes, canopy_bytes) = rest.split_at_mut(merkle_tree_size);

        let id = ctx.accounts.merkle_tree.key();
        merkle_tree_apply_fn_mut!(header, id, tree_bytes, prove_tree_is_empty,)?;

        // Close merkle tree account
        // 1. Move lamports
        let dest_starting_lamports = ctx.accounts.recipient.lamports();
        **ctx.accounts.recipient.lamports.borrow_mut() = dest_starting_lamports
            .checked_add(ctx.accounts.merkle_tree.lamports())
            .unwrap();
        **ctx.accounts.merkle_tree.lamports.borrow_mut() = 0;

        // 2. Set all CMT account bytes to 0
        header_bytes.fill(0);
        tree_bytes.fill(0);
        canopy_bytes.fill(0);

        Ok(())
    }
}
