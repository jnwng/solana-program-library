/**
 * This code was GENERATED using the solita package.
 * Please DO NOT EDIT THIS FILE, instead rerun solita to update it or write a wrapper to add functionality.
 *
 * See: https://github.com/metaplex-foundation/solita
 */

import * as beet from '@metaplex-foundation/beet';
import * as web3 from '@solana/web3.js';

/**
 * @category Instructions
 * @category CloseProofBuffer
 * @category generated
 */
export const closeProofBufferStruct = new beet.BeetArgsStruct<{
    instructionDiscriminator: number[] /* size: 8 */;
}>([['instructionDiscriminator', beet.uniformFixedSizeArray(beet.u8, 8)]], 'CloseProofBufferInstructionArgs');
/**
 * Accounts required by the _closeProofBuffer_ instruction
 *
 * @property [**signer**] payer
 * @property [**signer**] proofBuffer
 * @category Instructions
 * @category CloseProofBuffer
 * @category generated
 */
export type CloseProofBufferInstructionAccounts = {
    payer: web3.PublicKey;
    proofBuffer: web3.PublicKey;
    anchorRemainingAccounts?: web3.AccountMeta[];
};

export const closeProofBufferInstructionDiscriminator = [130, 150, 6, 35, 193, 34, 243, 87];

/**
 * Creates a _CloseProofBuffer_ instruction.
 *
 * @param accounts that will be accessed while the instruction is processed
 * @category Instructions
 * @category CloseProofBuffer
 * @category generated
 */
export function createCloseProofBufferInstruction(
    accounts: CloseProofBufferInstructionAccounts,
    programId = new web3.PublicKey('cmtDvXumGCrqC1Age74AVPhSRVXJMd8PJS91L8KbNCK')
) {
    const [data] = closeProofBufferStruct.serialize({
        instructionDiscriminator: closeProofBufferInstructionDiscriminator,
    });
    const keys: web3.AccountMeta[] = [
        {
            isSigner: true,
            isWritable: false,
            pubkey: accounts.payer,
        },
        {
            isSigner: true,
            isWritable: false,
            pubkey: accounts.proofBuffer,
        },
    ];

    if (accounts.anchorRemainingAccounts != null) {
        for (const acc of accounts.anchorRemainingAccounts) {
            keys.push(acc);
        }
    }

    const ix = new web3.TransactionInstruction({
        data,
        keys,
        programId,
    });
    return ix;
}
