/**
 * This code was GENERATED using the solita package.
 * Please DO NOT EDIT THIS FILE, instead rerun solita to update it or write a wrapper to add functionality.
 *
 * See: https://github.com/metaplex-foundation/solita
 */

import * as beet from '@metaplex-foundation/beet'
import * as web3 from '@solana/web3.js'

/**
 * @category Instructions
 * @category InitMerkleTreeWithRoot
 * @category generated
 */
export type InitMerkleTreeWithRootInstructionArgs = {
  maxDepth: number
  maxBufferSize: number
  root: number[] /* size: 32 */
  leafIndex: number
  leaf: number[] /* size: 32 */
  manifestUrl: string
}
/**
 * @category Instructions
 * @category InitMerkleTreeWithRoot
 * @category generated
 */
export const initMerkleTreeWithRootStruct = new beet.FixableBeetArgsStruct<
  InitMerkleTreeWithRootInstructionArgs & {
    instructionDiscriminator: number[] /* size: 8 */
  }
>(
  [
    ['instructionDiscriminator', beet.uniformFixedSizeArray(beet.u8, 8)],
    ['maxDepth', beet.u32],
    ['maxBufferSize', beet.u32],
    ['root', beet.uniformFixedSizeArray(beet.u8, 32)],
    ['leafIndex', beet.u32],
    ['leaf', beet.uniformFixedSizeArray(beet.u8, 32)],
    ['manifestUrl', beet.utf8String],
  ],
  'InitMerkleTreeWithRootInstructionArgs'
)
/**
 * Accounts required by the _initMerkleTreeWithRoot_ instruction
 *
 * @property [_writable_] merkleTree
 * @property [**signer**] authority
 * @property [] noop
 * @property [] proofBuffer (optional)
 * @category Instructions
 * @category InitMerkleTreeWithRoot
 * @category generated
 */
export type InitMerkleTreeWithRootInstructionAccounts = {
  merkleTree: web3.PublicKey
  authority: web3.PublicKey
  noop: web3.PublicKey
  proofBuffer?: web3.PublicKey
  anchorRemainingAccounts?: web3.AccountMeta[]
}

export const initMerkleTreeWithRootInstructionDiscriminator = [
  67, 221, 160, 236, 108, 179, 112, 198,
]

/**
 * Creates a _InitMerkleTreeWithRoot_ instruction.
 *
 * Optional accounts that are not provided default to the program ID since
 * this was indicated in the IDL from which this instruction was generated.
 *
 * @param accounts that will be accessed while the instruction is processed
 * @param args to provide as instruction data to the program
 *
 * @category Instructions
 * @category InitMerkleTreeWithRoot
 * @category generated
 */
export function createInitMerkleTreeWithRootInstruction(
  accounts: InitMerkleTreeWithRootInstructionAccounts,
  args: InitMerkleTreeWithRootInstructionArgs,
  programId = new web3.PublicKey('cmtDvXumGCrqC1Age74AVPhSRVXJMd8PJS91L8KbNCK')
) {
  const [data] = initMerkleTreeWithRootStruct.serialize({
    instructionDiscriminator: initMerkleTreeWithRootInstructionDiscriminator,
    ...args,
  })
  const keys: web3.AccountMeta[] = [
    {
      pubkey: accounts.merkleTree,
      isWritable: true,
      isSigner: false,
    },
    {
      pubkey: accounts.authority,
      isWritable: false,
      isSigner: true,
    },
    {
      pubkey: accounts.noop,
      isWritable: false,
      isSigner: false,
    },
    {
      pubkey: accounts.proofBuffer ?? programId,
      isWritable: false,
      isSigner: false,
    },
  ]

  if (accounts.anchorRemainingAccounts != null) {
    for (const acc of accounts.anchorRemainingAccounts) {
      keys.push(acc)
    }
  }

  const ix = new web3.TransactionInstruction({
    programId,
    keys,
    data,
  })
  return ix
}
