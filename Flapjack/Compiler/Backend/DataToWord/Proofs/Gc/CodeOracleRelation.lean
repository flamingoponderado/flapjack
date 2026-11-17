module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CodeRelation
public import Flapjack.Compiler.Backend.BackendCommon.UpperW2w
public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.WordSem.State

@[expose] public section

/-! Compiler callback and oracle relation for data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The buffers, compiler callbacks, and future compilation requests agree
across the data-to-word pass. This follows the complete shape of HOL's
`code_oracle_rel_def`; its tag remains pending source review of the executed
`compilePart` traversal and its finite-map and word carriers. -/
def codeOracleRel {storeWidth compilerWidth oracleWidth codeElemWidth dataElemWidth : Nat}
    [NeZero storeWidth] [NeZero compilerWidth] [NeZero oracleWidth]
    [NeZero codeElemWidth] [NeZero dataElemWidth] {C OracleKey OracleConfig : Type}
    (conf : Config) (sourceCompile : DataSem.Compiler C)
    (sourceOracle : OracleKey → OracleConfig × List (Nat × Nat × DataLang.Prog))
    (store : HolFiniteMapExact WordStoreHOL (WordLocW storeWidth))
    (targetCompile : C → List (Nat × Nat × WordLangProgHOL (BitVec compilerWidth)) →
      Option (List (BitVec 8) × List (BitVec compilerWidth) × C))
    (targetOracle : OracleKey → OracleConfig × List (Nat × Nat × WordLangProgHOL (BitVec oracleWidth)))
    (codeBuffer : WordSemBuffer storeWidth codeElemWidth)
    (dataBuffer : WordSemBuffer storeWidth dataElemWidth) : Prop :=
  codeBuffer.buffer = [] ∧ dataBuffer.buffer = [] ∧
  store.lookup .codeBuffer = some (.word codeBuffer.position) ∧
  store.lookup .codeBufferEnd = some (.word (codeBuffer.position + BitVec.ofNat storeWidth codeBuffer.spaceLeft)) ∧
  store.lookup .bitmapBuffer = some (.word dataBuffer.position) ∧
  store.lookup .bitmapBufferEnd = some (.word (dataBuffer.position +
    BitVec.ofNat storeWidth (storeWidth / 8) * BitVec.ofNat storeWidth dataBuffer.spaceLeft)) ∧
  sourceCompile = (fun config program =>
    (targetCompile config (program.map (compilePart (width := compilerWidth) conf))).map fun (bytes, words, next) =>
      (bytes, words.map upperW2w, next)) ∧
  targetOracle = (fun n => let (config, program) := sourceOracle n
    (config, program.map (compilePart (width := oracleWidth) conf))) ∧
  ∀ n, ∀ entry ∈ (sourceOracle n).2, dataNumStubs ≤ entry.1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
