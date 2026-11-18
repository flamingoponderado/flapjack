module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CodeRelation
public import Flapjack.Compiler.Backend.BackendCommon.UpperW2w
public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.WordSem.State
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorStore

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

/-- Flapjack-specific factoring of the oracle-relation reconstruction in
HOL's `state_rel_gc_gen` proof. There is no separate HOL theorem for this
combined step. The collector run supplies the unchanged buffer entries. -/
theorem codeOracleRel_afterWordGc
    {storeWidth compilerWidth oracleWidth codeElemWidth dataElemWidth : Nat}
    [NeZero storeWidth] [NeZero compilerWidth] [NeZero oracleWidth]
    [NeZero codeElemWidth] [NeZero dataElemWidth] {C OracleKey OracleConfig : Type}
    (conf : Config) (sourceCompile : DataSem.Compiler C)
    (sourceOracle : OracleKey → OracleConfig × List (Nat × Nat × DataLang.Prog))
    (store store' : HolFiniteMapExact WordStoreHOL (WordLocW storeWidth))
    (targetCompile : C → List (Nat × Nat × WordLangProgHOL (BitVec compilerWidth)) →
      Option (List (BitVec 8) × List (BitVec compilerWidth) × C))
    (targetOracle : OracleKey → OracleConfig × List (Nat × Nat × WordLangProgHOL (BitVec oracleWidth)))
    (codeBuffer : WordSemBuffer storeWidth codeElemWidth)
    (dataBuffer : WordSemBuffer storeWidth dataElemWidth)
    (roots moved : List (WordLocW storeWidth)) (memory memory' : BitVec storeWidth → WordLocW storeWidth)
    (domain : BitVec storeWidth → Bool)
    (run : WordGcFunctions.wordGcFun conf (roots, memory, domain, store) = some (moved, memory', store'))
    (related : codeOracleRel conf sourceCompile sourceOracle store targetCompile targetOracle codeBuffer dataBuffer) :
    codeOracleRel conf sourceCompile sourceOracle store' targetCompile targetOracle codeBuffer dataBuffer := by
  obtain ⟨_, _, code, codeEnd, bitmap, bitmapEnd, _, _, _⟩ :=
    wordGcFun_store_invariants conf roots moved memory memory' domain store store' run
  rcases related with ⟨hcode, hdata, hcodePos, hcodeEnd, hbitmapPos, hbitmapEnd, hcompile, horacle, hstubs⟩
  exact ⟨hcode, hdata, code ▸ hcodePos, codeEnd ▸ hcodeEnd,
    bitmap ▸ hbitmapPos, bitmapEnd ▸ hbitmapEnd, hcompile, horacle, hstubs⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
