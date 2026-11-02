import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CodeRelation
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.InitStoreOk
import Flapjack.Compiler.Backend.Semantics.DataSem.State
import Flapjack.Compiler.Backend.Semantics.WordSem.State

/-! The 64-bit data-to-word compiler callback and oracle relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The word callback and its oracle use the actual 64-bit lowering, and the
empty code and data buffers agree with their store bounds. This is a
production-backed candidate for HOL's code oracle relation; correspondence of
`compilePart64` with the unrestricted HOL compiler remains to be proved. -/
def codeOracleRel64 {C : Type} (conf : Config)
    (sourceCompile : DataSem.Compiler C) (sourceOracle : DataSem.CompileOracle C)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (targetCompile : C → List (Nat × Nat × WordLangProgHOL (BitVec 64)) →
      Option (List (BitVec 8) × List (BitVec 64) × C))
    (targetOracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeBuffer : WordSemBuffer 64 8) (dataBuffer : WordSemBuffer 64 64) : Prop :=
  codeBuffer.buffer = [] ∧ dataBuffer.buffer = [] ∧
  store.lookup .codeBuffer = some (.word codeBuffer.position) ∧
  store.lookup .codeBufferEnd = some (.word (codeBuffer.position + BitVec.ofNat 64 codeBuffer.spaceLeft)) ∧
  store.lookup .bitmapBuffer = some (.word dataBuffer.position) ∧
  store.lookup .bitmapBufferEnd = some (.word (dataBuffer.position + 8 * BitVec.ofNat 64 dataBuffer.spaceLeft)) ∧
  sourceCompile = (fun cfg entries => targetCompile cfg (entries.map (compilePart64 conf))) ∧
  targetOracle = (fun n => ((sourceOracle n).1, (sourceOracle n).2.map (compilePart64 conf))) ∧
  ∀ n entry, entry ∈ (sourceOracle n).2 → dataNumStubs ≤ entry.1

/-- The initial store invariant supplies all buffer obligations of the
64-bit oracle relation; the compiler and future-code equations are explicit. -/
theorem codeOracleRel64_of_initStore {C β : Type} (conf : Config)
    (sourceCompile : DataSem.Compiler C) (sourceOracle : DataSem.CompileOracle C)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (targetCompile : C → List (Nat × Nat × WordLangProgHOL (BitVec 64)) →
      Option (List (BitVec 8) × List (BitVec 64) × C))
    (targetOracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (memory : BitVec 64 → β) (domain : BitVec 64 → Bool)
    (codeBuffer : WordSemBuffer 64 8) (dataBuffer : WordSemBuffer 64 64)
    (initial : initStoreOk conf store memory domain codeBuffer dataBuffer)
    (compileEq : sourceCompile = (fun cfg entries => targetCompile cfg (entries.map (compilePart64 conf))))
    (oracleEq : targetOracle = (fun n => ((sourceOracle n).1, (sourceOracle n).2.map (compilePart64 conf))))
    (bounds : ∀ n entry, entry ∈ (sourceOracle n).2 → dataNumStubs ≤ entry.1) :
    codeOracleRel64 conf sourceCompile sourceOracle store targetCompile targetOracle codeBuffer dataBuffer := by
  obtain ⟨limit, curr, bound, globals, real, gen, heap, other, next, finish, trigger, length,
    code, codeEnd, bitmap, bitmapEnd, codeEmpty, dataEmpty, memoryOk, aligned⟩ := initial
  refine ⟨codeEmpty, dataEmpty, code, codeEnd, bitmap, ?_, compileEq, oracleEq, bounds⟩
  simpa [wordSemBytesInWord] using bitmapEnd

/-- The callback agrees on every concrete configuration and input program. -/
theorem codeOracleRel64_compile {C : Type} (conf : Config)
    (sourceCompile : DataSem.Compiler C) (sourceOracle : DataSem.CompileOracle C)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (targetCompile : C → List (Nat × Nat × WordLangProgHOL (BitVec 64)) →
      Option (List (BitVec 8) × List (BitVec 64) × C))
    (targetOracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeBuffer : WordSemBuffer 64 8) (dataBuffer : WordSemBuffer 64 64)
    (related : codeOracleRel64 conf sourceCompile sourceOracle store targetCompile targetOracle codeBuffer dataBuffer)
    (cfg : C) (entries : List (Nat × Nat × DataLang.Prog)) :
    sourceCompile cfg entries = targetCompile cfg (entries.map (compilePart64 conf)) := by
  rw [related.2.2.2.2.2.2.1]

/-- Updating the allocation pointer leaves the compiler callback relation
unchanged: none of its buffer bounds observes that store key. -/
theorem codeOracleRel64_nextFree {C : Type} (conf : Config)
    (sourceCompile : DataSem.Compiler C) (sourceOracle : DataSem.CompileOracle C)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64)) (value : WordLocW 64)
    (targetCompile : C → List (Nat × Nat × WordLangProgHOL (BitVec 64)) →
      Option (List (BitVec 8) × List (BitVec 64) × C))
    (targetOracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeBuffer : WordSemBuffer 64 8) (dataBuffer : WordSemBuffer 64 64) :
    codeOracleRel64 conf sourceCompile sourceOracle (store.update (.nextFree, value)) targetCompile targetOracle codeBuffer dataBuffer ↔
      codeOracleRel64 conf sourceCompile sourceOracle store targetCompile targetOracle codeBuffer dataBuffer := by
  simp [codeOracleRel64, HolFiniteMapExact.update, FUPDATE]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
