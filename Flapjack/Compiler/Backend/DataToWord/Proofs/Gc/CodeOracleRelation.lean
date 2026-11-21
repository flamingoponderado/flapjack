module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CodeRelation
public import Flapjack.Compiler.Backend.BackendCommon.UpperW2w
public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.WordSem.State
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CollectorStore
public import Flapjack.FiniteMap.BroadCodec

@[expose] public section

/-! Compiler callback and oracle relation for data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

namespace codeOracleRelMap
/-- Canonical lookup and support roundtrip for the oracle relation's store. -/
theorem holFmapAsFiniteSupportParamWitness_codeOracleRel_store
    {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad store)).lookup key = store.lookup key ∧
      (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
      FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad store) = store := ⟨rfl, rfl, rfl⟩
end codeOracleRelMap

/-- The buffers, compiler callbacks, and future compilation requests agree
across the data-to-word pass. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "code_oracle_rel_def"
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
def codeOracleRel {storeWidth : Nat} {compilerWidth : Nat} {oracleWidth : Nat}
    {codeElemWidth : Nat} {dataElemWidth : Nat}
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

namespace codeOracleRelNextFreeMap
/-- Canonical lookup and support roundtrip for `code_oracle_rel_NextFree`'s store. -/
theorem holFmapAsFiniteSupportParamWitness_code_oracle_rel_NextFree_ts
    {width : Nat} [NeZero width]
    (ts : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ts)).lookup key = ts.lookup key ∧
      (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ts)).finiteSupport = ts.finiteSupport ∧
      FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad ts) = ts := ⟨rfl, rfl, rfl⟩
end codeOracleRelNextFreeMap

/-- Exact HOL `code_oracle_rel_NextFree` (`data_to_word_gcProofScript.sml:4483-4488`):
updating `NextFree` does not affect the oracle relation. HOL `ts |+ (NextFree,x)`
is `ts.updateEq (.nextFree, x)`; the HOL free variables are universally
quantified, with the five word widths independent as in the typed capture. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "code_oracle_rel_NextFree"
  (fmap_as_finite_support_parameters := [ts]) (words_as_type_indexed_bitvec)]
theorem code_oracle_rel_NextFree
    {storeWidth : Nat} {compilerWidth : Nat} {oracleWidth : Nat}
    {codeElemWidth : Nat} {dataElemWidth : Nat}
    [NeZero storeWidth] [NeZero compilerWidth] [NeZero oracleWidth]
    [NeZero codeElemWidth] [NeZero dataElemWidth] {C OracleKey OracleConfig : Type}
    {c : Config} {scc : DataSem.Compiler C}
    {sco : OracleKey → OracleConfig × List (Nat × Nat × DataLang.Prog)}
    {ts : HolFiniteMapExact WordStoreHOL (WordLocW storeWidth)} {x : WordLocW storeWidth}
    {tcc : C → List (Nat × Nat × WordLangProgHOL (BitVec compilerWidth)) →
      Option (List (BitVec 8) × List (BitVec compilerWidth) × C)}
    {tco : OracleKey → OracleConfig × List (Nat × Nat × WordLangProgHOL (BitVec oracleWidth))}
    {cb : WordSemBuffer storeWidth codeElemWidth} {db : WordSemBuffer storeWidth dataElemWidth} :
    codeOracleRel c scc sco (ts.updateEq (.nextFree, x)) tcc tco cb db ↔
      codeOracleRel c scc sco ts tcc tco cb db := by
  simp [codeOracleRel, HolFiniteMapExact.updateEq, FUPDATE_HOL]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
