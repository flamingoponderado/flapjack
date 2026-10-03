import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.WordToStack.Proofs.Initialization
import Flapjack.Misc.Sptree.MapiLookup

namespace Flapjack.WordToStackProofs.InitializationStateRel
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization

/-- Imported canonical target-state roundtrip; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Same-module target codec witness for the full relation theorem. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Same-module source codec witness at the original bitmap/config product. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width (Nat × C) F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width (Nat × C) F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Complete original native initialization contract. Every bitmap/stack,
register/store/GC, compiler-oracle and program-convention condition remains.
No extra executable alignment or source/target run condition is introduced. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "init_state_ok_def"
  (fmap_as_finite_support := [regs, store]) (words_as_type_indexed_bitvec)]
def initStateOk {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat) (t : StackSemStateFiniteExact width C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width))) : Prop :=
  4 < k ∧ goodDimindex width ∧ 8 ≤ width ∧
  t.useStack = true ∧ t.useStore = true ∧ t.useAlloc = true ∧ wordGcFunOk t.gcFun ∧
  t.stackSpace ≤ t.stack.length ∧ t.regs.lookup 0 = some (.loc 1 0) ∧
  t.bitmaps.length + 1 < 2 ^ width ∧ List.IsPrefix [(4 : BitVec width)] t.bitmaps ∧
  t.stack.length < 2 ^ width ∧ t.stack.drop t.stackSpace = [.word 0] ∧
  t.store.lookup .handler ≠ none ∧
  t.bitmaps.length + t.dataBuffer.buffer.length + t.dataBuffer.spaceLeft + 1 < 2 ^ width ∧
  t.compileOracle = (fun n =>
    let ((bm0, cfg), progs) := coracle n
    let (progs, _, bm) := compileWordToStackNative ac false k progs (.nil, bm0)
    (cfg, progs, appListAppend bm.1)) ∧
  (∀ n,
    let ((bm0, _), progs) := coracle n
    progs.all (fun p => postAllocConventionsHOL k p.2.2) = true ∧
    progs.all (fun p => flatExpConventions p.2.2) = true ∧
    progs.all (fun p => decide (p.1 ≠ raiseStubLocation)) = true ∧
    progs.all (fun p => decide (p.1 ≠ storeConstsStubLocation)) = true ∧
    (n = 0 → bm0 = t.bitmaps.length))

/-- Frame size in the original compiler depends on program/argument/register
counts, not on the threaded bitmap accumulator; untagged infrastructure. -/
private theorem frameSizeIndependent {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (prog : WordLangProgHOL (BitVec width))
    (argc k : Nat) (bs : AppList (BitVec width)) (i : Nat)
    (compiled : Compiler.Backend.StackLang.HolProg width) (frame : Nat)
    (bs2 : AppList (BitVec width)) (i2 : Nat)
    (run : compileProgNative ac false prog argc k (bs, i) = (compiled, frame, (bs2, i2))) :
    (compileProgNative ac false prog argc k (.nil, 0)).2.1 = frame := by
  have sizes := congrArg (fun x => x.2.1) run
  simpa only [compileProgNative] using sizes

/-- Full original initialization-to-state-relation theorem. The only premises
are the original two stub lookups, code-entry compile/prefix witnesses, code
domain equation and complete initialization contract. The whole source state
relation is derived, including compiler frame-size lookup and all resource,
stack and local-placement clauses; no output relation is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "init_state_ok_IMP_state_rel"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem initStateOkImpliesStateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat) (t : StackSemStateFiniteExact width C F)
    (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (premises : sptLookup raiseStubLocation t.code = some (raiseStubNative false k) ∧
      sptLookup storeConstsStubLocation t.code = some (storeConstsStubNative k) ∧
      (∀ n wordProg argumentCount, sptLookup n code = some (argumentCount, wordProg) →
        postAllocConventionsHOL k wordProg = true ∧ flatExpConventions wordProg = true ∧
        ∃ (bs : AppList (BitVec width)) (i : Nat) (bs2 : AppList (BitVec width))
          (i2 frame : Nat) (stackProg : Compiler.Backend.StackLang.HolProg width),
          compileProgNative ac false wordProg argumentCount k (bs, i) = (stackProg, frame, (bs2, i2)) ∧
          (appListAppend bs).length ≤ i ∧ i - (appListAppend bs).length ≤ t.bitmaps.length ∧
          List.IsPrefix (appListAppend bs2) (t.bitmaps.drop (i - (appListAppend bs).length)) ∧
          sptLookup n t.code = some stackProg) ∧
      sptDomain t.code = (fun n => n = raiseStubLocation ∨ n = storeConstsStubLocation ∨ sptDomain code n) ∧
      initStateOk ac k t coracle) :
    stateRel ac k 0 0 (makeInit ac k t code coracle : WordSemStateFiniteExact width (Nat × C) F) t [] 0 := by
  rcases premises with ⟨raise, store, entries, domain, ok⟩
  rcases ok with ⟨kBound, dimension, widthBound, useStack, useStore, useAlloc, gc,
    stackSpace, register0, bitmapBound, bitmapPrefix, stackBound, stackDrop,
    handler, dataBound, oracle, oracleAll⟩
  have bitmapHead : 1 ≤ t.bitmaps.length ∧ Flapjack.holHd t.bitmaps = (4 : BitVec width) := by
    obtain ⟨tail, equal⟩ := bitmapPrefix
    rw [← equal]
    simp [Flapjack.holHd]
  have entryRelation : ∀ n wordProg argumentCount,
      sptLookup n code = some (argumentCount, wordProg) →
      postAllocConventionsHOL k wordProg = true ∧ flatExpConventions wordProg = true ∧
      ∃ (bs : AppList (BitVec width)) (i : Nat) (bs2 : AppList (BitVec width))
        (i2 frame : Nat) (stackProg : Compiler.Backend.StackLang.HolProg width),
        compileProgNative ac false wordProg argumentCount k (bs, i) = (stackProg, frame, (bs2, i2)) ∧
        (appListAppend bs).length ≤ i ∧ i - (appListAppend bs).length ≤ t.bitmaps.length ∧
        List.IsPrefix (appListAppend bs2) (t.bitmaps.drop (i - (appListAppend bs).length)) ∧
        sptLookup n t.code = some stackProg ∧
        (sptLookup n (makeInit ac k t code coracle).stackSize).getD frame = frame := by
    intro n prog argc lookup
    obtain ⟨allocated, flat, bs, i, bs2, i2, frame, compiled, run, bound, offset, prefixFact, target⟩ := entries n prog argc lookup
    refine ⟨allocated, flat, bs, i, bs2, i2, frame, compiled, run, bound, offset, prefixFact, target, ?_⟩
    simp only [makeInit, sptLookupMapi, lookup, Option.map_some, Option.getD_some]
    exact frameSizeIndependent ac prog argc k bs i compiled frame bs2 i2 run
  simp only [stateRel, makeInit]
  simp_all [stackSizeRel, stackRel, absStack, stackRelAux,
    sptWf, sptLookup, wordSemStackSize]
  refine ⟨rfl, ?_, ?_, ?_, by omega⟩
  · intro n
    exact ⟨(oracleAll n).1, (oracleAll n).2.1,
      (oracleAll n).2.2.1, (oracleAll n).2.2.2.1⟩
  · simpa only [makeInit] using entryRelation
  · have lengths := congrArg List.length stackDrop
    simp only [List.length_drop, List.length_cons, List.length_nil] at lengths
    constructor <;> omega

end Flapjack.WordToStackProofs.InitializationStateRel
