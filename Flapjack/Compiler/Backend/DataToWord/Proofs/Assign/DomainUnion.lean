module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvProperties
public import Flapjack.Compiler.Backend.Semantics.WordSem.Domain

@[expose] public section

/-! # `evaluate_IMP_domain_union` of `data_to_word_assignProofScript.sml` -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.WordSemStackEq

namespace DomainUnionWitness
/-- Canonical finite-map roundtrip for the word-state fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end DomainUnionWitness

/-- A key of an association list has a lookup; local proof infrastructure for
`evaluate_IMP_domain_union`. -/
private theorem aListLookup_isSome {α : Type} (key : Nat) (entries : List (Nat × α)) :
    (sptAListLookup key entries).isSome = true ↔ key ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [sptAListLookup]
  | cons head tail ih =>
    obtain ⟨k, v⟩ := head
    by_cases h : key = k
    · subst h
      simp [sptAListLookup]
    · simp only [sptAListLookup, h, if_false, ih, List.map_cons, List.mem_cons, false_or]

/-- A call whose callee returns normally and whose frame is popped restores
exactly the domains of both saved environments, including the return location.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_IMP_domain_union"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_IMP_domainUnion {width : Nat} [NeZero width] {C F β : Type}
    (p : WordLangProgHOL (BitVec width)) (args : List (WordLocW width)) (b : Option Nat)
    (y1 y2 : Spt (WordLocW width)) (t : WordSemStateFiniteExact width C F) (ck tp : Nat)
    (ret1 : WordLocW width) (ret2 : List (WordLocW width))
    (t1 t2 : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (keptNames : Spt β)
    (h : WordSemStateFiniteExact.evaluate p
        { WordSemStateFiniteExact.callEnv args b (WordSemStateFiniteExact.pushEnv (y1, y2) none t) with
          clock := ck, termdep := tp } = (some (.result ret1 ret2), t1) ∧
      WordSemStateFiniteExact.popEnv t1 = some t2 ∧
      sptLookup 0 y1 = some (.loc l1 l2) ∧
      wordSemCutEnvs (adjustSets keptNames) t.locals = some (y1, y2)) :
    sptDomainEqUnion t2.locals y1 y2 ∧
      sptLookup 0 t2.locals = some (.loc l1 l2) := by
  obtain ⟨run, pop, zero, cut⟩ := h
  have swap := evaluateStackSwap p
    { WordSemStateFiniteExact.callEnv args b (WordSemStateFiniteExact.pushEnv (y1, y2) none t) with
      clock := ck, termdep := tp }
  unfold stackSwapPost at swap
  rw [run] at swap
  obtain ⟨keyEq, -, -⟩ := swap
  cases envEq : wordSemEnvToList y2 t.permute with
  | mk l perm =>
  have equiv := (wordSemEnvToListLookupEquiv y2 t.permute l perm envEq).1
  simp only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, envEq] at keyEq
  cases ht1 : t1.stack with
  | nil => simp [ht1, sKeyEq] at keyEq
  | cons hr tr =>
    rw [ht1] at keyEq
    obtain ⟨-, frameEq⟩ := keyEq
    obtain ⟨m, e0, e, handler⟩ := hr
    cases handler with
    | some y => simp [sFrameKeyEq] at frameEq
    | none =>
      obtain ⟨keys, rfl, -⟩ := frameEq
      simp only [WordSemStateFiniteExact.popEnv, ht1, Option.some.injEq] at pop
      subst pop
      have y2Zero : sptLookup 0 y2 = none := by
        simp only [wordSemCutEnvs, adjustSets] at cut
        split at cut
        · rename_i e1 e2 c1 c2
          simp only [Option.some.injEq, Prod.mk.injEq] at cut
          obtain ⟨-, rfl⟩ := cut
          simp only [wordSemCutNames] at c2
          split at c2
          · simp only [Option.some.injEq] at c2
            subst c2
            rw [sptLookup_sptInterCases]
            have absent := not_zero_adjustSet keptNames
            simp only [sptDomain] at absent
            cases hz : sptLookup 0 (adjustSet keptNames) <;> simp_all
          · simp at c2
        · simp at cut
      have eKeys : ∀ k, (sptAListLookup k e).isSome = (sptLookup k y2).isSome := by
        intro k
        rw [← equiv k]
        apply Bool.eq_iff_iff.mpr
        rw [aListLookup_isSome, aListLookup_isSome, keys]
      constructor
      · intro k
        simp only [sptMem, sptDomain]
        rw [sptLookup_sptUnion, sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, ← eKeys k]
        cases sptAListLookup k e <;> cases sptLookup k y1 <;> simp
      · have e0 : sptAListLookup 0 e = none := by
          have := eKeys 0
          rw [y2Zero] at this
          cases h : sptAListLookup 0 e <;> simp_all
        rw [sptLookup_sptUnion, sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, e0]
        exact zero

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
