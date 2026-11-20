module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GiveUp
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.GcConst
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PopEnvConst

@[expose] public section

/-! Allocation-failure stack accounting for assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.BackendProps

namespace GiveUp2AssignmentWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end GiveUp2AssignmentWitness

/-- Allocation preserves the incoming stack maximum when the pushed frame
fits it. This factors the stack accounting in the HOL GiveUp proof. -/
private theorem allocStackBound {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (w : BitVec width) (names : WordLangCutsetsHOL)
    (bound : optionLe (Option.map₂ (· + ·) (wordSemStackSize s.stack) s.localsSize) s.stackMax) :
    optionLe (WordSemStateFiniteExact.alloc w names s).2.stackMax s.stackMax := by
  unfold WordSemStateFiniteExact.alloc
  cases cut : wordSemCutEnvs names s.locals with
  | none => simp [WordSemStateFiniteExact.flushState, optionLe_refl]
  | some envs =>
    have pushed : optionLe (WordSemStateFiniteExact.pushEnv envs none
        (WordSemStateFiniteExact.setStore .allocSize (.word w) s)).stackMax s.stackMax := by
      cases h : wordSemEnvToList envs.2 s.permute with
      | mk entries permute =>
        change optionLe (wordSemOptionMax s.stackMax
          (wordSemOptionAdd s.localsSize (wordSemStackSize s.stack))) s.stackMax
        cases hm : s.stackMax <;> cases hs : wordSemStackSize s.stack <;> cases hl : s.localsSize <;>
          simp [wordSemOptionMax, wordSemOptionAdd, optionLe, hm, hs, hl] at bound ⊢
        all_goals omega
    cases hg : WordSemStateFiniteExact.gc (WordSemStateFiniteExact.pushEnv envs none
        (WordSemStateFiniteExact.setStore .allocSize (.word w) s)) with
    | none => simp [hg, WordSemStateFiniteExact.flushState, optionLe_refl]
    | some g =>
      have hgmax := (WordSemStateFiniteExact.gcConst _ _ hg).2.2.2.2.2.2.2.2.2.2.2.1
      cases hp : WordSemStateFiniteExact.popEnv g with
      | none => simpa [cut, hg, hp, WordSemStateFiniteExact.flushState, hgmax] using pushed
      | some out =>
        have hpmax := (WordSemStateFiniteExact.popEnvConst _ _ hp).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [hg, hp]
        cases hstore : WordSemStateFiniteExact.getStore .allocSize out with
        | none => simpa [hstore, hpmax, hgmax] using pushed
        | some value =>
          cases hs : WordSemStateFiniteExact.hasSpace value out with
          | none => simpa [hstore, hs, hpmax, hgmax] using pushed
          | some flag =>
            cases flag <;> simpa [hstore, hs, WordSemStateFiniteExact.flushState, hpmax, hgmax] using pushed

/-- GiveUp reports insufficient space, preserves FFI, and respects the
original stack maximum bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_GiveUp2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateGiveUp2 {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target none locs) :
    ∃ r, WordSemStateFiniteExact.evaluate (giveUp (width := width)) target = (some .notEnoughSpace, r) ∧
      r.ffi = source.ffi ∧ target.ffi = source.ffi ∧ optionLe r.stackMax target.stackMax := by
  obtain ⟨r, run, ffi, targetFfi⟩ := evaluateGiveUp conf l1 l2 source target locs related
  refine ⟨r, run, ffi, targetFfi, ?_⟩
  have bound := allocStackBound target (-1) (adjustSets (.ln : NumSet))
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases ar : WordSemStateFiniteExact.alloc (-1) (adjustSets (.ln : NumSet)) target with
  | mk q out =>
    have same : WordSemStateFiniteExact.evaluate (giveUp (width := width)) target = (q, out) := by
      simp [giveUp, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, sptLookup_sptInsert_same, alloc_locals_insert_one]
      cases out
      simp_all
    rw [same] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rw [ar] at bound
    exact bound

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
