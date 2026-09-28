import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkLemmas
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact

/-!
# loop_live `compile_correct`, split by HOL's `Resume` cases

Pieces of `cakeml/pancake/proofs/loop_liveProofScript.sml`'s `compile_correct`
(17-64) over the exact `LoopSemStateFiniteExact.evaluate` (`evaluate_def`), the
tagged `shrinkHOL` (`loop_live$shrink_def`), `sptSubspt` (sptree `subspt`),
`sptInter` (`inter`) and `sptOel` (`oEL`) (bead `flapjack-pxn.18.5.8.1`).
HOL proves it by `recInduct loopSemTheory.evaluate_ind` and resumes one case
per constructor (`Resume compile_correct[Skip]`, ...); each Lean piece is one
such case, with HOL's quantifier order `∀v v1 res s1 lt locals prog1 l1 l0`
(constructor payload in place of `v`), all four premises and the full
conclusion, plus `evaluate_ind` hypotheses for sub-programs where the case has
any.  The assembling theorem is bead `flapjack-pxn.18.5.8.1.9`.
-/

namespace Flapjack

open LoopSemStateFiniteExact

namespace LoopLiveCompileCorrectWitnesses

/-- Same-module re-export of the canonical `loopSem$state` witness for the
    `fmap_as_finite_support := [globals]` qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  LoopSemStateFiniteExact.LoopEvaluateFiniteSupport.holFmapAsFiniteSupportWitness

end LoopLiveCompileCorrectWitnesses

/-- Flapjack-only abbreviation (no HOL declaration) of the `compile_correct`
    statement at a fixed program `v` and state `v1`: the `evaluate_ind`
    hypothesis HOL's case proofs receive for a sub-program. -/
def loopLiveCompileCorrectAt {width : Nat} [NeZero width] {F : Type}
    (v : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F) : Prop :=
  ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
    (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
    (l1 l0 : NumSet),
    evaluate v v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt v l0 = (prog1, l1) ∧
      sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals

private theorem sptSubspt_inter_lookup {width : Nat} [NeZero width]
    {a : Spt (WordLocW width)} {l : NumSet} {b : Spt (WordLocW width)}
    (h : sptSubspt (sptInter a l) b) {k : Nat} (hl : sptMem k l) (w : WordLocW width)
    (ha : sptLookup k a = some w) : sptLookup k b = some w := by
  have hm : sptMem k (sptInter a l) := by
    simp only [sptMem, sptDomain, sptLookup_sptInter]
    have : (sptLookup k l).isSome = true := hl
    simp [this, ha]
  rw [(h k hm).2, sptLookup_sptInter, if_pos (show (sptLookup k l).isSome = true from hl), ha]

private theorem sptMem_sptListInsert_of_mem (k : Nat) :
    ∀ (keys : List Nat) (t : NumSet), k ∈ keys → sptMem k (sptListInsert keys t)
  | [], _, h => by simp at h
  | key :: keys, t, h => by
      simp only [sptListInsert]
      rcases List.mem_cons.mp h with rfl | h
      · exact sptMem_sptListInsert_of k keys _ ((sptMem_sptInsert k k () t).mpr (Or.inl rfl))
      · exact sptMem_sptListInsert_of_mem k keys _ h

private theorem getVars_locals_agree {width : Nat} [NeZero width] {F : Type}
    (v1 : LoopSemStateFiniteExact width F) (locals : Spt (WordLocW width)) :
    ∀ (ns : List Nat) (vs : List (WordLocW width)),
      (∀ n ∈ ns, ∀ w, sptLookup n v1.locals = some w → sptLookup n locals = some w) →
      LoopSemStateFiniteExact.getVars ns v1 = some vs → LoopSemStateFiniteExact.getVars ns { v1 with locals := locals } = some vs
  | [], vs, _, h => h
  | n :: ns, vs, hag, h => by
      simp only [LoopSemStateFiniteExact.getVars] at h ⊢
      cases hn : sptLookup n v1.locals with
      | none => simp [hn] at h
      | some w =>
        cases hr : LoopSemStateFiniteExact.getVars ns v1 with
        | none => simp [hn, hr] at h
        | some ws =>
          simp [hn, hr] at h
          rw [hag n List.mem_cons_self w hn,
            getVars_locals_agree v1 locals ns ws (fun m hm => hag m (List.mem_cons_of_mem _ hm)) hr]
          simpa using h

/-- `compile_correct`, case `Skip` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Skip]` at 66-69). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_skip {width : Nat} [NeZero width] {F : Type} :
    ∀ (v1 : LoopSemStateFiniteExact width F),
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.skip : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.skip : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro v1 res s1 lt locals prog1 l1 l0 ⟨he, _, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  simp only [evaluate, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨locals, by simp [evaluate], hsub⟩

/-- `compile_correct`, case `Fail` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Fail]` at 71-74). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_fail {width : Nat} [NeZero width] {F : Type} :
    ∀ (v1 : LoopSemStateFiniteExact width F),
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.fail : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.fail : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, _, _⟩
  simp only [evaluate, Prod.mk.injEq] at he
  exact absurd he.1.symm hne

/-- `compile_correct`, case `Tick` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Tick]` at 76-79). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_tick {width : Nat} [NeZero width] {F : Type} :
    ∀ (v1 : LoopSemStateFiniteExact width F),
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.tick : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.tick : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro v1 res s1 lt locals prog1 l1 l0 ⟨he, _, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  by_cases hc : v1.clock = 0
  · simp only [evaluate, hc, if_true, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨.ln, by simp [evaluate, hc], rfl⟩
  · simp only [evaluate, hc, if_false, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨locals, by simp [evaluate, hc, decClock], hsub⟩

/-- `compile_correct`, case `Continue` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Continue]` at 81-87). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_continue {width : Nat} [NeZero width] {F : Type} :
    ∀ (k : Nat) (v1 : LoopSemStateFiniteExact width F),
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.continue k : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.continue k : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro k v1 res s1 lt locals prog1 l1 l0 ⟨he, _, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  simp only [evaluate, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨locals, by simp [evaluate], ?_⟩
  simp only
  split
  · rename_i cont brk heq; simpa [heq] using hsub
  · trivial

/-- `compile_correct`, case `Break` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Break]` at 89-95). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_break {width : Nat} [NeZero width] {F : Type} :
    ∀ (k : Nat) (v1 : LoopSemStateFiniteExact width F),
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.break k : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.break k : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro k v1 res s1 lt locals prog1 l1 l0 ⟨he, _, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  simp only [evaluate, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨locals, by simp [evaluate], ?_⟩
  simp only
  split
  · rename_i cont brk heq; simpa [heq] using hsub
  · trivial

/-- `compile_correct`, case `Mark` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Mark]` at 97-99). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_mark {width : Nat} [NeZero width] {F : Type} :
    ∀ (p : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F),
      loopLiveCompileCorrectAt p v1 →
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.mark p : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.mark p : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro p v1 ih res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL] at hs
  simp only [evaluate] at he
  exact ih res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩

/-- `compile_correct`, case `Return` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Return]` at 101-110). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_return {width : Nat} [NeZero width] {F : Type} :
    ∀ (ns : List Nat) (v1 : LoopSemStateFiniteExact width F),
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.return ns : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.return ns : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro ns v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hg : LoopSemStateFiniteExact.getVars ns v1 with
  | none => simp [evaluate, hg] at he; exact absurd he.1.symm hne
  | some vs =>
    simp only [evaluate, hg, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hg' := getVars_locals_agree v1 locals ns vs (fun n hn w hw =>
      sptSubspt_inter_lookup hsub (sptMem_sptListInsert_of_mem n ns _ hn) w hw) hg
    exact ⟨(LoopSemStateFiniteExact.callEnv [] v1).locals, by simp [evaluate, hg', LoopSemStateFiniteExact.callEnv], rfl⟩

/-- `compile_correct`, case `Raise` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Raise]` at 112-116). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_raise {width : Nat} [NeZero width] {F : Type} :
    ∀ (x : Nat) (v1 : LoopSemStateFiniteExact width F),
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.raise x : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.raise x : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro x v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hx : sptLookup x v1.locals with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some w =>
    simp only [evaluate, hx, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hx' := sptSubspt_inter_lookup hsub ((sptMem_sptInsert x x () _).mpr (Or.inl rfl)) w hx
    exact ⟨(LoopSemStateFiniteExact.callEnv [] v1).locals, by simp [evaluate, hx', LoopSemStateFiniteExact.callEnv], rfl⟩

/-- `compile_correct`, case `Seq c1 c2` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Seq]` at 118-129), with the `evaluate_ind` hypotheses:
    the statement for `c1` at `v1`, and for `c2` at every `s1` with
    `fix_clock v1 (evaluate (c1,v1)) = (NONE, s1)`. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_seq {width : Nat} [NeZero width] {F : Type} :
    ∀ (c1 c2 : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F),
      loopLiveCompileCorrectAt c1 v1 →
      (∀ s1', fixClock v1 (evaluate c1 v1) = (none, s1') → loopLiveCompileCorrectAt c2 s1') →
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.seq c1 c2) v1 = (res, s1) ∧ res ≠ some .error ∧
        shrinkHOL lt (.seq c1 c2) l0 = (prog1, l1) ∧ sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro c1 c2 v1 ih1 ih2 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  rcases h2s : shrinkHOL lt c2 l0 with ⟨p2', lm⟩
  rcases h1s : shrinkHOL lt c1 lm with ⟨p1', l1'⟩
  rw [shrinkHOL, h2s] at hs
  simp only [h1s, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  rw [evaluate_seq] at he
  rcases hc1 : evaluate c1 v1 with ⟨r1, sm⟩
  rw [hc1] at he
  cases r1 with
  | none =>
    simp only at he
    obtain ⟨nl1, hn1, hp1⟩ := ih1 none sm lt locals p1' l1' lm ⟨hc1, by simp, h1s, hsub⟩
    have hfix : fixClock v1 (evaluate c1 v1) = (none, sm) := by rw [fix_clock_evaluate, hc1]
    obtain ⟨nl2, hn2, hp2⟩ := ih2 sm hfix res s1 lt nl1 p2' lm l0 ⟨he, hne, h2s, hp1⟩
    refine ⟨nl2, ?_, hp2⟩
    rw [evaluate_seq, hn1]
    exact hn2
  | some r =>
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨nl1, hn1, hp1⟩ := ih1 (some r) sm lt locals p1' l1' lm ⟨hc1, hne, h1s, hsub⟩
    refine ⟨nl1, ?_, ?_⟩
    · rw [evaluate_seq, hn1]
    · cases r <;> exact hp1

/-! ## `vars_of_exp` / `eval_lemma` helpers and the Assign/SetGlobal/LocValue cases -/

private theorem sptLookup_sptUnion' {α : Type} :
    ∀ (a b : Spt α) (k : Nat), sptLookup k (sptUnion a b) = (sptLookup k a).or (sptLookup k b)
  | .ln, b, k => by simp [sptUnion, sptLookup]
  | .ls v, b, k => by cases b <;> cases k <;> simp [sptUnion, sptLookup]
  | .bn l r, b, k => by
      cases b with
      | ln => cases k <;> simp [sptUnion, sptLookup]
      | ls v => cases k <;> simp [sptUnion, sptLookup]
      | bn l' r' =>
        cases k with
        | zero => simp [sptUnion, sptLookup]
        | succ k =>
          simp only [sptUnion, sptLookup]
          by_cases h : (k + 1) % 2 = 0 <;> simp [h, sptLookup_sptUnion']
      | bs l' v r' =>
        cases k with
        | zero => simp [sptUnion, sptLookup]
        | succ k =>
          simp only [sptUnion, sptLookup]
          by_cases h : (k + 1) % 2 = 0 <;> simp [h, sptLookup_sptUnion']
  | .bs l v r, b, k => by
      cases b with
      | ln => cases k <;> simp [sptUnion, sptLookup]
      | ls v' => cases k <;> simp [sptUnion, sptLookup]
      | bn l' r' =>
        cases k with
        | zero => simp [sptUnion, sptLookup]
        | succ k =>
          simp only [sptUnion, sptLookup]
          by_cases h : (k + 1) % 2 = 0 <;> simp [h, sptLookup_sptUnion']
      | bs l' v' r' =>
        cases k with
        | zero => simp [sptUnion, sptLookup]
        | succ k =>
          simp only [sptUnion, sptLookup]
          by_cases h : (k + 1) % 2 = 0 <;> simp [h, sptLookup_sptUnion']

private theorem sptMem_sptUnion' {α : Type} (a b : Spt α) (k : Nat) :
    sptMem k (sptUnion a b) ↔ sptMem k a ∨ sptMem k b := by
  simp only [sptMem, sptDomain, sptLookup_sptUnion']
  cases sptLookup k a <;> cases sptLookup k b <;> simp

private theorem sptLookup_sptDelete' {α : Type} :
    ∀ (t : Spt α) (n k : Nat), sptLookup k (sptDelete n t) = if k = n then none else sptLookup k t
  | .ln, n, k => by simp [sptDelete, sptLookup]
  | .ls v, n, k => by
      by_cases hn : n = 0 <;> by_cases hk : k = 0 <;> simp [sptDelete, sptLookup, hn, hk] <;> omega
  | .bn l r, n, k => by
      by_cases hn : n = 0
      · subst hn; by_cases hk : k = 0 <;> simp [sptDelete, sptLookup, hk]
      · simp only [sptDelete, hn, if_false]
        by_cases he : n % 2 = 0
        · simp only [he, if_true, sptLookup_sptMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk] <;> omega
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, hk, hke, if_false, if_true, sptLookup_sptDelete' l]
              by_cases h : k = n
              · subst h; simp
              · have : (k - 1) / 2 ≠ (n - 1) / 2 := by omega
                simp [h, this]
            · simp only [sptLookup, hk, hke, if_false]
              have : k ≠ n := by omega
              simp [this]
        · simp only [he, if_false, sptLookup_sptMkBN]
          by_cases hk : k = 0
          · simp [sptLookup, hk] <;> omega
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, hk, hke, if_false, if_true]
              have : k ≠ n := by omega
              simp [this]
            · simp only [sptLookup, hk, hke, if_false, sptLookup_sptDelete' r]
              by_cases h : k = n
              · subst h; simp
              · have : (k - 1) / 2 ≠ (n - 1) / 2 := by omega
                simp [h, this]
  | .bs l v r, n, k => by
      by_cases hn : n = 0
      · subst hn; by_cases hk : k = 0 <;> simp [sptDelete, sptLookup, hk]
      · simp only [sptDelete, hn, if_false]
        by_cases he : n % 2 = 0
        · simp only [he, if_true, sptLookup_sptMkBS]
          by_cases hk : k = 0
          · simp [sptLookup, hk] <;> omega
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, hk, hke, if_false, if_true, sptLookup_sptDelete' l]
              by_cases h : k = n
              · subst h; simp
              · have : (k - 1) / 2 ≠ (n - 1) / 2 := by omega
                simp [h, this]
            · simp only [sptLookup, hk, hke, if_false]
              have : k ≠ n := by omega
              simp [this]
        · simp only [he, if_false, sptLookup_sptMkBS]
          by_cases hk : k = 0
          · simp [sptLookup, hk] <;> omega
          · by_cases hke : k % 2 = 0
            · simp only [sptLookup, hk, hke, if_false, if_true]
              have : k ≠ n := by omega
              simp [this]
            · simp only [sptLookup, hk, hke, if_false, sptLookup_sptDelete' r]
              by_cases h : k = n
              · subst h; simp
              · have : (k - 1) / 2 ≠ (n - 1) / 2 := by omega
                simp [h, this]

mutual
private theorem varsOfExp_mem_iff {width : Nat} [NeZero width] :
    ∀ (e : HolLoopExp width) (l : NumSet) (k : Nat),
      sptMem k (varsOfExpHOL e l) ↔ sptMem k (varsOfExpHOL e .ln) ∨ sptMem k l
  | .var n, l, k => by
      simp only [varsOfExpHOL, sptMem_sptInsert]
      simp [sptMem, sptDomain, sptLookup]
  | .const _, l, k => by simp [varsOfExpHOL, sptMem, sptDomain]
  | .lookup _, l, k => by simp [varsOfExpHOL, sptMem, sptDomain]
  | .baseAddr, l, k => by simp [varsOfExpHOL, sptMem, sptDomain]
  | .topAddr, l, k => by simp [varsOfExpHOL, sptMem, sptDomain]
  | .load a, l, k => by simp only [varsOfExpHOL]; exact varsOfExp_mem_iff a l k
  | .op _ es, l, k => by simp only [varsOfExpHOL]; exact varsOfExpList_mem_iff es l k
  | .shift _ a b, l, k => by
      simp only [varsOfExpHOL]
      rw [varsOfExp_mem_iff a (varsOfExpHOL b l), varsOfExp_mem_iff b l,
        varsOfExp_mem_iff a (varsOfExpHOL b .ln)]
      simp only [or_assoc]
private theorem varsOfExpList_mem_iff {width : Nat} [NeZero width] :
    ∀ (es : List (HolLoopExp width)) (l : NumSet) (k : Nat),
      sptMem k (varsOfExpListHOL es l) ↔ sptMem k (varsOfExpListHOL es .ln) ∨ sptMem k l
  | [], l, k => by simp [varsOfExpListHOL, sptMem, sptDomain]
  | e :: es, l, k => by
      simp only [varsOfExpListHOL]
      rw [varsOfExp_mem_iff e (varsOfExpListHOL es l), varsOfExpList_mem_iff es l,
        varsOfExp_mem_iff e (varsOfExpListHOL es .ln)]
      simp only [or_assoc]
end

/-- Exact HOL `vars_of_exp_acc` (`loop_liveProofScript.sml:339-342`):
    `∀exp l. domain (vars_of_exp exp l) = domain (union (vars_of_exp exp LN) l)`,
    with `domain` as the predicate `sptDomain` and `union` as `sptUnion`. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "vars_of_exp_acc"
  (words_as_type_indexed_bitvec)]
theorem vars_of_exp_acc {width : Nat} [NeZero width] :
    ∀ (exp : HolLoopExp width) (l : NumSet),
      sptDomain (varsOfExpHOL exp l) = sptDomain (sptUnion (varsOfExpHOL exp .ln) l) := by
  intro exp l
  funext k
  apply propext
  have h := varsOfExp_mem_iff exp l k
  have h2 := sptMem_sptUnion' (varsOfExpHOL exp .ln) l k
  simp only [sptMem] at h h2
  rw [h, h2]

private theorem numSet_lookup_of_mem {t : NumSet} {k : Nat} (h : sptMem k t) :
    sptLookup k t = some () := by
  simp only [sptMem, sptDomain] at h
  cases hk : sptLookup k t with
  | none => simp [hk] at h
  | some u => cases u; rfl

/-- Exact HOL `vars_of_exp_mono` (`loop_liveProofScript.sml:400-401`):
    `∀exp l. subspt l (vars_of_exp exp l)`. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "vars_of_exp_mono"
  (words_as_type_indexed_bitvec)]
theorem vars_of_exp_mono {width : Nat} [NeZero width] :
    ∀ (exp : HolLoopExp width) (l : NumSet), sptSubspt l (varsOfExpHOL exp l) := by
  intro exp l k hk
  have hm : sptMem k (varsOfExpHOL exp l) := (varsOfExp_mem_iff exp l k).mpr (Or.inr hk)
  exact ⟨hm, by rw [numSet_lookup_of_mem hm, numSet_lookup_of_mem hk]⟩

private theorem theWords_some_mem {width : Nat} [NeZero width] :
    ∀ (xs : List (Option (WordLocW width))) (ws : List (BitVec width)),
      theWords xs = some ws → ∀ x ∈ xs, ∃ w, x = some (.word w)
  | [], _, _, x, hx => by simp at hx
  | y :: ys, ws, h, x, hx => by
      simp only [theWords] at h
      cases hy : y with
      | none => simp [hy] at h
      | some yv =>
        cases yv with
        | loc _ _ => simp [hy] at h
        | word a =>
          cases hr : theWords ys with
          | none => simp [hy, hr] at h
          | some as =>
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨a, hy⟩
            · exact theWords_some_mem ys as hr x hx

private theorem eval_some_touched_defined {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) :
    ∀ (e : HolLoopExp width) (w : WordLocW width), eval s e = some w →
      ∀ n ∈ holLoopLocalsTouched e, (sptLookup n s.locals).isSome
  | .var v, w, h, n, hn => by
      simp only [holLoopLocalsTouched, List.mem_singleton] at hn
      subst hn; simp only [eval] at h; simp [h]
  | .const _, _, _, n, hn => by simp [holLoopLocalsTouched] at hn
  | .lookup _, _, _, n, hn => by simp [holLoopLocalsTouched] at hn
  | .baseAddr, _, _, n, hn => by simp [holLoopLocalsTouched] at hn
  | .topAddr, _, _, n, hn => by simp [holLoopLocalsTouched] at hn
  | .load a, w, h, n, hn => by
      simp only [holLoopLocalsTouched] at hn
      simp only [eval] at h
      split at h
      · rename_i x hx; exact eval_some_touched_defined s a _ hx n hn
      · cases h
  | .shift _ a b, w, h, n, hn => by
      simp only [holLoopLocalsTouched, List.mem_append] at hn
      simp only [eval] at h
      split at h
      · rename_i x y ha hb
        rcases hn with hn | hn
        · exact eval_some_touched_defined s a _ ha n hn
        · exact eval_some_touched_defined s b _ hb n hn
      · cases h
  | .op o es, w, h, n, hn => by
      rw [holLoopLocalsTouched_op] at hn
      obtain ⟨vs, hvs, hn⟩ := List.mem_flatten.mp hn
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvs
      simp only [eval] at h
      split at h
      · rename_i ws hws
        have hmem : eval s e ∈ es.attach.map (fun ⟨e, _⟩ => eval s e) :=
          List.mem_map.mpr ⟨⟨e, he⟩, List.mem_attach _ _, rfl⟩
        obtain ⟨x, hx⟩ := theWords_some_mem _ ws hws _ hmem
        exact eval_some_touched_defined s e _ hx n hn
      · cases h
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem he; omega)

private theorem mem_varsOfExpList_of_mem {width : Nat} [NeZero width] (n : Nat)
    (e : HolLoopExp width) {es0 : List (HolLoopExp width)} (_he : e ∈ es0)
    (h : ∀ l, sptMem n (varsOfExpHOL e l)) :
    ∀ (es : List (HolLoopExp width)) (l : NumSet), e ∈ es → sptMem n (varsOfExpListHOL es l)
  | [], _, he => by simp at he
  | x :: xs, l, he => by
      simp only [varsOfExpListHOL]
      rcases List.mem_cons.mp he with rfl | he'
      · exact h _
      · exact (varsOfExp_mem_iff x _ n).mpr (Or.inr (mem_varsOfExpList_of_mem n e _he h xs l he'))

private theorem touched_mem_varsOfExp {width : Nat} [NeZero width] :
    ∀ (e : HolLoopExp width) (l : NumSet) (n : Nat), n ∈ holLoopLocalsTouched e →
      sptMem n (varsOfExpHOL e l)
  | .var v, l, n, hn => by
      simp only [holLoopLocalsTouched, List.mem_singleton] at hn
      subst hn; simp only [varsOfExpHOL]; exact (sptMem_sptInsert _ _ _ _).mpr (Or.inl rfl)
  | .const _, _, n, hn => by simp [holLoopLocalsTouched] at hn
  | .lookup _, _, n, hn => by simp [holLoopLocalsTouched] at hn
  | .baseAddr, _, n, hn => by simp [holLoopLocalsTouched] at hn
  | .topAddr, _, n, hn => by simp [holLoopLocalsTouched] at hn
  | .load a, l, n, hn => by
      simp only [holLoopLocalsTouched] at hn; simp only [varsOfExpHOL]
      exact touched_mem_varsOfExp a l n hn
  | .shift _ a b, l, n, hn => by
      simp only [holLoopLocalsTouched, List.mem_append] at hn; simp only [varsOfExpHOL]
      rcases hn with hn | hn
      · exact touched_mem_varsOfExp a _ n hn
      · exact (varsOfExp_mem_iff a _ n).mpr (Or.inr (touched_mem_varsOfExp b l n hn))
  | .op o es, l, n, hn => by
      rw [holLoopLocalsTouched_op] at hn
      obtain ⟨vs, hvs, hn⟩ := List.mem_flatten.mp hn
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvs
      simp only [varsOfExpHOL]
      exact mem_varsOfExpList_of_mem n e he (fun l' => touched_mem_varsOfExp e l' n hn) es l he
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem he; omega)

/-- Exact HOL `eval_lemma'` (`loop_liveProofScript.sml:416-420`):
    `∀s exp w l. eval s exp = SOME w ∧ subspt s.locals locals ⇒
      eval (s with locals := locals) exp = SOME w`.  HOL's bound `l` does not
    occur in the body, so HOL infers it at a free type variable (here `β`); the
    free HOL variable `locals` is universally quantified last. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "eval_lemma'"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem eval_lemma' {width : Nat} [NeZero width] {F : Type} :
    ∀ (s : LoopSemStateFiniteExact width F) (exp : HolLoopExp width) (w : WordLocW width)
      {β : Type} (_l : β) (locals : Spt (WordLocW width)),
      eval s exp = some w ∧ sptSubspt s.locals locals →
      eval { s with locals := locals } exp = some w := by
  intro s exp w β _l locals ⟨he, hsub⟩
  rw [LoopSemStateFiniteExact.locals_touched_eq_eval_eq s exp { s with locals := locals }
    ⟨rfl, rfl, rfl, rfl, rfl, fun n hn => ?_⟩, he]
  have hdef := eval_some_touched_defined s exp w he n hn
  exact ((hsub n hdef).2).symm

/-- Exact HOL `eval_lemma` (`loop_liveProofScript.sml:443-447`):
    `∀s exp w l. eval s exp = SOME w ∧
      subspt (inter s.locals (vars_of_exp exp l)) locals ⇒
      eval (s with locals := locals) exp = SOME w`, the free HOL variable
    `locals` universally quantified last. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "eval_lemma"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem eval_lemma {width : Nat} [NeZero width] {F : Type} :
    ∀ (s : LoopSemStateFiniteExact width F) (exp : HolLoopExp width) (w : WordLocW width)
      (l : NumSet) (locals : Spt (WordLocW width)),
      eval s exp = some w ∧ sptSubspt (sptInter s.locals (varsOfExpHOL exp l)) locals →
      eval { s with locals := locals } exp = some w := by
  intro s exp w l locals ⟨he, hsub⟩
  rw [LoopSemStateFiniteExact.locals_touched_eq_eval_eq s exp { s with locals := locals }
    ⟨rfl, rfl, rfl, rfl, rfl, fun n hn => ?_⟩, he]
  have hdef : (sptLookup n s.locals).isSome = true := eval_some_touched_defined s exp w he n hn
  have hv : (sptLookup n (varsOfExpHOL exp l)).isSome = true := touched_mem_varsOfExp exp l n hn
  have hm : sptMem n (sptInter s.locals (varsOfExpHOL exp l)) := by
    simp only [sptMem, sptDomain, sptLookup_sptInter, hv, if_true]; exact hdef
  rw [(hsub n hm).2, sptLookup_sptInter, if_pos hv]

private theorem subspt_of_lookup {α : Type} {a b : Spt α}
    (h : ∀ k, sptMem k a → sptLookup k b = sptLookup k a) : sptSubspt a b := by
  intro k hk
  refine ⟨?_, h k hk⟩
  simp only [sptMem, sptDomain] at hk ⊢
  rw [h k (by simpa [sptMem, sptDomain] using hk)]; exact hk

private theorem mem_inter_iff {α β : Type} (a : Spt α) (l : Spt β) (k : Nat) :
    sptMem k (sptInter a l) ↔ sptMem k a ∧ sptMem k l := by
  simp only [sptMem, sptDomain, sptLookup_sptInter]
  by_cases h : (sptLookup k l).isSome = true <;> simp [h]

private theorem subspt_inter_apply {width : Nat} [NeZero width]
    {a b : Spt (WordLocW width)} {l : NumSet} (h : sptSubspt (sptInter a l) b) {k : Nat}
    (ha : sptMem k a) (hl : sptMem k l) : sptLookup k b = sptLookup k a := by
  rw [(h k ((mem_inter_iff a l k).mpr ⟨ha, hl⟩)).2, sptLookup_sptInter,
    if_pos (show (sptLookup k l).isSome = true from hl)]

/-- `compile_correct`, case `Assign` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Assign]` at 490-509). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_assign {width : Nat} [NeZero width] {F : Type} :
    ∀ (n : Nat) (x : HolLoopExp width) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.assign n x : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.assign n x : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro n x v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  cases hx : eval v1 x with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some w =>
  simp only [evaluate, hx, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  cases hn : sptLookup n l0 with
  | none =>
    simp only [shrinkHOL, hn, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨locals, by simp [evaluate, setVar], ?_⟩
    refine subspt_of_lookup fun k hk => ?_
    obtain ⟨hka, hkl⟩ := (mem_inter_iff _ _ k).mp hk
    have hkn : k ≠ n := fun e => by subst e; simp [sptMem, sptDomain, hn] at hkl
    have hka' : sptMem k v1.locals := by
      simpa [setVar, sptMem, sptDomain, sptLookup_sptInsert, hkn] using hka
    rw [subspt_inter_apply hsub hka' hkl, sptLookup_sptInter,
      if_pos (show (sptLookup k l0).isSome = true from hkl)]
    simp [setVar, sptLookup_sptInsert, hkn]
  | some u =>
    simp only [shrinkHOL, hn, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hx' := eval_lemma v1 x w (sptDelete n l0) locals ⟨hx, hsub⟩
    refine ⟨sptInsert n w locals, by simp [evaluate, hx', setVar], ?_⟩
    refine subspt_of_lookup fun k hk => ?_
    obtain ⟨hka, hkl⟩ := (mem_inter_iff _ _ k).mp hk
    rw [sptLookup_sptInter, if_pos (show (sptLookup k l0).isSome = true from hkl)]
    by_cases hkn : k = n
    · subst hkn; simp [setVar, sptLookup_sptInsert]
    · have hka' : sptMem k v1.locals := by
        simpa [setVar, sptMem, sptDomain, sptLookup_sptInsert, hkn] using hka
      have hkd : sptMem k (sptDelete n l0) := by
        simp only [sptMem, sptDomain, sptLookup_sptDelete', hkn, if_false]; exact hkl
      have hkv := (vars_of_exp_mono x (sptDelete n l0) k hkd).1
      simp only [setVar, sptLookup_sptInsert, hkn, if_false]
      exact subspt_inter_apply hsub hka' hkv

/-- `compile_correct`, case `SetGlobal` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[SetGlobal]` at 511-519). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_setGlobal {width : Nat} [NeZero width] {F : Type} :
    ∀ (g : BitVec 5) (x : HolLoopExp width) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.setGlobal g x : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.setGlobal g x : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro g x v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hx : eval v1 x with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some w =>
  simp only [evaluate, hx, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hx' := eval_lemma v1 x w l0 locals ⟨hx, hsub⟩
  refine ⟨locals, by simp [evaluate, hx', setGlobals], ?_⟩
  refine subspt_of_lookup fun k hk => ?_
  obtain ⟨hka, hkl⟩ := (mem_inter_iff _ _ k).mp hk
  rw [sptLookup_sptInter, if_pos (show (sptLookup k l0).isSome = true from hkl)]
  exact subspt_inter_apply hsub hka ((vars_of_exp_mono x l0 k hkl).1)

/-- `compile_correct`, case `LocValue` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[LocValue]` at 521-532). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_locValue {width : Nat} [NeZero width] {F : Type} :
    ∀ (r m : Nat) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.locValue r m : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.locValue r m : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro r m v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  by_cases hc : (sptLookup m v1.code).isSome = true
  · simp only [evaluate, hc, if_true, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hr : sptLookup r l0 with
    | none =>
      simp only [shrinkHOL, hr, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨locals, by simp [evaluate, setVar], ?_⟩
      refine subspt_of_lookup fun k hk => ?_
      obtain ⟨hka, hkl⟩ := (mem_inter_iff _ _ k).mp hk
      have hkn : k ≠ r := fun e => by subst e; simp [sptMem, sptDomain, hr] at hkl
      have hka' : sptMem k v1.locals := by
        simpa [setVar, sptMem, sptDomain, sptLookup_sptInsert, hkn] using hka
      rw [subspt_inter_apply hsub hka' hkl, sptLookup_sptInter,
        if_pos (show (sptLookup k l0).isSome = true from hkl)]
      simp [setVar, sptLookup_sptInsert, hkn]
    | some u =>
      simp only [shrinkHOL, hr, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨sptInsert r (.loc m 0) locals, by simp [evaluate, hc, setVar], ?_⟩
      refine subspt_of_lookup fun k hk => ?_
      obtain ⟨hka, hkl⟩ := (mem_inter_iff _ _ k).mp hk
      rw [sptLookup_sptInter, if_pos (show (sptLookup k l0).isSome = true from hkl)]
      by_cases hkn : k = r
      · subst hkn; simp [setVar, sptLookup_sptInsert]
      · have hka' : sptMem k v1.locals := by
          simpa [setVar, sptMem, sptDomain, sptLookup_sptInsert, hkn] using hka
        have hkd : sptMem k (sptDelete r l0) := by
          simp only [sptMem, sptDomain, sptLookup_sptDelete', hkn, if_false]; exact hkl
        simp only [setVar, sptLookup_sptInsert, hkn, if_false]
        exact subspt_inter_apply hsub hka' hkd
  · simp [evaluate, hc] at he
    exact absurd he.1.symm hne

/-! ## Store / Load cases -/

private theorem mem_insert_self' (k : Nat) (t : NumSet) : sptMem k (sptInsert k () t) :=
  (sptMem_sptInsert k k () t).mpr (Or.inl rfl)

private theorem mem_insert_of' {k : Nat} (x : Nat) {t : NumSet} (h : sptMem k t) :
    sptMem k (sptInsert x () t) :=
  (sptMem_sptInsert k x () t).mpr (Or.inr h)

private theorem lookup_of_subspt {width : Nat} [NeZero width]
    {a b : Spt (WordLocW width)} {l : NumSet} (h : sptSubspt (sptInter a l) b) {k : Nat}
    (hl : sptMem k l) {w : WordLocW width} (ha : sptLookup k a = some w) : sptLookup k b = some w := by
  rw [subspt_inter_apply h (by simp [sptMem, sptDomain, ha]) hl, ha]

private theorem post_none_same {width : Nat} [NeZero width]
    {a b : Spt (WordLocW width)} {l0 l1 : NumSet} (h : sptSubspt (sptInter a l1) b)
    (hsub : ∀ k, sptMem k l0 → sptMem k l1) : sptSubspt (sptInter a l0) b :=
  subspt_of_lookup fun k hk => by
    obtain ⟨hka, hkl⟩ := (mem_inter_iff _ _ k).mp hk
    rw [sptLookup_sptInter, if_pos (show (sptLookup k l0).isSome = true from hkl)]
    exact subspt_inter_apply h hka (hsub k hkl)

private theorem post_setVar {width : Nat} [NeZero width]
    {a b : Spt (WordLocW width)} {l0 l1 : NumSet} (y : Nat) (val : WordLocW width)
    (h : sptSubspt (sptInter a l1) b)
    (hsub : ∀ k, k ≠ y → sptMem k l0 → sptMem k l1) :
    sptSubspt (sptInter (sptInsert y val a) l0) (sptInsert y val b) :=
  subspt_of_lookup fun k hk => by
    obtain ⟨hka, hkl⟩ := (mem_inter_iff _ _ k).mp hk
    rw [sptLookup_sptInter, if_pos (show (sptLookup k l0).isSome = true from hkl)]
    by_cases hky : k = y
    · subst hky; simp [sptLookup_sptInsert]
    · have hka' : sptMem k a := by simpa [sptMem, sptDomain, sptLookup_sptInsert, hky] using hka
      simp only [sptLookup_sptInsert, hky, if_false]
      exact subspt_inter_apply h hka' (hsub k hky hkl)

/-- `compile_correct`, case `Store` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Store]` at 705-718). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_store {width : Nat} [NeZero width] {F : Type} :
    ∀ (e : HolLoopExp width) (n : Nat) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.store e n : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.store e n : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro e n v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hx : eval v1 e with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some a =>
  cases a with
  | loc _ _ => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | word adr =>
  cases hn : sptLookup n v1.locals with
  | none => simp [evaluate, hx, hn] at he; exact absurd he.1.symm hne
  | some w =>
  by_cases hd : v1.mdomain adr = true
  · simp only [evaluate, hx, hn, memStore, hd, if_true, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hx' := eval_lemma v1 e (.word adr) (sptInsert n () l0) locals ⟨hx, hsub⟩
    have hn' := lookup_of_subspt hsub
      ((vars_of_exp_mono e _ n (mem_insert_self' n l0)).1) hn
    refine ⟨locals, by simp [evaluate, hx', hn', memStore, hd], ?_⟩
    exact post_none_same hsub fun k hk => (vars_of_exp_mono e _ k (mem_insert_of' n hk)).1
  · simp [evaluate, hx, hn, memStore, hd] at he; exact absurd he.1.symm hne

/-- `compile_correct`, case `Store32` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Store32]` at 720-727). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_store32 {width : Nat} [NeZero width] {F : Type} :
    ∀ (a w : Nat) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.store32 a w : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.store32 a w : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro a w v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases ha : sptLookup a v1.locals with
  | none => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | some av =>
  cases hw : sptLookup w v1.locals with
  | none => cases av <;> simp [evaluate, ha, hw] at he <;> exact absurd he.1.symm hne
  | some wv =>
  have ha' := lookup_of_subspt hsub (mem_insert_self' a _) ha
  have hw' := lookup_of_subspt hsub (mem_insert_of' a (mem_insert_self' w l0)) hw
  cases av with
  | loc _ _ => simp [evaluate, ha, hw] at he; exact absurd he.1.symm hne
  | word x =>
  cases wv with
  | loc _ _ => simp [evaluate, ha, hw] at he; exact absurd he.1.symm hne
  | word y =>
  cases hm : memStore32Exact v1.memory v1.mdomain v1.be x (y.setWidth 32) with
  | none => simp [evaluate, ha, hw, hm] at he; exact absurd he.1.symm hne
  | some m =>
  simp only [evaluate, ha, hw, hm, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨locals, by simp [evaluate, ha', hw', hm], ?_⟩
  exact post_none_same hsub fun k hk => mem_insert_of' a (mem_insert_of' w hk)

/-- `compile_correct`, case `StoreByte` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[StoreByte]` at 729-736). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_storeByte {width : Nat} [NeZero width] {F : Type} :
    ∀ (a w : Nat) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.storeByte a w : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.storeByte a w : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro a w v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases ha : sptLookup a v1.locals with
  | none => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | some av =>
  cases hw : sptLookup w v1.locals with
  | none => cases av <;> simp [evaluate, ha, hw] at he <;> exact absurd he.1.symm hne
  | some wv =>
  have ha' := lookup_of_subspt hsub (mem_insert_self' a _) ha
  have hw' := lookup_of_subspt hsub (mem_insert_of' a (mem_insert_self' w l0)) hw
  cases av with
  | loc _ _ => simp [evaluate, ha, hw] at he; exact absurd he.1.symm hne
  | word x =>
  cases wv with
  | loc _ _ => simp [evaluate, ha, hw] at he; exact absurd he.1.symm hne
  | word y =>
  cases hm : memStoreByteAuxExact v1.memory v1.mdomain v1.be x (y.setWidth 8) with
  | none => simp [evaluate, ha, hw, hm] at he; exact absurd he.1.symm hne
  | some m =>
  simp only [evaluate, ha, hw, hm, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨locals, by simp [evaluate, ha', hw', hm], ?_⟩
  exact post_none_same hsub fun k hk => mem_insert_of' a (mem_insert_of' w hk)

/-- `compile_correct`, case `Load32` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Load32]` at 738-745). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_load32 {width : Nat} [NeZero width] {F : Type} :
    ∀ (a y : Nat) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.load32 a y : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.load32 a y : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro a y v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases ha : sptLookup a v1.locals with
  | none => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | some av =>
  cases av with
  | loc _ _ => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | word x =>
  have ha' := lookup_of_subspt hsub (mem_insert_self' a _) ha
  cases hm : memLoad32Exact v1.memory v1.mdomain v1.be x with
  | none => simp [evaluate, ha, hm] at he; exact absurd he.1.symm hne
  | some b =>
  simp only [evaluate, ha, hm, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨sptInsert y (.word (b.setWidth width)) locals, by simp [evaluate, ha', hm, setVar], ?_⟩
  refine post_setVar y _ hsub fun k hky hk => mem_insert_of' a ?_
  simp only [sptMem, sptDomain, sptLookup_sptDelete', hky, if_false]; exact hk

/-- `compile_correct`, case `LoadByte` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[LoadByte]` at 747-754). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_loadByte {width : Nat} [NeZero width] {F : Type} :
    ∀ (a y : Nat) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.loadByte a y : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.loadByte a y : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro a y v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases ha : sptLookup a v1.locals with
  | none => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | some av =>
  cases av with
  | loc _ _ => simp [evaluate, ha] at he; exact absurd he.1.symm hne
  | word x =>
  have ha' := lookup_of_subspt hsub (mem_insert_self' a _) ha
  cases hm : memLoadByteAuxExact v1.memory v1.mdomain v1.be x with
  | none => simp [evaluate, ha, hm] at he; exact absurd he.1.symm hne
  | some b =>
  simp only [evaluate, ha, hm, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨sptInsert y (.word (b.setWidth width)) locals, by simp [evaluate, ha', hm, setVar], ?_⟩
  refine post_setVar y _ hsub fun k hky hk => mem_insert_of' a ?_
  simp only [sptMem, sptDomain, sptLookup_sptDelete', hky, if_false]; exact hk

/-! ## Primitive / Arith / ShMem / FFI cases -/

/-- Exact HOL `dom_vars_of_exp_in` (`loop_liveProofScript.sml:792-793`):
    `v ∈ domain l ⇒ v ∈ domain (vars_of_exp x l)`, its free variables universally
    quantified in order of occurrence. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "dom_vars_of_exp_in"
  (words_as_type_indexed_bitvec)]
theorem dom_vars_of_exp_in {width : Nat} [NeZero width] :
    ∀ (v : Nat) (l : NumSet) (x : HolLoopExp width), sptMem v l → sptMem v (varsOfExpHOL x l) :=
  fun v l x h => (vars_of_exp_mono x l v h).1

/-- Exact HOL `get_vars_subspt` (`loop_liveProofScript.sml:828-832`, `[local]`):
    `∀rhss ws s extra locals. get_vars rhss s = SOME ws ∧
      subspt (inter s.locals (list_insert rhss extra)) locals ⇒
      get_vars rhss (s with locals := locals) = SOME ws`. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "get_vars_subspt"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem get_vars_subspt {width : Nat} [NeZero width] {F : Type} :
    ∀ (rhss : List Nat) (ws : List (WordLocW width)) (s : LoopSemStateFiniteExact width F)
      (extra : NumSet) (locals : Spt (WordLocW width)),
      LoopSemStateFiniteExact.getVars rhss s = some ws ∧
        sptSubspt (sptInter s.locals (sptListInsert rhss extra)) locals →
      LoopSemStateFiniteExact.getVars rhss { s with locals := locals } = some ws :=
  fun rhss ws s extra locals ⟨hg, hsub⟩ =>
    getVars_locals_agree s locals rhss ws (fun n hn _w hw =>
      lookup_of_subspt hsub (sptMem_sptListInsert_of_mem n rhss extra hn) hw) hg

private theorem sptLookup_sptListDelete {α : Type} :
    ∀ (ks : List Nat) (t : Spt α) (k : Nat),
      sptLookup k (sptListDelete ks t) = if k ∈ ks then none else sptLookup k t
  | [], t, k => by simp [sptListDelete]
  | x :: xs, t, k => by
      simp only [sptListDelete, sptLookup_sptListDelete xs, sptLookup_sptDelete', List.mem_cons]
      by_cases h1 : k = x <;> by_cases h2 : k ∈ xs <;> simp [h1, h2]

private theorem holAlookup_zip_none {β : Type} :
    ∀ (xs : List Nat) (ys : List β) (k : Nat), xs.length = ys.length →
      holAlookup (xs.zip ys) k = none → k ∉ xs
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, h, _ => by simp at h
  | x :: xs, y :: ys, k, h, hz => by
      simp only [List.zip_cons_cons, holAlookup] at hz
      split at hz
      · cases hz
      · rename_i hne
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hne e.symm, holAlookup_zip_none xs ys k (by simpa using h) hz⟩

/-- `compile_correct`, case `Primitive` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Primitive]` at 844-856). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_primitive {width : Nat} [NeZero width] {F : Type} :
    ∀ (lhss : List Nat) (pop : PrimOp) (rhss : List Nat) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.primitive lhss pop rhss : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧ shrinkHOL lt (.primitive lhss pop rhss : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro lhss pop rhss v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hg : LoopSemStateFiniteExact.getVars rhss v1 with
  | none => simp [evaluate, hg] at he; exact absurd he.1.symm hne
  | some ws =>
  cases hp : loopPrimop pop ws with
  | none => simp [evaluate, hg, hp] at he; exact absurd he.1.symm hne
  | some rws =>
  by_cases hl : lhss.length = rws.length
  · simp only [evaluate, hg, hp, hl, if_true, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hg' := get_vars_subspt rhss ws v1 _ locals ⟨hg, hsub⟩
    refine ⟨sptAlistInsert lhss rws locals, by simp [evaluate, hg', hp, hl, setVars], ?_⟩
    refine subspt_of_lookup fun k hk => ?_
    obtain ⟨hka, hkl⟩ := (mem_inter_iff _ _ k).mp hk
    rw [sptLookup_sptInter, if_pos (show (sptLookup k l0).isSome = true from hkl)]
    simp only [setVars]
    rw [lookup_alist_insert_any, lookup_alist_insert_any]
    cases hz : holAlookup (lhss.zip rws) k with
    | some _ => rfl
    | none =>
      simp only
      have hkn := holAlookup_zip_none lhss rws k hl hz
      have hka' : sptMem k v1.locals := by
        simpa [setVars, sptMem, sptDomain, lookup_alist_insert_any, hz] using hka
      have hkd : sptMem k (sptListDelete lhss l0) := by
        simp only [sptMem, sptDomain, sptLookup_sptListDelete, hkn, if_false]; exact hkl
      exact subspt_inter_apply hsub hka' (sptMem_sptListInsert_of k rhss _ hkd)
  · simp [evaluate, hg, hp, hl] at he; exact absurd he.1.symm hne

/-- `compile_correct`, case `Arith a` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[Arith]` at 781-790). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_arith {width : Nat} [NeZero width] {F : Type} :
    ∀ (a : LoopArith) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.arith a : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧
        shrinkHOL lt (.arith a : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro a v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hA : LoopSemStateFiniteExact.loopArith v1 a with
  | none => simp [evaluate, hA] at he; exact absurd he.1.symm hne
  | some s' =>
  simp only [evaluate, hA, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hdel : ∀ {k x : Nat} {t : NumSet}, k ≠ x → sptMem k t → sptMem k (sptDelete x t) :=
    fun hkx h => by simp only [sptMem, sptDomain, sptLookup_sptDelete', hkx, if_false]; exact h
  cases a with
  | div r1 r2 r3 =>
    simp only [arithVarsHOL] at hsub
    simp only [LoopSemStateFiniteExact.loopArith] at hA
    split at hA
    · rename_i q w2 h3 h2
      by_cases hq0 : q = 0
      · rw [if_neg (by simpa using hq0)] at hA; cases hA
      have hq : q ≠ 0 := hq0
      · rw [if_pos hq, Option.some.injEq] at hA
        subst hA
        have h3' := lookup_of_subspt hsub (mem_insert_of' r2 (mem_insert_self' r3 _)) h3
        have h2' := lookup_of_subspt hsub (mem_insert_self' r2 _) h2
        refine ⟨sptInsert r1 (.word (w2 / q)) locals,
          by
            have hq0' : ¬ q = 0#width := hq0
            simp [evaluate, LoopSemStateFiniteExact.loopArith, h3', h2', hq0', setVar], ?_⟩
        exact post_setVar r1 _ hsub fun k hk hl =>
          mem_insert_of' r2 (mem_insert_of' r3 (hdel hk hl))
    · cases hA
  | longMul r1 r2 r3 r4 =>
    simp only [arithVarsHOL] at hsub
    simp only [LoopSemStateFiniteExact.loopArith] at hA
    split at hA
    · rename_i w3 w4 h3 h4
      simp only [Option.some.injEq] at hA
      subst hA
      have h3' := lookup_of_subspt hsub (mem_insert_self' r3 _) h3
      have h4' := lookup_of_subspt hsub (mem_insert_of' r3 (mem_insert_self' r4 _)) h4
      refine ⟨sptInsert r2 (.word (BitVec.ofNat width (w3.toNat * w4.toNat)))
          (sptInsert r1 (.word (BitVec.ofNat width (w3.toNat * w4.toNat / 2 ^ width))) locals),
        by simp [evaluate, LoopSemStateFiniteExact.loopArith, h3', h4', setVar], ?_⟩
      refine post_setVar (l1 := sptDelete r2 l0) r2 _ ?_ fun k hk hl => hdel hk hl
      exact post_setVar r1 _ hsub fun k hk hl => by
        have hk2 : k ≠ r2 := fun e => by
          subst e; simp [sptMem, sptDomain, sptLookup_sptDelete'] at hl
        have hl0 : sptMem k l0 := by
          simpa [sptMem, sptDomain, sptLookup_sptDelete', hk2] using hl
        exact mem_insert_of' r3 (mem_insert_of' r4 (hdel hk (hdel hk2 hl0)))
    · cases hA
  | longDiv r1 r2 r3 r4 r5 =>
    simp only [arithVarsHOL] at hsub
    simp only [LoopSemStateFiniteExact.loopArith] at hA
    split at hA
    · rename_i w3 w4 w5 h3 h4 h5
      split at hA
      · rename_i hcond
        simp only [Option.some.injEq] at hA
        subst hA
        have h3' := lookup_of_subspt hsub (mem_insert_self' r3 _) h3
        have h4' := lookup_of_subspt hsub (mem_insert_of' r3 (mem_insert_self' r4 _)) h4
        have h5' := lookup_of_subspt hsub
          (mem_insert_of' r3 (mem_insert_of' r4 (mem_insert_self' r5 _))) h5
        refine ⟨_, by simp [evaluate, LoopSemStateFiniteExact.loopArith, h3', h4', h5', hcond, setVar]; rfl, ?_⟩
        refine post_setVar (l1 := sptDelete r1 l0) r1 _ ?_ fun k hk hl => hdel hk hl
        exact post_setVar r2 _ hsub fun k hk hl => by
          have hk1 : k ≠ r1 := fun e => by
            subst e; simp [sptMem, sptDomain, sptLookup_sptDelete'] at hl
          have hl0 : sptMem k l0 := by
            simpa [sptMem, sptDomain, sptLookup_sptDelete', hk1] using hl
          exact mem_insert_of' r3 (mem_insert_of' r4 (mem_insert_of' r5 (hdel hk1 (hdel hk hl0))))
      · cases hA
    · cases hA

private theorem shMemLoad_frame {width : Nat} [NeZero width] {F : Type}
    (v : Nat) (addr : BitVec width) (nb : Nat) (s : LoopSemStateFiniteExact width F)
    (L : Spt (WordLocW width)) :
    (∃ val ffi', shMemLoad v addr nb s = (none, { setVar v val s with ffi := ffi' }) ∧
        shMemLoad v addr nb { s with locals := L } =
          (none, { setVar v val { s with locals := L } with ffi := ffi' })) ∨
      (∃ e, shMemLoad v addr nb s = (some (.finalFfi e), LoopSemStateFiniteExact.callEnv [] s) ∧
        shMemLoad v addr nb { s with locals := L } =
          (some (.finalFfi e), LoopSemStateFiniteExact.callEnv [] { s with locals := L })) ∨
      (shMemLoad v addr nb s).1 = some .error := by
  unfold shMemLoad
  by_cases hnb : nb = 0
  · simp only [hnb, if_true]
    by_cases hd : s.shMdomain addr = true
    · simp only [hd, if_true]
      cases hf : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 0]
          (panWordToBytesHOL addr false) with
      | final e => exact Or.inr (Or.inl ⟨e, rfl, rfl⟩)
      | ret f b => exact Or.inl ⟨_, f, rfl, rfl⟩
    · simp [hd]
  · simp only [hnb, if_false]
    by_cases hd : s.shMdomain (riscvByteAlignHOL addr) = true
    · simp only [hd, if_true]
      cases hf : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL addr false) with
      | final e => exact Or.inr (Or.inl ⟨e, rfl, rfl⟩)
      | ret f b => exact Or.inl ⟨_, f, rfl, rfl⟩
    · simp [hd]

private theorem shMemStore_frame {width : Nat} [NeZero width] {F : Type}
    (v : Nat) (addr : BitVec width) (nb : Nat) (s : LoopSemStateFiniteExact width F)
    (L : Spt (WordLocW width)) (hL : sptLookup v L = sptLookup v s.locals) :
    (∃ ffi', shMemStore v addr nb s = (none, { s with ffi := ffi' }) ∧
        shMemStore v addr nb { s with locals := L } =
          (none, { { s with locals := L } with ffi := ffi' })) ∨
      (∃ e, shMemStore v addr nb s = (some (.finalFfi e), LoopSemStateFiniteExact.callEnv [] s) ∧
        shMemStore v addr nb { s with locals := L } =
          (some (.finalFfi e), LoopSemStateFiniteExact.callEnv [] { s with locals := L })) ∨
      (shMemStore v addr nb s).1 = some .error := by
  unfold shMemStore
  simp only [hL]
  cases hv : sptLookup v s.locals with
  | none => simp
  | some x =>
    cases x with
    | loc _ _ => simp
    | word w =>
      simp only
      by_cases hnb : nb = 0
      · simp only [hnb, if_true]
        by_cases hd : s.shMdomain addr = true
        · simp only [hd, if_true]
          cases hf : callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 0]
              (panWordToBytesHOL w false ++ panWordToBytesHOL addr false) with
          | final e => exact Or.inr (Or.inl ⟨e, rfl, rfl⟩)
          | ret f b => exact Or.inl ⟨f, rfl, rfl⟩
        · simp [hd]
      · simp only [hnb, if_false]
        by_cases hd : s.shMdomain (riscvByteAlignHOL addr) = true
        · simp only [hd, if_true]
          cases hf : callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
              ((panWordToBytesHOL w false).take nb ++ panWordToBytesHOL addr false) with
          | final e => exact Or.inr (Or.inl ⟨e, rfl, rfl⟩)
          | ret f b => exact Or.inl ⟨f, rfl, rfl⟩
        · simp [hd]

/-- `compile_correct`, case `ShMem op r ad` (`loop_liveProofScript.sml:17-37` statement;
    `Resume compile_correct[ShMem]` at 799-826). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_shMem {width : Nat} [NeZero width] {F : Type} :
    ∀ (op : CrepMemOp) (r : Nat) (ad : HolLoopExp width) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.shMem op r ad : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧
        shrinkHOL lt (.shMem op r ad : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro op r ad v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hx : eval v1 ad with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some a =>
  cases a with
  | loc _ _ => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | word addr =>
  have hx' := eval_lemma v1 ad (.word addr) (sptInsert r () l0) locals ⟨hx, hsub⟩
  have hsubr : ∀ k, sptMem k (sptInsert r () l0) →
      sptMem k (varsOfExpHOL ad (sptInsert r () l0)) := fun k hk => (vars_of_exp_mono ad _ k hk).1
  cases hrv : sptLookup r v1.locals with
  | none =>
    cases hl : crepIsLoadMemOp op <;> simp [evaluate, hx, hrv, hl] at he <;>
      exact absurd he.1.symm hne
  | some rv =>
  have hr' := lookup_of_subspt hsub (hsubr r (mem_insert_self' r l0)) hrv
  cases op with
  | load =>
    simp only [evaluate, hx, crepIsLoadMemOp, if_true, hrv, shMemOp] at he
    rcases shMemLoad_frame r addr 0 v1 locals with ⟨val, ffi', h1, h2⟩ | ⟨e, h1, h2⟩ | h1
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨sptInsert r val locals, ?_, ?_⟩
      · simp only [evaluate, hx', crepIsLoadMemOp, if_true, hr', shMemOp, h2]; rfl
      · exact post_setVar r val hsub fun k hk hl => hsubr k (mem_insert_of' r hl)
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, by simp only [evaluate, hx', crepIsLoadMemOp, if_true, hr', shMemOp, h2]; rfl, rfl⟩
    · rw [he] at h1; exact absurd h1 hne
  | store =>
    cases rv with
    | loc _ _ =>
      simp [evaluate, hx, crepIsLoadMemOp, hrv] at he; exact absurd he.1.symm hne
    | word _ =>
    simp only [evaluate, hx, crepIsLoadMemOp, Bool.false_eq_true, if_false, hrv, shMemOp] at he
    rcases shMemStore_frame r addr 0 v1 locals (by rw [hr', hrv]) with ⟨ffi', h1, h2⟩ | ⟨e, h1, h2⟩ | h1
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨locals, ?_, ?_⟩
      · simp only [evaluate, hx', crepIsLoadMemOp, Bool.false_eq_true, if_false, hr', shMemOp, h2]
      · exact post_none_same hsub fun k hk => hsubr k (mem_insert_of' r hk)
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, by simp only [evaluate, hx', crepIsLoadMemOp, Bool.false_eq_true, if_false, hr',
        shMemOp, h2]; rfl, rfl⟩
    · rw [he] at h1; exact absurd h1 hne
  | load8 =>
    simp only [evaluate, hx, crepIsLoadMemOp, if_true, hrv, shMemOp] at he
    rcases shMemLoad_frame r addr 1 v1 locals with ⟨val, ffi', h1, h2⟩ | ⟨e, h1, h2⟩ | h1
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨sptInsert r val locals, ?_, ?_⟩
      · simp only [evaluate, hx', crepIsLoadMemOp, if_true, hr', shMemOp, h2]; rfl
      · exact post_setVar r val hsub fun k hk hl => hsubr k (mem_insert_of' r hl)
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, by simp only [evaluate, hx', crepIsLoadMemOp, if_true, hr', shMemOp, h2]; rfl, rfl⟩
    · rw [he] at h1; exact absurd h1 hne
  | store8 =>
    cases rv with
    | loc _ _ =>
      simp [evaluate, hx, crepIsLoadMemOp, hrv] at he; exact absurd he.1.symm hne
    | word _ =>
    simp only [evaluate, hx, crepIsLoadMemOp, Bool.false_eq_true, if_false, hrv, shMemOp] at he
    rcases shMemStore_frame r addr 1 v1 locals (by rw [hr', hrv]) with ⟨ffi', h1, h2⟩ | ⟨e, h1, h2⟩ | h1
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨locals, ?_, ?_⟩
      · simp only [evaluate, hx', crepIsLoadMemOp, Bool.false_eq_true, if_false, hr', shMemOp, h2]
      · exact post_none_same hsub fun k hk => hsubr k (mem_insert_of' r hk)
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, by simp only [evaluate, hx', crepIsLoadMemOp, Bool.false_eq_true, if_false, hr',
        shMemOp, h2]; rfl, rfl⟩
    · rw [he] at h1; exact absurd h1 hne
  | load16 =>
    simp only [evaluate, hx, crepIsLoadMemOp, if_true, hrv, shMemOp] at he
    rcases shMemLoad_frame r addr 2 v1 locals with ⟨val, ffi', h1, h2⟩ | ⟨e, h1, h2⟩ | h1
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨sptInsert r val locals, ?_, ?_⟩
      · simp only [evaluate, hx', crepIsLoadMemOp, if_true, hr', shMemOp, h2]; rfl
      · exact post_setVar r val hsub fun k hk hl => hsubr k (mem_insert_of' r hl)
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, by simp only [evaluate, hx', crepIsLoadMemOp, if_true, hr', shMemOp, h2]; rfl, rfl⟩
    · rw [he] at h1; exact absurd h1 hne
  | store16 =>
    cases rv with
    | loc _ _ =>
      simp [evaluate, hx, crepIsLoadMemOp, hrv] at he; exact absurd he.1.symm hne
    | word _ =>
    simp only [evaluate, hx, crepIsLoadMemOp, Bool.false_eq_true, if_false, hrv, shMemOp] at he
    rcases shMemStore_frame r addr 2 v1 locals (by rw [hr', hrv]) with ⟨ffi', h1, h2⟩ | ⟨e, h1, h2⟩ | h1
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨locals, ?_, ?_⟩
      · simp only [evaluate, hx', crepIsLoadMemOp, Bool.false_eq_true, if_false, hr', shMemOp, h2]
      · exact post_none_same hsub fun k hk => hsubr k (mem_insert_of' r hk)
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, by simp only [evaluate, hx', crepIsLoadMemOp, Bool.false_eq_true, if_false, hr',
        shMemOp, h2]; rfl, rfl⟩
    · rw [he] at h1; exact absurd h1 hne
  | load32 =>
    simp only [evaluate, hx, crepIsLoadMemOp, if_true, hrv, shMemOp] at he
    rcases shMemLoad_frame r addr 4 v1 locals with ⟨val, ffi', h1, h2⟩ | ⟨e, h1, h2⟩ | h1
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨sptInsert r val locals, ?_, ?_⟩
      · simp only [evaluate, hx', crepIsLoadMemOp, if_true, hr', shMemOp, h2]; rfl
      · exact post_setVar r val hsub fun k hk hl => hsubr k (mem_insert_of' r hl)
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, by simp only [evaluate, hx', crepIsLoadMemOp, if_true, hr', shMemOp, h2]; rfl, rfl⟩
    · rw [he] at h1; exact absurd h1 hne
  | store32 =>
    cases rv with
    | loc _ _ =>
      simp [evaluate, hx, crepIsLoadMemOp, hrv] at he; exact absurd he.1.symm hne
    | word _ =>
    simp only [evaluate, hx, crepIsLoadMemOp, Bool.false_eq_true, if_false, hrv, shMemOp] at he
    rcases shMemStore_frame r addr 4 v1 locals (by rw [hr', hrv]) with ⟨ffi', h1, h2⟩ | ⟨e, h1, h2⟩ | h1
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨locals, ?_, ?_⟩
      · simp only [evaluate, hx', crepIsLoadMemOp, Bool.false_eq_true, if_false, hr', shMemOp, h2]
      · exact post_none_same hsub fun k hk => hsubr k (mem_insert_of' r hk)
    · rw [h1, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, by simp only [evaluate, hx', crepIsLoadMemOp, Bool.false_eq_true, if_false, hr',
        shMemOp, h2]; rfl, rfl⟩
    · rw [he] at h1; exact absurd h1 hne

/-- `compile_correct`, case `FFI name ptr1 len1 ptr2 len2 cutset`
    (`loop_liveProofScript.sml:17-37` statement; `Resume compile_correct[FFI]` at 756-779). -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_ffi {width : Nat} [NeZero width] {F : Type} :
    ∀ (idx : Basis.Pure.MlString.MlString) (p1 n1 p2 n2 : Nat) (cs : NumSet) (v1 : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.ffi idx p1 n1 p2 n2 cs : HolLoopProg width) v1 = (res, s1) ∧ res ≠ some .error ∧
        shrinkHOL lt (.ffi idx p1 n1 p2 n2 cs : HolLoopProg width) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro idx p1 n1 p2 n2 cs v1 res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  simp only [shrinkHOL, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hl1 : sptLookup n1 v1.locals with
  | none => simp [evaluate, hl1] at he; exact absurd he.1.symm hne
  | some a1 =>
  cases a1 with
  | loc _ _ => simp [evaluate, hl1] at he; exact absurd he.1.symm hne
  | word w =>
  cases hp1 : sptLookup p1 v1.locals with
  | none => simp [evaluate, hl1, hp1] at he; exact absurd he.1.symm hne
  | some a2 =>
  cases a2 with
  | loc _ _ => simp [evaluate, hl1, hp1] at he; exact absurd he.1.symm hne
  | word w2 =>
  cases hl2 : sptLookup n2 v1.locals with
  | none => simp [evaluate, hl1, hp1, hl2] at he; exact absurd he.1.symm hne
  | some a3 =>
  cases a3 with
  | loc _ _ => simp [evaluate, hl1, hp1, hl2] at he; exact absurd he.1.symm hne
  | word w3 =>
  cases hp2 : sptLookup p2 v1.locals with
  | none => simp [evaluate, hl1, hp1, hl2, hp2] at he; exact absurd he.1.symm hne
  | some a4 =>
  cases a4 with
  | loc _ _ => simp [evaluate, hl1, hp1, hl2, hp2] at he; exact absurd he.1.symm hne
  | word w4 =>
  by_cases hnS : ¬ sptSubsetLive cs v1.locals
  · simp [evaluate, hl1, hp1, hl2, hp2, cutState_eq_none_of_not_subset cs v1 hnS] at he
    exact absurd he.1.symm hne
  have hS : sptSubsetLive cs v1.locals := Classical.not_not.mp hnS
  have hin : ∀ {k : Nat}, sptMem k (sptInter cs l0) →
      sptMem k (sptInsert p1 () (sptInsert n1 () (sptInsert p2 () (sptInsert n2 () (sptInter cs l0))))) :=
    fun h => mem_insert_of' p1 (mem_insert_of' n1 (mem_insert_of' p2 (mem_insert_of' n2 h)))
  have hl1' := lookup_of_subspt hsub (mem_insert_of' p1 (mem_insert_self' n1 _)) hl1
  have hp1' := lookup_of_subspt hsub (mem_insert_self' p1 _) hp1
  have hl2' := lookup_of_subspt hsub
    (mem_insert_of' p1 (mem_insert_of' n1 (mem_insert_of' p2 (mem_insert_self' n2 _)))) hl2
  have hp2' := lookup_of_subspt hsub
    (mem_insert_of' p1 (mem_insert_of' n1 (mem_insert_self' p2 _))) hp2
  have hS' : sptSubsetLive (sptInter cs l0) locals := by
    intro k hk
    obtain ⟨hkc, _⟩ := (mem_inter_iff _ _ k).mp hk
    have hkv := hS k hkc
    have := subspt_inter_apply hsub hkv (hin hk)
    simp only [sptMem, sptDomain, this]; exact hkv
  have hcut := cutState_of_subset cs v1 hS
  have hcut' := cutState_of_subset (sptInter cs l0) { v1 with locals := locals } hS'
  simp only [evaluate, hl1, hp1, hl2, hp2, hcut] at he
  cases hb1 : readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact v1.memory v1.mdomain v1.be) with
  | none => simp [hb1] at he; exact absurd he.1.symm hne
  | some bytes =>
  cases hb2 : readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact v1.memory v1.mdomain v1.be) with
  | none => simp [hb1, hb2] at he; exact absurd he.1.symm hne
  | some bytes2 =>
  cases hf : callFFIHOL v1.ffi (.extCall idx) bytes bytes2 with
  | final e =>
    simp only [hb1, hb2, hf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨_, ?_, rfl⟩
    simp only [evaluate, hl1', hp1', hl2', hp2', hcut', hb1, hb2, hf]
    rfl
  | ret f nb =>
    simp only [hb1, hb2, hf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨sptInter locals (sptInter cs l0), ?_, ?_⟩
    · simp only [evaluate, hl1', hp1', hl2', hp2', hcut', hb1, hb2, hf]
    · refine subspt_of_lookup fun k hk => ?_
      obtain ⟨hk1, hkl⟩ := (mem_inter_iff _ _ k).mp hk
      obtain ⟨hkv, hkc⟩ := (mem_inter_iff _ _ k).mp hk1
      have hkcl : sptMem k (sptInter cs l0) := (mem_inter_iff _ _ k).mpr ⟨hkc, hkl⟩
      rw [sptLookup_sptInter, if_pos (show (sptLookup k (sptInter cs l0)).isSome = true from hkcl),
        sptLookup_sptInter, if_pos (show (sptLookup k l0).isSome = true from hkl),
        sptLookup_sptInter, if_pos (show (sptLookup k cs).isSome = true from hkc)]
      exact subspt_inter_apply hsub hkv (hin hkcl)

/-- Flapjack helper (no HOL declaration): the branch-independent tail of HOL's
    `Resume compile_correct[If]` — the `cut_res` step after the chosen branch. -/
private theorem loopLive_if_branch {width : Nat} [NeZero width] {F : Type}
    (c p' : HolLoopProg width) (v1 : LoopSemStateFiniteExact width F) (lt : List (NumSet × NumSet))
    (lx l0 liveOut : NumSet) (locals : Spt (WordLocW width))
    (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
    (ih : loopLiveCompileCorrectAt c v1)
    (hshr : shrinkHOL lt c (sptInter l0 liveOut) = (p', lx))
    (hsub : sptSubspt (sptInter v1.locals lx) locals) :
    cutRes liveOut (evaluate c v1) = (res, s1) → res ≠ some .error →
    ∃ new_locals, cutRes (sptInter l0 liveOut) (evaluate p' { v1 with locals := locals }) =
        (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro he hne
  rcases hc : evaluate c v1 with ⟨rc, sc⟩
  rw [hc] at he
  have hrc : rc ≠ some .error := fun e => by
    subst e; simp [cutRes] at he; exact hne he.1.symm
  obtain ⟨nl, hn, hp⟩ := ih rc sc lt locals p' lx (sptInter l0 liveOut) ⟨hc, hrc, hshr, hsub⟩
  rw [hn]
  cases rc with
  | some r =>
    simp only [cutRes, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨nl, by simp [cutRes], ?_⟩
    cases r <;> exact hp
  | none =>
    simp only at hp
    by_cases hS : sptSubsetLive liveOut sc.locals
    · have hS' : sptSubsetLive (sptInter l0 liveOut) nl := by
        intro k hk
        obtain ⟨hk0, hkl⟩ := (mem_inter_iff _ _ k).mp hk
        have hks := hS k hkl
        have := subspt_inter_apply hp hks hk
        simp only [sptMem, sptDomain, this]; exact hks
      simp only [cutRes, cutState_of_subset liveOut sc hS] at he
      simp only [cutRes, cutState_of_subset (sptInter l0 liveOut) { sc with locals := nl } hS']
      by_cases hz : sc.clock = 0
      · simp only [hz, if_true, Prod.mk.injEq] at he ⊢
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨.ln, by constructor <;> rfl, rfl⟩
      · simp only [hz, if_false, Prod.mk.injEq] at he ⊢
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨sptInter nl (sptInter l0 liveOut), by constructor <;> rfl, ?_⟩
        refine subspt_of_lookup fun k hk => ?_
        obtain ⟨hk1, hk0⟩ := (mem_inter_iff _ _ k).mp hk
        obtain ⟨hks, hkl⟩ := (mem_inter_iff _ _ k).mp hk1
        have hkL : sptMem k (sptInter l0 liveOut) := (mem_inter_iff _ _ k).mpr ⟨hk0, hkl⟩
        have hk0' : (sptLookup k l0).isSome = true := hk0
        have hkl' : (sptLookup k liveOut).isSome = true := hkl
        simp only [decClock, sptLookup_sptInter, hk0', hkl', if_true]
        exact subspt_inter_apply hp hks hkL
    · simp [cutRes, cutState_eq_none_of_not_subset liveOut sc hS] at he
      exact absurd he.1.symm hne

/-- Flapjack helper (no HOL declaration): the `l3` live set of HOL `shrink`'s `If`
    clause, `case x3 of Reg r => insert r () LN | _ => LN`. -/
def regImmLive {α : Type} : RegImm α → NumSet
  | .reg r => sptInsert r () .ln
  | .imm _ => .ln

/-- `compile_correct`, case `If cmp r1 ri c1 c2 live_out` (`loop_liveProofScript.sml:17-37`
    statement; `Resume compile_correct[If]` at 534-559), with the `evaluate_ind`
    hypothesis for the branch `if word_cmp cmp x y then c1 else c2` selected by the
    register values. -/
@[hol "cakeml/pancake/proofs/loop_liveProofScript.sml" "compile_correct"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem loopLive_compile_correct_if {width : Nat} [NeZero width] {F : Type} :
    ∀ (cmp : Cmp) (r1 : Nat) (ri : RegImm (BitVec width)) (c1 c2 : HolLoopProg width)
      (liveOut : NumSet) (v1 : LoopSemStateFiniteExact width F),
      (∀ x y, sptLookup r1 v1.locals = some (.word x) → LoopSemStateFiniteExact.getVarImm ri v1 = some (.word y) →
        loopLiveCompileCorrectAt (if Compiler.Encoders.Asm.wordCmpHOL cmp x y then c1 else c2) v1) →
    ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
      (lt : List (NumSet × NumSet)) (locals : Spt (WordLocW width)) (prog1 : HolLoopProg width)
      (l1 l0 : NumSet),
      evaluate (.ite cmp r1 ri c1 c2 liveOut) v1 = (res, s1) ∧ res ≠ some .error ∧
        shrinkHOL lt (.ite cmp r1 ri c1 c2 liveOut) l0 = (prog1, l1) ∧
        sptSubspt (sptInter v1.locals l1) locals →
    ∃ new_locals, evaluate prog1 { v1 with locals := locals } = (res, { s1 with locals := new_locals }) ∧
      match res with
      | none => sptSubspt (sptInter s1.locals l0) new_locals
      | some (.result _) => new_locals = s1.locals
      | some (.exception _) => new_locals = s1.locals
      | some (.break n) =>
          (match sptOel n lt with
           | some (_, brk) => sptSubspt (sptInter s1.locals brk) new_locals
           | none => True)
      | some (.continue n) =>
          (match sptOel n lt with
           | some (cont, _) => sptSubspt (sptInter s1.locals cont) new_locals
           | none => True)
      | some .timeOut => new_locals = s1.locals
      | some (.finalFfi _) => new_locals = s1.locals
      | some .error => new_locals = s1.locals := by
  intro cmp r1 ri c1 c2 liveOut v1 ih res s1 lt locals prog1 l1 l0 ⟨he, hne, hs, hsub⟩
  rcases h1s : shrinkHOL lt c1 (sptInter l0 liveOut) with ⟨p1', l1'⟩
  rcases h2s : shrinkHOL lt c2 (sptInter l0 liveOut) with ⟨p2', l2'⟩
  have hshr : shrinkHOL lt (.ite cmp r1 ri c1 c2 liveOut) l0 =
      (.ite cmp r1 ri p1' p2' (sptInter l0 liveOut),
        sptInsert r1 () (sptUnion (regImmLive ri) (sptUnion l1' l2'))) := by
    cases ri <;> simp [shrinkHOL, h1s, h2s, regImmLive]
  rw [hshr, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases hx : sptLookup r1 v1.locals with
  | none => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | some a =>
  cases a with
  | loc _ _ => simp [evaluate, hx] at he; exact absurd he.1.symm hne
  | word x =>
  cases hy : LoopSemStateFiniteExact.getVarImm ri v1 with
  | none => simp [evaluate, hx, hy] at he; exact absurd he.1.symm hne
  | some b =>
  cases b with
  | loc _ _ => simp [evaluate, hx, hy] at he; exact absurd he.1.symm hne
  | word y =>
  have hmem : ∀ {k : Nat} {t : NumSet}, sptMem k t → ∀ u : NumSet, sptMem k (sptUnion u t) :=
    fun h u => (sptMem_sptUnion' u _ _).mpr (Or.inr h)
  have hmeml : ∀ {k : Nat} {t : NumSet}, sptMem k t → ∀ u : NumSet, sptMem k (sptUnion t u) :=
    fun h u => (sptMem_sptUnion' _ u _).mpr (Or.inl h)
  have hx' := lookup_of_subspt hsub (mem_insert_self' r1 _) hx
  have hy' : LoopSemStateFiniteExact.getVarImm ri { v1 with locals := locals } = some (.word y) := by
    cases ri with
    | imm w => simpa [LoopSemStateFiniteExact.getVarImm] using hy
    | reg r =>
      simp only [LoopSemStateFiniteExact.getVarImm, regImmLive] at hy hsub ⊢
      exact lookup_of_subspt hsub (mem_insert_of' r1 (hmeml (mem_insert_self' r .ln) _)) hy
  have ih' := ih x y hx hy
  simp only [evaluate, hx, hy] at he
  simp only [evaluate, hx', hy']
  by_cases hb : Compiler.Encoders.Asm.wordCmpHOL cmp x y = true
  · simp only [hb, if_true] at he ih' ⊢
    exact loopLive_if_branch c1 p1' v1 lt l1' l0 liveOut locals res s1 ih' h1s
      (post_none_same hsub fun k hk => mem_insert_of' r1 (hmem (hmeml hk _) _)) he hne
  · simp only [hb, if_false, Bool.false_eq_true] at he ih' ⊢
    exact loopLive_if_branch c2 p2' v1 lt l2' l0 liveOut locals res s1 ih' h2s
      (post_none_same hsub fun k hk => mem_insert_of' r1 (hmem (hmem hk _) _)) he hne

end Flapjack
