import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate
import Flapjack.Pancake.Semantics.LoopProps.EvalExact
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact
import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOkLemmas

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

end Flapjack
