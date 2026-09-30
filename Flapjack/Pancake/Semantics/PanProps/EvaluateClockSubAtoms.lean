import Flapjack.HolRef
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase

/-!
# panProps `evaluate_clock_sub`: non-recursive atom cases

Cases of HOL `evaluate_clock_sub` (`cakeml/pancake/semantics/panPropsScript.sml:724-728`)
for `Primitive`, `Store`, `Store32`, `StoreByte`, `ShMemLoad`, `ShMemStore` and
`ExtCall` (bead `flapjack-4ac.4.60.1.1.11`), in the statement shape of the
accepted cases in `EvalInvariant.lean`.  These atoms have no `evaluate_ind`
premise and never end in `SOME TimeOut`.  The shared untagged step
`clockSub_of_noTimeout` derives the case from the tagged
`evaluate_add_clock_eq` and `evaluate_clock`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

namespace EvaluateClockSubAtoms

theorem with_clock_inj {width : Nat} {σ : Type} [NeZero width]
    {a b : PanSemStateFiniteExact width σ} {x y : Nat}
    (h : ({ a with clock := a.clock + x } : PanSemStateFiniteExact width σ) =
      { b with clock := b.clock + y }) (hxy : x = y) : a = b := by
  subst hxy
  cases a; cases b
  simp only [PanSemStateFiniteExact.mk.injEq, Nat.add_right_cancel_iff] at h ⊢
  exact h

/-- HOL `evaluate_clock_sub` for one run, given that the low-clock run does not
    end in `TimeOut`: lift the low run by `ck` with `evaluate_add_clock_eq` and
    compare it with the high run. -/
theorem clockSub_of_lowNoTimeout {width : Nat} {σ : Type} [NeZero width] (p : ProgHOL width)
    (t : PanSemStateFiniteExact width σ) (res : Option (PanSemResultExact width))
    (st : PanSemStateFiniteExact width σ) (ck : Nat)
    (h : evaluateHOLFiniteState t p = (res, { st with clock := st.clock + ck }))
    (hlow : (evaluateHOLFiniteState { t with clock := t.clock - ck } p).1 ≠ some .timeOut) :
    evaluateHOLFiniteState { t with clock := t.clock - ck } p = (res, st) := by
  have hle := evaluateHOLFiniteState_clock_le_result t p _ _ h
  simp only at hle
  rcases hl : evaluateHOLFiniteState { t with clock := t.clock - ck } p with ⟨r', st'⟩
  have hup := panPropsEvaluateAddClockEq p { t with clock := t.clock - ck } r' st' ck
    ⟨hl, by rw [hl] at hlow; exact hlow⟩
  have ht : ({ { t with clock := t.clock - ck } with clock := t.clock - ck + ck } :
      PanSemStateFiniteExact width σ) = t := by
    have hck : ck ≤ t.clock := by omega
    cases t
    simp only at hck
    simp only [PanSemStateFiniteExact.mk.injEq, and_true, true_and]
    omega
  simp only at hup
  rw [ht, h] at hup
  obtain ⟨h1, h2⟩ := Prod.mk.inj hup
  rw [← h1, with_clock_inj h2.symm rfl]

/-- A program that never ends in `TimeOut` satisfies HOL `evaluate_clock_sub`
    over the canonical carrier. -/
theorem clockSub_of_noTimeout {width : Nat} {σ : Type} [NeZero width] (p : ProgHOL width)
    (hnt : ∀ u : PanSemStateFiniteExact width σ, (evaluateHOLFiniteState u p).1 ≠ some .timeOut)
    (t : PanSemStateFiniteExact width σ) (res : Option (PanSemResultExact width))
    (st : PanSemStateFiniteExact width σ) (ck : Nat)
    (h : evaluateHOLFiniteState t p = (res, { st with clock := st.clock + ck })) :
    evaluateHOLFiniteState { t with clock := t.clock - ck } p = (res, st) :=
  clockSub_of_lowNoTimeout p t res st ck h (hnt _)

/-- `clockSub_of_noTimeout` over the `PanPropsEvalStateFiniteExact` pair
    carrier of the tagged `evaluate_clock_sub` cases. -/
theorem pairClockSub_of_noTimeout {width : Nat} {σ : Type} [NeZero width] (p : ProgHOL width)
    (hnt : ∀ u : PanSemStateFiniteExact width σ, (evaluateHOLFiniteState u p).1 ≠ some .timeOut) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state p =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } p = (result, st) := by
  classical
  intro state result st ck hRun _
  have hCan : evaluateHOLFiniteState state.toPanSemFinite p =
      (result, { st.toPanSemFinite with clock := st.toPanSemFinite.clock + ck }) := by
    have e := congrArg (fun pair => (pair.1, pair.2.toPanSemFinite)) hRun
    simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
      PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at e
    exact e
  have hLow := clockSub_of_noTimeout p hnt _ _ _ _ hCan
  have hstate : ({ state with clock := state.clock - ck } :
      PanPropsEvalStateFiniteExact width σ).toPanSemFinite =
      { state.toPanSemFinite with clock := state.toPanSemFinite.clock - ck } := rfl
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, hstate, hLow,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]

theorem nt_primitive {width : Nat} {σ : Type} [NeZero width] (name : MlS) (op : PrimOp)
    (args : List (ExpHOL width)) :
    ∀ u : PanSemStateFiniteExact width σ,
      (evaluateHOLFiniteState u (.primitive name op args)).1 ≠ some .timeOut := by
  intro u hr
  rcases he : evaluateHOLFiniteState u _ with ⟨r, st⟩
  rw [he] at hr
  simp only at hr
  subst hr
  rw [evaluateHOLFiniteState_primitive] at he
  repeat' split at he
  all_goals simp at he

theorem nt_store {width : Nat} {σ : Type} [NeZero width] (a b : ExpHOL width) :
    ∀ u : PanSemStateFiniteExact width σ,
      (evaluateHOLFiniteState u (.store a b)).1 ≠ some .timeOut := by
  intro u hr
  rcases he : evaluateHOLFiniteState u _ with ⟨r, st⟩
  rw [he] at hr
  simp only at hr
  subst hr
  rw [evaluateHOLFiniteState_store] at he
  repeat' split at he
  all_goals simp at he

theorem nt_store32 {width : Nat} {σ : Type} [NeZero width] (a b : ExpHOL width) :
    ∀ u : PanSemStateFiniteExact width σ,
      (evaluateHOLFiniteState u (.store32 a b)).1 ≠ some .timeOut := by
  intro u hr
  rcases he : evaluateHOLFiniteState u _ with ⟨r, st⟩
  rw [he] at hr
  simp only at hr
  subst hr
  rw [evaluateHOLFiniteState_store32] at he
  repeat' split at he
  all_goals simp at he

theorem nt_storeByte {width : Nat} {σ : Type} [NeZero width] (a b : ExpHOL width) :
    ∀ u : PanSemStateFiniteExact width σ,
      (evaluateHOLFiniteState u (.storeByte a b)).1 ≠ some .timeOut := by
  intro u hr
  rcases he : evaluateHOLFiniteState u _ with ⟨r, st⟩
  rw [he] at hr
  simp only at hr
  subst hr
  rw [evaluateHOLFiniteState_storeByte] at he
  repeat' split at he
  all_goals simp at he

theorem shMemLoad_nt {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateFiniteExact width σ) (inst : DecidablePred u.shMemaddrs)
    (k : VarKind) (name : MlS) (addr : RiscV.Word width) (nb : Nat) :
    (@shMemLoadHOLFiniteExact width σ _ u inst k name addr nb).1 ≠ some .timeOut := by
  unfold shMemLoadHOLFiniteExact
  split <;> split <;> (try split) <;> simp

theorem shMemStore_nt {width : Nat} {σ : Type} [NeZero width]
    (u : PanSemStateExact width σ) (inst : DecidablePred u.shMemaddrs)
    (w addr : RiscV.Word width) (nb : Nat) :
    (@shMemStoreHOLExact width σ _ u inst w addr nb).1 ≠ some .timeOut := by
  unfold shMemStoreHOLExact
  split <;> split <;> (try split) <;> simp

theorem nt_shMemLoad {width : Nat} {σ : Type} [NeZero width] (op : OpSize) (k : VarKind)
    (name : MlS) (a : ExpHOL width) :
    ∀ u : PanSemStateFiniteExact width σ,
      (evaluateHOLFiniteState u (.shMemLoad op k name a)).1 ≠ some .timeOut := by
  intro u hr
  rcases he : evaluateHOLFiniteState u _ with ⟨r, st⟩
  rw [he] at hr
  simp only at hr
  subst hr
  rw [evaluateHOLFiniteState_shMemLoad_source] at he
  repeat' split at he
  all_goals simp at he
  all_goals exact shMemLoad_nt _ _ _ _ _ _ he.1

theorem nt_shMemStore {width : Nat} {σ : Type} [NeZero width] (op : OpSize) (a b : ExpHOL width) :
    ∀ u : PanSemStateFiniteExact width σ,
      (evaluateHOLFiniteState u (.shMemStore op a b)).1 ≠ some .timeOut := by
  intro u hr
  rcases he : evaluateHOLFiniteState u _ with ⟨r, st⟩
  rw [he] at hr
  simp only at hr
  subst hr
  rw [evaluateHOLFiniteState_shMemStore_total] at he
  dsimp only at he
  revert he
  split
  · intro he
    simp only [Prod.mk.injEq] at he
    exact shMemStore_nt _ _ _ _ _ he.1
  · intro he; simp at he

theorem nt_extCall {width : Nat} {σ : Type} [NeZero width] (f : MlS) (a b c d : ExpHOL width) :
    ∀ u : PanSemStateFiniteExact width σ,
      (evaluateHOLFiniteState u (.extCall f a b c d)).1 ≠ some .timeOut := by
  intro u hr
  rcases he : evaluateHOLFiniteState u _ with ⟨r, st⟩
  rw [he] at hr
  simp only at hr
  subst hr
  rw [evaluateHOLFiniteState_extCall_source] at he
  repeat' split at he
  all_goals simp at he

end EvaluateClockSubAtoms

namespace EvaluateClockSubAtomsWitness
/-- Same-module canonical witness for the `locals`/`globals`/`code`/`eshapes`
    finite-map qualifier of the case theorems below. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanPropsEvalStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
        PanPropsEvalStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanPropsEvalStateFiniteExact.holFmapAsFiniteSupportWitness
end EvaluateClockSubAtomsWitness

open EvaluateClockSubAtoms

/-- `Primitive` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`).
    `evaluate_ind` gives this atom no induction hypothesis.  The clause never
    returns `SOME TimeOut`, so shifting the low-clock run up with the tagged
    `evaluate_add_clock_eq` and comparing it with the given run yields the
    result (`clockSub_of_noTimeout`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubPrimitiveCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (op : PrimOp) (args : List (ExpHOL width)) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.primitive name op args : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.primitive name op args) = (result, st) :=
  pairClockSub_of_noTimeout _ (nt_primitive name op args)

/-- `Store` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`).
    `evaluate_ind` gives this atom no induction hypothesis.  The clause never
    returns `SOME TimeOut`, so shifting the low-clock run up with the tagged
    `evaluate_add_clock_eq` and comparing it with the given run yields the
    result (`clockSub_of_noTimeout`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubStoreCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (a b : ExpHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.store a b : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.store a b) = (result, st) :=
  pairClockSub_of_noTimeout _ (nt_store a b)

/-- `Store32` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`).
    `evaluate_ind` gives this atom no induction hypothesis.  The clause never
    returns `SOME TimeOut`, so shifting the low-clock run up with the tagged
    `evaluate_add_clock_eq` and comparing it with the given run yields the
    result (`clockSub_of_noTimeout`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubStore32CaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (a b : ExpHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.store32 a b : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.store32 a b) = (result, st) :=
  pairClockSub_of_noTimeout _ (nt_store32 a b)

/-- `StoreByte` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`).
    `evaluate_ind` gives this atom no induction hypothesis.  The clause never
    returns `SOME TimeOut`, so shifting the low-clock run up with the tagged
    `evaluate_add_clock_eq` and comparing it with the given run yields the
    result (`clockSub_of_noTimeout`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubStoreByteCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (a b : ExpHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.storeByte a b : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.storeByte a b) = (result, st) :=
  pairClockSub_of_noTimeout _ (nt_storeByte a b)

/-- `ShMemLoad` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`).
    `evaluate_ind` gives this atom no induction hypothesis.  The clause never
    returns `SOME TimeOut`, so shifting the low-clock run up with the tagged
    `evaluate_add_clock_eq` and comparing it with the given run yields the
    result (`clockSub_of_noTimeout`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubShMemLoadCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (op : OpSize) (k : VarKind) (name : MlS) (a : ExpHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.shMemLoad op k name a : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.shMemLoad op k name a) = (result, st) :=
  pairClockSub_of_noTimeout _ (nt_shMemLoad op k name a)

/-- `ShMemStore` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`).
    `evaluate_ind` gives this atom no induction hypothesis.  The clause never
    returns `SOME TimeOut`, so shifting the low-clock run up with the tagged
    `evaluate_add_clock_eq` and comparing it with the given run yields the
    result (`clockSub_of_noTimeout`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubShMemStoreCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (op : OpSize) (a b : ExpHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.shMemStore op a b : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.shMemStore op a b) = (result, st) :=
  pairClockSub_of_noTimeout _ (nt_shMemStore op a b)

/-- `ExtCall` case of HOL `evaluate_clock_sub` (`panPropsScript.sml:724-728`).
    `evaluate_ind` gives this atom no induction hypothesis.  The clause never
    returns `SOME TimeOut`, so shifting the low-clock run up with the tagged
    `evaluate_add_clock_eq` and comparing it with the given run yields the
    result (`clockSub_of_noTimeout`). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubExtCallCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (f : MlS) (a b c d : ExpHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.extCall f a b c d : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.extCall f a b c d) = (result, st) :=
  pairClockSub_of_noTimeout _ (nt_extCall f a b c d)

end Flapjack
