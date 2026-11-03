import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelOrigins

/-! Lookup of individual body traversals. These lemmas are Flapjack-specific
infrastructure for the bounded direct-call adapter. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- A selected entry of a successful list traversal comes from an actual
single-expression traversal at a smaller depth, whose resulting state is
extended by the final state. -/
theorem callsListFuel_lookup_run (fuel : Nat) (source target : List Exp) (initial final : State)
    (run : callsListFuel fuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialWf : wellFormed initial) (index : Nat) (e out : Exp)
    (sourceLookup : source[index]? = some e) (targetLookup : target[index]? = some out) :
    ∃ depth before after, depth < fuel ∧ callsFuel depth e before = some (out, after) ∧
      (codeLocationsExp e).Nodup ∧ LabelsFresh (codeLocationsExp e) before ∧
      wellFormed before ∧ stateExtends after final := by
  induction fuel generalizing source target initial final index with
  | zero =>
    cases source with
    | nil => simp at sourceLookup
    | cons e es => simp [callsListFuel] at run
  | succ depth ih =>
    cases source with
    | nil => simp at sourceLookup
    | cons head tail =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨headOut, middle⟩, headRun, ⟨tailOut, next⟩, tailRun, rfl, rfl⟩ := run
      have allDistinct : (codeLocationsExp head ++ codeLocations tail).Nodup := by
        simpa [codeLocations] using distinct
      have allFresh : LabelsFresh (codeLocationsExp head ++ codeLocations tail) initial := by
        simpa [codeLocations] using fresh
      have headDistinct := List.Nodup.of_append_left allDistinct
      have tailDistinct := List.Nodup.of_append_right allDistinct
      have headFresh : LabelsFresh (codeLocationsExp head) initial := by
        intro loc member
        exact allFresh loc (List.mem_append_left _ member)
      have middleFresh : LabelsFresh (codeLocations tail) middle := by
        have labels := callsFuel_labelsBound depth head initial middle headOut headRun
        intro loc member labelMember
        rcases labels (loc + 1) labelMember with old | ⟨origin, originMember, equal⟩
        · exact allFresh loc (List.mem_append_right _ member) old
        · have unequal := (List.nodup_append.mp allDistinct).2.2 origin originMember loc member
          exact unequal (Nat.add_right_cancel equal.symm)
      have singletonRun : callsListFuel (depth + 1) [head] initial = some ([headOut], middle) := by
        simp [callsListFuel, headRun]
      have middleWf := callsListFuel_wellFormed (depth + 1) [head] initial middle [headOut] singletonRun
        (by simpa [codeLocations] using headDistinct) (by simpa [codeLocations] using headFresh) initialWf
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceLookup targetLookup
        subst e
        subst out
        have boundedTail : callsListBounded depth tail middle = some (tailOut, next) := by
          simp [callsListBounded, tailRun]
        have tailExt := callsListBounded_stateExtends depth tail middle next tailOut boundedTail
          tailDistinct middleFresh middleWf.2
        exact ⟨depth, initial, middle, by omega, headRun, headDistinct, headFresh, initialWf, tailExt⟩
      | succ index =>
        simp only [List.getElem?_cons_succ] at sourceLookup targetLookup
        obtain ⟨n, before, after, depthLt, selected, selectedDistinct, selectedFresh, beforeWf, extended⟩ :=
          ih tail tailOut middle next tailRun tailDistinct middleFresh middleWf index sourceLookup targetLookup
        exact ⟨n, before, after, by omega, selected, selectedDistinct, selectedFresh, beforeWf, extended⟩

/-- A selected expression traversal extends to the final list state when
only label distinctness is known initially. This also covers speculative
recursive-group states, which need not be fully well formed. -/
theorem callsListFuel_lookup_run_distinct (fuel : Nat) (source target : List Exp) (initial final : State)
    (run : callsListFuel fuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialDistinct : (initial.2.map Prod.fst).Nodup) (index : Nat) (e out : Exp)
    (sourceLookup : source[index]? = some e) (targetLookup : target[index]? = some out) :
    ∃ depth before after, depth < fuel ∧ callsFuel depth e before = some (out, after) ∧
      (codeLocationsExp e).Nodup ∧ LabelsFresh (codeLocationsExp e) before ∧
      (before.2.map Prod.fst).Nodup ∧ stateExtends after final := by
  induction fuel generalizing source target initial final index with
  | zero =>
    cases source with
    | nil => simp at sourceLookup
    | cons e es => simp [callsListFuel] at run
  | succ depth ih =>
    cases source with
    | nil => simp at sourceLookup
    | cons head tail =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨headOut, middle⟩, headRun, ⟨tailOut, next⟩, tailRun, rfl, rfl⟩ := run
      have allDistinct : (codeLocationsExp head ++ codeLocations tail).Nodup := by
        simpa [codeLocations] using distinct
      have allFresh : LabelsFresh (codeLocationsExp head ++ codeLocations tail) initial := by
        simpa [codeLocations] using fresh
      have headDistinct := List.Nodup.of_append_left allDistinct
      have tailDistinct := List.Nodup.of_append_right allDistinct
      have headFresh : LabelsFresh (codeLocationsExp head) initial := by
        intro loc member
        exact allFresh loc (List.mem_append_left _ member)
      have middleFresh : LabelsFresh (codeLocations tail) middle := by
        have labels := callsFuel_labelsBound depth head initial middle headOut headRun
        intro loc member labelMember
        rcases labels (loc + 1) labelMember with old | ⟨origin, originMember, equal⟩
        · exact allFresh loc (List.mem_append_right _ member) old
        · have unequal := (List.nodup_append.mp allDistinct).2.2 origin originMember loc member
          exact unequal (Nat.add_right_cancel equal.symm)
      have singletonRun : callsListFuel (depth + 1) [head] initial = some ([headOut], middle) := by
        simp [callsListFuel, headRun]
      have middleDistinct := callsListFuel_labelsDistinct (depth + 1) [head] initial middle [headOut] singletonRun
        (by simpa [codeLocations] using headDistinct) (by simpa [codeLocations] using headFresh) initialDistinct
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceLookup targetLookup
        subst e
        subst out
        have boundedTail : callsListBounded depth tail middle = some (tailOut, next) := by
          simp [callsListBounded, tailRun]
        have tailExt := callsListBounded_stateExtends depth tail middle next tailOut boundedTail
          tailDistinct middleFresh middleDistinct
        exact ⟨depth, initial, middle, by omega, headRun, headDistinct, headFresh, initialDistinct, tailExt⟩
      | succ index =>
        simp only [List.getElem?_cons_succ] at sourceLookup targetLookup
        obtain ⟨n, before, after, depthLt, selected, selectedDistinct, selectedFresh, beforeWf, extended⟩ :=
          ih tail tailOut middle next tailRun tailDistinct middleFresh middleDistinct index sourceLookup targetLookup
        exact ⟨n, before, after, by omega, selected, selectedDistinct, selectedFresh, beforeWf, extended⟩

/-- A selected expression traversal preserves weak well-formedness and
extends to the final list state. This also covers speculative
recursive-group states, which need not be fully well formed. -/
theorem callsListFuel_lookup_run_weak (fuel : Nat) (source target : List Exp) (initial final : State)
    (run : callsListFuel fuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialDistinct : (initial.2.map Prod.fst).Nodup) (initialWeak : weaklyWellFormed initial) (index : Nat) (e out : Exp)
    (sourceLookup : source[index]? = some e) (targetLookup : target[index]? = some out) :
    ∃ depth before after, depth < fuel ∧ callsFuel depth e before = some (out, after) ∧
      (codeLocationsExp e).Nodup ∧ LabelsFresh (codeLocationsExp e) before ∧
      (before.2.map Prod.fst).Nodup ∧ weaklyWellFormed before ∧ stateExtends after final := by
  induction fuel generalizing source target initial final index with
  | zero =>
    cases source with
    | nil => simp at sourceLookup
    | cons e es => simp [callsListFuel] at run
  | succ depth ih =>
    cases source with
    | nil => simp at sourceLookup
    | cons head tail =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
        Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨headOut, middle⟩, headRun, ⟨tailOut, next⟩, tailRun, rfl, rfl⟩ := run
      have allDistinct : (codeLocationsExp head ++ codeLocations tail).Nodup := by
        simpa [codeLocations] using distinct
      have allFresh : LabelsFresh (codeLocationsExp head ++ codeLocations tail) initial := by
        simpa [codeLocations] using fresh
      have headDistinct := List.Nodup.of_append_left allDistinct
      have tailDistinct := List.Nodup.of_append_right allDistinct
      have headFresh : LabelsFresh (codeLocationsExp head) initial := by
        intro loc member
        exact allFresh loc (List.mem_append_left _ member)
      have middleFresh : LabelsFresh (codeLocations tail) middle := by
        have labels := callsFuel_labelsBound depth head initial middle headOut headRun
        intro loc member labelMember
        rcases labels (loc + 1) labelMember with old | ⟨origin, originMember, equal⟩
        · exact allFresh loc (List.mem_append_right _ member) old
        · have unequal := (List.nodup_append.mp allDistinct).2.2 origin originMember loc member
          exact unequal (Nat.add_right_cancel equal.symm)
      have singletonRun : callsListFuel (depth + 1) [head] initial = some ([headOut], middle) := by
        simp [callsListFuel, headRun]
      have middleDistinct := callsListFuel_labelsDistinct (depth + 1) [head] initial middle [headOut] singletonRun
        (by simpa [codeLocations] using headDistinct) (by simpa [codeLocations] using headFresh) initialDistinct
      have middleWeak := callsFuel_weaklyWellFormed depth head initial middle headOut headRun initialWeak
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceLookup targetLookup
        subst e
        subst out
        have boundedTail : callsListBounded depth tail middle = some (tailOut, next) := by
          simp [callsListBounded, tailRun]
        have tailExt := callsListBounded_stateExtends depth tail middle next tailOut boundedTail
          tailDistinct middleFresh middleDistinct
        exact ⟨depth, initial, middle, by omega, headRun, headDistinct, headFresh, initialDistinct, initialWeak, tailExt⟩
      | succ index =>
        simp only [List.getElem?_cons_succ] at sourceLookup targetLookup
        obtain ⟨n, before, after, depthLt, selected, selectedDistinct, selectedFresh, beforeWf, beforeWeak, extended⟩ :=
          ih tail tailOut middle next tailRun tailDistinct middleFresh middleDistinct middleWeak index sourceLookup targetLookup
        exact ⟨n, before, after, by omega, selected, selectedDistinct, selectedFresh, beforeWf, beforeWeak, extended⟩

/-- The bounded retry wrapper exposes the selected single-expression run,
including its freshness and state extension, whether the first attempt or
the structural retry succeeded. -/
theorem callsListBounded_lookup_run (fuel : Nat) (source target : List Exp) (initial final : State)
    (run : callsListBounded fuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialWf : wellFormed initial) (index : Nat) (e out : Exp)
    (sourceLookup : source[index]? = some e) (targetLookup : target[index]? = some out) :
    ∃ depth before after, depth < max fuel (listBudget source + 1) ∧
      callsFuel depth e before = some (out, after) ∧
      (codeLocationsExp e).Nodup ∧ LabelsFresh (codeLocationsExp e) before ∧
      wellFormed before ∧ stateExtends after final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel source initial with
  | none =>
    exact callsListFuel_lookup_run (max fuel (listBudget source + 1)) source target initial final
      (by simpa [first] using run) distinct fresh initialWf index e out sourceLookup targetLookup
  | some value =>
    have eq : value = (target, final) := by simpa [first] using run
    subst value
    obtain ⟨depth, before, after, depthLt, selected, selectedDistinct, selectedFresh, beforeWf, extended⟩ :=
      callsListFuel_lookup_run fuel source target initial final first distinct fresh initialWf index e out
        sourceLookup targetLookup
    exact ⟨depth, before, after, by omega, selected, selectedDistinct, selectedFresh, beforeWf, extended⟩

/-- The bounded retry wrapper also exposes selected traversals under
label distinctness alone. This covers speculative recursive groups. -/
theorem callsListBounded_lookup_run_distinct (fuel : Nat) (source target : List Exp) (initial final : State)
    (run : callsListBounded fuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialDistinct : (initial.2.map Prod.fst).Nodup) (index : Nat) (e out : Exp)
    (sourceLookup : source[index]? = some e) (targetLookup : target[index]? = some out) :
    ∃ depth before after, depth < max fuel (listBudget source + 1) ∧
      callsFuel depth e before = some (out, after) ∧
      (codeLocationsExp e).Nodup ∧ LabelsFresh (codeLocationsExp e) before ∧
      (before.2.map Prod.fst).Nodup ∧ stateExtends after final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel source initial with
  | none =>
    exact callsListFuel_lookup_run_distinct (max fuel (listBudget source + 1)) source target initial final
      (by simpa [first] using run) distinct fresh initialDistinct index e out sourceLookup targetLookup
  | some value =>
    have eq : value = (target, final) := by simpa [first] using run
    subst value
    obtain ⟨depth, before, after, depthLt, selected, selectedDistinct, selectedFresh, beforeWf, extended⟩ :=
      callsListFuel_lookup_run_distinct fuel source target initial final first distinct fresh initialDistinct index e out
        sourceLookup targetLookup
    exact ⟨depth, before, after, by omega, selected, selectedDistinct, selectedFresh, beforeWf, extended⟩

/-- The bounded retry wrapper exposes selected traversals while retaining
weak well-formedness. This covers speculative recursive groups. -/
theorem callsListBounded_lookup_run_weak (fuel : Nat) (source target : List Exp) (initial final : State)
    (run : callsListBounded fuel source initial = some (target, final))
    (distinct : (codeLocations source).Nodup) (fresh : LabelsFresh (codeLocations source) initial)
    (initialDistinct : (initial.2.map Prod.fst).Nodup) (initialWeak : weaklyWellFormed initial) (index : Nat) (e out : Exp)
    (sourceLookup : source[index]? = some e) (targetLookup : target[index]? = some out) :
    ∃ depth before after, depth < max fuel (listBudget source + 1) ∧
      callsFuel depth e before = some (out, after) ∧
      (codeLocationsExp e).Nodup ∧ LabelsFresh (codeLocationsExp e) before ∧
      (before.2.map Prod.fst).Nodup ∧ weaklyWellFormed before ∧ stateExtends after final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel source initial with
  | none =>
    exact callsListFuel_lookup_run_weak (max fuel (listBudget source + 1)) source target initial final
      (by simpa [first] using run) distinct fresh initialDistinct initialWeak index e out sourceLookup targetLookup
  | some value =>
    have eq : value = (target, final) := by simpa [first] using run
    subst value
    obtain ⟨depth, before, after, depthLt, selected, selectedDistinct, selectedFresh, beforeWf, beforeWeak, extended⟩ :=
      callsListFuel_lookup_run_weak fuel source target initial final first distinct fresh initialDistinct initialWeak index e out
        sourceLookup targetLookup
    exact ⟨depth, before, after, by omega, selected, selectedDistinct, selectedFresh, beforeWf, beforeWeak, extended⟩

/-- An entry of an open recursive group identifies the corresponding
single-expression traversal through the zipped arities and bodies. -/
theorem callsListBounded_open_body (fuel : Nat) (fns : List (Nat × Exp)) (bodies : List Exp)
    (initial final : State) (run : callsListBounded fuel (fns.map Prod.snd) initial = some (bodies, final))
    (distinct : (codeLocations (fns.map Prod.snd)).Nodup)
    (fresh : LabelsFresh (codeLocations (fns.map Prod.snd)) initial) (initialWf : wellFormed initial)
    (index arity : Nat) (body out : Exp) (sourceLookup : fns[index]? = some (arity, body))
    (targetLookup : ((fns.map Prod.fst).zip bodies)[index]? = some (arity, out)) :
    ∃ depth before after, depth < max fuel (listBudget (fns.map Prod.snd) + 1) ∧
      callsFuel depth body before = some (out, after) ∧
      (codeLocationsExp body).Nodup ∧ LabelsFresh (codeLocationsExp body) before ∧
      wellFormed before ∧ stateExtends after final := by
  have sourceIndex : (fns.map Prod.snd)[index]? = some body := by
    simp [List.getElem?_map, sourceLookup]
  have targetIndex : bodies[index]? = some out := by
    exact (List.getElem?_zip_eq_some.mp targetLookup).2
  exact callsListBounded_lookup_run fuel (fns.map Prod.snd) bodies initial final run distinct fresh initialWf
    index body out sourceIndex targetIndex

end Flapjack.Compiler.Backend.ClosCall
