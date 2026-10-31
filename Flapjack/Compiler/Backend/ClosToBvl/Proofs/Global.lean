import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IntegerRelation

/-! Global-variable correspondence for the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Pointwise-related optional globals preserve successful indexed lookup. -/
theorem relatedGlobals_lookup {C F : Type} {f : HolFiniteMapExact Nat Nat}
    {s : ClosSem.State C F} {t : BvlSem.State C F} (states : stateRel f s t)
    (index : Nat) (value : ClosSem.Value)
    (found : ClosSem.getGlobal index s.globals = some (some value)) :
    ∃ target, t.globals[index + numAddedGlobals]? = some (some target) ∧
      vRel s.maxApp f t.refs t.code value target := by
  have related := states.2.1
  have sourceLookup : s.globals[index]? = some (some value) := found
  have lookup : ∀ (xs : List (Option ClosSem.Value)) (ys : List (Option BvlSem.Value)),
      List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code)) xs ys →
      ∀ (n : Nat) (v : ClosSem.Value), xs[n]? = some (some v) →
      ∃ w, ys[n]? = some (some w) ∧ vRel s.maxApp f t.refs t.code v w := by
    intro xs ys rel
    induction rel with
    | nil =>
      intro n v h
      simp at h
    | @cons x y xs ys head tail ih =>
      intro n v h
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst x
        cases y with
        | none => simp [optionValueRel] at head
        | some w => exact ⟨w, rfl, head⟩
      | succ n =>
        simp only [List.getElem?_cons_succ] at h ⊢
        exact ih n v h
  obtain ⟨target, targetLookup, valueRel⟩ := lookup _ _ related index value sourceLookup
  exact ⟨target, by simpa [List.getElem?_drop, Nat.add_comm] using targetLookup, valueRel⟩

/-- Static global reads use the shifted BVL index. -/
theorem global_static_read {C F : Type} {f : HolFiniteMapExact Nat Nat}
    {s : ClosSem.State C F} {t : BvlSem.State C F} (states : stateRel f s t)
    (index : Nat) (value : ClosSem.Value)
    (found : ClosSem.getGlobal index s.globals = some (some value)) :
    ∃ target, BvlSem.doApp (.globOp (.global (index + numAddedGlobals))) [] t = .val (target, t) ∧
      vRel s.maxApp f t.refs t.code value target := by
  obtain ⟨target, lookup, rel⟩ := relatedGlobals_lookup states index value found
  exact ⟨target, by simp [BvlSem.doApp, BvlSem.applyGlobal, lookup], rel⟩

/-- Dynamic global reads preserve the source integer index while the target
semantics applies the reserved-global offset. -/
theorem global_dynamic_read {C F : Type} {f : HolFiniteMapExact Nat Nat}
    {s : ClosSem.State C F} {t : BvlSem.State C F} (states : stateRel f s t)
    (index : Int) (nonnegative : ¬ index < 0) (unused : Nat) (value : ClosSem.Value)
    (found : ClosSem.getGlobal index.toNat s.globals = some (some value)) :
    ∃ target, BvlSem.doApp (.globOp (.global (unused + numAddedGlobals))) [.number index] t =
        .val (target, t) ∧ vRel s.maxApp f t.refs t.code value target := by
  obtain ⟨target, lookup, rel⟩ := relatedGlobals_lookup states index.toNat value found
  exact ⟨target, by simp [BvlSem.doApp, BvlSem.applyGlobal, nonnegative, lookup], rel⟩

/-- Every successful global read is matched by its compiled operation. -/
theorem global_read_dispatch {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (index : Nat) (args : List ClosSem.Value) (targetArgs : List BvlSem.Value)
    (s sLast : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (value : ClosSem.Value)
    (run : ClosSem.doApp (.globOp (.global index)) args s = .val (value, sLast)) :
    ∃ target, BvlSem.doApp (.globOp (.global (index + numAddedGlobals))) targetArgs t = .val (target, t) ∧
      sLast = s ∧ vRel s.maxApp f t.refs t.code value target := by
  cases args with
  | nil =>
    cases related
    cases found : ClosSem.getGlobal index s.globals with
    | none => simp [ClosSem.doApp, ClosSem.applyGlobal, found] at run
    | some entry =>
      cases entry with
      | none => simp [ClosSem.doApp, ClosSem.applyGlobal, found] at run
      | some original =>
        simp [ClosSem.doApp, ClosSem.applyGlobal, found] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨target, targetRun, rel⟩ := global_static_read states index original found
        exact ⟨target, targetRun, rfl, rel⟩
  | cons first rest =>
    cases rest with
    | cons second rest => simp [ClosSem.doApp, ClosSem.applyGlobal] at run
    | nil =>
      cases first <;> simp only [ClosSem.doApp, ClosSem.applyGlobal] at run
      all_goals try contradiction
      case number number =>
        cases related with
        | cons head tail =>
          cases tail
          have targetEq := vRel_number_inv head
          subst_vars
          by_cases negative : number < 0
          · simp [negative] at run
          · simp only [if_neg negative] at run
            cases found : ClosSem.getGlobal number.toNat s.globals with
            | none => simp [found] at run
            | some entry =>
              cases entry with
              | none => simp [found] at run
              | some original =>
                simp [found] at run
                rcases run with ⟨rfl, rfl⟩
                obtain ⟨target, targetRun, rel⟩ := global_dynamic_read states number negative index original found
                exact ⟨target, targetRun, rfl, rel⟩

/-- A failed global read reports the source type error. -/
theorem global_read_error {C F : Type} (index : Nat) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.globOp (.global index)) args s = .err error) :
    error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyGlobal (.global index) args s <;> simp [h] at run
  exact run.symm

/-- Replacing only global lists preserves the other components of the
candidate relation when the value relation and reserved table are retained. -/
theorem stateRel_replace_globals {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (sourceGlobals : List (Option ClosSem.Value)) (targetGlobals : List (Option BvlSem.Value))
    (related : List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code))
      sourceGlobals (targetGlobals.drop numAddedGlobals))
    (table : ClosSem.getGlobal 0 targetGlobals = some (some (globalTable s.maxApp))) :
    stateRel f { s with globals := sourceGlobals } { t with globals := targetGlobals } := by
  rcases states with ⟨ffi, _, _, rest⟩
  exact ⟨ffi, related, table, rest⟩

/-- Allocating the same number of empty globals preserves the candidate state
relation and leaves the reserved target global untouched. -/
theorem stateRel_alloc_globals {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t) (count : Nat) :
    stateRel f { s with globals := s.globals ++ List.replicate count none }
      { t with globals := t.globals ++ List.replicate count none } := by
  have nonempty : t.globals ≠ [] := by
    intro empty
    have table := states.2.2.1
    simp [ClosSem.getGlobal, empty] at table
  have replicated : List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code))
      (List.replicate count none) (List.replicate count none) := by
    induction count with
    | zero => exact .nil
    | succ count ih => exact .cons trivial ih
  have dropAppend : (t.globals ++ List.replicate count none).drop numAddedGlobals =
      t.globals.drop numAddedGlobals ++ List.replicate count none := by
    rw [List.drop_append]
    have length : numAddedGlobals ≤ t.globals.length := by
      simp only [numAddedGlobals]
      exact List.length_pos_of_ne_nil nonempty
    simp [Nat.sub_eq_zero_of_le length]
  apply stateRel_replace_globals s t states
  · rw [dropAppend]
    have appendRel : ∀ {xs ys : List (Option ClosSem.Value)} {us vs : List (Option BvlSem.Value)},
        List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code)) xs us →
        List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code)) ys vs →
        List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code)) (xs ++ ys) (us ++ vs) := by
      intro xs ys us vs first second
      induction first with
      | nil => exact second
      | cons head tail ih => exact .cons head ih
    exact appendRel states.2.1 replicated
  · have table := states.2.2.1
    cases globals : t.globals with
    | nil => contradiction
    | cons first rest =>
      simp [ClosSem.getGlobal, globals] at table ⊢
      exact table

/-- Successful global allocation returns related unit values and allocates
matching empty slots in both states. -/
theorem global_alloc_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (count : Int) (nonnegative : ¬ count < 0) :
    ClosSem.doApp (.globOp .allocGlobal) [.number count] s =
      .val (ClosSem.unitValue, { s with globals := s.globals ++ List.replicate count.toNat none }) ∧
    BvlSem.doApp (.globOp .allocGlobal) [.number count] t =
      .val (BvlSem.unitValue, { t with globals := t.globals ++ List.replicate count.toNat none }) ∧
    vRel s.maxApp f t.refs t.code ClosSem.unitValue BvlSem.unitValue ∧
    stateRel f { s with globals := s.globals ++ List.replicate count.toNat none }
      { t with globals := t.globals ++ List.replicate count.toNat none } := by
  refine ⟨?_, ?_, .block .nil, stateRel_alloc_globals s t states count.toNat⟩
  · simp [ClosSem.doApp, ClosSem.applyGlobal, nonnegative]
  · simp [BvlSem.doApp, BvlSem.applyGlobal, nonnegative]

/-- A successful allocation has exactly one nonnegative numeric argument. -/
theorem global_alloc_success {C F : Type} (args : List ClosSem.Value)
    (s sLast : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp (.globOp .allocGlobal) args s = .val (value, sLast)) :
    ∃ count : Int, args = [.number count] ∧ ¬ count < 0 ∧
      value = ClosSem.unitValue ∧
      sLast = { s with globals := s.globals ++ List.replicate count.toNat none } := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyGlobal] at run
  | cons first rest =>
    cases rest with
    | cons second rest => simp [ClosSem.doApp, ClosSem.applyGlobal] at run
    | nil =>
      cases first <;> simp only [ClosSem.doApp, ClosSem.applyGlobal] at run
      all_goals try contradiction
      case number count =>
        by_cases negative : count < 0
        · simp [negative] at run
        · simp [negative] at run
          exact ⟨count, rfl, negative, run.1.symm, run.2.symm⟩

/-- A failed global allocation reports a source type error. -/
theorem global_alloc_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.globOp .allocGlobal) args s = .err error) :
    error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyGlobal .allocGlobal args s <;> simp [h] at run
  exact run.symm

/-- Updating corresponding empty slots preserves the relation on global
lists, and the reserved target table at index zero. -/
theorem stateRel_set_global {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (index : Nat) (value : ClosSem.Value) (target : BvlSem.Value)
    (valueRel : vRel s.maxApp f t.refs t.code value target)
    (empty : ClosSem.getGlobal index s.globals = some none) :
    t.globals[index + numAddedGlobals]? = some none ∧
    stateRel f { s with globals := s.globals.set index (some value) }
      { t with globals := t.globals.set (index + numAddedGlobals) (some target) } := by
  have setRelated : ∀ (xs : List (Option ClosSem.Value)) (ys : List (Option BvlSem.Value)),
      List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code)) xs ys →
      ∀ (i : Nat), xs[i]? = some none →
      ys[i]? = some none ∧
      List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code))
        (xs.set i (some value)) (ys.set i (some target)) := by
    intro xs ys rel
    induction rel with
    | nil => intro i h; simp at h
    | @cons x y xs ys head tail ih =>
      intro i h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst x
        cases y with
        | some v => simp [optionValueRel] at head
        | none => exact ⟨rfl, .cons valueRel tail⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨found, rest⟩ := ih i h
        exact ⟨found, .cons head rest⟩
  cases targetGlobals : t.globals with
  | nil =>
    have table := states.2.2.1
    simp [ClosSem.getGlobal, targetGlobals] at table
  | cons first rest =>
    have related : List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code)) s.globals rest := by
      simpa [targetGlobals, numAddedGlobals] using states.2.1
    have sourceEmpty : s.globals[index]? = some none := empty
    obtain ⟨targetEmpty, updated⟩ := setRelated _ _ related index sourceEmpty
    constructor
    · simpa [targetGlobals, numAddedGlobals, Nat.add_comm] using targetEmpty
    · apply stateRel_replace_globals s t states
      · simpa [targetGlobals, numAddedGlobals, Nat.add_comm] using updated
      · have table := states.2.2.1
        simpa [ClosSem.getGlobal, targetGlobals, numAddedGlobals, Nat.add_comm] using table

/-- A successful source write has one argument and writes an empty slot. -/
theorem global_set_success {C F : Type} (index : Nat) (args : List ClosSem.Value)
    (s sLast : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp (.globOp (.setGlobal index)) args s = .val (value, sLast)) :
    ∃ stored, args = [stored] ∧ ClosSem.getGlobal index s.globals = some none ∧
      value = ClosSem.unitValue ∧ sLast = { s with globals := s.globals.set index (some stored) } := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyGlobal] at run
  | cons first rest =>
    cases rest with
    | cons second rest => simp [ClosSem.doApp, ClosSem.applyGlobal] at run
    | nil =>
      cases found : ClosSem.getGlobal index s.globals with
      | none => simp [ClosSem.doApp, ClosSem.applyGlobal, found] at run
      | some slot =>
        cases slot with
        | some old => simp [ClosSem.doApp, ClosSem.applyGlobal, found] at run
        | none =>
          simp [ClosSem.doApp, ClosSem.applyGlobal, found] at run
          exact ⟨first, rfl, rfl, run.1.symm, run.2.symm⟩

/-- A failed global write reports the source type error. -/
theorem global_set_error {C F : Type} (index : Nat) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.globOp (.setGlobal index)) args s = .err error) :
    error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyGlobal (.setGlobal index) args s <;> simp [h] at run
  exact run.symm

/-- Corresponding writes return related unit values and preserve the state
relation. -/
theorem global_set_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (index : Nat) (value : ClosSem.Value) (target : BvlSem.Value)
    (valueRel : vRel s.maxApp f t.refs t.code value target)
    (empty : ClosSem.getGlobal index s.globals = some none) :
    BvlSem.doApp (.globOp (.setGlobal (index + numAddedGlobals))) [target] t =
      .val (BvlSem.unitValue, { t with globals := t.globals.set (index + numAddedGlobals) (some target) }) ∧
    stateRel f { s with globals := s.globals.set index (some value) }
      { t with globals := t.globals.set (index + numAddedGlobals) (some target) } := by
  obtain ⟨targetEmpty, state⟩ := stateRel_set_global s t states index value target valueRel empty
  exact ⟨by simp [BvlSem.doApp, BvlSem.applyGlobal, targetEmpty], state⟩

end Flapjack.Compiler.Backend.ClosToBvl
