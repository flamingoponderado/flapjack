import Flapjack.Compiler.Backend.ClosToBvl.Proofs.MappedRefsUpdate

/-! Thunk restrictions and reference correspondence for closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- A related target value is not a thunk when the source value is not a
thunk. This includes byte vectors represented by frozen target arrays. -/
theorem destThunk_notThunk_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    {source : ClosSem.Value} {target : BvlSem.Value}
    (related : vRel s.maxApp f t.refs t.code source target)
    (notThunk : ClosSem.destThunk [source] s.refs = .notThunk) :
    BvlSem.destThunk target t.refs = .notThunk := by
  cases related with
  | number n => rfl
  | word64 w => rfl
  | block rel => rfl
  | byteVector found fresh => simp [BvlSem.destThunk, found]
  | @refPtr flag sourcePtr targetPtr mapped =>
    have sourceOccupied := (states.2.2.2.2.2.1 sourcePtr).mp (by simp [mapped])
    obtain ⟨cell, found⟩ := Option.ne_none_iff_exists.mp sourceOccupied
    have sourceFound : s.refs.lookup sourcePtr = some cell := found.symm
    obtain ⟨targetCell, targetFound, cellRel⟩ :=
      stateRel_ref_lookup states sourcePtr targetPtr cell mapped sourceFound
    cases cell with
    | valueArray values =>
      cases targetCell <;> simp [refRel] at cellRel
      simp [BvlSem.destThunk, targetFound]
    | byteArray bytes =>
      cases targetCell <;> simp [refRel] at cellRel
      simp [BvlSem.destThunk, targetFound]
    | thunk mode value =>
      cases flag <;> simp [ClosSem.destThunk, sourceFound] at notThunk
  | closure envRel closure => rfl
  | partialClosure envRel argsRel nonempty bound lookup added arity closure => rfl

/-- The target accepts every thunk update accepted by the source for related
values and related reference states. -/
theorem badThunkUpdate_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (mode : AstHOL.ThunkMode) {source : ClosSem.Value} {target : BvlSem.Value}
    (related : vRel s.maxApp f t.refs t.code source target)
    (good : ClosSem.badThunkUpdate mode source s.refs = false) :
    ¬ BvlSem.badThunkUpdate mode target t.refs := by
  intro bad
  obtain ⟨evaluated, targetNot⟩ := bad
  subst mode
  simp [ClosSem.badThunkUpdate] at good
  cases h : ClosSem.destThunk [source] s.refs with
  | badRef => simp [h] at good
  | isThunk mode value => simp [h] at good
  | notThunk => exact targetNot (destThunk_notThunk_related s t states related h)

/-- Allocating related thunk cells extends the pointer map and preserves the
candidate state relation and target-only reference frame. -/
theorem alloc_thunk_related {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (mode : AstHOL.ThunkMode)
    (sourceValue : ClosSem.Value) (targetValue : BvlSem.Value)
    (states : stateRel f s t) (valueRel : vRel s.maxApp f t.refs t.code sourceValue targetValue)
    (good : ClosSem.badThunkUpdate mode sourceValue s.refs = false) :
    let sourcePtr := ClosSem.leastUnusedRef s.refs
    let targetPtr := BvlSem.leastUnusedRef t.refs
    let newMap := f.updateEq (sourcePtr, targetPtr)
    let sourceNext := { s with refs := s.refs.updateEq (sourcePtr, .thunk mode sourceValue) }
    let targetNext := { t with refs := t.refs.updateEq (targetPtr, .thunk mode targetValue) }
    ClosSem.doApp (.thunkOp (.allocThunk mode)) [sourceValue] s = .val (.refPtr false sourcePtr, sourceNext) ∧
    BvlSem.doApp (.thunkOp (.allocThunk mode)) [targetValue] t = .val (.refPtr false targetPtr, targetNext) ∧
    stateRel newMap sourceNext targetNext ∧
    vRel s.maxApp newMap targetNext.refs targetNext.code (.refPtr false sourcePtr) (.refPtr false targetPtr) ∧
    relocationSubmap f newMap ∧ unmappedRefsSubmap t.refs targetNext.refs f newMap := by
  let sourcePtr := ClosSem.leastUnusedRef s.refs
  let targetPtr := BvlSem.leastUnusedRef t.refs
  have sourceFree : s.refs.lookup sourcePtr = none := ClosSem.leastUnusedRef_unused s.refs
  have targetFree : t.refs.lookup targetPtr = none := BvlSem.leastUnusedRef_unused t.refs
  have ⟨submap, frame⟩ := freshMapped_growth s t f sourcePtr targetPtr (.thunk mode targetValue)
    states sourceFree targetFree
  have targetGood := badThunkUpdate_related s t states mode valueRel good
  have grown := vRel_grow_refs valueRel submap frame
  refine ⟨?_, ?_, ?_, .refPtr (by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]), submap, frame⟩
  · simp [ClosSem.doApp, good]
  · simp [BvlSem.doApp, targetGood]
  · exact stateRel_alloc_mapped s t f sourcePtr targetPtr (.thunk mode sourceValue) (.thunk mode targetValue)
      states sourceFree targetFree (by simp) ⟨rfl, grown⟩

/-- Successful thunk allocation has one permitted source value. -/
theorem allocThunk_success {C F : Type} (mode : AstHOL.ThunkMode) (args : List ClosSem.Value)
    (s next : ClosSem.State C F) (result : ClosSem.Value)
    (run : ClosSem.doApp (.thunkOp (.allocThunk mode)) args s = .val (result, next)) :
    ∃ value, args = [value] ∧ ClosSem.badThunkUpdate mode value s.refs = false ∧
      result = .refPtr false (ClosSem.leastUnusedRef s.refs) ∧
      next = { s with refs := s.refs.updateEq (ClosSem.leastUnusedRef s.refs, .thunk mode value) } := by
  cases args with
  | nil => simp [ClosSem.doApp] at run
  | cons value rest =>
    cases rest with
    | cons second rest => simp [ClosSem.doApp] at run
    | nil =>
      by_cases bad : ClosSem.badThunkUpdate mode value s.refs = true
      · simp [ClosSem.doApp, bad] at run
      · have good : ClosSem.badThunkUpdate mode value s.refs = false := by
          cases h : ClosSem.badThunkUpdate mode value s.refs <;> simp_all
        simp [ClosSem.doApp, good] at run
        exact ⟨value, rfl, good, run.1.symm, run.2.symm⟩

/-- Failed thunk allocation reports a source type error. -/
theorem allocThunk_error {C F : Type} (mode : AstHOL.ThunkMode) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.thunkOp (.allocThunk mode)) args s = .err error) : error = .abort .typeError := by
  cases args with
  | nil => simpa [ClosSem.doApp] using run.symm
  | cons first rest =>
    cases rest with
    | cons second rest => simpa [ClosSem.doApp] using run.symm
    | nil =>
      by_cases bad : ClosSem.badThunkUpdate mode first s.refs = true
      · simpa [ClosSem.doApp, bad] using run.symm
      · have good : ClosSem.badThunkUpdate mode first s.refs = false := by
          cases h : ClosSem.badThunkUpdate mode first s.refs <;> simp_all
        simp [ClosSem.doApp, good] at run

/-- Looking up a related source thunk produces a target thunk with the same
mode and a related payload. -/
theorem stateRel_thunk_lookup {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (sourcePtr targetPtr : Nat) (mode : AstHOL.ThunkMode) (value : ClosSem.Value)
    (mapped : f.lookup sourcePtr = some targetPtr) (found : s.refs.lookup sourcePtr = some (.thunk mode value)) :
    ∃ targetValue, t.refs.lookup targetPtr = some (.thunk mode targetValue) ∧
      vRel s.maxApp f t.refs t.code value targetValue := by
  obtain ⟨target, targetFound, related⟩ := stateRel_ref_lookup states sourcePtr targetPtr _ mapped found
  cases target <;> simp [refRel] at related
  obtain ⟨rfl, valueRel⟩ := related
  exact ⟨_, targetFound, valueRel⟩

/-- Updating a related unevaluated thunk preserves the candidate state
relation and all unmapped target references. -/
theorem updateThunk_related {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (mode : AstHOL.ThunkMode)
    (sourcePtr targetPtr : Nat) (mapped : f.lookup sourcePtr = some targetPtr)
    (old : ClosSem.Value) (found : s.refs.lookup sourcePtr = some (.thunk .notEvaluated old))
    (value : ClosSem.Value) (targetValue : BvlSem.Value) (states : stateRel f s t)
    (valueRel : vRel s.maxApp f t.refs t.code value targetValue)
    (good : ClosSem.badThunkUpdate mode value s.refs = false) :
    let sourceNext := { s with refs := s.refs.updateEq (sourcePtr, .thunk mode value) }
    let targetNext := { t with refs := t.refs.updateEq (targetPtr, .thunk mode targetValue) }
    ClosSem.doApp (.thunkOp (.updateThunk mode)) [.refPtr false sourcePtr, value] s = .val (ClosSem.unitValue, sourceNext) ∧
    BvlSem.doApp (.thunkOp (.updateThunk mode)) [.refPtr false targetPtr, targetValue] t = .val (BvlSem.unitValue, targetNext) ∧
    stateRel f sourceNext targetNext ∧
    vRel s.maxApp f targetNext.refs targetNext.code ClosSem.unitValue BvlSem.unitValue ∧
    unmappedRefsSubmap t.refs targetNext.refs f f := by
  obtain ⟨targetOld, targetFound, _⟩ := stateRel_thunk_lookup s t states sourcePtr targetPtr .notEvaluated old mapped found
  have targetGood := badThunkUpdate_related s t states mode valueRel good
  let targetCell := BvlSem.Ref.thunk mode targetValue
  have frame := mappedUpdate_frame f t.refs sourcePtr targetPtr mapped targetCell
  have submap : relocationSubmap f f := by intro key val lookup; exact lookup
  have grown := vRel_grow_refs valueRel submap frame
  refine ⟨?_, ?_, ?_, .block .nil, frame⟩
  · simp [ClosSem.doApp, good, found]
  · simp [BvlSem.doApp, targetGood, targetFound]
  · exact stateRel_update_mapped s t f sourcePtr targetPtr _ _ states mapped (by simp) ⟨rfl, grown⟩

/-- Successful thunk updates require an unevaluated thunk and an admissible
new value. -/
theorem updateThunk_success {C F : Type} (mode : AstHOL.ThunkMode) (args : List ClosSem.Value)
    (s next : ClosSem.State C F) (result : ClosSem.Value)
    (run : ClosSem.doApp (.thunkOp (.updateThunk mode)) args s = .val (result, next)) :
    ∃ (ptr : Nat) (value old : ClosSem.Value), args = [.refPtr false ptr, value] ∧
      ClosSem.badThunkUpdate mode value s.refs = false ∧ s.refs.lookup ptr = some (.thunk .notEvaluated old) ∧
      result = ClosSem.unitValue ∧ next = { s with refs := s.refs.updateEq (ptr, .thunk mode value) } := by
  cases args with
  | nil => simp [ClosSem.doApp] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp] at run
    | cons value rest =>
      cases rest with
      | cons third rest => simp [ClosSem.doApp] at run
      | nil =>
        cases first <;> simp only [ClosSem.doApp] at run
        all_goals try contradiction
        case refPtr flag ptr =>
          cases flag with
          | true => simp at run
          | false =>
            by_cases bad : ClosSem.badThunkUpdate mode value s.refs = true
            · simp [bad] at run
            · have good : ClosSem.badThunkUpdate mode value s.refs = false := by
                cases h : ClosSem.badThunkUpdate mode value s.refs <;> simp_all
              cases found : s.refs.lookup ptr with
              | none => simp [good, found] at run
              | some cell =>
                cases cell with
                | valueArray values => simp [good, found] at run
                | byteArray bytes => simp [good, found] at run
                | thunk oldMode old =>
                  cases oldMode with
                  | evaluated => simp [good, found] at run
                  | notEvaluated =>
                    simp [good, found] at run
                    exact ⟨ptr, value, old, rfl, good, found, run.1.symm, run.2.symm⟩

/-- Failed thunk updates report a source type error. -/
theorem updateThunk_error {C F : Type} (mode : AstHOL.ThunkMode) (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.thunkOp (.updateThunk mode)) args s = .err error) : error = .abort .typeError := by
  cases args with
  | nil => simpa [ClosSem.doApp] using run.symm
  | cons first rest =>
    cases rest with
    | nil => simpa [ClosSem.doApp] using run.symm
    | cons second rest =>
      cases rest with
      | cons third rest => simpa [ClosSem.doApp] using run.symm
      | nil =>
        cases first <;> simp only [ClosSem.doApp] at run
        all_goals try (simpa using run.symm)
        case refPtr flag ptr =>
          cases flag with
          | true => simpa using run.symm
          | false =>
            by_cases bad : ClosSem.badThunkUpdate mode second s.refs = true
            · simpa [bad] using run.symm
            · have good : ClosSem.badThunkUpdate mode second s.refs = false := by
                cases h : ClosSem.badThunkUpdate mode second s.refs <;> simp_all
              cases found : s.refs.lookup ptr with
              | none => simpa [good, found] using run.symm
              | some cell =>
                cases cell with
                | valueArray values => simpa [good, found] using run.symm
                | byteArray bytes => simpa [good, found] using run.symm
                | thunk oldMode old =>
                  cases oldMode with
                  | evaluated => simpa [good, found] using run.symm
                  | notEvaluated => simp [good, found] at run

/-- Inspecting a related source thunk finds the same mode and a related
payload in the target store. -/
theorem destThunk_isThunk_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    {source : ClosSem.Value} {target : BvlSem.Value}
    (related : vRel s.maxApp f t.refs t.code source target)
    (mode : AstHOL.ThunkMode) (value : ClosSem.Value)
    (found : ClosSem.destThunk [source] s.refs = .isThunk mode value) :
    ∃ targetValue, BvlSem.destThunk target t.refs = .isThunk mode targetValue ∧
      vRel s.maxApp f t.refs t.code value targetValue := by
  cases source with
  | refPtr flag ptr =>
    cases flag with
    | true =>
      cases h : s.refs.lookup ptr with
      | none => simp [ClosSem.destThunk, h] at found
      | some cell => cases cell <;> simp [ClosSem.destThunk, h] at found
    | false =>
      cases h : s.refs.lookup ptr with
      | none => simp [ClosSem.destThunk, h] at found
      | some cell =>
        cases cell with
        | valueArray values => simp [ClosSem.destThunk, h] at found
        | byteArray bytes => simp [ClosSem.destThunk, h] at found
        | thunk oldMode oldValue =>
          simp [ClosSem.destThunk, h] at found
          rcases found with ⟨rfl, rfl⟩
          obtain ⟨targetPtr, rfl, mapped⟩ := vRel_refPtr_inv related
          obtain ⟨targetValue, targetFound, valueRel⟩ :=
            stateRel_thunk_lookup s t states ptr targetPtr oldMode oldValue mapped h
          exact ⟨targetValue, by simp [BvlSem.destThunk, targetFound], valueRel⟩
  | _ => simp [ClosSem.destThunk] at found

/-- A successful source thunk inspection can only inspect one correctly
flagged reference to a thunk cell. -/
theorem destThunk_isThunk_shape (values : List ClosSem.Value)
    (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (mode : AstHOL.ThunkMode) (value : ClosSem.Value)
    (found : ClosSem.destThunk values refs = .isThunk mode value) :
    ∃ ptr, values = [.refPtr false ptr] ∧ refs.lookup ptr = some (.thunk mode value) := by
  cases values with
  | nil => simp [ClosSem.destThunk] at found
  | cons first rest =>
    cases rest with
    | cons second rest => simp [ClosSem.destThunk] at found
    | nil =>
      cases first <;> simp only [ClosSem.destThunk] at found
      all_goals try contradiction
      case refPtr flag ptr =>
        cases flag with
        | true =>
          cases h : refs.lookup ptr with
          | none => simp [h] at found
          | some cell => cases cell <;> simp [h] at found
        | false =>
          cases h : refs.lookup ptr with
          | none => simp [h] at found
          | some cell =>
            cases cell with
            | valueArray values => simp [h] at found
            | byteArray bytes => simp [h] at found
            | thunk oldMode oldValue =>
              simp [h] at found
              rcases found with ⟨rfl, rfl⟩
              exact ⟨ptr, rfl, h⟩

end Flapjack.Compiler.Backend.ClosToBvl
