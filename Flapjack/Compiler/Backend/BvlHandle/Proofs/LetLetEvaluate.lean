import Flapjack.Compiler.Backend.BvlHandle.Proofs.EnvRel
import Flapjack.Compiler.Backend.BvlHandle.Proofs.LetLet
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Evaluation of the handler compiler's environment-packing bindings. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.DbVars
open Flapjack.Compiler.Backend.BvlSem

/-- Evaluating a list of variable references reads each specified value in
order and does not change the state. -/
theorem evaluate_vars {C F : Type} (indices : List Nat) (env : List Value)
    (state : State C F) (value : Nat → Value)
    (lookup : ∀ index ∈ indices, env[index]? = some (value index)) :
    evaluate (indices.map Bvl.Exp.var) env state = (.val (indices.map value), state) := by
  induction indices with
  | nil => simp [evaluate]
  | cons index indices ih =>
    have head := lookup index (by simp)
    have tail : ∀ i ∈ indices, env[i]? = some (value i) := by
      intro i member
      exact lookup i (by simp [member])
    have cons := BvlProps.evaluateCons (.var index) (indices.map Bvl.Exp.var) env state
    simp only [evaluateTuple] at cons
    rw [List.map_cons, cons]
    simp [evaluate, head, ih tail, Flapjack.holHd]

/-- The first let in environment packing extracts exactly the original
values at the live indices, even when the target environment has a suffix. -/
theorem evaluate_retained_vars {C F : Type} (live : DbVarSet)
    (source target extra : List Value) (state : State C F)
    (related : envRel live source target) :
    let retained := (List.range source.length).filter (fun n => (sptLookup n (dbToSet live)).isSome)
    evaluate (retained.map Bvl.Exp.var) (target ++ extra) state =
      (.val (retained.map fun i => (source[i]?).getD (.number 0)), state) := by
  dsimp only
  apply evaluate_vars
  intro index member
  have bounds : index < source.length := by
    have h := (List.mem_filter.mp member).1
    simpa using h
  have present : hasVar index live = true := by
    have h := (List.mem_filter.mp member).2
    simpa [isSomeLookupDbToSet] using h
  rw [envRel_live_lookup live source target extra related index bounds present]
  cases h : source[index]? with
  | none =>
    have := List.getElem?_eq_none_iff.mp h
    omega
  | some value => simp

/-- A successful packed-index lookup identifies the corresponding original
index, including when the input list contains duplicates. -/
theorem lookup_zipIdx_getElem (indices : List Nat) (index packed : Nat)
    (found : indices.zipIdx.lookup index = some packed) :
    indices[packed]? = some index := by
  obtain ⟨before, after, eq, _⟩ := List.lookup_eq_some_iff.mp found
  have member : (index, packed) ∈ indices.zipIdx := by rw [eq]; simp
  exact List.mk_mem_zipIdx_iff_getElem?.mp member

/-- An absent packed-index lookup means that the index was not retained. -/
theorem lookup_zipIdx_none (indices : List Nat) (index : Nat)
    (missing : indices.zipIdx.lookup index = none) : index ∉ indices := by
  intro member
  obtain ⟨packed, found⟩ := List.getElem?_of_mem member
  have packedMember : (index, packed) ∈ indices.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr found
  have := (List.lookup_eq_none_iff.mp missing) (index, packed) packedMember
  simp at this

/-- A reconstructed binding either reads the retained value for a live
index or produces zero for a non-live index. -/
theorem evaluate_reconstructed_binding {C F : Type} (live : DbVarSet)
    (size index : Nat) (bound : index < size) (value : Nat → Value)
    (rest : List Value) (state : State C F) :
    let retained := (List.range size).filter (fun n => (sptLookup n (dbToSet live)).isSome)
    let expression := match retained.zipIdx.lookup index with
      | some packed => Bvl.Exp.var packed
      | none => zero
    evaluate [expression] ((retained.map value) ++ rest) state =
      (.val [if hasVar index live then value index else .number 0], state) := by
  dsimp only
  let retained := (List.range size).filter (fun n => (sptLookup n (dbToSet live)).isSome)
  change evaluate [match retained.zipIdx.lookup index with
    | some packed => Bvl.Exp.var packed | none => zero] ((retained.map value) ++ rest) state = _
  cases found : retained.zipIdx.lookup index with
  | none =>
    have notMember := lookup_zipIdx_none retained index found
    have notLive : hasVar index live = false := by
      cases h : hasVar index live with
      | false => rfl
      | true =>
        have member : index ∈ retained := by
          simp [retained, bound, isSomeLookupDbToSet, h]
        exact False.elim (notMember member)
    simp [notLive, zero, evaluate, doApp, applyNumeric, doIntApp, fixClock]
  | some packed =>
    have slot := lookup_zipIdx_getElem retained index packed found
    have member : index ∈ retained := List.mem_of_getElem? slot
    have present : hasVar index live = true := by
      have h := (List.mem_filter.mp member).2
      simpa [isSomeLookupDbToSet] using h
    have packedBound : packed < retained.length := (List.getElem?_eq_some_iff.mp slot).1
    have slotEq : retained[packed] = index := (List.getElem?_eq_some_iff.mp slot).2
    have read : ((retained.map value) ++ rest)[packed]? = some (value index) := by
      simp [List.getElem?_append, packedBound, slotEq]
    simp [present, evaluate, read]

/-- Independent, state-preserving singleton evaluations compose in order. -/
theorem evaluate_map_pure {C F : Type} (indices : List Nat) (expression : Nat → Bvl.Exp)
    (value : Nat → Value) (env : List Value) (state : State C F)
    (runs : ∀ index ∈ indices, evaluate [expression index] env state = (.val [value index], state)) :
    evaluate (indices.map expression) env state = (.val (indices.map value), state) := by
  induction indices with
  | nil => simp [evaluate]
  | cons index indices ih =>
    have head := runs index (by simp)
    have tail : ∀ i ∈ indices, evaluate [expression i] env state = (.val [value i], state) := by
      intro i member
      exact runs i (by simp [member])
    have cons := BvlProps.evaluateCons (expression index) (indices.map expression) env state
    simp only [evaluateTuple] at cons
    rw [List.map_cons, cons]
    simp [head, ih tail, Flapjack.holHd]

/-- The second set of bindings reconstructs the source environment with
non-live positions replaced by zero. -/
theorem evaluate_reconstructed_vars {C F : Type} (live : DbVarSet)
    (source : List Value) (rest : List Value) (state : State C F) :
    let retained := (List.range source.length).filter (fun n => (sptLookup n (dbToSet live)).isSome)
    let expression := fun index => match retained.zipIdx.lookup index with
      | some packed => Bvl.Exp.var packed
      | none => zero
    let value := fun i => (source[i]?).getD (.number 0)
    evaluate ((List.range source.length).map expression) ((retained.map value) ++ rest) state =
      (.val (source.mapIdx fun index v => if hasVar index live then v else .number 0), state) := by
  dsimp only
  let retained := (List.range source.length).filter (fun n => (sptLookup n (dbToSet live)).isSome)
  let expression := fun index => match retained.zipIdx.lookup index with
    | some packed => Bvl.Exp.var packed | none => zero
  let value : Nat → Value := fun i => (source[i]?).getD (.number 0)
  have runs := evaluate_map_pure (List.range source.length) expression
    (fun i => if hasVar i live then value i else .number 0) ((retained.map value) ++ rest) state (by
      intro index member
      exact evaluate_reconstructed_binding live source.length index (by simpa using member) value rest state)
  have valuesEq : (List.range source.length).map (fun i => if hasVar i live then value i else .number 0) =
      source.mapIdx (fun index v => if hasVar index live then v else .number 0) := by
    apply List.ext_getElem
    · simp
    · intro index leftBound rightBound
      have bound : index < source.length := by simpa using rightBound
      simp [value, List.getElem_mapIdx, bound]
  exact runs.trans (by rw [valuesEq])

/-- The handler pass's environment packer preserves any body evaluation
that depends only on live variables. This is untagged while the underlying
BVL evaluator and indexed environment relation await HOL correspondence review. -/
theorem evaluate_letLet {C F : Type} (live : DbVarSet) (body : Bvl.Exp)
    (source target extra : List Value) (state : State C F)
    (result : SemanticPrimitivesHOL.Result (List Value) Value × State C F)
    (bodyRun : ∀ env suffix, envRel live source env → evaluate [body] (env ++ suffix) state = result)
    (related : envRel live source target) :
    evaluate [letLet source.length (dbToSet live) body] (target ++ extra) state = result := by
  let retained := (List.range source.length).filter (fun n => (sptLookup n (dbToSet live)).isSome)
  let value : Nat → Value := fun i => (source[i]?).getD (.number 0)
  let long := (List.range source.length).map fun index =>
    match retained.zipIdx.lookup index with
    | some packed => Bvl.Exp.var packed | none => zero
  let masked := source.mapIdx fun index v => if hasVar index live then v else .number 0
  have retainedRun := evaluate_retained_vars live source target extra state related
  change evaluate (retained.map Bvl.Exp.var) (target ++ extra) state =
    (.val (retained.map value), state) at retainedRun
  have rebuiltRun := evaluate_reconstructed_vars live source (target ++ extra) state
  change evaluate long ((retained.map value) ++ (target ++ extra)) state =
    (.val masked, state) at rebuiltRun
  have finalRun := bodyRun masked ((retained.map value) ++ (target ++ extra))
    (envRel_mask live source)
  have definition : letLet source.length (dbToSet live) body =
      .let (retained.map Bvl.Exp.var) (smartLet long body) := by
    simp [letLet, retained, long, List.zipIdx_eq_zip_range', ← List.range_eq_range']
    rfl
  rw [definition, evaluate, fixClock_evaluate, retainedRun]
  simp only
  by_cases empty : source = []
  · subst source
    simpa [retained, value, long, masked, smartLet] using finalRun
  · have nonempty : long.isEmpty = false := by
      simp [long, empty]
    simp only [smartLet, nonempty, Bool.false_eq_true, ↓reduceIte, evaluate, fixClock_evaluate]
    rw [rebuiltRun]
    simpa [List.append_assoc] using finalRun

/-- Both branches of the singleton size cut preserve the body's evaluation
under the live-variable relation returned by the cut. Untagged pending
review of the evaluator and environment relation against HOL. -/
theorem evaluate_optionalLetLetSing {C F : Type} (live : DbVarSet) (body : Bvl.Exp)
    (size limit : Nat) (noRaise : Bool) (source target extra : List Value)
    (state : State C F) (result : SemanticPrimitivesHOL.Result (List Value) Value × State C F)
    (bodyRun : ∀ env suffix, envRel live source env → evaluate [body] (env ++ suffix) state = result)
    (related : envRel (optionalLetLetSing body source.length live size limit noRaise).2.1 source target) :
    evaluate [(optionalLetLetSing body source.length live size limit noRaise).1] (target ++ extra) state = result := by
  by_cases small : size < limit
  · simp only [optionalLetLetSing, small, ↓reduceIte] at related ⊢
    exact bodyRun target extra related
  · simp only [optionalLetLetSing, small, ↓reduceIte] at related ⊢
    have related' : envRel live source target := (envRel_flatten live source target).mp related
    have run := evaluate_letLet live body source target extra state result bodyRun related'
    simpa [evaluate, fixClock] using run

/-- The list-valued size cut has the same evaluation behavior as the
singleton cut, with the same returned live-variable relation. -/
theorem evaluate_optionalLetLet {C F : Type} (live : DbVarSet) (body : Bvl.Exp)
    (size limit : Nat) (noRaise : Bool) (source target extra : List Value)
    (state : State C F) (result : SemanticPrimitivesHOL.Result (List Value) Value × State C F)
    (bodyRun : ∀ env suffix, envRel live source env → evaluate [body] (env ++ suffix) state = result)
    (related : envRel (optionalLetLet body source.length live size limit noRaise).2.1 source target) :
    evaluate (optionalLetLet body source.length live size limit noRaise).1 (target ++ extra) state = result := by
  by_cases small : size < limit
  · simp only [optionalLetLet, small, ↓reduceIte] at related ⊢
    exact bodyRun target extra related
  · simp only [optionalLetLet, small, ↓reduceIte] at related ⊢
    have related' : envRel live source target := (envRel_flatten live source target).mp related
    have run := evaluate_letLet live body source target extra state result bodyRun related'
    simpa [evaluate, fixClock] using run

end Flapjack.Compiler.Backend.BvlHandle.Proofs
