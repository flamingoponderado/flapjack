import Flapjack.Compiler.Backend.RegAlloc.ProductionInitialSeed
import Flapjack.Compiler.Backend.RegAlloc.ProductionSimplify
import Flapjack.Compiler.Backend.RegAlloc.Proofs.CoalesceSuccess

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem setFold_length {α : Type} (nodes : List Nat) (values : List α) (value : α) :
    (nodes.foldl (fun values node => values.set node value) values).length = values.length := by
  induction nodes generalizing values with
  | nil => rfl
  | cons node rest ih => simpa only [List.foldl_cons, List.length_set] using ih (values.set node value)

private theorem setFold_get {α : Type} (nodes : List Nat) (values : List α) (value : α)
    (index : Nat) (bound : index < values.length) :
    (nodes.foldl (fun values node => values.set node value) values)[index]? =
      if index ∈ nodes then some value else values[index]? := by
  induction nodes generalizing values with
  | nil => simp
  | cons node rest ih =>
    rw [List.foldl_cons, ih (values.set node value) (by simpa using bound)]
    by_cases member : index ∈ rest
    · simp [member]
    · by_cases equal : index = node
      · subst index
        simp [member, bound]
      · simp [member, equal, Ne.symm equal, List.getElem?_set_ne]

/-- Clearing each list index produces the complete replicated list, for every
initial payload. This bulk-reset codec fact has no independent HOL original. -/
theorem moveReset_list_range (values : List Bool) :
    (List.range values.length).foldl (fun values node => values.set node false) values =
      List.replicate values.length false := by
  apply List.ext_getElem?
  intro index
  by_cases bound : index < values.length
  · rw [setFold_get _ _ _ index bound]
    simp [bound]
  · rw [List.getElem?_eq_none (by rw [setFold_length]; omega)]
    simp [bound]

private theorem moveWrites_foreach (nodes : List Nat) (native : State) (value : Bool)
    (bounds : ∀ node ∈ nodes, node < native.move_related.length) :
    stExForeach nodes (fun node => updateMoveRelated node value) native =
      (.success (), {native with
        move_related :=
        nodes.foldl (fun values node => values.set node value) native.move_related}) := by
  induction nodes generalizing native with
  | nil => rfl
  | cons node rest ih =>
    have bound := bounds node List.mem_cons_self
    have tailBounds : ∀ next ∈ rest,
        next < ({native with move_related := native.move_related.set node value} : State).move_related.length := by
      intro next member
      simpa only [List.length_set] using bounds next (List.mem_cons_of_mem node member)
    simp only [stExForeach, ignoreBind, updateMoveRelatedEqn, if_pos bound]
    rw [ih _ tailBounds]
    rfl

private theorem moveClear_foreach (native : State) (good : goodRaState native) :
    stExForeach (List.range native.dim) (fun node => updateMoveRelated node false) native =
      (.success (), {native with move_related := List.replicate native.dim false}) := by
  rw [← good.2.2.2.2.1]
  rw [moveWrites_foreach _ _ _ (fun _ member => List.mem_range.mp member)]
  rw [moveReset_list_range]
  simp only [good.2.2.2.2.1]

/-- Complete Fixed-tag query correspondence at an original valid node. The
bound and constructor translation are derived, not supplied lookup values.
Flapjack infrastructure, without a separate HOL original. -/
theorem isFixed_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bound : node < native.dim) :
    isFixed node native = (.success (cakeIsFixed production node), native) := by
  have tagBound : node < native.node_tag.length := by rwa [good.2.1]
  have tagRead := related.tag_read node tagBound
  simp only [isFixed, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, if_pos tagBound,
    holEl_eq_getElem node native.node_tag tagBound, ret, cakeIsFixed, tagRead, Option.getD_some]
  cases native.node_tag[node] <;> rfl

private def markEndpoints (state : CakeRaState) (move : Nat × (Nat × Nat)) : CakeRaState :=
  {state with
    moveRelated :=
      (state.moveRelated.set move.2.1 (!cakeIsFixed state move.2.1)).set
        move.2.2 (!cakeIsFixed state move.2.2)}

private def nativeMarkEndpoints (move : Nat × (Nat × Nat)) : M State Unit StateException :=
  bind (isFixed move.2.1) fun left =>
    bind (isFixed move.2.2) fun right =>
      ignoreBind (updateMoveRelated move.2.1 (!left)) (updateMoveRelated move.2.2 (!right))

private theorem markEndpoints_production (move : Nat × (Nat × Nat))
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : move.2.1 < native.dim ∧ move.2.2 < native.dim) :
    ∃ result : State, nativeMarkEndpoints move native = (.success (), result) ∧
      goodRaState result ∧ ProductionStateRel result (markEndpoints production move) ∧
      result.dim = native.dim := by
  let result : State := {native with
    move_related :=
      (native.move_related.set move.2.1 (!cakeIsFixed production move.2.1)).set
        move.2.2 (!cakeIsFixed production move.2.2)}
  have left := isFixed_production move.2.1 related good bounds.1
  have right := isFixed_production move.2.2 related good bounds.2
  have leftBound : move.2.1 < native.move_related.length := by
    simpa only [good.2.2.2.2.1] using bounds.1
  have rightBound : move.2.2 < native.move_related.length := by
    simpa only [good.2.2.2.2.1] using bounds.2
  refine ⟨result, ?_, ?_, ?_, rfl⟩
  · simp only [nativeMarkEndpoints, Translator.Monadic.MonadBase.bind, left, right,
      ignoreBind, updateMoveRelatedEqn, if_pos leftBound, List.length_set, if_pos rightBound]
    rfl
  · obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
    exact ⟨a,b,c,d,(List.length_set.trans List.length_set).trans e,f,g,h,i,j,k,l,m,n⟩
  · exact (related.moveRelated_write move.2.1 _ leftBound).moveRelated_write move.2.2 _
      (by simpa only [List.length_set] using rightBound)


private theorem markEndpoints_foreach (moves : List (Nat × (Nat × Nat)))
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ move ∈ moves, move.2.1 < native.dim ∧ move.2.2 < native.dim) :
    ∃ result : State, stExForeach moves nativeMarkEndpoints native = (.success (), result) ∧
      goodRaState result ∧ ProductionStateRel result (moves.foldl markEndpoints production) ∧
      result.dim = native.dim := by
  induction moves generalizing native production with
  | nil => exact ⟨native, rfl, good, related, rfl⟩
  | cons move rest ih =>
    obtain ⟨first, run, goodFirst, represented, dimension⟩ :=
      markEndpoints_production move related good (bounds move List.mem_cons_self)
    obtain ⟨result, tailRun, goodResult, finalRel, finalDim⟩ := ih represented goodFirst (by
      intro next member
      rw [dimension]
      exact bounds next (List.mem_cons_of_mem move member))
    refine ⟨result, ?_, goodResult, finalRel, finalDim.trans dimension⟩
    simpa only [stExForeach, ignoreBind, run] using tailRun

private theorem markEndpoints_fold (moves : List (Nat × (Nat × Nat))) (production : CakeRaState) :
    moves.foldl markEndpoints production = {production with
      moveRelated := moves.foldl (fun flags move =>
        (flags.set move.2.1 (!cakeIsFixed production move.2.1)).set
          move.2.2 (!cakeIsFixed production move.2.2)) production.moveRelated} := by
  induction moves generalizing production with
  | nil => rfl
  | cons move rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rfl

/-- Actual bulk clearing and endpoint marking implement the complete native
reset_move_related transition under the original success invariant and move
bounds. All lookup domains, native success, phase order and final represented
fields are derived. This cross-implementation theorem has no independent HOL
original and does not establish prefreeze or the whole allocator by itself. -/
theorem resetMoveRelated_production (moves : List (Nat × (Nat × Nat)))
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (bounds : ∀ move ∈ moves, move.2.1 < native.dim ∧ move.2.2 < native.dim) :
    ∃ result : State, resetMoveRelated moves native = (.success (), result) ∧
      ProductionStateRel result (cakeResetMoveRelated moves production) := by
  let cleared : State := {native with move_related := List.replicate native.dim false}
  let actualCleared : CakeRaState := {production with
    moveRelated := CakeNodeMap.filled production.dim false}
  have clearRel : ProductionStateRel cleared actualCleared :=
    {related with
      moveRelated := by
        change CakeNodeMap.RepresentsHOLNodeList
          (CakeNodeMap.filled production.dim false) (List.replicate native.dim false)
        rw [related.dimension]
        exact filled_representsHOLNodeList _ _}
  have goodClear : goodRaState cleared := by
    obtain ⟨a,b,c,d,_,f,g,h,i,j,k,l,m,n⟩ := good
    exact ⟨a,b,c,d,List.length_replicate,f,g,h,i,j,k,l,m,n⟩
  obtain ⟨result, run, _, represented, _⟩ := markEndpoints_foreach moves clearRel goodClear bounds
  have source : resetMoveRelated moves native = (.success (), result) := by
    simp only [resetMoveRelated, Translator.Monadic.MonadBase.bind, getDim, ignoreBind,
      moveClear_foreach native good]
    exact run
  have actual : cakeResetMoveRelated moves production = moves.foldl markEndpoints actualCleared := by
    rw [markEndpoints_fold]
    rfl
  refine ⟨result, source, ?_⟩
  simpa only [actual] using represented

end Flapjack.RegAlloc
