import Flapjack.Compiler.Backend.ClosToBvl.Proofs.RecursiveValues
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshTargetRefs

/-! State and value relations for a completed recursive closure array. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- If a fresh target array contains the completed recursive blocks and their
captured values, allocating it preserves the source state relation and makes
the complete recursive closure bundle pointwise related. The generated BVL
program initially allocates placeholders and fills the array; proving that
execution sequence reaches this completed layout is a separate obligation. -/
theorem recursiveValues_allocate {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (functions : List (Nat × ClosLang.Exp)) (label : Nat)
    (sourceValues : List ClosSem.Value) (targetValues : List BvlSem.Value)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Bvl.Exp))
    (states : stateRel f s t)
    (valuesRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceValues targetValues)
    (length : 1 < functions.length)
    (locations : ClosProps.everyFnLocationSome (functions.map Prod.snd))
    (varsAnnotated : ClosProps.everyFnVarsSome (functions.map Prod.snd))
    (run : compileExpFunsHOL s.maxApp functions aux = (compiled, finalAux))
    (installed : codeInstalled (buildAux (label + numStubs s.maxApp)
      (compiled.map (fun (n, exp) => codeForReccCase (sourceValues.length + functions.length) n exp)) finalAux).2 t.code)
    (valid : ∀ n body, (n, body) ∈ functions → n ≤ s.maxApp ∧ n ≠ 0) :
    let ptr := BvlSem.leastUnusedRef t.refs
    let entries := recursiveEntries functions (label + numStubs s.maxApp)
    let targets := recursiveValues entries ptr
    let next := { t with refs := t.refs.updateEq (ptr, .valueArray (targets ++ targetValues)) }
    stateRel f s next ∧ unmappedRefsSubmap t.refs next.refs f f ∧
    (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
    List.Forall₂ (vRel s.maxApp f next.refs next.code)
      ((List.range functions.length).map (fun index => .recclosure (some label) [] sourceValues functions index)) targets := by
  dsimp only
  let ptr := BvlSem.leastUnusedRef t.refs
  let entries := recursiveEntries functions (label + numStubs s.maxApp)
  let targets := recursiveValues entries ptr
  let newRefs := t.refs.updateEq (ptr, .valueArray (targets ++ targetValues))
  have allocated := stateRel_targetRefs_allocate s t f (.valueArray (targets ++ targetValues)) states
  change stateRel f s { t with refs := newRefs } ∧ unmappedRefsSubmap t.refs newRefs f f ∧
    (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
    newRefs.lookup ptr = some (.valueArray (targets ++ targetValues)) at allocated
  obtain ⟨nextState, frame, fresh, stored⟩ := allocated
  have submap : relocationSubmap f f := by intro key value found; exact found
  have newValuesRel : List.Forall₂ (vRel s.maxApp f newRefs t.code) sourceValues targetValues :=
    valuesRel.imp (fun _ _ related => vRel_grow_refs related submap frame)
  have codeInstalled' : closureCodeInstalled s.maxApp t.code entries sourceValues := by
    simpa [entries, recursiveEntries] using
      recursiveFunctions_closureCodeInstalled s.maxApp functions aux finalAux compiled t.code label sourceValues run installed valid
  have groupRelated := recursiveValues_related s.maxApp f newRefs t.code functions label ptr sourceValues targetValues
    newValuesRel fresh stored length locations varsAnnotated codeInstalled'
  exact ⟨nextState, frame, fresh, groupRelated⟩

end Flapjack.Compiler.Backend.ClosToBvl
