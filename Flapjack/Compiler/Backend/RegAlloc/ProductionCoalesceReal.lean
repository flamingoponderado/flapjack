import Flapjack.Compiler.Backend.RegAlloc.ProductionEdgeUpdate

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Actual bounded degree increment agrees with the native monadic read/write
and preserves the complete state relation. The input representation supplies
the read value; no successful lookup or post-state premise is added. This is
actual/native infrastructure, without a separate HOL original. -/
theorem incDeg_production (node amount : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (bound : node < native.degrees.length) :
    ∃ result, incDeg node amount native = (.success (), result) ∧
      result.degrees.length = native.degrees.length ∧
      ProductionStateRel result (cakeIncDeg node amount production) := by
  let value := native.degrees[node] + amount
  refine ⟨{native with degrees := native.degrees.set node value}, ?_, List.length_set, ?_⟩
  · simp [incDeg, Translator.Monadic.MonadBase.bind, degreesSubEqn, updateDegreesEqn,
      bound, holEl_eq_getElem node native.degrees bound, value]
  · simpa only [cakeIncDeg, related.degree_read node bound, Option.getD_some, value] using
      related.degree_write node value bound

/-- The original coalescing parent update represents the full actual state;
all other fields and the cache remain related. This primitive transport has
no separate HOL declaration and does not assert the complete phase. -/
theorem coalesceParentWrite_production (node parent : Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (bound : node < native.coalesced.length) :
    updateCoalesced node parent native =
      (.success (), {native with coalesced := native.coalesced.set node parent}) ∧
    ProductionStateRel {native with coalesced := native.coalesced.set node parent}
      {production with coalesced := production.coalesced.set node parent} := by
  exact ⟨by simp [updateCoalescedEqn, bound], related.parent_write node parent bound⟩

private theorem good_parent {native : State} (good : goodRaState native) (node parent : Nat)
    (parentBound : parent < native.dim) :
    goodRaState {native with coalesced := native.coalesced.set node parent} := by
  obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
  refine ⟨a,b,c,List.length_set.trans d,e,?_,g,h,i,j,k,l,m,n⟩
  intro value member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact f value old
  · exact parentBound

private theorem good_degrees {native : State} {degrees : List Nat}
    (good : goodRaState native) (length : degrees.length = native.degrees.length) :
    goodRaState {native with degrees := degrees} := by
  obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n⟩ := good
  exact ⟨a,b,length.trans c,d,e,f,g,h,i,j,k,l,m,n⟩

private theorem conditionalIncrement_production (node amount : Nat)
    {native : State} {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) (bound : node < native.dim) :
    ∃ result,
      (if cakeIsFixed production node then ret () else incDeg node amount) native = (.success (), result) ∧
      goodRaState result ∧ result.dim = native.dim ∧
      ProductionStateRel result (if !cakeIsFixed production node then cakeIncDeg node amount production else production) := by
  cases fixed : cakeIsFixed production node with
  | true => exact ⟨native, by simp [ret], good, rfl, by simpa [fixed] using related⟩
  | false =>
    have degreeBound : node < native.degrees.length := by rwa [good.2.2.1]
    let degrees := native.degrees.set node (native.degrees[node] + amount)
    have run : incDeg node amount native = (.success (), {native with degrees := degrees}) := by
      simp [incDeg, Translator.Monadic.MonadBase.bind, degreesSubEqn, updateDegreesEqn,
        degreeBound, holEl_eq_getElem node native.degrees degreeBound, degrees]
    refine ⟨{native with degrees := degrees}, by simpa [fixed] using run,
      good_degrees good (List.length_set), rfl, ?_⟩
    simpa only [fixed, Bool.not_false, Bool.false_eq_true, if_false, if_true,
      cakeIncDeg, related.degree_read node degreeBound, Option.getD_some, degrees] using
      related.degree_write node (native.degrees[node] + amount) degreeBound

private theorem foreach_single (action : Nat → M State Unit StateException) (node : Nat) (state : State) :
    stExForeach [node] action state = action node state := by
  simp only [stExForeach, ignoreBind, ret]
  cases action node state with
  | mk result final =>
    cases result with
    | success payload => cases payload; rfl
    | failure error => rfl

/-- The complete actual real-coalescing update has the native unit result and
represents every post-state field, including its updated query cache. Its
domains and intermediate good states follow from the original good state and
endpoint/case bounds. This is actual/native infrastructure, not a duplicate
port of do_coalesce_real_success; the chooser and initializer remain separate. -/
theorem doCoalesceReal_production (x y : Nat) (case1 case2 : List Nat)
    {native : State} {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) (xBound : x < native.dim) (yBound : y < native.dim)
    (case1Bound : ∀ node ∈ case1, node < native.dim)
    (case2Bound : ∀ node ∈ case2, node < native.dim) :
    ∃ result, doCoalesceReal x y case1 case2 native = (.success (), result) ∧
      ProductionStateRel result (cakeDoCoalesceReal x y case1 case2 production) := by
  let parented := {native with coalesced := native.coalesced.set y x}
  let actualParented := {production with coalesced := production.coalesced.set y x}
  have parentBound : y < native.coalesced.length := by rwa [good.2.2.2.1]
  obtain ⟨parentRun, parentRel⟩ := coalesceParentWrite_production y x related parentBound
  have parentGood : goodRaState parented := good_parent good y x xBound
  have fixedRun := isFixed_production x parentRel parentGood xBound
  obtain ⟨incremented, incrementRun, incrementGood, incrementDim, incrementRel⟩ :=
    conditionalIncrement_production x case2.length parentRel parentGood xBound
  let actualIncremented := if !cakeIsFixed actualParented x then
    cakeIncDeg x case2.length actualParented else actualParented
  have edgeXBound : x < incremented.adj_ls.length := by rw [incrementGood.1, incrementDim]; exact xBound
  have edgeBounds : ∀ node ∈ case2, node < incremented.adj_ls.length := by
    intro node member
    rw [incrementGood.1, incrementDim]
    exact case2Bound node member
  obtain ⟨edged, edgeRun, _, edgeRel⟩ := listInsertEdge_production x case2 incrementRel edgeXBound edgeBounds
  obtain ⟨nativeEdged, nativeEdgeRun, edgeGood, edgeShape, _⟩ :=
    listInsertEdgeSucceeds case2 x incremented ⟨incrementGood, by rwa [incrementDim],
      fun node member => by rw [incrementDim]; exact case2Bound node member⟩
  have edgeEq := congrArg Prod.snd (edgeRun.symm.trans nativeEdgeRun)
  simp only at edgeEq
  subst nativeEdged
  have edgeDim : edged.dim = native.dim := by
    have shape := congrArg State.dim edgeShape
    exact shape.trans incrementDim
  obtain ⟨degrees, degreeRun, degreeLength⟩ := decDegSuccess case1 edged
    ⟨fun node member => by rw [edgeDim]; exact case1Bound node member, edgeGood⟩
  have degreeRel := degreeForeach_production case1 edgeRel
  rw [degreeRun] at degreeRel
  simp only [ProductionLatchedUnitRel] at degreeRel
  have degreeGood := good_degrees edgeGood degreeLength
  have pushBound : y < ({edged with degrees := degrees} : State).dim := by rwa [edgeDim]
  obtain ⟨pushed, pushRun, pushRel⟩ := pushStack_foreach_production [y] degreeRel degreeGood
    (by simpa using pushBound)
  rw [foreach_single] at pushRun
  refine ⟨pushed, ?_, ?_⟩
  · simp only [doCoalesceReal, ignoreBind, parentRun, Translator.Monadic.MonadBase.bind,
      fixedRun, incrementRun, edgeRun, degreeRun, pushRun]
  · simpa only [cakeDoCoalesceReal, actualParented, actualIncremented, List.foldl_cons,
      List.foldl_nil] using pushRel

end Flapjack.RegAlloc
