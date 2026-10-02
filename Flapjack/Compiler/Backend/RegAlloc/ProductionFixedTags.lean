import Flapjack.RiscV.CakeRegAlloc

/-!
Production tag preservation needed by the executed Word-to-Stack caller.
Source comparison: reg_allocScript degree updates, worklist phases, parent
compression, initialization and assignment only update tags in assign_Atemp_tag
and assign_Stemp_tag; those branches require an Atemp or Stemp input tag.
The captured reg_alloc_phase_closure_probe records the original monadic phase
order. These proofs follow the actual CakeRaState wrappers, including latched
failure and missing-degree-slot behavior absent from the original HOL list
carrier. Consequently they are Flapjack implementation invariants, deliberately
untagged, and do not establish native monadic phase equivalence. Initial mk_tags
ownership, optimized bijection/index correspondence, and extracted colour lookup
remain separate obligations before physical ABI colour or caller bounds follow.
-/

namespace Flapjack
open RiscV RiscV.CakeRegAlloc

/-- A concrete assignment step cannot overwrite an existing fixed node.
Flapjack-only production invariant; it is not the native monadic HOL theorem. -/
theorem assignAtempTag_preserves_fixed (k node fixedNode register : Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat) (state : CakeRaState)
    (fixed : state.nodeTag.get fixedNode = some (.fixed register)) :
    (cakeAssignAtempTag k prefs node state).nodeTag.get fixedNode =
      some (.fixed register) := by
  by_cases equal : node = fixedNode
  · subst node
    simp [cakeAssignAtempTag, fixed]
  · unfold cakeAssignAtempTag
    split
    · dsimp only
      split
      · simp [CakeNodeMap.get_set_of_ne, equal, fixed]
      · split <;> simp [CakeNodeMap.get_set_of_ne, equal, fixed]
    · exact fixed

/-- The production spill-assignment step likewise preserves fixed nodes.
No colour preference correctness or target bound is assumed. -/
theorem assignStempTag_preserves_fixed (k node fixedNode register : Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat) (state : CakeRaState)
    (fixed : state.nodeTag.get fixedNode = some (.fixed register)) :
    (cakeAssignStempTag k prefs node state).nodeTag.get fixedNode =
      some (.fixed register) := by
  by_cases equal : node = fixedNode
  · subst node
    simp [cakeAssignStempTag, fixed]
  · unfold cakeAssignStempTag
    split
    · dsimp only
      split <;> simp [CakeNodeMap.get_set_of_ne, equal, fixed]
    · exact fixed

private theorem fold_preserves_fixed (step : CakeRaState → Nat → CakeRaState)
    (preserves : ∀ state node fixedNode register,
      state.nodeTag.get fixedNode = some (.fixed register) →
      (step state node).nodeTag.get fixedNode = some (.fixed register))
    (nodes : List Nat) (state : CakeRaState) (fixedNode register : Nat)
    (fixed : state.nodeTag.get fixedNode = some (.fixed register)) :
    (nodes.foldl step state).nodeTag.get fixedNode = some (.fixed register) := by
  induction nodes generalizing state with
  | nil => exact fixed
  | cons head tail ih => exact ih (step state head) (preserves state head _ _ fixed)

/-- Both actual register-assignment traversals preserve already fixed nodes,
including indices outside the dense array. Production invariant only. -/
theorem assignAtemps_preserves_fixed (k fixedNode register : Nat) (nodes : List Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat) (state : CakeRaState)
    (fixed : state.nodeTag.get fixedNode = some (.fixed register)) :
    (cakeAssignAtemps k nodes prefs state).nodeTag.get fixedNode =
      some (.fixed register) := by
  unfold cakeAssignAtemps
  apply fold_preserves_fixed (fun s n => cakeAssignAtempTag k prefs n s)
    (fun s n f r h => assignAtempTag_preserves_fixed k n f r prefs s h)
  exact fold_preserves_fixed (fun s n => cakeAssignAtempTag k prefs n s)
    (fun s n f r h => assignAtempTag_preserves_fixed k n f r prefs s h) _ _ _ _ fixed

/-- The full actual spill-assignment traversal preserves already fixed nodes.
This does not assume successful allocation or a desired output colour. -/
theorem assignStemps_preserves_fixed (k fixedNode register : Nat)
    (prefs : CakeRaState → Nat → List Nat → Option Nat) (state : CakeRaState)
    (fixed : state.nodeTag.get fixedNode = some (.fixed register)) :
    (cakeAssignStemps k prefs state).nodeTag.get fixedNode =
      some (.fixed register) := by
  exact fold_preserves_fixed (fun s n => cakeAssignStempTag k prefs n s)
    (fun s n f r h => assignStempTag_preserves_fixed k n f r prefs s h) _ _ _ _ fixed

/-- The actual latched degree update preserves the complete node-tag map,
including its explicit error branches. This is production infrastructure. -/
theorem decDeg_nodeTag (node : Nat) (state : CakeRaState) :
    (cakeDecDeg node state).nodeTag = state.nodeTag := by
  unfold cakeDecDeg cakeDecDegStep cakeDecDegMonadic
  repeat' split at *
  all_goals simp_all
  all_goals subst_vars
  all_goals rfl

private theorem fold_nodeTag {α : Type} (step : CakeRaState → α → CakeRaState)
    (preserves : ∀ state item, (step state item).nodeTag = state.nodeTag)
    (items : List α) (state : CakeRaState) :
    (items.foldl step state).nodeTag = state.nodeTag := by
  induction items generalizing state with
  | nil => rfl
  | cons head tail ih =>
      exact (ih (step state head)).trans (preserves state head)

/-- Decrementing all adjacent degrees changes no production tags. -/
theorem decDegree_nodeTag (node : Nat) (state : CakeRaState) :
    (cakeDecDegree node state).nodeTag = state.nodeTag := by
  unfold cakeDecDegree
  split
  · exact fold_nodeTag (fun s n => cakeDecDeg n s) (fun s n => decDeg_nodeTag n s) _ _
  · rfl

/-- The actual simplify phase preserves all tags through degree updates,
stack pushes and worklist revival. No success premise is required. -/
theorem doSimplify_nodeTag (k : Nat) (state : CakeRaState) :
    (cakeDoSimplify k state).2.nodeTag = state.nodeTag := by
  unfold cakeDoSimplify
  split
  · rfl
  · simp only [cakeUnspill, cakeReviveMoves, cakeAddSimpWl, cakeAddFreezeWl]
    rw [fold_nodeTag (fun s n => cakePushStack n s) (fun _ _ => rfl)]
    exact fold_nodeTag (fun s n => cakeDecDegree n s)
      (fun s n => decDegree_nodeTag n s) _ _

/-- Freezing a production node preserves tags on both empty and nonempty
worklists, including degree-update failure. -/
theorem doFreeze_nodeTag (k : Nat) (state : CakeRaState) :
    (cakeDoFreeze k state).2.nodeTag = state.nodeTag := by
  unfold cakeDoFreeze
  split
  · rfl
  · simpa only [cakeUnspill, cakeReviveMoves, cakeAddSimpWl,
      cakeAddFreezeWl, cakePushStack] using decDegree_nodeTag _ state

/-- Production prefreeze only changes worklists and move-related flags before
running the checked simplify phase; the complete tag map is preserved. -/
theorem doPrefreeze_nodeTag (k : Nat) (state : CakeRaState) :
    (cakeDoPrefreeze k state).2.nodeTag = state.nodeTag := by
  unfold cakeDoPrefreeze
  rw [doSimplify_nodeTag]
  rfl

/-- The actual real-coalescing update preserves tags even when a degree update
fails; coalescing changes links, graph data, degrees and the stack only. -/
theorem doCoalesceReal_nodeTag (x y : Nat) (left right : List Nat)
    (state : CakeRaState) :
    (cakeDoCoalesceReal x y left right state).nodeTag = state.nodeTag := by
  unfold cakeDoCoalesceReal cakePushStack
  rw [fold_nodeTag (fun s n => cakeDecDeg n s) (fun s n => decDeg_nodeTag n s)]
  split <;> rfl

/-- Actual recursive parent compression updates only the coalescing map.
All input nodes and malformed link chains retain their tag map. -/
theorem coalesceParent_nodeTag (node : Nat) (state : CakeRaState) :
    (cakeCoalesceParent node state).2.nodeTag = state.nodeTag := by
  fun_induction cakeCoalesceParent node state
  all_goals simp_all

/-- The real coalescing scan preserves tags while recursively compressing
parents and classifying rejected moves. Predicates are arbitrary because their
results cannot update the production state. -/
theorem stExFirst_nodeTag
    (P : CakeRaState → Nat → Nat → Bool)
    (Q : CakeRaState → Nat → Nat → Option (List Nat × List Nat))
    (state : CakeRaState) (moves rejected : List (Nat × (Nat × Nat))) :
    (cakeStExFirst P Q state moves rejected).2.2.nodeTag = state.nodeTag := by
  fun_induction cakeStExFirst P Q state moves rejected
  all_goals grind [coalesceParent_nodeTag]

/-- Worklist revival in the actual allocator leaves all node tags unchanged. -/
theorem unspill_nodeTag (k : Nat) (state : CakeRaState) :
    (cakeUnspill k state).nodeTag = state.nodeTag := by
  rfl

/-- The production coalescing phase preserves the complete tag map on both
failed-search and successful-coalescing paths. -/
theorem doCoalesce_nodeTag (k : Nat) (state : CakeRaState) :
    (cakeDoCoalesce k state).2.nodeTag = state.nodeTag := by
  have scan := stExFirst_nodeTag cakeConsistencyOk
    (fun s x y => cakeBgOk k x y s) state state.availMovesWl []
  unfold cakeDoCoalesce
  generalize result : cakeStExFirst cakeConsistencyOk
    (fun s x y => cakeBgOk k x y s) state state.availMovesWl [] = found at *
  rcases found with ⟨outcome, rejected, updated⟩
  clear result
  cases outcome with
  | none => exact scan
  | some result =>
      rcases result with ⟨⟨x,y⟩,⟨left,right⟩,remaining⟩
      have respillTags : ∀ s : CakeRaState, (cakeRespill k x s).nodeTag = s.nodeTag := by
        intro s
        unfold cakeRespill
        split
        · rfl
        · split <;> rfl
      simp only [respillTags, unspill_nodeTag, doCoalesceReal_nodeTag]
      exact scan

/-- Both actual spill-selection policies preserve tags; only the selected
node's degrees, stack and worklists are modified. -/
theorem doSpill_nodeTag (cost : Option (CakeNodeMap Nat)) (k : Nat)
    (state : CakeRaState) :
    (cakeDoSpill cost k state).2.nodeTag = state.nodeTag := by
  unfold cakeDoSpill
  split
  · rfl
  · simp only [unspill_nodeTag, cakePushStack]
    exact decDegree_nodeTag _ state

/-- The complete executed IRC step preserves tags across every policy branch. -/
theorem doStep_nodeTag (cost : Option (CakeNodeMap Nat)) (k : Nat)
    (state : CakeRaState) :
    (cakeDoStep cost k state).2.nodeTag = state.nodeTag := by
  unfold cakeDoStep
  repeat' split
  all_goals grind [doSimplify_nodeTag, doCoalesce_nodeTag,
    doPrefreeze_nodeTag, doFreeze_nodeTag, doSpill_nodeTag]

/-- Every fuel length of the actual IRC driver preserves the original tags;
no termination-success or desired-colour premise is used. -/
theorem rptDoStep_nodeTag (cost : Option (CakeNodeMap Nat)) (k fuel : Nat)
    (state : CakeRaState) :
    (cakeRptDoStep cost k fuel state).nodeTag = state.nodeTag := by
  fun_induction cakeRptDoStep cost k fuel state
  all_goals grind [doStep_nodeTag]

private theorem fold_pair_nodeTag {α β : Type}
    (step : β × CakeRaState → α → β × CakeRaState)
    (preserves : ∀ state item, (step state item).2.nodeTag = state.2.nodeTag)
    (items : List α) (state : β × CakeRaState) :
    (items.foldl step state).2.nodeTag = state.2.nodeTag := by
  induction items generalizing state with
  | nil => rfl
  | cons head tail ih => exact (ih (step state head)).trans (preserves state head)

/-- Actual degree/worklist initialization preserves the entire input tag map;
this is independent of move eligibility and node-map validity. -/
theorem initAlloc1Heu_nodeTag (moves : List (Nat × (Nat × Nat))) (k : Nat)
    (state : CakeRaState) :
    (cakeInitAlloc1Heu moves k state).2.nodeTag = state.nodeTag := by
  unfold cakeInitAlloc1Heu
  dsimp only
  rw [fold_nodeTag (fun (st : CakeRaState) (move : Nat × (Nat × Nat)) =>
    { st with moveRelated :=
      ((st.moveRelated.set move.2.1 (!cakeIsFixed st move.2.1)).set move.2.2 (!cakeIsFixed st move.2.2)) }) (fun _ _ => rfl)]
  apply fold_pair_nodeTag
  intro acc item
  rfl

/-- Every successful actual colouring run extracts from a state preserving
all initially fixed nodes. This exposes the real production result and cannot
replace the missing initial ABI-tag/bijection proof. No target colouring
identity or successful target evaluation is assumed; no HOL tag is claimed. -/
theorem regAllocFromState_preserves_fixed
    (algorithm : CakeAlgorithm) (cost : Option (CakeNodeMap Nat)) (k : Nat)
    (moves : List (Nat × (Nat × Nat))) (bijection : CakeNodeBijection)
    (state : CakeRaState) (output : NatInfoMap Nat)
    (allocated : cakeDoRegAllocFromState algorithm cost k moves bijection state = some output) :
    ∃ finalState : CakeRaState,
      output = cakeExtractColor finalState bijection.toAllocator ∧
      ∀ node register, state.nodeTag.get node = some (.fixed register) →
        finalState.nodeTag.get node = some (.fixed register) := by
  cases algorithm <;> unfold cakeDoRegAllocFromState at allocated
  all_goals dsimp only at allocated
  all_goals split at allocated
  all_goals simp only [Option.some.injEq, reduceCtorEq] at allocated
  all_goals try contradiction
  all_goals subst output
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals intro node register fixed
  all_goals apply assignStemps_preserves_fixed
  all_goals apply assignAtemps_preserves_fixed
  all_goals rw [rptDoStep_nodeTag, initAlloc1Heu_nodeTag]
  all_goals exact fixed

end Flapjack
