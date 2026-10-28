import Flapjack.Compiler.Backend.FlatElim.Reachability
import Flapjack.Misc.Sptree.ToAList
import Mathlib.Data.Finset.Card
import Aesop

/-! Dependency bounds for flat elimination closure. -/
namespace Flapjack.Compiler.Backend.FlatElim

/-- Payload sets contained in a sparse dependency tree. This list is used
only to reason about the executed tree fold. -/
def dependencySets : Spt NumSet → List NumSet
  | .ln => []
  | .ls value => [value]
  | .bn left right => dependencySets left ++ dependencySets right
  | .bs left value right => dependencySets left ++ value :: dependencySets right

private theorem dependencySets_mkBN (left right : Spt NumSet) :
    dependencySets (sptMkBN left right) = dependencySets left ++ dependencySets right := by
  cases left <;> cases right <;> rfl

private theorem dependencySets_mkBS (left : Spt NumSet) (value : NumSet) (right : Spt NumSet) :
    dependencySets (sptMkBS left value right) = dependencySets left ++ value :: dependencySets right := by
  cases left <;> cases right <;> rfl

/-- The fold contains exactly the accumulator keys and the keys in its
dependency-set payloads. -/
theorem foldUnion_mem_iff (tree : Spt NumSet) (acc : NumSet) (key : Nat) :
    sptMem key (foldUnion acc tree) ↔
      sptMem key acc ∨ ∃ values ∈ dependencySets tree, sptMem key values := by
  induction tree generalizing acc with
  | ln => simp [foldUnion, dependencySets]
  | ls values => simp [foldUnion, dependencySets, sptMem_sptUnion, or_comm]
  | bn left right ihLeft ihRight =>
    simp only [foldUnion, ihRight, ihLeft, dependencySets, List.mem_append, or_and_right, exists_or]
    aesop
  | bs left values right ihLeft ihRight =>
    simp only [foldUnion, ihRight, ihLeft, dependencySets, List.mem_append, List.mem_cons,
      or_and_right, exists_or, exists_eq_left, sptMem_sptUnion]
    aesop

/-- Intersecting a dependency tree with a key set cannot introduce a new
dependency-set payload. -/
theorem dependencySets_inter_subset (tree : Spt NumSet) (keys : NumSet) :
    ∀ values, values ∈ dependencySets (sptInter tree keys) → values ∈ dependencySets tree := by
  induction tree generalizing keys with
  | ln => simp [sptInter, dependencySets]
  | ls value => cases keys <;> simp [sptInter, dependencySets]
  | bn left right ihLeft ihRight =>
    cases keys <;> simp [sptInter, dependencySets, dependencySets_mkBN] <;> aesop
  | bs left value right ihLeft ihRight =>
    cases keys <;> simp [sptInter, dependencySets, dependencySets_mkBN, dependencySets_mkBS] <;> aesop

/-- Every dependency target discovered by one closure iteration occurs in
the union of all target sets in the original dependency tree. -/
theorem closure_nodes_bounded (tree : Spt NumSet) (reachable : NumSet) (key : Nat)
    (present : sptMem key (foldUnion .ln (sptInter tree reachable))) :
    sptMem key (foldUnion .ln tree) := by
  rw [foldUnion_mem_iff] at present ⊢
  simp only [sptMem, sptDomain, sptLookup, Option.isSome_none, Bool.false_eq_true, false_or] at present ⊢
  obtain ⟨values, member, inValues⟩ := present
  exact ⟨values, dependencySets_inter_subset tree reachable values member, inValues⟩

/-- Enumeration counts each stored sparse-tree value once, independently of
the input accumulator and the tree's canonical shape. -/
theorem sptFoldi_entries_length {α : Type} (tree : Spt α) (index : Nat) (acc : List (Nat × α)) :
    (sptFoldi (fun k v entries => (k, v) :: entries) index acc tree).length =
      sptSize tree + acc.length := by
  induction tree generalizing index acc with
  | ln => simp [sptFoldi]
  | ls value => simp [sptFoldi, Nat.add_comm]
  | bn left right ihLeft ihRight =>
    simp only [sptFoldi, ihRight, ihLeft, sptSize]
    omega
  | bs left value right ihLeft ihRight =>
    simp only [sptFoldi, ihRight, ihLeft, sptSize, List.length_cons]
    omega

/-- The number of enumerated sparse-tree keys equals the native size. -/
theorem sptToAList_length {α : Type} (tree : Spt α) : (sptToAList tree).length = sptSize tree := by
  simpa [sptToAList] using sptFoldi_entries_length tree 0 []

/-- The finite universe of possible closure targets. -/
def dependencyUniverse (tree : Spt NumSet) : Finset Nat :=
  ((sptToAList (foldUnion .ln tree)).map Prod.fst).toFinset

/-- Targets that have not yet been reached; this is a proof-only measure. -/
noncomputable def missingTargets (tree : Spt NumSet) (reachable : NumSet) : Finset Nat := by
  classical
  exact (dependencyUniverse tree).filter (fun key => ¬ sptMem key reachable)

theorem mem_missingTargets (tree : Spt NumSet) (reachable : NumSet) (key : Nat) :
    key ∈ missingTargets tree reachable ↔
      sptMem key (foldUnion .ln tree) ∧ ¬ sptMem key reachable := by
  classical
  change key ∈ (dependencyUniverse tree).filter (fun key => ¬ sptMem key reachable) ↔ _
  rw [Finset.mem_filter]
  change (key ∈ ((sptToAList (foldUnion .ln tree)).map Prod.fst).toFinset ∧ ¬ sptMem key reachable) ↔ _
  rw [List.mem_toFinset, sptMemMapFstToAList]
  rfl

/-- The number of missing targets never exceeds the executable fuel bound. -/
theorem missingTargets_card_le (tree : Spt NumSet) (reachable : NumSet) :
    (missingTargets tree reachable).card ≤ sptSize (foldUnion .ln tree) := by
  classical
  calc
    (missingTargets tree reachable).card ≤ (dependencyUniverse tree).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ ((sptToAList (foldUnion .ln tree)).map Prod.fst).length := List.toFinset_card_le _
    _ = sptSize (foldUnion .ln tree) := by simp [sptToAList_length]

/-- A nonterminal iteration strictly decreases the finite missing-target
measure. -/
theorem missingTargets_decrease (tree : Spt NumSet) (reachable : NumSet)
    (notDone : ¬ sptSubspt (foldUnion .ln (sptInter tree reachable)) reachable) :
    (missingTargets tree (sptUnion reachable (foldUnion .ln (sptInter tree reachable)))).card <
      (missingTargets tree reachable).card := by
  classical
  let nodes := foldUnion .ln (sptInter tree reachable)
  have subset : missingTargets tree (sptUnion reachable nodes) ⊆ missingTargets tree reachable := by
    intro key member
    rw [mem_missingTargets] at member ⊢
    refine ⟨member.1, ?_⟩
    intro inReachable
    exact member.2 ((sptMem_sptUnion _ _ _).mpr (Or.inl inReachable))
  have fresh : ∃ key, sptMem key nodes ∧ ¬ sptMem key reachable := by
    simp only [sptSubsptLookup, not_forall] at notDone
    obtain ⟨key, value, found, absent⟩ := notDone
    change sptLookup key nodes = some value at found
    refine ⟨key, ?_, ?_⟩
    · simp [sptMem, sptDomain, found]
    · intro inReachable
      cases target : sptLookup key reachable with
      | none => simp [sptMem, sptDomain, target] at inReachable
      | some value' => cases value; cases value'; exact absent target
  obtain ⟨key, inNodes, notInReachable⟩ := fresh
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset subset).mpr
  refine ⟨key, ?_, ?_⟩
  · rw [mem_missingTargets]
    exact ⟨closure_nodes_bounded tree reachable key inNodes, notInReachable⟩
  · rw [mem_missingTargets]
    intro member
    exact member.2 ((sptMem_sptUnion _ _ _).mpr (Or.inr inNodes))

/-- Fuel strictly greater than the missing-target count always suffices for
the original closure iteration. -/
theorem closureFuel_sufficient (tree : Spt NumSet) (fuel : Nat) (reachable : NumSet)
    (bound : (missingTargets tree reachable).card < fuel) :
    ∃ result, closureFuel fuel reachable tree = some result := by
  induction fuel generalizing reachable with
  | zero => omega
  | succ fuel ih =>
    classical
    by_cases done : sptSubspt (foldUnion .ln (sptInter tree reachable)) reachable
    · exact ⟨reachable, by simp [closureFuel_step, done]⟩
    · have decrease := missingTargets_decrease tree reachable done
      have nextBound : (missingTargets tree
          (sptUnion reachable (foldUnion .ln (sptInter tree reachable)))).card < fuel := by omega
      obtain ⟨result, resultEq⟩ := ih _ nextBound
      exact ⟨result, by simpa [closureFuel_step, done] using resultEq⟩

/-- The executable's target-count fuel cannot be exhausted. -/
theorem closureFuel_target_bound (tree : Spt NumSet) (reachable : NumSet) :
    ∃ result, closureFuel (sptSize (foldUnion .ln tree) + 1) reachable tree = some result := by
  apply closureFuel_sufficient
  have bound := missingTargets_card_le tree reachable
  omega

open Classical in
/-- Total lookup-based closure with the same recursive clauses as HOL. This
proof-side definition is untagged pending source review of the fold carrier
and equation. -/
noncomputable def closure (reachable : NumSet) (tree : Spt NumSet) : NumSet :=
  if sptSubspt (foldUnion .ln (sptInter tree reachable)) reachable then reachable
  else closure (sptUnion reachable (foldUnion .ln (sptInter tree reachable))) tree
termination_by (missingTargets tree reachable).card
decreasing_by exact missingTargets_decrease tree reachable ‹_›

/-- Every successful executable iteration returns the total closure result. -/
theorem closureFuel_eq_closure (tree : Spt NumSet) (fuel : Nat) (reachable result : NumSet)
    (computed : closureFuel fuel reachable tree = some result) : closure reachable tree = result := by
  induction fuel generalizing reachable with
  | zero => simp [closureFuel] at computed
  | succ fuel ih =>
    classical
    rw [closureFuel_step] at computed
    by_cases done : sptSubspt (foldUnion .ln (sptInter tree reachable)) reachable
    · simp [done] at computed
      rw [closure]
      simp only [done, if_true]
      exact computed
    · simp [done] at computed
      rw [closure]
      simp only [done, if_false]
      exact ih _ computed

/-- The executable fuel choice computes the total lookup-based closure. -/
theorem closureFuel_target_eq_closure (tree : Spt NumSet) (reachable : NumSet) :
    closureFuel (sptSize (foldUnion .ln tree) + 1) reachable tree = some (closure reachable tree) := by
  obtain ⟨result, computed⟩ := closureFuel_target_bound tree reachable
  rw [closureFuel_eq_closure tree _ reachable result computed]
  exact computed

/-- Flat elimination cannot fail through exhaustion of its closure bound. -/
theorem removeFlatProg_succeeds (code : List FlatLang.Exp) :
    ∃ result, removeFlatProg code = some result := by
  unfold removeFlatProg
  split
  · exact ⟨code, rfl⟩
  · generalize analysis : analyseCode code = pair
    obtain ⟨roots, tree⟩ := pair
    obtain ⟨reachable, reached⟩ := closureFuel_target_bound tree roots
    exact ⟨removeUnreachable reachable code, by simp [reached]⟩

end Flapjack.Compiler.Backend.FlatElim
