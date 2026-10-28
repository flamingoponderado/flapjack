import Flapjack.Compiler.Backend.FlatElim.Reachability
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Misc.Sptree.UnionAlgebra
import Mathlib.Data.Finset.Card
import Aesop

/-! Dependency bounds for flat elimination closure. -/
namespace Flapjack.Compiler.Backend.FlatElim

/-- A dependency edge looks up the source key and then the target key in its
stored set. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "is_adjacent_def"]
def isAdjacent (tree : Spt NumSet) (source target : Nat) : Prop :=
  ∃ targets, sptLookup source tree = some targets ∧ sptLookup target targets = some ()

/-- Reflexive transitive reachability through dependency edges. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "is_reachable_def"]
def isReachable (tree : Spt NumSet) : Nat → Nat → Prop :=
  Relation.ReflTransGen (isAdjacent tree)

/-- Lookup through dependency-tree union combines the two payload sets when
both trees contain the queried key. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "lookup_num_set_tree_union"]
theorem lookupNumSetTreeUnion (first second : Spt NumSet) (key : Nat) :
    sptLookup key (numSetTreeUnion first second) =
      match sptLookup key first, sptLookup key second with
      | some a, some b => some (sptUnion a b)
      | some a, none => some a
      | none, result => result := by
  induction first generalizing second key with
  | ln => simp [numSetTreeUnion, sptLookup]
  | ls value =>
    cases second <;> by_cases zero : key = 0 <;> simp [numSetTreeUnion, sptLookup, zero]
  | bn left right ihLeft ihRight =>
    cases second <;> by_cases zero : key = 0 <;> by_cases even : key % 2 = 0 <;>
      simp [numSetTreeUnion, sptLookup, zero, even, ihLeft, ihRight]
    all_goals split <;> simp_all
  | bs left value right ihLeft ihRight =>
    cases second <;> by_cases zero : key = 0 <;> by_cases even : key % 2 = 0 <;>
      simp [numSetTreeUnion, sptLookup, zero, even, ihLeft, ihRight]
    all_goals split <;> simp_all

/-- Dependency-tree union is symmetric for unit-valued target sets. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "num_set_tree_union_sym"]
theorem numSetTreeUnion_sym (first second : Spt NumSet) :
    numSetTreeUnion first second = numSetTreeUnion second first := by
  induction first generalizing second with
  | ln => cases second <;> rfl
  | ls value => cases second <;> simp [numSetTreeUnion, sptUnion_numSet_sym]
  | bn left right ihLeft ihRight =>
    cases second <;> simp [numSetTreeUnion, ihLeft, ihRight]
  | bs left value right ihLeft ihRight =>
    cases second <;> simp [numSetTreeUnion, ihLeft, ihRight, sptUnion_numSet_sym]
/-- Adding another dependency tree retains each edge from the first. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "is_adjacent_num_set_tree_union"]
theorem isAdjacent_union (first second : Spt NumSet) (source target : Nat)
    (edge : isAdjacent first source target) : isAdjacent (numSetTreeUnion first second) source target := by
  obtain ⟨values, found, targetFound⟩ := edge
  cases other : sptLookup source second with
  | none => exact ⟨values, by simp [lookupNumSetTreeUnion, found, other], targetFound⟩
  | some values' =>
    refine ⟨sptUnion values values', by simp [lookupNumSetTreeUnion, found, other], ?_⟩
    simp [sptLookup_sptUnion, targetFound]

/-- Adding another dependency tree retains every existing path. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "is_reachable_num_set_tree_union"]
theorem isReachable_union (first second : Spt NumSet) (source target : Nat)
    (path : isReachable first source target) : isReachable (numSetTreeUnion first second) source target := by
  induction path with
  | refl => exact .refl
  | tail path edge ih => exact ih.tail (isAdjacent_union first second _ _ edge)

/-- Payload sets contained in a sparse dependency tree. This list is used
only to reason about the executed tree fold. -/
def dependencySets {α : Type} : Spt (Spt α) → List (Spt α)
  | .ln => []
  | .ls value => [value]
  | .bn left right => dependencySets left ++ dependencySets right
  | .bs left value right => dependencySets left ++ value :: dependencySets right

/-- A successful sparse-tree lookup identifies one of its payload sets. -/
theorem dependencySets_of_lookup {α : Type} (tree : Spt (Spt α)) (key : Nat) (values : Spt α)
    (found : sptLookup key tree = some values) : values ∈ dependencySets tree := by
  induction tree generalizing key with
  | ln => simp [sptLookup] at found
  | ls value =>
    by_cases zero : key = 0 <;> simp [sptLookup, zero] at found
    subst values
    simp [dependencySets]
  | bn left right ihLeft ihRight =>
    by_cases zero : key = 0
    · simp [sptLookup, zero] at found
    · by_cases even : key % 2 = 0
      · have nested : sptLookup ((key - 1) / 2) left = some values := by
          simpa [sptLookup, zero, even] using found
        exact List.mem_append_left _ (ihLeft _ nested)
      · have nested : sptLookup ((key - 1) / 2) right = some values := by
          simpa [sptLookup, zero, even] using found
        exact List.mem_append_right _ (ihRight _ nested)
  | bs left value right ihLeft ihRight =>
    by_cases zero : key = 0
    · simp [sptLookup, zero] at found
      subst values
      simp [dependencySets]
    · by_cases even : key % 2 = 0
      · have nested : sptLookup ((key - 1) / 2) left = some values := by
          simpa [sptLookup, zero, even] using found
        simp [dependencySets, ihLeft _ nested]
      · have nested : sptLookup ((key - 1) / 2) right = some values := by
          simpa [sptLookup, zero, even] using found
        simp [dependencySets, ihRight _ nested]

/-- Every dependency-set payload is found at some sparse-tree key. -/
theorem lookup_of_dependencySets {α : Type} (tree : Spt (Spt α)) (values : Spt α)
    (member : values ∈ dependencySets tree) : ∃ key, sptLookup key tree = some values := by
  induction tree with
  | ln => simp [dependencySets] at member
  | ls value =>
    simp [dependencySets] at member
    subst values
    exact ⟨0, rfl⟩
  | bn left right ihLeft ihRight =>
    simp only [dependencySets, List.mem_append] at member
    rcases member with member | member
    · obtain ⟨key, found⟩ := ihLeft member
      exact ⟨2 * key + 2, by simpa [sptLookup_left_bn] using found⟩
    · obtain ⟨key, found⟩ := ihRight member
      exact ⟨2 * key + 1, by simpa [sptLookup_right_bn] using found⟩
  | bs left value right ihLeft ihRight =>
    simp only [dependencySets, List.mem_append, List.mem_cons] at member
    rcases member with member | equal | member
    · obtain ⟨key, found⟩ := ihLeft member
      exact ⟨2 * key + 2, by simpa [sptLookup_left_bs] using found⟩
    · subst values
      exact ⟨0, rfl⟩
    · obtain ⟨key, found⟩ := ihRight member
      exact ⟨2 * key + 1, by simpa [sptLookup_right_bs] using found⟩

private theorem dependencySets_mkBN {α : Type} (left right : Spt (Spt α)) :
    dependencySets (sptMkBN left right) = dependencySets left ++ dependencySets right := by
  cases left <;> cases right <;> rfl

private theorem dependencySets_mkBS {α : Type} (left : Spt (Spt α)) (value : Spt α) (right : Spt (Spt α)) :
    dependencySets (sptMkBS left value right) = dependencySets left ++ value :: dependencySets right := by
  cases left <;> cases right <;> rfl

/-- The fold contains exactly the accumulator keys and the keys in its
dependency-set payloads. -/
theorem foldUnion_mem_iff {α : Type} (tree : Spt (Spt α)) (acc : Spt α) (key : Nat) :
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

/-- The union fold's domain is the accumulator domain plus the domains of
every payload found in the dependency tree. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "domain_spt_fold_union"]
theorem domainFoldUnion {α : Type} (tree : Spt (Spt α)) (acc : Spt α) :
    sptDomain (foldUnion acc tree) = fun key =>
      sptDomain acc key ∨ ∃ source values, sptLookup source tree = some values ∧ sptDomain values key := by
  funext key
  apply propext
  change sptMem key (foldUnion acc tree) ↔
    sptMem key acc ∨ ∃ source values, sptLookup source tree = some values ∧ sptMem key values
  rw [foldUnion_mem_iff]
  constructor
  · rintro (accMem | ⟨values, member, inValues⟩)
    · exact Or.inl accMem
    · obtain ⟨source, found⟩ := lookup_of_dependencySets tree values member
      exact Or.inr ⟨source, values, found, inValues⟩
  · rintro (accMem | ⟨source, values, found, inValues⟩)
    · exact Or.inl accMem
    · exact Or.inr ⟨values, dependencySets_of_lookup tree source values found, inValues⟩

/-- One closure step discovers exactly the targets adjacent to currently
reachable source keys. -/
theorem closureNodes_iff (tree : Spt NumSet) (reachable : NumSet) (target : Nat) :
    sptMem target (foldUnion .ln (sptInter tree reachable)) ↔
      ∃ source, sptMem source reachable ∧ isAdjacent tree source target := by
  rw [foldUnion_mem_iff]
  simp only [sptMem, sptDomain, sptLookup, Option.isSome_none, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨values, member, targetMem⟩
    obtain ⟨source, found⟩ := lookup_of_dependencySets (sptInter tree reachable) values member
    rw [sptLookup_sptInterCases] at found
    cases sourceFound : sptLookup source tree with
    | none => simp [sourceFound] at found
    | some sourceValues =>
      cases reachableFound : sptLookup source reachable with
      | none => simp [sourceFound, reachableFound] at found
      | some reachedValue =>
        simp [sourceFound, reachableFound] at found
        subst sourceValues
        cases targetFound : sptLookup target values with
        | none => simp [targetFound] at targetMem
        | some targetValue =>
          cases targetValue
          exact ⟨source, by simp [reachableFound], values, sourceFound, targetFound⟩
  · rintro ⟨source, reachableMem, values, sourceFound, targetFound⟩
    cases reachableFound : sptLookup source reachable with
    | none => simp [reachableFound] at reachableMem
    | some reachedValue =>
      have found : sptLookup source (sptInter tree reachable) = some values := by
        simp [sptLookup_sptInterCases, sourceFound, reachableFound]
      exact ⟨values, dependencySets_of_lookup _ source values found, by simp [targetFound]⟩
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

/-- The production total closure is the source-shaped recursive closure. -/
theorem closureTotal_eq_closure (reachable : NumSet) (tree : Spt NumSet) :
    closureTotal reachable tree = closure reachable tree := by
  simp [closureTotal, closureFuel_target_eq_closure]

/-- Fuelled closure preserves every input key. -/
theorem closureFuel_preserves (tree : Spt NumSet) (fuel : Nat) (initial result : NumSet)
    (computed : closureFuel fuel initial tree = some result) :
    ∀ key, sptMem key initial → sptMem key result := by
  induction fuel generalizing initial with
  | zero => simp [closureFuel] at computed
  | succ fuel ih =>
    classical
    rw [closureFuel_step] at computed
    by_cases done : sptSubspt (foldUnion .ln (sptInter tree initial)) initial
    · simp [done] at computed
      subst result
      exact fun _ member => member
    · simp [done] at computed
      intro key member
      apply ih _ computed key
      exact (sptMem_sptUnion _ _ _).mpr (Or.inl member)

/-- Every key in a successful fuelled closure is reachable from an input key. -/
theorem closureFuel_reachable (tree : Spt NumSet) (fuel : Nat) (initial result : NumSet)
    (computed : closureFuel fuel initial tree = some result) :
    ∀ key, sptMem key result → ∃ root, sptMem root initial ∧ isReachable tree root key := by
  induction fuel generalizing initial with
  | zero => simp [closureFuel] at computed
  | succ fuel ih =>
    classical
    rw [closureFuel_step] at computed
    by_cases done : sptSubspt (foldUnion .ln (sptInter tree initial)) initial
    · simp [done] at computed
      subst result
      intro key member
      exact ⟨key, member, .refl⟩
    · simp [done] at computed
      intro key member
      obtain ⟨root, rootMem, path⟩ := ih _ computed key member
      rcases (sptMem_sptUnion _ _ _).mp rootMem with rootMem | nodeMem
      · exact ⟨root, rootMem, path⟩
      · obtain ⟨source, sourceMem, adjacent⟩ := (closureNodes_iff tree initial root).mp nodeMem
        exact ⟨source, sourceMem, Relation.ReflTransGen.head adjacent path⟩

/-- A successful fuelled closure is closed under every dependency edge. -/
theorem closureFuel_closed (tree : Spt NumSet) (fuel : Nat) (initial result : NumSet)
    (computed : closureFuel fuel initial tree = some result) :
    ∀ source target, sptMem source result → isAdjacent tree source target → sptMem target result := by
  induction fuel generalizing initial with
  | zero => simp [closureFuel] at computed
  | succ fuel ih =>
    classical
    rw [closureFuel_step] at computed
    by_cases done : sptSubspt (foldUnion .ln (sptInter tree initial)) initial
    · simp [done] at computed
      subst result
      intro source target sourceMem adjacent
      exact (done target ((closureNodes_iff tree initial target).mpr ⟨source, sourceMem, adjacent⟩)).1
    · simp [done] at computed
      exact ih _ computed

/-- The executed closure contains precisely the nodes reachable from its
input roots in the dependency graph. -/
@[hol "HOL/examples/algorithms/spt_closureScript.sml" "closure_spt_thm"]
theorem closureTotal_reachable (tree : Spt NumSet) (roots : NumSet) :
    sptDomain (closureTotal roots tree) = fun key =>
      ∃ root, sptDomain roots root ∧ isReachable tree root key := by
  have computed := closureFuel_target_eq_closure tree roots
  have equal := closureTotal_eq_closure roots tree
  rw [← equal] at computed
  funext key
  apply propext
  constructor
  · exact closureFuel_reachable tree _ roots _ computed key
  · rintro ⟨root, rootMem, path⟩
    have initial := closureFuel_preserves tree _ roots _ computed root rootMem
    induction path with
    | refl => exact initial
    | tail path edge ih =>
      exact closureFuel_closed tree _ roots _ computed _ _ ih edge

/-- Elimination executes the source-shaped closure before filtering. -/
theorem removeFlatProgTotal_eq (code : List FlatLang.Exp) :
    removeFlatProgTotal code =
      if code.any hasEvalDec then code else
        let (roots, tree) := analyseCode code
        removeUnreachable (closure roots tree) code := by
  simp only [removeFlatProgTotal]
  split
  · rfl
  · cases analyseCode code with
    | mk roots tree => simp [closureTotal_eq_closure]

/-- Flat elimination cannot fail through exhaustion of its closure bound. -/
theorem removeFlatProg_succeeds (code : List FlatLang.Exp) :
    ∃ result, removeFlatProg code = some result := by
  exact ⟨removeFlatProgTotal code, rfl⟩

end Flapjack.Compiler.Backend.FlatElim
