import Flapjack.Compiler.Backend.RegAlloc.ProductionFixedTags
import Std.Data.HashMap.Lemmas
import Std.Data.TreeMap.Lemmas

/-!
Actual optimized allocator correspondence infrastructure. Source comparison:
HOL reg_alloc list_remap/mk_bij assigns fresh nodes only to previously absent
names; mk_tags selects MOD 4 roles and Fixed (source DIV 2); extract_color
reads tags through the inverse bijection. These proofs connect the production
TreeMap membership index, paired association histories, HashMap decoding,
range tag fold and sorted extraction without assuming desired output colours.
They have no HOL tags because they concern the optimized CakeNodeMap/index
implementation and successful production wrapper, rather than the HOL monadic
good_ra_state theorem statements. They establish physical-binding preservation,
not full allocator semantic correctness or whole compiler frame bounds.
-/

namespace Flapjack
open RiscV RiscV.CakeRegAlloc

private theorem indexFold_lookup (entries : NatInfoMap Nat)
    (index : Std.HashMap Nat Nat) (key : Nat) :
    (entries.foldl (fun index entry =>
      match index[entry.1]? with
      | some _ => index
      | none => index.insert entry.1 entry.2) index)[key]? =
    (index[key]?).orElse (fun _ => lookupNatInfo key entries) := by
  induction entries generalizing index with
  | nil => simp [lookupNatInfo]
  | cons head tail ih =>
      simp only [List.foldl_cons]
      cases present : index[head.1]? with
      | some value =>
          rw [ih]
          by_cases equal : key = head.1
          · subst key
            simp [present, lookupNatInfo]
          · simp [lookupNatInfo, Ne.symm equal]
      | none =>
          rw [ih]
          by_cases equal : key = head.1
          · subst key
            simp [present, lookupNatInfo]
          · simp [Std.HashMap.getElem?_insert, lookupNatInfo, Ne.symm equal]

/-- The actual hash accelerator preserves first-binding association lookup,
including duplicate keys. This is production infrastructure, with no HOL
original; absence/default decoding is handled separately. -/
theorem spDefaultIndex_lookup (entries : NatInfoMap Nat) (key : Nat) :
    (cakeSpDefaultIndex entries)[key]? = lookupNatInfo key entries := by
  exact (indexFold_lookup entries {} key).trans (by simp)

private theorem association_find_lookup (entries : NatInfoMap Nat) (key : Nat) :
    (entries.find? (fun entry => entry.1 == key)).map Prod.snd =
      lookupNatInfo key entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.find?_cons, lookupNatInfo]
      split <;> simp_all

/-- Indexed production lookup preserves the original first-binding decoder,
including physical-name DIV 2 and absent nonphysical zero defaults. The
statement is unconditional and permits duplicate input keys. -/
theorem spDefaultIndexed_corresponds (entries : NatInfoMap Nat) (key : Nat) :
    cakeSpDefaultIndexed (cakeSpDefaultIndex entries) key =
      CakeAlloc.spDefault entries key := by
  unfold cakeSpDefaultIndexed CakeAlloc.spDefault
  rw [spDefaultIndex_lookup]
  have lookup := association_find_lookup entries key
  cases found : entries.find? (fun entry => entry.1 == key) with
  | none => simp [found] at lookup; rw [← lookup]
  | some pair => simp [found] at lookup; rw [← lookup]

/-- The actual optimized remapper records the reverse list alongside every
new forward binding, preserving order even with repeated input names. This
list identity is infrastructure, not yet the inverse-lookup uniqueness law. -/
theorem listRemapBuild_reverse (names : List Nat) (bijection : CakeNodeBijectionBuild) :
    bijection.fromAllocator = bijection.toAllocator.map Prod.swap →
    (cakeListRemapBuild names bijection).fromAllocator =
      (cakeListRemapBuild names bijection).toAllocator.map Prod.swap := by
  fun_induction cakeListRemapBuild names bijection
  all_goals simp_all

/-- The same paired history is preserved by every real clash-tree traversal. -/
theorem mkBijBuildAux_reverse (tree : WordClashTree) (bijection : CakeNodeBijectionBuild) :
    bijection.fromAllocator = bijection.toAllocator.map Prod.swap →
    (cakeMkBijBuildAux tree bijection).fromAllocator =
      (cakeMkBijBuildAux tree bijection).toAllocator.map Prod.swap := by
  fun_induction cakeMkBijBuildAux tree bijection
  all_goals grind [listRemapBuild_reverse]

/-- The actual emitted bijection has matched forward/reverse binding histories.
Lookup inversion and node bounds remain separate obligations. -/
theorem mkBij_reverse (tree : WordClashTree) :
    (cakeMkBij tree).fromAllocator = (cakeMkBij tree).toAllocator.map Prod.swap := by
  exact mkBijBuildAux_reverse tree _ rfl

/-- Fresh-node counters in the actual remapper never decrease. -/
theorem listRemapBuild_nextNode (names : List Nat) (bijection : CakeNodeBijectionBuild) :
    bijection.nextNode ≤ (cakeListRemapBuild names bijection).nextNode := by
  fun_induction cakeListRemapBuild names bijection
  all_goals simp_all
  all_goals omega

/-- Every actual clash-tree branch preserves the monotonically fresh counter. -/
theorem mkBijBuildAux_nextNode (tree : WordClashTree) (bijection : CakeNodeBijectionBuild) :
    bijection.nextNode ≤ (cakeMkBijBuildAux tree bijection).nextNode := by
  fun_induction cakeMkBijBuildAux tree bijection
  all_goals grind [listRemapBuild_nextNode]

/-- Actual remapping keeps every emitted allocator node below the fresh
counter. The generic prefix premise is discharged by the empty actual builder. -/
theorem listRemapBuild_bounds (names : List Nat) (bijection : CakeNodeBijectionBuild) :
    (∀ entry ∈ bijection.toAllocator, entry.2 < bijection.nextNode) →
    ∀ entry ∈ (cakeListRemapBuild names bijection).toAllocator,
      entry.2 < (cakeListRemapBuild names bijection).nextNode := by
  fun_induction cakeListRemapBuild names bijection
  all_goals simp_all
  all_goals grind

/-- The real whole clash-tree traversal preserves these emitted-node bounds. -/
theorem mkBijBuildAux_bounds (tree : WordClashTree) (bijection : CakeNodeBijectionBuild) :
    (∀ entry ∈ bijection.toAllocator, entry.2 < bijection.nextNode) →
    ∀ entry ∈ (cakeMkBijBuildAux tree bijection).toAllocator,
      entry.2 < (cakeMkBijBuildAux tree bijection).nextNode := by
  fun_induction cakeMkBijBuildAux tree bijection
  case case1 =>
    intro bounds
    exact listRemapBuild_bounds _ _ (listRemapBuild_bounds _ _ bounds)
  case case2 =>
    intro bounds
    exact listRemapBuild_bounds _ _ bounds
  case case3 =>
    rename_i thenBranch elseBranch bij mapped ih2 ih1
    intro bounds
    exact ih1 (ih2 bounds)
  case case4 =>
    rename_i thenBranch elseBranch bij mapped names ih2 ih1
    intro bounds
    exact listRemapBuild_bounds _ _ (ih1 (ih2 bounds))
  case case5 =>
    rename_i first second bij ih2 ih1
    intro bounds
    exact ih1 (ih2 bounds)

/-- Every node in the actual emitted bijection is in its initialization domain;
no assumed bounded-output relation is used. -/
theorem mkBij_bounds (tree : WordClashTree) :
    ∀ entry ∈ (cakeMkBij tree).toAllocator, entry.2 < (cakeMkBij tree).nextNode := by
  apply mkBijBuildAux_bounds tree
  simp

/-- The real ordered membership index observes exactly the emitted forward
association list, including the skip-on-duplicate branch. -/
theorem listRemapBuild_index (names : List Nat) (bijection : CakeNodeBijectionBuild) :
    (∀ key, bijection.index[key]? = lookupNatInfo key bijection.toAllocator) →
    ∀ key, (cakeListRemapBuild names bijection).index[key]? =
      lookupNatInfo key (cakeListRemapBuild names bijection).toAllocator := by
  fun_induction cakeListRemapBuild names bijection
  all_goals simp_all [lookupNatInfo, Std.TreeMap.getElem?_insert]
  all_goals grind

/-- Index/history correspondence survives every actual clash-tree case. -/
theorem mkBijBuildAux_index (tree : WordClashTree) (bijection : CakeNodeBijectionBuild) :
    (∀ key, bijection.index[key]? = lookupNatInfo key bijection.toAllocator) →
    ∀ key, (cakeMkBijBuildAux tree bijection).index[key]? =
      lookupNatInfo key (cakeMkBijBuildAux tree bijection).toAllocator := by
  fun_induction cakeMkBijBuildAux tree bijection
  case case1 =>
    intro correspondence
    exact listRemapBuild_index _ _ (listRemapBuild_index _ _ correspondence)
  case case2 =>
    intro correspondence
    exact listRemapBuild_index _ _ correspondence
  case case3 =>
    rename_i thenBranch elseBranch bij mapped ih2 ih1
    intro correspondence
    exact ih1 (ih2 correspondence)
  case case4 =>
    rename_i thenBranch elseBranch bij mapped names ih2 ih1
    intro correspondence
    exact listRemapBuild_index _ _ (ih1 (ih2 correspondence))
  case case5 =>
    rename_i first second bij ih2 ih1
    intro correspondence
    exact ih1 (ih2 correspondence)

/-- The production builder starts with the empty index/history, so its actual
output satisfies correspondence without an assumed output relation. -/
theorem mkBijBuild_index (tree : WordClashTree) (key : Nat) :
    (cakeMkBijBuild tree).index[key]? =
      lookupNatInfo key (cakeMkBijBuild tree).toAllocator := by
  apply mkBijBuildAux_index tree
  intro key
  simp [lookupNatInfo]

private theorem lookup_none_not_mem (entries : NatInfoMap Nat) (key : Nat) :
    lookupNatInfo key entries = none → key ∉ entries.map Prod.fst := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    rcases entry with ⟨name, value⟩
    by_cases equal : name = key
    · simp [lookupNatInfo, equal]
    · intro absent
      have tailAbsent : lookupNatInfo key entries = none := by
        simpa [lookupNatInfo, equal] using absent
      have missing := ih tailAbsent
      simpa only [List.map_cons, List.mem_cons, not_or] using
        And.intro (Ne.symm equal) missing

/-- Fresh insertion cannot duplicate a source name: the actual index miss,
transported through checked history correspondence, rules out prior ownership. -/
theorem listRemapBuild_unique_names (names : List Nat)
    (bijection : CakeNodeBijectionBuild) :
    (∀ key, bijection.index[key]? = lookupNatInfo key bijection.toAllocator) →
    (bijection.toAllocator.map Prod.fst).Nodup →
    ((cakeListRemapBuild names bijection).toAllocator.map Prod.fst).Nodup := by
  induction names generalizing bijection with
  | nil => simp [cakeListRemapBuild]
  | cons name names ih =>
    intro correspondence unique
    unfold cakeListRemapBuild
    split
    · exact ih _ correspondence unique
    · rename_i absent
      apply ih
      · intro key
        simp [Std.TreeMap.getElem?_insert, lookupNatInfo, correspondence]
      · have missing := lookup_none_not_mem bijection.toAllocator name
          ((correspondence name).symm.trans absent)
        simpa only [List.map_cons, List.nodup_cons] using And.intro missing unique

/-- Every actual clash-tree traversal preserves unique source ownership. -/
theorem mkBijBuildAux_unique_names (tree : WordClashTree)
    (bijection : CakeNodeBijectionBuild) :
    (∀ key, bijection.index[key]? = lookupNatInfo key bijection.toAllocator) →
    (bijection.toAllocator.map Prod.fst).Nodup →
    ((cakeMkBijBuildAux tree bijection).toAllocator.map Prod.fst).Nodup := by
  fun_induction cakeMkBijBuildAux tree bijection
  case case1 =>
    intro correspondence unique
    exact listRemapBuild_unique_names _ _
      (listRemapBuild_index _ _ correspondence)
      (listRemapBuild_unique_names _ _ correspondence unique)
  case case2 =>
    intro correspondence unique
    exact listRemapBuild_unique_names _ _ correspondence unique
  case case3 =>
    rename_i thenBranch elseBranch bij mapped ih2 ih1
    intro correspondence unique
    exact ih1 (mkBijBuildAux_index _ _ correspondence) (ih2 correspondence unique)
  case case4 =>
    rename_i thenBranch elseBranch bij mapped names ih2 ih1
    intro correspondence unique
    exact listRemapBuild_unique_names _ _
      (mkBijBuildAux_index _ _ (mkBijBuildAux_index _ _ correspondence))
      (ih1 (mkBijBuildAux_index _ _ correspondence) (ih2 correspondence unique))
  case case5 =>
    rename_i first second bij ih2 ih1
    intro correspondence unique
    exact ih1 (mkBijBuildAux_index _ _ correspondence) (ih2 correspondence unique)

/-- Source names in the actual public bijection are unique, independently of
input repetition and without assuming uniqueness of the output. -/
theorem mkBij_unique_names (tree : WordClashTree) :
    ((cakeMkBij tree).toAllocator.map Prod.fst).Nodup := by
  apply mkBijBuildAux_unique_names tree
  · intro key
    simp [lookupNatInfo]
  · simp

/-- Fresh counters distinguish every newly emitted node from prior nodes. -/
theorem listRemapBuild_unique_nodes (names : List Nat)
    (bijection : CakeNodeBijectionBuild) :
    (∀ entry ∈ bijection.toAllocator, entry.2 < bijection.nextNode) →
    (bijection.toAllocator.map Prod.snd).Nodup →
    ((cakeListRemapBuild names bijection).toAllocator.map Prod.snd).Nodup := by
  induction names generalizing bijection with
  | nil => simp [cakeListRemapBuild]
  | cons name names ih =>
    intro bounds unique
    unfold cakeListRemapBuild
    split
    · exact ih _ bounds unique
    · apply ih
      · intro entry member
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · subst entry
          simp
        · have bounded := bounds entry member
          exact Nat.lt_trans bounded (Nat.lt_succ_self _)
      · have missing : bijection.nextNode ∉ bijection.toAllocator.map Prod.snd := by
          intro member
          obtain ⟨entry, member, equal⟩ := List.mem_map.mp member
          have bounded := bounds entry member
          omega
        simpa only [List.map_cons, List.nodup_cons] using And.intro missing unique

/-- Actual tree composition retains distinct allocator nodes. -/
theorem mkBijBuildAux_unique_nodes (tree : WordClashTree)
    (bijection : CakeNodeBijectionBuild) :
    (∀ entry ∈ bijection.toAllocator, entry.2 < bijection.nextNode) →
    (bijection.toAllocator.map Prod.snd).Nodup →
    ((cakeMkBijBuildAux tree bijection).toAllocator.map Prod.snd).Nodup := by
  fun_induction cakeMkBijBuildAux tree bijection
  case case1 =>
    intro bounds unique
    exact listRemapBuild_unique_nodes _ _ (listRemapBuild_bounds _ _ bounds)
      (listRemapBuild_unique_nodes _ _ bounds unique)
  case case2 =>
    intro bounds unique
    exact listRemapBuild_unique_nodes _ _ bounds unique
  case case3 =>
    rename_i thenBranch elseBranch bij mapped ih2 ih1
    intro bounds unique
    exact ih1 (mkBijBuildAux_bounds _ _ bounds) (ih2 bounds unique)
  case case4 =>
    rename_i thenBranch elseBranch bij mapped names ih2 ih1
    intro bounds unique
    exact listRemapBuild_unique_nodes _ _
      (mkBijBuildAux_bounds _ _ (mkBijBuildAux_bounds _ _ bounds))
      (ih1 (mkBijBuildAux_bounds _ _ bounds) (ih2 bounds unique))
  case case5 =>
    rename_i first second bij ih2 ih1
    intro bounds unique
    exact ih1 (mkBijBuildAux_bounds _ _ bounds) (ih2 bounds unique)

/-- Actual public bijection nodes are distinct, from empty initialization. -/
theorem mkBij_unique_nodes (tree : WordClashTree) :
    ((cakeMkBij tree).toAllocator.map Prod.snd).Nodup := by
  apply mkBijBuildAux_unique_nodes tree
  · simp
  · simp

private theorem lookup_of_unique_member (entries : NatInfoMap Nat) (key value : Nat)
    (unique : (entries.map Prod.fst).Nodup) (member : (key, value) ∈ entries) :
    lookupNatInfo key entries = some value := by
  induction entries with
  | nil => simp at member
  | cons entry entries ih =>
    rcases entry with ⟨name, stored⟩
    have parts : name ∉ entries.map Prod.fst ∧ (entries.map Prod.fst).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using unique
    rcases List.mem_cons.mp member with equal | tailMember
    · cases equal
      simp [lookupNatInfo]
    · have different : name ≠ key := by
        intro equal
        apply parts.1
        exact List.mem_map.mpr ⟨(key, value), tailMember, equal.symm⟩
      simpa [lookupNatInfo, different] using ih parts.2 tailMember

/-- Every actual emitted forward binding is returned by first-binding lookup. -/
theorem mkBij_forward_lookup (tree : WordClashTree) (name node : Nat)
    (member : (name, node) ∈ (cakeMkBij tree).toAllocator) :
    lookupNatInfo name (cakeMkBij tree).toAllocator = some node := by
  exact lookup_of_unique_member _ _ _ (mkBij_unique_names tree) member

/-- Paired actual histories and unique node ownership give the reverse lookup
for each emitted forward binding. -/
theorem mkBij_reverse_lookup (tree : WordClashTree) (name node : Nat)
    (member : (name, node) ∈ (cakeMkBij tree).toAllocator) :
    lookupNatInfo node (cakeMkBij tree).fromAllocator = some name := by
  apply lookup_of_unique_member
  · rw [mkBij_reverse]
    simpa only [List.map_map, Function.comp_def, Prod.swap, Prod.fst] using
      mkBij_unique_nodes tree
  · rw [mkBij_reverse]
    exact List.mem_map.mpr ⟨(name, node), member, rfl⟩

/-- Sorting the actual bijection and mapping node tags retains each emitted
binding's colour in first-binding lookup; uniqueness is derived from mkBij. -/
theorem extractColor_lookup (tree : WordClashTree) (state : CakeRaState)
    (name node : Nat) (member : (name, node) ∈ (cakeMkBij tree).toAllocator) :
    lookupNatInfo name (cakeExtractColor state (cakeMkBij tree).toAllocator) =
      some (cakeTagCol state node) := by
  apply lookup_of_unique_member
  · unfold cakeExtractColor
    have unique := (List.mergeSort_perm (cakeMkBij tree).toAllocator
      (fun a b => a.1 < b.1)).map Prod.fst
    have sortedUnique := unique.nodup_iff.mpr (mkBij_unique_names tree)
    simpa only [List.map_map, Function.comp_def] using sortedUnique
  · unfold cakeExtractColor
    apply List.mem_map.mpr
    exact ⟨(name, node), (List.mergeSort_perm _ _).mem_iff.mpr member, rfl⟩

private theorem tagFold_unchanged (nodes : List Nat) (tags : CakeNodeMap CakeNodeTag)
    (tag : Nat → CakeNodeTag) (node : Nat) (missing : node ∉ nodes) :
    (nodes.foldl (fun tags i => tags.set i (tag i)) tags).get node = tags.get node := by
  induction nodes generalizing tags with
  | nil => rfl
  | cons head rest ih =>
    have parts : node ≠ head ∧ node ∉ rest := by simpa using missing
    simp only [List.foldl_cons]
    rw [ih _ parts.2, CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm parts.1)]

private theorem tagFold_member (nodes : List Nat) (tags : CakeNodeMap CakeNodeTag)
    (tag : Nat → CakeNodeTag) (node : Nat) (unique : nodes.Nodup)
    (member : node ∈ nodes) :
    (nodes.foldl (fun tags i => tags.set i (tag i)) tags).get node = some (tag node) := by
  induction nodes generalizing tags with
  | nil => simp at member
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with equal | member
    · subst node
      rw [tagFold_unchanged _ _ _ _ parts.1, CakeNodeMap.get_set_self]
    · exact ih _ parts.2 member

/-- Actual initialization writes its indexed source role at each node in range. -/
theorem mkTags_get (n node : Nat) (fromAllocator : NatInfoMap Nat) (fs : List Nat)
    (bounded : node < n) :
    (cakeMkTags n fromAllocator fs).get node = some
      (let v := cakeSpDefaultIndexed (cakeSpDefaultIndex fromAllocator) node
       match v % 4 with
       | 1 => if (Flapjack.natSetOfList fs).contains v then .sTemp else .aTemp
       | 3 => .sTemp
       | _ => .fixed (v / 2)) := by
  let tag : Nat → CakeNodeTag := fun i =>
    let v := cakeSpDefaultIndexed (cakeSpDefaultIndex fromAllocator) i
    match v % 4 with
    | 1 => if (Flapjack.natSetOfList fs).contains v then .sTemp else .aTemp
    | 3 => .sTemp
    | _ => .fixed (v / 2)
  have stepEquality :
      (fun (tags : CakeNodeMap CakeNodeTag) i =>
        let v := cakeSpDefaultIndexed (cakeSpDefaultIndex fromAllocator) i
        match v % 4 with
        | 1 => tags.set i (if (Flapjack.natSetOfList fs).contains v then .sTemp else .aTemp)
        | 3 => tags.set i .sTemp
        | _ => tags.set i (.fixed (v / 2))) =
      (fun tags i => tags.set i (tag i)) := by
    funext tags i
    dsimp [tag]
    split <;> rfl
  unfold cakeMkTags
  dsimp only
  dsimp only at stepEquality
  have folded := congrArg
    (fun step => (List.range n).foldl step (CakeNodeMap.ofSize n)) stepEquality
  exact (congrArg (fun tags => tags.get node) folded).trans
    (tagFold_member _ _ _ _ List.nodup_range (List.mem_range.mpr bounded))

/-- Every actual emitted physical source binding starts fixed at its hardware
register; bounds and reverse ownership are derived from the real builder. -/
theorem mkTags_physical (tree : WordClashTree) (fs : List Nat) (name node : Nat)
    (member : (name, node) ∈ (cakeMkBij tree).toAllocator)
    (physical : name % 2 = 0) :
    (cakeMkTags (cakeMkBij tree).nextNode (cakeMkBij tree).fromAllocator fs).get node =
      some (.fixed (name / 2)) := by
  have source : cakeSpDefaultIndexed
      (cakeSpDefaultIndex (cakeMkBij tree).fromAllocator) node = name := by
    unfold cakeSpDefaultIndexed
    rw [spDefaultIndex_lookup, mkBij_reverse_lookup tree name node member]
  rw [mkTags_get _ _ _ _ (mkBij_bounds tree _ member), source]
  have notOne : name % 4 ≠ 1 := by omega
  have notThree : name % 4 ≠ 3 := by omega
  dsimp only
  split <;> simp_all

/-- The actual successful allocator returns the original hardware register for
an emitted physical binding. This composes real initialization, all allocator
phases and sorted extraction; it assumes no desired colouring relation. -/
theorem regAlloc_physical_lookup (tree : WordClashTree)
    (forced : List (Nat × Nat)) (fs : List Nat)
    (algorithm : CakeAlgorithm) (cost : Option (CakeNodeMap Nat)) (k : Nat)
    (moves : List (Nat × (Nat × Nat))) (output : NatInfoMap Nat) (name node : Nat)
    (member : (name, node) ∈ (cakeMkBij tree).toAllocator)
    (physical : name % 2 = 0)
    (allocated : cakeDoRegAllocFromState algorithm cost k moves (cakeMkBij tree)
      (cakeInitRaStateFromBij (cakeMkBij tree) tree forced fs) = some output) :
    lookupNatInfo name output = some (name / 2) := by
  obtain ⟨finalState, extracted, preserved⟩ :=
    regAllocFromState_preserves_fixed algorithm cost k moves (cakeMkBij tree) _ output allocated
  have initialized :
      (cakeInitRaStateFromBij (cakeMkBij tree) tree forced fs).nodeTag.get node =
        some (.fixed (name / 2)) := by
    change (cakeMkTags (cakeMkBij tree).nextNode (cakeMkBij tree).fromAllocator fs).get node = _
    exact mkTags_physical tree fs name node member physical
  have fixed := preserved node (name / 2) initialized
  rw [extracted, extractColor_lookup tree finalState name node member]
  simp [cakeTagCol, fixed]

end Flapjack
