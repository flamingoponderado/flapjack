import Flapjack.Compiler.Backend.RegAlloc.ProductionGraphRows

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- Admission-only projection of the reference clique traversal. This
Flapjack helper has no separate HOL original; its equations are proved below
to be the live-list projection of the actual reference graph builder. -/
def cliqueAdmission : List Nat → List Nat → List Nat
  | [], live => live
  | node :: rest, live =>
      if live.contains node then cliqueAdmission rest live
      else cliqueAdmission rest (node :: live)

private def admissionStep (state : Std.TreeSet Nat × List Nat) (node : Nat) :
    Std.TreeSet Nat × List Nat :=
  if state.1.contains node then (state.1, state.2)
  else (state.1.insert node, node :: state.2)

private theorem admissionFold (new initial : List Nat) (seen : Std.TreeSet Nat) (added : List Nat)
    (indexed : ∀ key, seen.contains key = (added ++ initial).contains key) :
    (new.foldl admissionStep (seen, added)).2 ++ initial =
      cliqueAdmission new (added ++ initial) := by
  induction new generalizing seen added with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.foldl_cons, admissionStep, cliqueAdmission]
    rw [← indexed node]
    cases present : seen.contains node with
    | true => simpa only [present, ↓reduceIte] using ih seen added indexed
    | false =>
      apply ih (seen.insert node) (node :: added)
      intro key
      simp only [Std.TreeSet.contains_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        Bool.beq_eq_decide_eq, indexed, List.cons_append, List.contains_cons]
      simp only [eq_comm]

/-- Full executed batch admission keeps exactly the reference's newest-first
live list, including repeated new names and repeated initial entries. This
proves the actual TreeSet fold, without assuming its result. Untagged
production correspondence infrastructure. Graph row transport is separate. -/
theorem extendCliqueBatch_live (new initial : List Nat) (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendCliqueSetBatch new initial cache).2 = cliqueAdmission new initial := by
  have run := admissionFold new initial (Std.TreeSet.ofList initial) []
    (by intro key; simp [Std.TreeSet.contains_ofList])
  unfold cakeExtendCliqueSetBatch
  change (new.foldl admissionStep (Std.TreeSet.ofList initial, [])).2 ++ initial = _
  simpa only [List.nil_append] using run

/-- The admission projection is derived from the real recursive reference,
independently of its starting graph or intermediate edge updates. -/
theorem extendCliqueSetReference_live (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendCliqueSetReference new initial cache).2 = cliqueAdmission new initial := by
  induction new generalizing initial cache with
  | nil => simp [cakeExtendCliqueSetReference, cliqueAdmission]
  | cons node rest ih =>
    simp only [cakeExtendCliqueSetReference, cliqueAdmission]
    split <;> exact ih _ _

/-- The executed batch has exactly the reference's complete live-list result.
This alone does not establish graph correspondence or native state success. -/
theorem extendCliqueBatch_live_reference (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendCliqueSetBatch new initial cache).2 =
      (cakeExtendCliqueSetReference new initial cache).2 := by
  rw [extendCliqueBatch_live, extendCliqueSetReference_live]

/-- Missing input slots distinguish batching from recursive edge insertion:
an isolated admitted node receives an empty row in the batch. Full native
correspondence must derive present in-domain slots from the actual initializer
and bijection bounds; arbitrary missing slots cannot be assumed equivalent. -/
theorem extendCliqueBatch_missingSlot :
    ((cakeExtendCliqueSetBatch [0] [] (cakeAdjSetMapOfSize 0)).1.get 0).map cakeAdjSetList = some [] ∧
    ((cakeExtendCliqueSetReference [0] [] (cakeAdjSetMapOfSize 0)).1.get 0).map cakeAdjSetList = none := by
  simp only [cakeExtendCliqueSetReference, List.contains_nil, Bool.false_eq_true,
    ↓reduceIte, cakeListInsertEdgeSet]
  decide

/-- The actual graph seed supplies present empty rows at precisely the
initializer dimension. This is the real input-domain fact needed to avoid
the missing-slot discrepancy above, rather than a supplied graph output. -/
theorem graphSeed_get (dimension key : Nat) :
    (cakeAdjSetMapOfSize dimension).get key =
      if key < dimension then some (∅ : Std.TreeSet Nat) else none := by
  by_cases bounded : key < dimension <;>
    simp [cakeAdjSetMapOfSize, CakeNodeMap.get, bounded, cakeMapLookup, lookupNatInfo]

private def unionRow (partners : Nat → Std.TreeSet Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (node : Nat) : CakeNodeMap (Std.TreeSet Nat) :=
  cache.set node (((cache.get node).getD ∅).union (partners node))

private theorem unionRowsFold_membership (nodes : List Nat) (partners : Nat → Std.TreeSet Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (key member : Nat) :
    ((nodes.foldl (unionRow partners) cache).get key).map (fun set => set.contains member) =
      if nodes.contains key then
        some (((cache.get key).getD ∅).contains member || (partners key).contains member)
      else (cache.get key).map (fun set => set.contains member) := by
  induction nodes generalizing cache with
  | nil => rfl
  | cons node rest ih =>
    rw [List.foldl_cons, ih]
    by_cases equal : key = node
    · subst key
      simp [unionRow, CakeNodeMap.get_set_self, Std.TreeSet.contains_union]
    · simp [unionRow, CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm equal),
        equal]

/-- The actual batch's admission tuple, including its membership set and
newest-first admitted list. Untagged proof infrastructure for the executed
fold; no desired admission output is a parameter. -/
def cliqueBatchAdmissions (new initial : List Nat) : Std.TreeSet Nat × List Nat :=
  new.foldl admissionStep (Std.TreeSet.ofList initial, [])

private theorem defaultContains (row : Option (Std.TreeSet Nat)) (member : Nat) :
    (row.getD ∅).contains member = (row.map (fun set => set.contains member)).getD false := by
  cases row <;> rfl

private theorem batchGraph_eq (new initial : List Nat) (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendCliqueSetBatch new initial cache).1 =
      initial.foldl (unionRow (fun _ => Std.TreeSet.ofList (cliqueBatchAdmissions new initial).2))
        ((cliqueBatchAdmissions new initial).2.foldl
          (unionRow (fun node => (cliqueBatchAdmissions new initial).1.erase node)) cache) := by
  unfold cakeExtendCliqueSetBatch cliqueBatchAdmissions admissionStep unionRow
  rfl

/-- Complete all-key batch graph observation calculated from the real
admission fold and incoming graph. The two updates include missing-row
creation explicitly. This producer equation is used below to prove complete
valid-input reference and native-state correspondence. -/
theorem extendCliqueBatch_graphMembership (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (key member : Nat) :
    let admitted := cliqueBatchAdmissions new initial
    let afterAdded := if admitted.2.contains key then
        some (((cache.get key).getD ∅).contains member ||
          (admitted.1.erase key).contains member)
      else (cache.get key).map (fun set => set.contains member)
    ((cakeExtendCliqueSetBatch new initial cache).1.get key).map
      (fun set => set.contains member) =
      if initial.contains key then
        some (afterAdded.getD false || (Std.TreeSet.ofList admitted.2).contains member)
      else afterAdded := by
  let admitted := cliqueBatchAdmissions new initial
  let first := admitted.2.foldl (unionRow (fun node => admitted.1.erase node)) cache
  have firstRows := unionRowsFold_membership admitted.2
    (fun node => admitted.1.erase node) cache key member
  have finalRows := unionRowsFold_membership initial
    (fun _ => Std.TreeSet.ofList admitted.2) first key member
  rw [defaultContains] at finalRows
  dsimp only [first] at finalRows
  rw [firstRows] at finalRows
  rw [batchGraph_eq]
  exact finalRows

private theorem admissionFold_seed (new : List Nat)
    (first second : Std.TreeSet Nat) (firstAdded secondAdded suffix : List Nat)
    (indexed : ∀ key, first.contains key = second.contains key)
    (history : secondAdded = firstAdded ++ suffix) :
    (∀ key, (new.foldl admissionStep (first, firstAdded)).1.contains key =
      (new.foldl admissionStep (second, secondAdded)).1.contains key) ∧
    (new.foldl admissionStep (second, secondAdded)).2 =
      (new.foldl admissionStep (first, firstAdded)).2 ++ suffix := by
  induction new generalizing first second firstAdded secondAdded with
  | nil => exact ⟨indexed, history⟩
  | cons node rest ih =>
    simp only [List.foldl_cons, admissionStep, indexed node]
    cases present : second.contains node with
    | true => simpa only [present, ↓reduceIte] using ih first second firstAdded secondAdded indexed history
    | false =>
      apply ih (first.insert node) (second.insert node) (node :: firstAdded) (node :: secondAdded)
      · intro key
        simp only [Std.TreeSet.contains_insert, indexed]
      · simp only [history, List.cons_append]

/-- A fresh leading admission has the same final membership set as starting
the remaining traversal with that node in the clique. Its emitted history is
the later history followed by this first admission, as required by the
newest-first reference order. This derives both facts from executed folds. -/
theorem cliqueBatchAdmissions_cons_fresh (node : Nat) (rest initial : List Nat)
    (fresh : initial.contains node = false) :
    (∀ key, (cliqueBatchAdmissions (node :: rest) initial).1.contains key =
      (cliqueBatchAdmissions rest (node :: initial)).1.contains key) ∧
    (cliqueBatchAdmissions (node :: rest) initial).2 =
      (cliqueBatchAdmissions rest (node :: initial)).2 ++ [node] := by
  have seeds : ∀ key, (Std.TreeSet.ofList (node :: initial)).contains key =
      ((Std.TreeSet.ofList initial).insert node).contains key := by
    intro key
    simp only [Std.TreeSet.contains_ofList, Std.TreeSet.contains_insert,
      Std.LawfulEqCmp.compare_eq_iff_eq, Bool.beq_eq_decide_eq, List.contains_cons]
    simp only [eq_comm]
  have run := admissionFold_seed rest (Std.TreeSet.ofList (node :: initial))
    ((Std.TreeSet.ofList initial).insert node) [] [node] [node] seeds rfl
  unfold cliqueBatchAdmissions
  rw [List.foldl_cons]
  simp only [admissionStep, Std.TreeSet.contains_ofList, fresh]
  exact ⟨fun key => (run.1 key).symm, run.2⟩

/-- A repeated leading name leaves the complete executed admission tuple
unchanged, including its membership carrier, rather than merely its live list. -/
theorem cliqueBatchAdmissions_cons_present (node : Nat) (rest initial : List Nat)
    (present : initial.contains node = true) :
    cliqueBatchAdmissions (node :: rest) initial = cliqueBatchAdmissions rest initial := by
  unfold cliqueBatchAdmissions
  rw [List.foldl_cons]
  simp only [admissionStep, Std.TreeSet.contains_ofList, present, ↓reduceIte]

private theorem admissionFold_addedContains (new : List Nat) (seen : Std.TreeSet Nat)
    (added : List Nat) (key : Nat) :
    (new.foldl admissionStep (seen, added)).2.contains key =
      (added.contains key || (new.contains key && !seen.contains key)) := by
  induction new generalizing seen added with
  | nil => simp
  | cons node rest ih =>
    simp only [List.foldl_cons, admissionStep]
    cases present : seen.contains node
    all_goals rw [ih]
    all_goals by_cases atNode : key = node
    all_goals first
      | subst key; simp [present, Std.TreeSet.contains_insert]
      | simp [Std.TreeSet.contains_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
          Bool.beq_eq_decide_eq, atNode, Ne.symm atNode]

private theorem admissionFold_membersContains (new : List Nat) (seen : Std.TreeSet Nat)
    (added : List Nat) (key : Nat) :
    (new.foldl admissionStep (seen, added)).1.contains key =
      (seen.contains key || new.contains key) := by
  induction new generalizing seen added with
  | nil => simp
  | cons node rest ih =>
    simp only [List.foldl_cons, admissionStep]
    cases present : seen.contains node
    all_goals rw [ih]
    all_goals by_cases atNode : key = node
    all_goals first
      | subst key; simp [present, Std.TreeSet.contains_insert]
      | simp [Std.TreeSet.contains_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
          Bool.beq_eq_decide_eq, atNode, Ne.symm atNode]

/-- Exactly the input names absent from the initial clique are admitted.
This all-key fact follows from the executed fold, including duplicate inputs;
it is not an assumed property of its output list. -/
theorem cliqueBatchAdmissions_addedContains (new initial : List Nat) (key : Nat) :
    (cliqueBatchAdmissions new initial).2.contains key =
      (new.contains key && !initial.contains key) := by
  have run := admissionFold_addedContains new (Std.TreeSet.ofList initial) [] key
  rw [Std.TreeSet.contains_ofList] at run
  simpa only [cliqueBatchAdmissions, List.contains_nil, Bool.false_or] using run

/-- The actual final membership set is exactly the union of incoming and new
names, derived from the executed admission fold without output premises. -/
theorem cliqueBatchAdmissions_membersContains (new initial : List Nat) (key : Nat) :
    (cliqueBatchAdmissions new initial).1.contains key =
      (initial.contains key || new.contains key) := by
  have run := admissionFold_membersContains new (Std.TreeSet.ofList initial) [] key
  rw [Std.TreeSet.contains_ofList] at run
  exact run

/-- Edges introduced by extending a clique: distinct final members with at
least one newly admitted endpoint. This is untagged graph correspondence
infrastructure, expressed entirely in the original input lists. -/
def cliqueNewEdge (new initial : List Nat) (key member : Nat) : Bool :=
  !(key == member) &&
    ((initial.contains key || new.contains key) && (initial.contains member || new.contains member)) &&
    ((new.contains key && !initial.contains key) || (new.contains member && !initial.contains member))

/-- Complete executed graph observations from the incoming rows and the
original input lists. Present rows are required only for input nodes; the
initializer's checked domain supplies them. This does not assume a graph
output or successful native evaluation. -/
theorem extendCliqueBatch_staticMembership (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat))
    (present : ∀ node, node ∈ new ∨ node ∈ initial → (cache.get node).isSome = true)
    (key member : Nat) :
    ((cakeExtendCliqueSetBatch new initial cache).1.get key).map
      (fun set => set.contains member) =
      (cache.get key).map (fun set => set.contains member || cliqueNewEdge new initial key member) := by
  rw [extendCliqueBatch_graphMembership]
  simp only [Std.TreeSet.contains_ofList, cliqueBatchAdmissions_addedContains,
    Std.TreeSet.contains_erase, cliqueBatchAdmissions_membersContains]
  unfold cliqueNewEdge
  cases old : cache.get key with
  | none =>
    have notNew : key ∉ new := by
      intro belongs
      have available := present key (Or.inl belongs)
      simp [old] at available
    have notInitial : key ∉ initial := by
      intro belongs
      have available := present key (Or.inr belongs)
      simp [old] at available
    simp [notNew, notInitial]
  | some row =>
    by_cases same : key = member
    · subst member
      cases new.contains key <;> cases initial.contains key <;> simp
    · cases new.contains key <;> cases initial.contains key
      all_goals cases new.contains member <;> cases initial.contains member
      all_goals simp [same]
      all_goals simp [bne, Bool.beq_eq_decide_eq, Std.LawfulEqCmp.compare_eq_iff_eq, same]

private theorem set_present (cache : CakeNodeMap (Std.TreeSet Nat)) (node key : Nat)
    (row : Std.TreeSet Nat) (present : (cache.get key).isSome = true) :
    ((cache.set node row).get key).isSome = true := by
  by_cases same : key = node
  · subst key; simp only [CakeNodeMap.get_set_self, Option.isSome_some]
  · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm same)]; exact present

private theorem insertEdgeSet_present (cache : CakeNodeMap (Std.TreeSet Nat)) (x y key : Nat)
    (present : (cache.get key).isSome = true) :
    ((cakeInsertEdgeSet x y cache).get key).isSome = true := by
  unfold cakeInsertEdgeSet
  exact set_present _ _ _ _ (set_present _ _ _ _ present)

private theorem listInsertEdgeSet_present (nodes : List Nat) (cache : CakeNodeMap (Std.TreeSet Nat))
    (node key : Nat) (present : (cache.get key).isSome = true) :
    ((cakeListInsertEdgeSet node nodes cache).get key).isSome = true := by
  induction nodes generalizing cache with
  | nil => exact present
  | cons partner rest ih =>
    exact ih _ (insertEdgeSet_present cache node partner key present)

private theorem containsInsert (set : Std.TreeSet Nat) (node member : Nat) :
    (set.insert node).contains member = (set.contains member || (member == node)) := by
  simp only [Std.TreeSet.contains_insert, Bool.beq_eq_decide_eq,
    Std.LawfulEqCmp.compare_eq_iff_eq]
  simp only [eq_comm, Bool.or_comm]

private theorem insertEdgeSet_membership (cache : CakeNodeMap (Std.TreeSet Nat))
    (x y key member : Nat) (xPresent : (cache.get x).isSome = true)
    (yPresent : (cache.get y).isSome = true) :
    ((cakeInsertEdgeSet x y cache).get key).map (fun set => set.contains member) =
      (cache.get key).map (fun set => set.contains member ||
        ((key == x && member == y) || (key == y && member == x))) := by
  unfold cakeInsertEdgeSet
  by_cases atY : key = y
  · subst key
    rw [CakeNodeMap.get_set_self]
    cases old : cache.get y with
    | none => simp [old] at yPresent
    | some row =>
      simp only [Option.getD_some, Option.map_some, containsInsert]
      by_cases same : x = y
      · subst x; simp
      · simp only [Bool.beq_eq_decide_eq]
        simp [Ne.symm same]
  · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atY)]
    by_cases atX : key = x
    · subst key
      rw [CakeNodeMap.get_set_self]
      cases old : cache.get x with
      | none => simp [old] at xPresent
      | some row =>
        simp only [Option.getD_some, Option.map_some, containsInsert, Bool.beq_eq_decide_eq]
        simp [atY]
    · rw [CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm atX)]
      simp only [Bool.beq_eq_decide_eq]
      simp [atX, atY]

private theorem listInsertEdgeSet_membership (nodes : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (node key member : Nat)
    (nodePresent : (cache.get node).isSome = true)
    (partnersPresent : ∀ partner ∈ nodes, (cache.get partner).isSome = true) :
    ((cakeListInsertEdgeSet node nodes cache).get key).map (fun set => set.contains member) =
      (cache.get key).map (fun set => set.contains member ||
        ((key == node && nodes.contains member) || (member == node && nodes.contains key))) := by
  induction nodes generalizing cache with
  | nil => simp [cakeListInsertEdgeSet]
  | cons partner rest ih =>
    have nodeStill := insertEdgeSet_present cache node partner node nodePresent
    have partnersStill : ∀ next ∈ rest, ((cakeInsertEdgeSet node partner cache).get next).isSome = true := by
      intro next belongs
      exact insertEdgeSet_present cache node partner next
        (partnersPresent next (List.mem_cons_of_mem _ belongs))
    simp only [cakeListInsertEdgeSet]
    rw [ih _ nodeStill partnersStill]
    have step := insertEdgeSet_membership cache node partner key member nodePresent
      (partnersPresent partner List.mem_cons_self)
    have carried := congrArg
      (Option.map (fun bit => bit || ((key == node && rest.contains member) ||
        (member == node && rest.contains key)))) step
    simp only [Option.map_map, Function.comp_def] at carried
    rw [carried]
    simp only [List.contains_cons, Bool.and_or_distrib_left]
    congr 1
    funext row
    simp only [Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem cliqueNewEdge_cons_present (node : Nat) (rest initial : List Nat)
    (present : initial.contains node = true) (key member : Nat) :
    cliqueNewEdge (node :: rest) initial key member = cliqueNewEdge rest initial key member := by
  unfold cliqueNewEdge
  simp only [List.contains_cons, Bool.beq_eq_decide_eq]
  by_cases atKey : key = node
  · subst key
    by_cases atMember : member = node
    · subst member; simp
    · rw [present]; simp [atMember]
  · by_cases atMember : member = node
    · subst member; rw [present]; simp [atKey]
    · simp [atKey, atMember]

private theorem cliqueNewEdge_cons_fresh (node : Nat) (rest initial : List Nat)
    (fresh : initial.contains node = false) (key member : Nat) :
    cliqueNewEdge (node :: rest) initial key member =
      (((key == node && initial.contains member) || (member == node && initial.contains key)) ||
        cliqueNewEdge rest (node :: initial) key member) := by
  unfold cliqueNewEdge
  simp only [List.contains_cons, Bool.beq_eq_decide_eq]
  by_cases atKey : key = node
  · subst key
    by_cases atMember : member = node
    · subst member; rw [fresh]; simp
    · rw [fresh]
      cases initial.contains member <;> cases rest.contains member <;> simp [atMember, Ne.symm atMember]
  · by_cases atMember : member = node
    · subst member
      rw [fresh]
      cases initial.contains key <;> cases rest.contains key <;> simp [atKey]
    · simp [atKey, atMember]

/-- The actual recursive reference produces the same static added-edge
relation from valid incoming rows. Every intermediate row-domain fact is
derived from real edge updates; no final graph is assumed. -/
theorem extendCliqueSetReference_staticMembership (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat))
    (present : ∀ node, node ∈ new ∨ node ∈ initial → (cache.get node).isSome = true)
    (key member : Nat) :
    ((cakeExtendCliqueSetReference new initial cache).1.get key).map
      (fun set => set.contains member) =
      (cache.get key).map (fun set => set.contains member || cliqueNewEdge new initial key member) := by
  induction new generalizing initial cache with
  | nil => simp [cakeExtendCliqueSetReference, cliqueNewEdge]
  | cons node rest ih =>
    simp only [cakeExtendCliqueSetReference]
    cases admitted : initial.contains node with
    | true =>
      simp only [↓reduceIte]
      rw [ih _ _ (fun next belongs => present next (belongs.elim
        (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr)),
        cliqueNewEdge_cons_present node rest initial admitted]
    | false =>
      have nodePresent := present node (Or.inl List.mem_cons_self)
      have initialPresent : ∀ partner ∈ initial, (cache.get partner).isSome = true :=
        fun partner belongs => present partner (Or.inr belongs)
      have nextPresent : ∀ next, next ∈ rest ∨ next ∈ node :: initial →
          ((cakeListInsertEdgeSet node initial cache).get next).isSome = true := by
        intro next belongs
        apply listInsertEdgeSet_present initial cache node next
        apply present next
        rcases belongs with belongs | belongs
        · exact Or.inl (List.mem_cons_of_mem _ belongs)
        · rcases List.mem_cons.mp belongs with rfl | belongs
          · exact Or.inl List.mem_cons_self
          · exact Or.inr belongs
      simp only [Bool.false_eq_true, if_false]
      rw [ih _ _ nextPresent]
      have edges := listInsertEdgeSet_membership initial cache node key member nodePresent initialPresent
      have carried := congrArg (Option.map (fun bit => bit || cliqueNewEdge rest (node :: initial) key member)) edges
      simp only [Option.map_map, Function.comp_def] at carried
      rw [carried, cliqueNewEdge_cons_fresh node rest initial admitted]
      simp only [Bool.or_assoc]

private theorem mapUpdate_materialize (entries : NatInfoMap (Std.TreeSet Nat)) (key : Nat)
    (row : Std.TreeSet Nat) :
    (cakeMapUpdate entries key row).map (fun entry => (entry.1, cakeAdjSetList entry.2)) =
      cakeMapUpdate (entries.map (fun entry => (entry.1, cakeAdjSetList entry.2))) key (cakeAdjSetList row) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨node, previous⟩ := entry
    simp only [cakeMapUpdate, List.map_cons]
    split <;> simp only [List.map_cons, ih]

private theorem set_materialize (cache : CakeNodeMap (Std.TreeSet Nat)) (key : Nat) (row : Std.TreeSet Nat) :
    (cache.set key row).mapValues cakeAdjSetList =
      (cache.mapValues cakeAdjSetList).set key (cakeAdjSetList row) := by
  by_cases bounded : key < cache.slots.size
  · simp [CakeNodeMap.set, CakeNodeMap.mapValues, bounded]
  · simp [CakeNodeMap.set, CakeNodeMap.mapValues, bounded, mapUpdate_materialize]

/-- Complete dense and extension map codec for actual cached edge insertion.
Unlike the lookup-only observation, this also preserves the map structure.
Untagged infrastructure for actual/native graph producer proofs. -/
theorem cakeInsertEdgeSet_materialize_eq (cache : CakeNodeMap (Std.TreeSet Nat)) (x y : Nat) :
    (cakeInsertEdgeSet x y cache).mapValues cakeAdjSetList =
      cakeInsertEdge x y (cache.mapValues cakeAdjSetList) := by
  unfold cakeInsertEdgeSet cakeInsertEdge cakeAdjSub
  rw [set_materialize, set_materialize]
  simp only [cakeAdjSetList_insert, CakeNodeMap.get_mapValues]
  cases cache.get x <;> cases cache.get y <;> rfl

private theorem listInsertEdgeSet_materialize_eq (nodes : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (node : Nat) :
    (cakeListInsertEdgeSet node nodes cache).mapValues cakeAdjSetList =
      cakeListInsertEdge node nodes (cache.mapValues cakeAdjSetList) := by
  induction nodes generalizing cache with
  | nil => rfl
  | cons partner rest ih =>
    simp only [cakeListInsertEdgeSet, cakeListInsertEdge]
    rw [ih, cakeInsertEdgeSet_materialize_eq]

/-- Full graph and live-list materialization of the recursive reference,
including dense and extension map structure. No domain or result premise is
needed for this set/list codec equation. Untagged actual infrastructure. -/
theorem extendCliqueSetReference_materialize (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (((cakeExtendCliqueSetReference new initial cache).1.mapValues cakeAdjSetList),
      (cakeExtendCliqueSetReference new initial cache).2) =
        cakeExtendClique new initial (cache.mapValues cakeAdjSetList) := by
  induction new generalizing initial cache with
  | nil => simp [cakeExtendCliqueSetReference, cakeExtendClique]
  | cons node rest ih =>
    simp only [cakeExtendCliqueSetReference, cakeExtendClique]
    cases present : initial.contains node with
    | true => simpa only [↓reduceIte] using ih initial cache
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have run := ih (node :: initial) (cakeListInsertEdgeSet node initial cache)
      rw [listInsertEdgeSet_materialize_eq] at run
      exact run

/-- Complete ordered row equality of the executed batch and the recursive
reference at every key. The original incoming row domain is the only extra
condition; missing slots outside the input names remain covered. -/
theorem extendCliqueBatch_rows_reference (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat))
    (present : ∀ node, node ∈ new ∨ node ∈ initial → (cache.get node).isSome = true) (key : Nat) :
    (((cakeExtendCliqueSetBatch new initial cache).1.mapValues cakeAdjSetList).get key) =
      (((cakeExtendCliqueSetReference new initial cache).1.mapValues cakeAdjSetList).get key) := by
  have observations (member : Nat) :=
    (extendCliqueBatch_staticMembership new initial cache present key member).trans
      (extendCliqueSetReference_staticMembership new initial cache present key member).symm
  rw [CakeNodeMap.get_mapValues, CakeNodeMap.get_mapValues]
  cases left : (cakeExtendCliqueSetBatch new initial cache).1.get key <;>
    cases right : (cakeExtendCliqueSetReference new initial cache).1.get key
  · rfl
  · have impossible := observations 0; simp [left, right] at impossible
  · have impossible := observations 0; simp [left, right] at impossible
  · rename_i first second
    have same : ∀ member, first.contains member = second.contains member := by
      intro member
      have observed := observations member
      simpa only [left, right, Option.map_some, Option.some.injEq] using observed
    exact congrArg some (congrArg List.reverse
      (Std.TreeSet.Equiv.toList_eq (Std.TreeSet.Equiv.of_forall_contains_eq same)))

/-- Full executed batch versus list-reference output: exact live-list order
and complete descending row values, including arbitrary outside keys. The
incoming input-node slots must be present, as derived from real initialization
and bijection bounds. This is untagged actual/native infrastructure. -/
theorem extendCliqueBatch_materialize (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat))
    (present : ∀ node, node ∈ new ∨ node ∈ initial → (cache.get node).isSome = true) :
    (cakeExtendCliqueSetBatch new initial cache).2 =
        (cakeExtendClique new initial (cache.mapValues cakeAdjSetList)).2 ∧
      ∀ key, ((cakeExtendCliqueSetBatch new initial cache).1.mapValues cakeAdjSetList).get key =
        (cakeExtendClique new initial (cache.mapValues cakeAdjSetList)).1.get key := by
  have reference := extendCliqueSetReference_materialize new initial cache
  constructor
  · rw [extendCliqueBatch_live_reference]
    exact congrArg Prod.snd reference
  · intro key
    exact (extendCliqueBatch_rows_reference new initial cache present key).trans
      (congrArg (fun rows => rows.get key) (congrArg Prod.fst reference))

private theorem unionRowsFold_frame (nodes : List Nat) (partners : Nat → Std.TreeSet Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (bounds : ∀ node ∈ nodes, node < cache.slots.size) :
    (nodes.foldl (unionRow partners) cache).slots.size = cache.slots.size ∧
      (nodes.foldl (unionRow partners) cache).outside = cache.outside := by
  induction nodes generalizing cache with
  | nil => exact ⟨rfl, rfl⟩
  | cons node rest ih =>
    have bounded := bounds node List.mem_cons_self
    have size : (unionRow partners cache node).slots.size = cache.slots.size :=
      CakeNodeMap.slots_size_set _ _ _
    have outside : (unionRow partners cache node).outside = cache.outside := by
      simp only [unionRow, CakeNodeMap.set, bounded, if_true]
    have tail := ih (unionRow partners cache node) (by
      intro next belongs
      rw [size]
      exact bounds next (List.mem_cons_of_mem _ belongs))
    exact ⟨tail.1.trans size, tail.2.trans outside⟩

/-- All executed batch writes stay in the original dense domain when the
original input names do. Admitted-node bounds are derived from the real fold;
neither a bounded output nor unchanged extension map is assumed. -/
theorem extendCliqueBatch_frame (new initial : List Nat) (cache : CakeNodeMap (Std.TreeSet Nat))
    (bounds : ∀ node, node ∈ new ∨ node ∈ initial → node < cache.slots.size) :
    (cakeExtendCliqueSetBatch new initial cache).1.slots.size = cache.slots.size ∧
      (cakeExtendCliqueSetBatch new initial cache).1.outside = cache.outside := by
  let admitted := cliqueBatchAdmissions new initial
  have admittedBounds : ∀ node ∈ admitted.2, node < cache.slots.size := by
    intro node belongs
    have included := List.contains_iff_mem.mpr belongs
    change (cliqueBatchAdmissions new initial).2.contains node = true at included
    rw [cliqueBatchAdmissions_addedContains] at included
    exact bounds node (Or.inl (List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp included).1))
  let first := admitted.2.foldl (unionRow (fun node => admitted.1.erase node)) cache
  have firstFrame := unionRowsFold_frame admitted.2 (fun node => admitted.1.erase node) cache admittedBounds
  have finalFrame := unionRowsFold_frame initial (fun _ => Std.TreeSet.ofList admitted.2) first (by
    intro node belongs
    rw [firstFrame.1]
    exact bounds node (Or.inr belongs))
  rw [batchGraph_eq]
  exact ⟨finalFrame.1.trans firstFrame.1, finalFrame.2.trans firstFrame.2⟩

/-- Full native recursive extendClique success and all-field state transport.
Only the original input-node subscript bounds are used. The production side
here is the recursive list/set reference; executed batching is assembled in
the theorem below. No target evaluation or resulting state is assumed. -/
theorem extendCliqueReference_production (new initial : List Nat)
    {native : State} {production : CakeRaState} (related : ProductionStateRel native production)
    (bounds : ∀ node, node ∈ new ∨ node ∈ initial → node < native.adj_ls.length) :
    ∃ result, extendClique new initial native =
        (.success (cakeExtendClique new initial production.adjLists).2, result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := (cakeExtendClique new initial production.adjLists).1
        adjSets := production.adjSets.map (fun cache => (cakeExtendCliqueSetReference new initial cache).1)} := by
  induction new generalizing native production initial with
  | nil =>
    refine ⟨native, ?_, rfl, ?_⟩
    · simp only [extendClique, cakeExtendClique, Translator.Monadic.MonadBase.ret]
    · have identity : production.adjSets.map (fun cache => cache) = production.adjSets := by
        cases production.adjSets <;> rfl
      simpa only [cakeExtendClique, cakeExtendCliqueSetReference, identity] using related
  | cons node rest ih =>
    by_cases inInitial : node ∈ initial
    · have present : initial.contains node = true := List.contains_iff_mem.mpr inInitial
      obtain ⟨result, run, length, rel⟩ := ih initial related (by
        intro next belongs
        exact bounds next (belongs.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr))
      refine ⟨result, ?_, length, ?_⟩
      · simpa only [extendClique, if_pos inInitial, cakeExtendClique, present, ↓reduceIte] using run
      · simpa only [cakeExtendClique, cakeExtendCliqueSetReference, present, ↓reduceIte] using rel
    · have absent : initial.contains node = false := by
        apply Bool.eq_false_iff.mpr
        intro present
        exact inInitial (List.contains_iff_mem.mp present)
      obtain ⟨first, firstRun, firstLength, firstRel⟩ := listInsertEdge_production node initial related
        (bounds node (Or.inl List.mem_cons_self)) (fun partner belongs => bounds partner (Or.inr belongs))
      obtain ⟨result, run, length, rel⟩ := ih (node :: initial) firstRel (by
        intro next belongs
        rw [firstLength]
        rcases belongs with belongs | belongs
        · exact bounds next (Or.inl (List.mem_cons_of_mem _ belongs))
        · rcases List.mem_cons.mp belongs with rfl | belongs
          · exact bounds _ (Or.inl List.mem_cons_self)
          · exact bounds next (Or.inr belongs))
      refine ⟨result, ?_, length.trans firstLength, ?_⟩
      · simp only [extendClique, if_neg inInitial, Translator.Monadic.MonadBase.ignoreBind,
          firstRun, run, cakeExtendClique, absent, Bool.false_eq_true, if_false]
      · simpa only [cakeExtendClique, cakeExtendCliqueSetReference, absent, Bool.false_eq_true,
          if_false, Option.map_map, Function.comp_def] using rel

/-- Complete executed batch/native extendClique correspondence, including
the actual live list, ordered adjacency rows, all other native state fields,
the production cache and failure latch. The incoming carrier relation and
original input-node bounds derive the batch's row-domain and frame facts;
no successful target evaluation or desired graph is a premise. This is
untagged actual/native infrastructure, not a different HOL theorem port. -/
theorem extendCliqueBatch_production (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native {production with
      adjLists := cache.mapValues cakeAdjSetList, adjSets := some cache})
    (bounds : ∀ node, node ∈ new ∨ node ∈ initial → node < native.adj_ls.length) :
    ∃ result, extendClique new initial native =
        (.success (cakeExtendCliqueSetBatch new initial cache).2, result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := (cakeExtendCliqueSetBatch new initial cache).1.mapValues cakeAdjSetList
        adjSets := some (cakeExtendCliqueSetBatch new initial cache).1} := by
  have present : ∀ node, node ∈ new ∨ node ∈ initial → (cache.get node).isSome = true := by
    intro node belongs
    have read := related.adjacency_read node (bounds node belongs)
    change (cache.mapValues cakeAdjSetList).get node = _ at read
    rw [CakeNodeMap.get_mapValues] at read
    cases found : cache.get node <;> simp_all
  have dimension : cache.slots.size = native.adj_ls.length := by
    simpa only [CakeNodeMap.mapValues, Array.size_map] using related.adjacency.2.1
  have frame := extendCliqueBatch_frame new initial cache (by
    intro node belongs
    rw [dimension]
    exact bounds node belongs)
  have materialized := extendCliqueBatch_materialize new initial cache present
  obtain ⟨result, run, length, rel⟩ := extendCliqueReference_production new initial related bounds
  change extendClique new initial native =
    (.success (cakeExtendClique new initial (cache.mapValues cakeAdjSetList)).2, result) at run
  rw [← materialized.1] at run
  refine ⟨result, run, length, {rel with adjacency := ?_, adjacencyCache := ?_}⟩
  · refine ⟨?_, ?_, ?_⟩
    · change (cakeExtendCliqueSetBatch new initial cache).1.outside.map
        (fun entry => (entry.1, cakeAdjSetList entry.2)) = []
      rw [frame.2]
      exact related.adjacency.1
    · change ((cakeExtendCliqueSetBatch new initial cache).1.slots.map
        (fun entry => entry.map cakeAdjSetList)).size = result.adj_ls.length
      rw [Array.size_map, frame.1, dimension, length]
    · intro node bounded
      rw [materialized.2 node]
      exact rel.adjacency.2.2 node bounded
  · change ∀ node neighbour,
      ((cakeExtendCliqueSetBatch new initial cache).1.get node).map
        (fun set => set.contains neighbour) =
      (((cakeExtendCliqueSetBatch new initial cache).1.mapValues cakeAdjSetList).get node).map
        (fun row => decide (neighbour ∈ row))
    exact productionAdjacencyMap_membership _

/-- The actual graph builder's public extend-clique caller executes the
proved batch. Complete native success and state transport therefore applies
to its real route, without a proof-only replacement or output premise.
This is untagged cross-implementation infrastructure. -/
theorem extendCliqueSet_production (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native {production with
      adjLists := cache.mapValues cakeAdjSetList, adjSets := some cache})
    (bounds : ∀ node, node ∈ new ∨ node ∈ initial → node < native.adj_ls.length) :
    ∃ result, extendClique new initial native =
        (.success (cakeExtendCliqueSet new initial cache).2, result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := (cakeExtendCliqueSet new initial cache).1.mapValues cakeAdjSetList
        adjSets := some (cakeExtendCliqueSet new initial cache).1} := by
  simpa only [cakeExtendCliqueSet, cakeExtendCliqueSetFast] using
    extendCliqueBatch_production new initial cache related bounds

/-- Actual fast clique insertion observations on its genuine duplicate-free
input domain. This is untagged production infrastructure: the native HOL
operation inserts pairs recursively rather than executing this union fold.
Present input rows are required; no output graph is assumed. -/
theorem cliqueInsertEdgeFast_membership (live : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (distinct : live.Nodup)
    (present : ∀ node ∈ live, (cache.get node).isSome = true)
    (key member : Nat) :
    ((cakeCliqueInsertEdgeSetFast live cache).get key).map
      (fun row => row.contains member) =
      (cache.get key).map (fun row => row.contains member ||
        (live.contains key && live.contains member && !(key == member))) := by
  have folded := unionRowsFold_membership live
    (fun node => (Std.TreeSet.ofList live).erase node) cache key member
  have graph : cakeCliqueInsertEdgeSetFast live cache =
      live.foldl (unionRow (fun node => (Std.TreeSet.ofList live).erase node)) cache := by
    unfold cakeCliqueInsertEdgeSetFast unionRow
    simp only [distinct, dif_pos]
  rw [graph]
  rw [folded]
  simp only [Std.TreeSet.contains_erase, Std.TreeSet.contains_ofList]
  cases old : cache.get key with
  | none =>
    have absent : key ∉ live := by
      intro belongs
      have available := present key belongs
      simp [old] at available
    simp [absent]
  | some row =>
    by_cases same : key = member
    · subst member; cases live.contains key <;> simp
    · cases live.contains key <;> cases live.contains member
      all_goals simp [same, bne, Bool.beq_eq_decide_eq,
        Std.LawfulEqCmp.compare_eq_iff_eq]

/-- Complete native recursive clique insertion correspondence on original
input bounds, including the optional actual set cache and failure latch.
Untagged production infrastructure; native cliqueInsertEdge already carries
its reviewed HOL definition tag. Duplicate inputs follow the same recursion. -/
theorem cliqueInsertEdgeReference_production (live : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production)
    (bounds : ∀ node ∈ live, node < native.adj_ls.length) :
    ∃ result, cliqueInsertEdge live native = (.success (), result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := cakeCliqueInsertEdge live production.adjLists
        adjSets := production.adjSets.map (cakeCliqueInsertEdgeSet live)} := by
  induction live generalizing native production with
  | nil =>
    refine ⟨native, ?_, rfl, ?_⟩
    · rfl
    · have identity : production.adjSets.map (fun cache => cache) = production.adjSets := by
        cases production.adjSets <;> rfl
      simpa only [cakeCliqueInsertEdge, cakeCliqueInsertEdgeSet, identity] using related
  | cons node rest ih =>
    obtain ⟨first, firstRun, firstLength, firstRel⟩ := listInsertEdge_production node rest related
      (bounds node List.mem_cons_self)
      (fun partner belongs => bounds partner (List.mem_cons_of_mem _ belongs))
    obtain ⟨result, run, length, rel⟩ := ih firstRel (by
      intro next belongs
      rw [firstLength]
      exact bounds next (List.mem_cons_of_mem _ belongs))
    refine ⟨result, ?_, length.trans firstLength, ?_⟩
    · simp only [cliqueInsertEdge, Translator.Monadic.MonadBase.ignoreBind, firstRun, run]
    · simpa only [cakeCliqueInsertEdge, cakeCliqueInsertEdgeSet,
        Option.map_map, Function.comp_def] using rel

private theorem cliqueEdge_cons (node : Nat) (rest : List Nat)
    (fresh : node ∉ rest) (key member : Nat) :
    ((node :: rest).contains key && (node :: rest).contains member && !(key == member)) =
      (((key == node && rest.contains member) || (member == node && rest.contains key)) ||
        (rest.contains key && rest.contains member && !(key == member))) := by
  by_cases atKey : key = node
  · subst key
    by_cases atMember : member = node
    · subst member; simp [fresh]
    · simp [fresh, atMember, Ne.symm atMember]
  · by_cases atMember : member = node
    · subst member; simp [fresh, atKey]
    · simp [atKey, atMember]

/-- Recursive cache insertion has the same complete incoming-row observation
as the fast union fold on duplicate-free inputs. Present rows are an input
domain fact; they are propagated through the actual edge writes. -/
theorem cliqueInsertEdgeSet_membership (live : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (distinct : live.Nodup)
    (present : ∀ node ∈ live, (cache.get node).isSome = true)
    (key member : Nat) :
    ((cakeCliqueInsertEdgeSet live cache).get key).map (fun row => row.contains member) =
      (cache.get key).map (fun row => row.contains member ||
        (live.contains key && live.contains member && !(key == member))) := by
  induction live generalizing cache with
  | nil => simp [cakeCliqueInsertEdgeSet]
  | cons node rest ih =>
    have nodePresent := present node List.mem_cons_self
    have restPresent : ∀ next ∈ rest, (cache.get next).isSome = true :=
      fun next belongs => present next (List.mem_cons_of_mem _ belongs)
    have still : ∀ next ∈ rest,
        ((cakeListInsertEdgeSet node rest cache).get next).isSome = true := by
      intro next belongs
      exact listInsertEdgeSet_present rest cache node next (restPresent next belongs)
    rw [cakeCliqueInsertEdgeSet, ih _ distinct.of_cons still]
    have step := listInsertEdgeSet_membership rest cache node key member nodePresent restPresent
    have carried := congrArg (Option.map (fun bit => bit ||
      (rest.contains key && rest.contains member && !(key == member)))) step
    simp only [Option.map_map, Function.comp_def] at carried
    rw [carried, cliqueEdge_cons node rest (List.nodup_cons.mp distinct).1]
    congr 1
    funext row
    simp only [Bool.or_assoc]

/-- Complete ordered row equality for the actual fast clique caller.
Duplicate inputs use the literal recursive fallback; distinct inputs use
the independently proved union and recursive membership equations. -/
theorem cliqueInsertEdgeFast_rows_reference (live : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat))
    (present : ∀ node ∈ live, (cache.get node).isSome = true) (key : Nat) :
    ((cakeCliqueInsertEdgeSetFast live cache).mapValues cakeAdjSetList).get key =
      ((cakeCliqueInsertEdgeSet live cache).mapValues cakeAdjSetList).get key := by
  by_cases distinct : live.Nodup
  · have observations (member : Nat) :=
      (cliqueInsertEdgeFast_membership live cache distinct present key member).trans
        (cliqueInsertEdgeSet_membership live cache distinct present key member).symm
    rw [CakeNodeMap.get_mapValues, CakeNodeMap.get_mapValues]
    cases left : (cakeCliqueInsertEdgeSetFast live cache).get key <;>
      cases right : (cakeCliqueInsertEdgeSet live cache).get key
    · rfl
    · have impossible := observations 0; simp [left, right] at impossible
    · have impossible := observations 0; simp [left, right] at impossible
    · rename_i first second
      have same : ∀ member, first.contains member = second.contains member := by
        intro member
        have observed := observations member
        simpa only [left, right, Option.map_some, Option.some.injEq] using observed
      exact congrArg some (congrArg List.reverse
        (Std.TreeSet.Equiv.toList_eq (Std.TreeSet.Equiv.of_forall_contains_eq same)))
  · simp only [cakeCliqueInsertEdgeSetFast, dif_neg distinct]

private theorem cliqueInsertEdgeSet_materialize (live : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeCliqueInsertEdgeSet live cache).mapValues cakeAdjSetList =
      cakeCliqueInsertEdge live (cache.mapValues cakeAdjSetList) := by
  induction live generalizing cache with
  | nil => rfl
  | cons node rest ih =>
    rw [cakeCliqueInsertEdgeSet, ih, listInsertEdgeSet_materialize_eq]
    rfl

/-- Full state transport for the executed fast clique caller, including its
duplicate fallback. Original native input bounds derive every present row;
the output graph, successful result and post-state are proved here.
This is untagged correspondence infrastructure for the actual compiler. -/
theorem cliqueInsertEdgeFast_production (live : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native {production with
      adjLists := cache.mapValues cakeAdjSetList, adjSets := some cache})
    (bounds : ∀ node ∈ live, node < native.adj_ls.length) :
    ∃ result, cliqueInsertEdge live native = (.success (), result) ∧
      result.adj_ls.length = native.adj_ls.length ∧
      ProductionStateRel result {production with
        adjLists := (cakeCliqueInsertEdgeSetFast live cache).mapValues cakeAdjSetList
        adjSets := some (cakeCliqueInsertEdgeSetFast live cache)} := by
  have present : ∀ node ∈ live, (cache.get node).isSome = true := by
    intro node belongs
    have read := related.adjacency_read node (bounds node belongs)
    change (cache.mapValues cakeAdjSetList).get node = _ at read
    rw [CakeNodeMap.get_mapValues] at read
    cases found : cache.get node <;> simp_all
  obtain ⟨result, run, length, rel⟩ := cliqueInsertEdgeReference_production live related bounds
  have materialized := cliqueInsertEdgeSet_materialize live cache
  have rows (key : Nat) := (cliqueInsertEdgeFast_rows_reference live cache present key).trans
    (congrArg (fun graph => graph.get key) materialized)
  by_cases distinct : live.Nodup
  · have dimension : cache.slots.size = native.adj_ls.length := by
      simpa only [CakeNodeMap.mapValues, Array.size_map] using related.adjacency.2.1
    have graph : cakeCliqueInsertEdgeSetFast live cache =
        live.foldl (unionRow (fun node => (Std.TreeSet.ofList live).erase node)) cache := by
      unfold cakeCliqueInsertEdgeSetFast unionRow
      simp only [distinct, dif_pos]
    have frame := unionRowsFold_frame live
      (fun node => (Std.TreeSet.ofList live).erase node) cache (by
        intro node belongs
        rw [dimension]
        exact bounds node belongs)
    rw [← graph] at frame
    refine ⟨result, run, length, {rel with adjacency := ?_, adjacencyCache := ?_}⟩
    · refine ⟨?_, ?_, ?_⟩
      · change (cakeCliqueInsertEdgeSetFast live cache).outside.map
          (fun entry => (entry.1, cakeAdjSetList entry.2)) = []
        rw [frame.2]
        exact related.adjacency.1
      · change ((cakeCliqueInsertEdgeSetFast live cache).slots.map
          (fun entry => entry.map cakeAdjSetList)).size = result.adj_ls.length
        rw [Array.size_map, frame.1, dimension, length]
      · intro node bounded
        rw [rows node]
        exact rel.adjacency.2.2 node bounded
    · exact productionAdjacencyMap_membership _
  · refine ⟨result, run, length, ?_⟩
    have adjusted : ProductionStateRel result {production with
        adjLists := (cakeCliqueInsertEdgeSet live cache).mapValues cakeAdjSetList
        adjSets := some (cakeCliqueInsertEdgeSet live cache)} := by
      simpa only [materialized, Option.map_some] using rel
    simpa only [cakeCliqueInsertEdgeSetFast, dif_neg distinct] using adjusted

end Flapjack.RegAlloc
