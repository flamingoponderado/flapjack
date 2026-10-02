import Flapjack.Compiler.Backend.RegAlloc.ProductionExtraction

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem lookup_first (key : Nat) (entries : NatInfoMap Nat) :
    lookupNatInfo key entries = sptAListLookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨other, value⟩ := entry
    simp only [lookupNatInfo, sptAListLookup, Bool.beq_eq_decide_eq]
    by_cases equal : key = other
    · subst other
      simp
    · simp [equal, Ne.symm equal, ih]

private theorem find_lookup (entries : NatInfoMap Nat) (key : Nat) :
    (entries.find? (fun entry => entry.1 == key)).map Prod.snd = lookupNatInfo key entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.find?_cons, lookupNatInfo]
    split <;> simp_all

/-- Actual indexed reverse decoding agrees with native spDefault on the same
canonical associations, including absent physical and nonphysical names.
This is untagged actual/native infrastructure without a HOL original. -/
theorem tagDecoder_production (entries : NatInfoMap Nat) (key : Nat) :
    cakeSpDefaultIndexed (cakeSpDefaultIndex entries) key =
      Flapjack.spDefault (sptFromAList entries) key := by
  rw [Flapjack.spDefaultIndexed_corresponds]
  unfold CakeAlloc.spDefault Flapjack.spDefault
  rw [sptLookup_sptFromAList, ← lookup_first]
  have lookup := find_lookup entries key
  cases found : entries.find? (fun entry => entry.1 == key) with
  | none =>
    simp [found] at lookup
    rw [← lookup]
    rfl
  | some pair => simp [found] at lookup; rw [← lookup]

private theorem setFold_mem (names : List Nat) (seen : Std.TreeSet Nat) (key : Nat) :
    key ∈ names.foldl (fun seen name => seen.insert name) seen ↔ key ∈ names ∨ key ∈ seen := by
  induction names generalizing seen with
  | nil => simp
  | cons name rest ih =>
    simp only [List.foldl_cons, ih, Std.TreeSet.mem_insert,
      Std.LawfulEqCmp.compare_eq_iff_eq, List.mem_cons]
    simp only [or_assoc, or_left_comm, eq_comm]

private theorem stackLookup (names : List Nat) (key : Nat) :
    sptAListLookup key (names.map (fun name => (name, ()))) =
      if key ∈ names then some () else none := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    by_cases equal : key = name <;> simp [sptAListLookup, ih, equal]

/-- The real stack-only membership accelerator and native canonical unit tree
observe precisely the same input names, including duplicates. No membership
equivalence is supplied as a premise. Untagged carrier correspondence. -/
theorem stackOnlyCodec_production (names : List Nat) (key : Nat) :
    (natSetOfList names).contains key =
      (sptLookup key (sptFromAList (names.map (fun name => (name, ()))))).isSome := by
  rw [sptLookup_sptFromAList, stackLookup]
  have members := setFold_mem names (∅ : Std.TreeSet Nat) key
  by_cases member : key ∈ names
  · have setMember : key ∈ natSetOfList names := by simpa [natSetOfList] using members.mpr (Or.inl member)
    simpa [member] using (Std.TreeSet.contains_iff_mem).mpr setMember
  · have setMissing : key ∉ natSetOfList names := by simpa [natSetOfList, member] using members
    simp only [if_neg member, Option.isSome_none]
    exact Bool.eq_false_iff.mpr (fun h => setMissing (Std.TreeSet.contains_iff_mem.mp h))

private def initializerTag (fs : NumSet) (decode : Nat → Nat) (node : Nat) : Tag :=
  let value := decode node
  if value % 4 = 1 then
    match sptLookup value fs with
    | none => .Atemp
    | some () => .Stemp
  else if value % 4 = 3 then .Stemp else .Fixed (value / 2)

private theorem tagFold_length (nodes : List Nat) (tags : List Tag) (role : Nat → Tag) :
    (nodes.foldl (fun tags node => tags.set node (role node)) tags).length = tags.length := by
  induction nodes generalizing tags with
  | nil => rfl
  | cons node rest ih => simp only [List.foldl_cons, ih, List.length_set]

private theorem tagFold_unchanged (nodes : List Nat) (tags : List Tag)
    (role : Nat → Tag) (node : Nat) (missing : node ∉ nodes) :
    (nodes.foldl (fun tags node => tags.set node (role node)) tags)[node]? = tags[node]? := by
  induction nodes generalizing tags with
  | nil => rfl
  | cons head rest ih =>
    have parts : node ≠ head ∧ node ∉ rest := by simpa using missing
    rw [List.foldl_cons, ih _ parts.2, List.getElem?_set_ne (Ne.symm parts.1)]

private theorem tagFold_member (nodes : List Nat) (tags : List Tag)
    (role : Nat → Tag) (node : Nat) (unique : nodes.Nodup)
    (member : node ∈ nodes) (bound : node < tags.length) :
    (nodes.foldl (fun tags node => tags.set node (role node)) tags)[node]? = some (role node) := by
  induction nodes generalizing tags with
  | nil => simp at member
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    rw [List.foldl_cons]
    rcases List.mem_cons.mp member with equal | member
    · subst node
      rw [tagFold_unchanged _ _ _ _ parts.1, List.getElem?_set_self bound]
    · exact ih _ parts.2 member (by simpa only [List.length_set] using bound)

private theorem foreach_tagWrites (nodes : List Nat) (role : Nat → Tag) (native : State)
    (bounds : ∀ node ∈ nodes, node < native.node_tag.length) :
    stExForeach nodes (fun node => updateNodeTag node (role node)) native =
      (.success (), {native with node_tag := nodes.foldl (fun tags node => tags.set node (role node)) native.node_tag}) := by
  induction nodes generalizing native with
  | nil => rfl
  | cons node rest ih =>
    have bound := bounds node List.mem_cons_self
    have tailBounds : ∀ next ∈ rest,
        next < ({native with node_tag := native.node_tag.set node (role node)} : State).node_tag.length := by
      intro next member
      simpa only [List.length_set] using bounds next (List.mem_cons_of_mem node member)
    simp only [stExForeach, ignoreBind, updateNodeTagEqn, if_pos bound, ih _ tailBounds, List.foldl_cons]

private theorem mkTags_equation (dimension : Nat) (fs : NumSet) (decode : Nat → Nat)
    (native : State) (length : native.node_tag.length = dimension) :
    mkTags dimension fs decode native =
      (.success (), {native with node_tag := ((List.range dimension).foldl
        (fun tags node => tags.set node (initializerTag fs decode node)) native.node_tag)}) := by
  have action : (fun i =>
      if decode i % 4 = 1 then
        match sptLookup (decode i) fs with
        | none => updateNodeTag i .Atemp
        | some () => updateNodeTag i .Stemp
      else if decode i % 4 = 3 then updateNodeTag i .Stemp
      else updateNodeTag i (.Fixed (decode i / 2)) : Nat → M State Unit StateException) =
      (fun i => updateNodeTag i (initializerTag fs decode i)) := by
    funext i
    by_cases first : decode i % 4 = 1
    · cases found : sptLookup (decode i) fs with
      | none => simp [initializerTag, first, found]
      | some payload => cases payload; simp [initializerTag, first, found]
    · by_cases third : decode i % 4 = 3 <;> simp [initializerTag, first, third]
  simp only [mkTags, Translator.Monadic.MonadBase.bind, ret]
  have run := foreach_tagWrites (List.range dimension) (initializerTag fs decode) native
    (fun node member => by rw [length]; exact List.mem_range.mp member)
  rw [← action] at run
  exact run

private theorem mkTags_fold (dimension : Nat) (entries : NatInfoMap Nat) (names : List Nat) :
    cakeMkTags dimension entries names = (List.range dimension).foldl
      (fun tags node => tags.set node ((initializerTag
        (sptFromAList (names.map (fun name => (name, ()))))
        (Flapjack.spDefault (sptFromAList entries)) node).toProduction))
      (CakeNodeMap.ofSize dimension) := by
  have steps : (fun (tags : CakeNodeMap CakeNodeTag) node =>
      let value := cakeSpDefaultIndexed (cakeSpDefaultIndex entries) node
      match value % 4 with
      | 1 => tags.set node (if (natSetOfList names).contains value then .sTemp else .aTemp)
      | 3 => tags.set node .sTemp
      | _ => tags.set node (.fixed (value / 2))) =
      (fun tags node => tags.set node ((initializerTag
        (sptFromAList (names.map (fun name => (name, ()))))
        (Flapjack.spDefault (sptFromAList entries)) node).toProduction)) := by
    funext tags node
    simp only [tagDecoder_production, initializerTag, stackOnlyCodec_production]
    have values : Flapjack.spDefault (sptFromAList entries) node % 4 = 0 ∨
        Flapjack.spDefault (sptFromAList entries) node % 4 = 1 ∨
        Flapjack.spDefault (sptFromAList entries) node % 4 = 2 ∨
        Flapjack.spDefault (sptFromAList entries) node % 4 = 3 := by omega
    rcases values with h | h | h | h <;>
      cases found : sptLookup (Flapjack.spDefault (sptFromAList entries) node)
        (sptFromAList (names.map (fun name => (name, ())))) <;>
      simp [h, Tag.toProduction]
  unfold cakeMkTags
  exact congrArg (fun action => (List.range dimension).foldl action (CakeNodeMap.ofSize dimension)) steps

private theorem arrayFold_frame (nodes : List Nat) (tags : CakeNodeMap CakeNodeTag)
    (role : Nat → CakeNodeTag) (dimension : Nat) (size : tags.slots.size = dimension)
    (outside : tags.outside = []) (bounds : ∀ node ∈ nodes, node < dimension) :
    (nodes.foldl (fun tags node => tags.set node (role node)) tags).slots.size = dimension ∧
    (nodes.foldl (fun tags node => tags.set node (role node)) tags).outside = [] := by
  induction nodes generalizing tags with
  | nil => exact ⟨size, outside⟩
  | cons node rest ih =>
    have bound : node < tags.slots.size := by rw [size]; exact bounds node List.mem_cons_self
    have nextSize : (tags.set node (role node)).slots.size = dimension :=
      (CakeNodeMap.slots_size_set ..).trans size
    have nextOutside : (tags.set node (role node)).outside = [] := by
      simp only [CakeNodeMap.set, if_pos bound, outside]
    exact ih _ nextSize nextOutside (fun next member => bounds next (List.mem_cons_of_mem node member))

private theorem arrayFold_unchanged (nodes : List Nat) (tags : CakeNodeMap CakeNodeTag)
    (role : Nat → CakeNodeTag) (node : Nat) (missing : node ∉ nodes) :
    (nodes.foldl (fun tags node => tags.set node (role node)) tags).get node = tags.get node := by
  induction nodes generalizing tags with
  | nil => rfl
  | cons head rest ih =>
    have parts : node ≠ head ∧ node ∉ rest := by simpa using missing
    rw [List.foldl_cons, ih _ parts.2, CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm parts.1)]

private theorem arrayFold_member (nodes : List Nat) (tags : CakeNodeMap CakeNodeTag)
    (role : Nat → CakeNodeTag) (node : Nat) (unique : nodes.Nodup) (member : node ∈ nodes) :
    (nodes.foldl (fun tags node => tags.set node (role node)) tags).get node = some (role node) := by
  induction nodes generalizing tags with
  | nil => simp at member
  | cons head rest ih =>
    have parts := List.nodup_cons.mp unique
    rw [List.foldl_cons]
    rcases List.mem_cons.mp member with equal | member
    · subst node
      rw [arrayFold_unchanged _ _ _ _ parts.1, CakeNodeMap.get_set_self]
    · exact ih _ parts.2 member

/-- Complete indexed tag initialization corresponds to native mkTags, including
every nonphysical role and stack-only branch. The actual HashMap/TreeSet inputs
are connected to native decoding by checked canonical codecs. All writes and
the complete post-state relation are derived from originalGood; neither a
desired tag map nor role classification is assumed. This is untagged Flapjack
infrastructure, not a duplicate HOL theorem. Original graph and whole bijection
initialization correspondence remain separate work. -/
theorem mkTags_production (entries : NatInfoMap Nat) (names : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native) :
    ∃ result,
      mkTags native.dim (sptFromAList (names.map (fun name => (name, ()))))
        (Flapjack.spDefault (sptFromAList entries)) native = (.success (), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧
      ProductionStateRel result {production with nodeTag := cakeMkTags native.dim entries names} := by
  let role := initializerTag (sptFromAList (names.map (fun name => (name, ()))))
    (Flapjack.spDefault (sptFromAList entries))
  let finalTags := (List.range native.dim).foldl (fun tags node => tags.set node (role node)) native.node_tag
  let result : State := {native with node_tag := finalTags}
  have finalLength : finalTags.length = native.node_tag.length := tagFold_length _ _ _
  have run := mkTags_equation native.dim (sptFromAList (names.map (fun name => (name, ()))))
    (Flapjack.spDefault (sptFromAList entries)) native good.2.1
  have resultGood : goodRaState result := by
    obtain ⟨g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14⟩ := good
    exact ⟨g1, finalLength.trans g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14⟩
  refine ⟨result, run, resultGood, rfl, ?_⟩
  refine {related with tags := ?_}
  change CakeNodeMap.RepresentsHOLNodeList (cakeMkTags native.dim entries names) (finalTags.map Tag.toProduction)
  rw [mkTags_fold]
  have frame := arrayFold_frame (List.range native.dim)
    (CakeNodeMap.ofSize native.dim) (fun node => (role node).toProduction) native.dim
    (by simp [CakeNodeMap.ofSize]) rfl (fun node member => List.mem_range.mp member)
  refine ⟨frame.2, ?_, ?_⟩
  · simpa only [List.length_map, finalLength, good.2.1] using frame.1
  · intro node bound
    have nodeBound : node < native.dim := by
      simpa only [List.length_map, finalLength, good.2.1] using bound
    have member : node ∈ List.range native.dim := List.mem_range.mpr nodeBound
    have originalBound : node < native.node_tag.length := by rwa [good.2.1]
    have finalBound : node < finalTags.length := by rwa [finalLength]
    have read := tagFold_member (List.range native.dim) native.node_tag role node
      List.nodup_range member originalBound
    change finalTags[node]? = some (role node) at read
    simp only [List.getElem?_eq_getElem finalBound, Option.some.injEq] at read
    rw [arrayFold_member _ _ _ _ List.nodup_range member]
    simp only [List.get_eq_getElem, List.getElem_map, read]
    rfl

end Flapjack.RegAlloc
