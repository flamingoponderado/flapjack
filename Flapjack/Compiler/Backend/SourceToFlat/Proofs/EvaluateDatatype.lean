import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateException

/-! Prerequisites for the datatype-declaration case of the preliminary
factored source-to-flat simulation. These helpers do not claim the upstream
allocation invariant or cross-language correspondence. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A reserved type index has neither a type entry nor a constructor entry. -/
theorem idxRangeRel_type_free {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other))
    (fits : start.tidx < finish.tidx) :
    genv.tys.lookup start.tidx = none ∧
      ∀ cn arity, genv.c.lookup ((cn, some start.tidx), arity) = none := by
  obtain ⟨_, _, _, _, tuple, _, _, disjoint, _, _⟩ := range
  cases tuple
  have separate := disjoint 0 3 (by simp) (by simp) (by decide)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at separate
  have block : (start.tidx, IndexKind.type) ∈ idxBlock start finish := by
    change idxBlock start finish (start.tidx, IndexKind.type)
    simp [idxBlock, fits]
  have unallocated : (start.tidx, IndexKind.type) ∉ genvAllocatedIndices genv := by
    intro allocated
    have member : (start.tidx, IndexKind.type) ∈ idxBlock start finish ∩ genvAllocatedIndices genv :=
      ⟨block, allocated⟩
    rw [separate] at member
    exact member.elim
  constructor
  · cases lookup : genv.tys.lookup start.tidx with
    | none => rfl
    | some tags =>
      apply False.elim
      apply unallocated
      right
      simp [lookup]
  · intro cn arity
    cases lookup : genv.c.lookup ((cn, some start.tidx), arity) with
    | none => rfl
    | some stamp =>
      apply False.elim
      apply unallocated
      left
      exact ⟨cn, arity, by simp [lookup]⟩

/-- The next source type stamp is absent from the global constructor map. -/
theorem idxRangeRel_typeStamp_fresh {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other)) :
    ∀ name key, genv.c.lookup key ≠ some (.typeStamp name nextType) := by
  obtain ⟨_, _, _, _, _, _, _, _, fresh, _⟩ := range
  intro name key found
  exact fresh name nextType (Nat.le_refl _) ⟨key, found⟩

/-- Successful datatype validation guarantees that each individual type has
distinct constructor names, the side condition used by tag allocation. -/
theorem checkedTypeDef_constructor_names (types : TypeDef)
    (checked : types.all checkDupCtors = true)
    (parameters : List TvarN) (name : TypeN) (constructors : List (ConN × List AstT))
    (member : (parameters, name, constructors) ∈ types) :
    (constructors.map Prod.fst).Nodup := by
  have valid := (List.all_eq_true.mp checked) _ member
  simpa [checkDupCtors] using valid

/-- Tag allocation records the arity of every constructor in input order. -/
theorem allocTags1_arities {M N A : Type} (constructors : List (N × List A)) :
    ((allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2).map Prod.snd =
      constructors.map (fun constructor => constructor.2.length) := by
  induction constructors with
  | nil => rfl
  | cons constructor rest ih =>
    rcases constructor with ⟨name, args⟩
    generalize eq : (allocTags1 rest : Namespace M N Nat × Spt Nat × List (Nat × Nat)) = result at ih ⊢
    rcases result with ⟨ns, cids, tags⟩
    generalize inc : lookupInc args.length cids = result
    rcases result with ⟨tag, newCids⟩
    simp only [allocTags1, eq, inc, List.map_cons] at ⊢
    exact congrArg (List.cons args.length) ih

/-- The final tag table has the original constructor arities in order. -/
theorem allocTags1_reverse_arities {M N A : Type} (constructors : List (N × List A)) :
    ((allocTags1 constructors.reverse : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2).reverse.map Prod.snd =
      constructors.map (fun constructor => constructor.2.length) := by
  rw [List.map_reverse, allocTags1_arities, List.map_reverse, List.reverse_reverse]

/-- The tag table contains exactly the tags below the counter for each
arity. This is an allocation invariant over the actual executable pass. -/
theorem allocTags1_membership {M N A : Type} (constructors : List (N × List A)) :
    ∀ tag arity,
      (tag, arity) ∈ (allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2 ↔
      ∃ max, sptLookup arity (allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.1 =
        some max ∧ tag < max := by
  induction constructors with
  | nil =>
    intro tag arity
    simp [allocTags1]
  | cons constructor rest ih =>
    rcases constructor with ⟨name, args⟩
    generalize eq : (allocTags1 rest : Namespace M N Nat × Spt Nat × List (Nat × Nat)) = result at ih ⊢
    rcases result with ⟨ns, cids, tags⟩
    intro tag arity
    by_cases same : arity = args.length
    · subst arity
      cases found : sptLookup args.length cids with
      | none =>
        have old := ih tag args.length
        simp only [found] at old
        simp [allocTags1, eq, lookupInc, found, sptLookup_sptInsert_same, old]
      | some count =>
        have old := ih tag args.length
        simp only [found, Option.some.injEq, exists_eq_left'] at old
        simp only [allocTags1, eq, lookupInc, found, sptLookup_sptInsert_same, List.mem_cons,
          Prod.mk.injEq, Option.some.injEq, exists_eq_left', old]
        constructor
        · rintro (⟨same, _⟩ | less) <;> omega
        · intro less
          by_cases same : tag = count
          · exact Or.inl ⟨same, trivial⟩
          · exact Or.inr (by omega)
    · cases found : sptLookup args.length cids with
      | none =>
        have old := ih tag arity
        simp [allocTags1, eq, lookupInc, found, sptLookup_sptInsert_ne _ _ _ _ same, same, old]
      | some count =>
        have old := ih tag arity
        simp [allocTags1, eq, lookupInc, found, sptLookup_sptInsert_ne _ _ _ _ same, same, old]

/-- Distinct allocated tags never collide at the same arity. -/
theorem allocTags1_tags_nodup {M N A : Type} (constructors : List (N × List A)) :
    ((allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2).Nodup := by
  induction constructors with
  | nil => simp [allocTags1]
  | cons constructor rest ih =>
    rcases constructor with ⟨name, args⟩
    have membership := allocTags1_membership (M := M) rest
    generalize eq : (allocTags1 rest : Namespace M N Nat × Spt Nat × List (Nat × Nat)) = result at ih membership ⊢
    rcases result with ⟨ns, cids, tags⟩
    cases found : sptLookup args.length cids with
    | none =>
      have absent : (0, args.length) ∉ tags := by
        have h := membership 0 args.length
        simp [found] at h
        exact h
      simpa [allocTags1, eq, lookupInc, found, absent] using ih
    | some count =>
      have absent : (count, args.length) ∉ tags := by
        have h := membership count args.length
        simp [found] at h
        exact h
      simpa [allocTags1, eq, lookupInc, found, absent] using ih

/-- The allocator's namespace associates each input constructor name with
the tag in the corresponding tag-table position. -/
theorem allocTags1_namespace {M N A : Type} (constructors : List (N × List A)) :
    (allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).1 =
      alistToNs ((constructors.map Prod.fst).zip
        ((allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2.map Prod.fst)) := by
  induction constructors with
  | nil => rfl
  | cons constructor rest ih =>
    rcases constructor with ⟨name, args⟩
    generalize eq : (allocTags1 rest : Namespace M N Nat × Spt Nat × List (Nat × Nat)) = result at ih ⊢
    rcases result with ⟨ns, cids, tags⟩
    generalize inc : lookupInc args.length cids = result
    rcases result with ⟨tag, newCids⟩
    simp only [allocTags1, eq, inc, List.map_cons, List.zip_cons_cons] at ⊢
    change ns = alistToNs ((rest.map Prod.fst).zip (tags.map Prod.fst)) at ih
    rw [ih]
    rfl

/-- Pair source constructor names with the tag table emitted by the actual
allocator, preserving their source order. -/
def allocatedConstructorEntries {M N A : Type} (constructors : List (N × List A)) : List (N × Nat × Nat) :=
  ((constructors.map Prod.fst).zip
    ((allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2)).map
      fun (name, tag, arity) => (name, tag, arity)

/-- The allocator emits one tag per source constructor. -/
theorem allocTags1_length {M N A : Type} (constructors : List (N × List A)) :
    ((allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2).length =
      constructors.length := by
  have h := congrArg List.length (allocTags1_arities (M := M) constructors)
  simpa using h

/-- Projections of the zipped allocation entries are exactly the source
names and the allocator's tag table. -/
theorem allocatedConstructorEntries_projections {M N A : Type} (constructors : List (N × List A)) :
    (allocatedConstructorEntries (M := M) constructors).map Prod.fst = constructors.map Prod.fst ∧
    (allocatedConstructorEntries (M := M) constructors).map Prod.snd =
      (allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2 := by
  have lengths : (constructors.map Prod.fst).length =
      ((allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2).length := by
    simp [allocTags1_length]
  constructor
  · simp only [allocatedConstructorEntries, List.map_map]
    change (((constructors.map Prod.fst).zip
      ((allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2)).map
        (fun pair => pair.1)) = _
    exact List.map_fst_zip (Nat.le_of_eq lengths)
  · simp only [allocatedConstructorEntries, List.map_map]
    change (((constructors.map Prod.fst).zip
      ((allocTags1 constructors : Namespace M N Nat × Spt Nat × List (Nat × Nat)).2.2)).map
        (fun pair => pair.2)) = _
    exact List.map_snd_zip (Nat.le_of_eq lengths.symm)

/-- Distinct source constructor names and the allocator's fresh tags give
both distinctness conditions required by the list-level invariant. -/
theorem allocatedConstructorEntries_nodup {M N A : Type} (constructors : List (N × List A))
    (names : (constructors.map Prod.fst).Nodup) :
    ((allocatedConstructorEntries (M := M) constructors).map Prod.fst).Nodup ∧
      ((allocatedConstructorEntries (M := M) constructors).map Prod.snd).Nodup := by
  rw [(allocatedConstructorEntries_projections (M := M) constructors).1,
    (allocatedConstructorEntries_projections (M := M) constructors).2]
  exact ⟨names, allocTags1_tags_nodup (M := M) constructors⟩

private theorem zipConstructor_member_arity {N A : Type} (constructors : List (N × List A))
    (tags : List (Nat × Nat)) (arities : tags.map Prod.snd = constructors.map (fun c => c.2.length)) :
    ∀ name tag arity, (name, tag, arity) ∈ ((constructors.map Prod.fst).zip tags).map
      (fun (name, tag, arity) => (name, tag, arity)) →
      ∃ args, (name, args) ∈ constructors ∧ args.length = arity := by
  induction constructors generalizing tags with
  | nil =>
    intro name tag arity member
    simp at member
  | cons constructor rest ih =>
    rcases constructor with ⟨headName, headArgs⟩
    cases tags with
    | nil => simp at arities
    | cons headTag restTags =>
      rcases headTag with ⟨headTag, headArity⟩
      have arities' : headArity = headArgs.length ∧
          restTags.map Prod.snd = rest.map (fun c => c.2.length) := by simpa using arities
      intro name tag arity member
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at member
      rcases member with same | member
      · have fields : name = headName ∧ tag = headTag ∧ arity = headArity := by simpa [and_assoc] using same
        obtain ⟨rfl, rfl, rfl⟩ := fields
        exact ⟨headArgs, by simp, arities'.1.symm⟩
      · obtain ⟨args, found, length⟩ := ih restTags arities'.2 name tag arity member
        exact ⟨args, List.mem_cons_of_mem _ found, length⟩

/-- Every allocator entry refers to a source constructor with the same
name and arity. -/
theorem allocatedConstructorEntries_source {M N A : Type} (constructors : List (N × List A))
    (name : N) (tag arity : Nat) (member : (name, tag, arity) ∈ allocatedConstructorEntries (M := M) constructors) :
    ∃ args, (name, args) ∈ constructors ∧ args.length = arity := by
  exact zipConstructor_member_arity constructors _ (allocTags1_arities (M := M) constructors) name tag arity member

private theorem constructorLookup_exists_iff_key_mem {α : Type} (entries : List (ConN × α)) (name : ConN) :
    (∃ value, entries.lookup name = some value) ↔ name ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    by_cases equal : name = key
    · subst key
      simp
    · simp [List.lookup_cons, BEq.beq, equal, ih]

/-- Allocating tags for a type and building its source constructors export
the same constructor and module domains. -/
theorem envDomainEq_allocTags (idx stamp : Nat) (constructors : List (ConN × List AstT)) :
    EnvDomainEq { v := nsEmpty, c := (allocTags idx constructors :
      Namespace ModN ConN (Nat × Option (Nat × List (Nat × Nat))) × Spt Nat).1 }
      ({ v := nsEmpty, c := alistToNs (buildConstrs stamp constructors).reverse } : SemEnv Value) := by
  have namespaceEq := allocTags1_namespace (M := ModN) constructors.reverse
  have lengthEq := allocTags1_length (M := ModN) constructors.reverse
  generalize eq : (allocTags1 constructors.reverse : Namespace ModN ConN Nat × Spt Nat × List (Nat × Nat)) = result
    at namespaceEq lengthEq ⊢
  rcases result with ⟨ns, cids, tags⟩
  change ns = alistToNs ((constructors.reverse.map Prod.fst).zip (tags.map Prod.fst)) at namespaceEq
  change tags.length = constructors.reverse.length at lengthEq
  have keys : (((constructors.reverse.map Prod.fst).zip (tags.map Prod.fst)).map Prod.fst) =
      constructors.reverse.map Prod.fst := by
    apply List.map_fst_zip
    simp [lengthEq]
  simp only [allocTags, eq, namespaceEq, nsMap, alistToNs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext id
    apply propext
    cases id <;> simp [nsDom, nsLookup, nsEmpty]
  · funext path
    apply propext
    cases path <;> simp [nsDomMod, nsLookupMod, nsEmpty]
  · funext id
    apply propext
    cases id with
    | short name =>
      simp only [nsDom, nsLookup]
      rw [constructorLookup_exists_iff_key_mem, constructorLookup_exists_iff_key_mem]
      simp only [List.map_map, Function.comp_def, List.map_reverse, buildConstrs]
      simpa only [List.map_map, Function.comp_def, List.map_reverse] using
        Iff.of_eq (congrArg (fun xs => name ∈ xs) keys)
    | long moduleName rest => simp [nsDom, nsLookup]
  · funext path
    apply propext
    cases path <;> simp [nsDomMod, nsLookupMod]

/-- Recording a type's tag table allocates exactly that type index. -/
theorem allocatedIndices_installTypeTable (genv : GlobalEnv) (idx : Nat) (tags : List (Nat × Nat)) :
    genvAllocatedIndices { genv with tys := finiteUpdate genv.tys idx tags } =
      genvAllocatedIndices genv ∪ {(idx, .type)} := by
  classical
  ext ⟨i, kind⟩
  cases kind with
  | «variable» =>
    change (i < genv.v.length ∧ genv.v[i]?.getD none ≠ none) ↔
      (i < genv.v.length ∧ genv.v[i]?.getD none ≠ none) ∨ (i, IndexKind.variable) = (idx, .type)
    simp
  | «type» =>
    change ((∃ cn a, (genv.c.lookup ((cn, some i), a)).isSome) ∨
      ((finiteUpdate genv.tys idx tags).lookup i).isSome) ↔
      ((∃ cn a, (genv.c.lookup ((cn, some i), a)).isSome) ∨ (genv.tys.lookup i).isSome) ∨
        (i, IndexKind.type) = (idx, .type)
    by_cases same : i = idx
    · subst i
      simp [finiteUpdate, FUPDATE_HOL]
    · simp [finiteUpdate, FUPDATE_HOL, same]
  | «exception» =>
    change (∃ a, (genv.c.lookup ((i, none), a)).isSome) ↔
      (∃ a, (genv.c.lookup ((i, none), a)).isSome) ∨ (i, IndexKind.exception) = (idx, .type)
    simp

/-- Recording a typed constructor allocates exactly its type index. -/
theorem allocatedIndices_installTypeConstructor (genv : GlobalEnv)
    (idx tag arity : Nat) (name : ConN) (stamp : Nat) :
    genvAllocatedIndices
      { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) } =
      genvAllocatedIndices genv ∪ {(idx, .type)} := by
  classical
  ext ⟨i, kind⟩
  cases kind with
  | «variable» =>
    change (i < genv.v.length ∧ genv.v[i]?.getD none ≠ none) ↔
      (i < genv.v.length ∧ genv.v[i]?.getD none ≠ none) ∨ (i, IndexKind.variable) = (idx, .type)
    simp
  | «type» =>
    change ((∃ cn a, ((finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp)).lookup
      ((cn, some i), a)).isSome) ∨ (genv.tys.lookup i).isSome) ↔
      ((∃ cn a, (genv.c.lookup ((cn, some i), a)).isSome) ∨ (genv.tys.lookup i).isSome) ∨
        (i, IndexKind.type) = (idx, .type)
    by_cases same : i = idx
    · subst i
      constructor
      · intro _
        exact Or.inr rfl
      · intro _
        exact Or.inl ⟨tag, arity, by simp [finiteUpdate, FUPDATE_HOL]⟩
    · simp [finiteUpdate, FUPDATE_HOL, same]
  | «exception» =>
    change (∃ a, ((finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp)).lookup
      ((i, none), a)).isSome) ↔
      (∃ a, (genv.c.lookup ((i, none), a)).isSome) ∨ (i, IndexKind.exception) = (idx, .type)
    simp [finiteUpdate, FUPDATE_HOL]

/-- Installing a fresh type table preserves all previously recorded globals. -/
theorem GlobalGrowth.installTypeTable (genv : GlobalEnv) (idx : Nat) (tags : List (Nat × Nat))
    (fresh : genv.tys.lookup idx = none) :
    GlobalGrowth genv { genv with tys := finiteUpdate genv.tys idx tags } := by
  classical
  refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
  · intro _ _ lookup
    exact lookup
  · intro _ _ lookup
    exact lookup
  · intro key value lookup
    have different : key ≠ idx := by
      intro eq
      subst key
      rw [fresh] at lookup
      contradiction
    simpa [finiteUpdate, FUPDATE_HOL, different] using lookup

/-- A fresh type table cannot invalidate any existing typed constructor. -/
theorem genvCTysOk_installTypeTable (genv : GlobalEnv) (idx : Nat) (tags : List (Nat × Nat))
    (valid : genvCTysOk genv.c genv.tys) (fresh : genv.tys.lookup idx = none) :
    genvCTysOk genv.c (finiteUpdate genv.tys idx tags) := by
  intro cn tyId arity present
  obtain ⟨ctors, lookup, member⟩ := valid cn tyId arity present
  exact ⟨ctors, (GlobalGrowth.installTypeTable genv idx tags fresh).types tyId ctors lookup, member⟩

/-- A constructor can be installed once its key is listed in the type table. -/
theorem genvCTysOk_installTypeConstructor (genv : GlobalEnv) (idx tag arity : Nat)
    (name : ConN) (stamp : Nat) (tags : List (Nat × Nat))
    (valid : genvCTysOk genv.c genv.tys) (table : genv.tys.lookup idx = some tags)
    (member : (tag, arity) ∈ tags) :
    genvCTysOk (finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp)) genv.tys := by
  classical
  intro cn tyId a present
  by_cases same : ((cn, some tyId), a) = ((tag, some idx), arity)
  · have fields : cn = tag ∧ tyId = idx ∧ a = arity := by simpa [and_assoc] using same
    obtain ⟨rfl, rfl, rfl⟩ := fields
    exact ⟨tags, table, member⟩
  · apply valid cn tyId a
    simpa [finiteUpdate, FUPDATE_HOL, same] using present

/-- A fresh constructor key and stamp preserve constructor-map validity
when the new constructor has the same type relation to every old entry as
its flat key. This is a single-entry building block for tag allocation. -/
theorem genvCOk_installConstructor (genv : GlobalEnv) (cn : FlatLang.CtorId × FlatLang.TypeId)
    (arity : Nat) (stamp : Stamp) (valid : genvCOk genv.c)
    (free : genv.c.lookup (cn, arity) = none)
    (fresh : ∀ key, genv.c.lookup key ≠ some stamp)
    (compatible : ∀ cn' arity' stamp', genv.c.lookup (cn', arity') = some stamp' →
      (SemanticPrimitivesHOL.ctorSameType (some stamp) (some stamp') = true ↔
        FlatSem.ctorSameType (some cn) (some cn'))) :
    genvCOk (finiteUpdate genv.c (cn, arity) stamp) := by
  classical
  let updated := finiteUpdate genv.c (cn, arity) stamp
  have oldLookup {key value} (h : genv.c.lookup key = some value) : updated.lookup key = some value := by
    have different : key ≠ (cn, arity) := by
      intro eq
      subst key
      rw [free] at h
      contradiction
    simpa [updated, finiteUpdate, FUPDATE_HOL, different] using h
  have classify (key : ConstructorKey) (s : Stamp) (h : updated.lookup key = some s) :
      (key = (cn, arity) ∧ s = stamp) ∨ genv.c.lookup key = some s := by
    by_cases same : key = (cn, arity)
    · left
      refine ⟨same, ?_⟩
      simp [updated, finiteUpdate, FUPDATE_HOL, same] at h
      exact h.symm
    · right
      simpa [updated, finiteUpdate, FUPDATE_HOL, same] using h
  refine ⟨⟨oldLookup valid.1.1, oldLookup valid.1.2⟩,
    ⟨oldLookup valid.2.1.1, oldLookup valid.2.1.2.1, oldLookup valid.2.1.2.2.1, oldLookup valid.2.1.2.2.2⟩,
    ⟨oldLookup valid.2.2.1.1, oldLookup valid.2.2.1.2⟩, ?_, ?_⟩
  · intro cn1 cn2 a1 a2 s1 s2 h1 h2
    rcases classify (cn1, a1) s1 h1 with ⟨eq1, rfl⟩ | old1 <;>
      rcases classify (cn2, a2) s2 h2 with ⟨eq2, rfl⟩ | old2
    · have cnEq1 : cn1 = cn := congrArg Prod.fst eq1
      have cnEq2 : cn2 = cn := congrArg Prod.fst eq2
      subst cn1
      subst cn2
      cases s2 <;> cases cn <;>
        simp [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType, FlatSem.ctorSameType]
    · have cnEq : cn1 = cn := congrArg Prod.fst eq1
      subst cn1
      exact compatible cn2 a2 s2 old2
    · have cnEq : cn2 = cn := congrArg Prod.fst eq2
      subst cn2
      have h := compatible cn1 a1 s1 old1
      cases s2 <;> cases s1 <;> cases cn <;> cases cn1 <;>
        simpa only [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType,
          FlatSem.ctorSameType, Bool.beq_comm, eq_comm] using h
    · exact valid.2.2.2.1 cn1 cn2 a1 a2 s1 s2 old1 old2
  · intro cn1 cn2 a1 a2 s h1 h2
    rcases classify (cn1, a1) s h1 with ⟨eq1, eqStamp1⟩ | old1 <;>
      rcases classify (cn2, a2) s h2 with ⟨eq2, eqStamp2⟩ | old2
    · have eq := eq1.trans eq2.symm
      exact Prod.mk.inj eq
    · subst s
      exact False.elim (fresh (cn2, a2) old2)
    · subst s
      exact False.elim (fresh (cn1, a1) old1)
    · exact valid.2.2.2.2 cn1 cn2 a1 a2 s old1 old2

/-- The first constructor of a newly reserved type is compatible with all
existing entries when both its type index and source stamp are fresh. -/
theorem genvCOk_installFreshTypeConstructor (genv : GlobalEnv) (idx tag arity : Nat)
    (name : ConN) (stamp : Nat) (valid : genvCOk genv.c)
    (free : ∀ tag' arity', genv.c.lookup ((tag', some idx), arity') = none)
    (fresh : ∀ name' key, genv.c.lookup key ≠ some (.typeStamp name' stamp)) :
    genvCOk (finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp)) := by
  apply genvCOk_installConstructor genv (tag, some idx) arity (.typeStamp name stamp) valid
    (free tag arity) (fresh name)
  intro cn' arity' stamp' lookup
  have otherIndex : cn'.2 ≠ some idx := by
    intro same
    cases cn' with
    | mk tag' typ =>
      change typ = some idx at same
      subst typ
      rw [free tag' arity'] at lookup
      contradiction
  cases stamp' with
  | exnStamp n =>
    simp [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType,
      FlatSem.ctorSameType, Ne.symm otherIndex]
  | typeStamp name' n =>
    have otherStamp : n ≠ stamp := by
      intro same
      subst n
      exact fresh name' (cn', arity') lookup
    simp [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType,
      FlatSem.ctorSameType, Ne.symm otherIndex, Ne.symm otherStamp]

/-- Once one constructor of a type has been installed, its compatibility
establishes the type relation for any additional constructor of that type. -/
theorem genvCOk_sameType_compatible (genv : GlobalEnv) (idx tag anchorTag anchorArity : Nat)
    (name anchorName : ConN) (stamp : Nat) (valid : genvCOk genv.c)
    (anchor : genv.c.lookup ((anchorTag, some idx), anchorArity) = some (.typeStamp anchorName stamp)) :
    ∀ cn' arity' stamp', genv.c.lookup (cn', arity') = some stamp' →
      (SemanticPrimitivesHOL.ctorSameType (some (.typeStamp name stamp)) (some stamp') = true ↔
        FlatSem.ctorSameType (some (tag, some idx)) (some cn')) := by
  intro cn' arity' stamp' lookup
  have existing := valid.2.2.2.1 (anchorTag, some idx) cn' anchorArity arity'
    (.typeStamp anchorName stamp) stamp' anchor lookup
  cases stamp' <;> simpa only [SemanticPrimitivesHOL.ctorSameType, SemanticPrimitivesHOL.sameType,
    FlatSem.ctorSameType] using existing

/-- Adding a constructor at an unused key preserves existing globals. -/
theorem GlobalGrowth.installTypeConstructor (genv : GlobalEnv) (idx tag arity : Nat)
    (name : ConN) (stamp : Nat) (free : genv.c.lookup ((tag, some idx), arity) = none) :
    GlobalGrowth genv
      { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) } := by
  classical
  refine ⟨Nat.le_refl _, ?_, ?_, fun _ _ lookup => lookup⟩
  · intro _ _ lookup
    exact lookup
  · intro key value lookup
    have different : key ≠ ((tag, some idx), arity) := by
      intro same
      subst key
      rw [free] at lookup
      contradiction
    simpa [finiteUpdate, FUPDATE_HOL, different] using lookup

/-- A constructor belonging to an already allocated type leaves the
reserved-index partition and future stamp freshness intact. -/
theorem idxRangeRel_installTypeConstructor {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (idx tag arity : Nat) (name : ConN) (stamp : Nat) (tags : List (Nat × Nat))
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other))
    (table : genv.tys.lookup idx = some tags) (older : stamp < nextType) :
    idxRangeRel interp
      { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) }
      nextType nextExn evalState (start, finish, other) := by
  classical
  obtain ⟨_, _, final, _, tuple, nextMatch, previous, disjoint, types, exceptions⟩ := range
  cases tuple
  refine ⟨_, _, final, other, rfl, nextMatch, previous, ?_, ?_, ?_⟩
  · have allocated : (idx, IndexKind.type) ∈ genvAllocatedIndices genv := by
      right
      simp [table]
    have unchanged : genvAllocatedIndices genv ∪ {(idx, IndexKind.type)} = genvAllocatedIndices genv := by
      ext item
      change (item ∈ genvAllocatedIndices genv ∨ item = (idx, IndexKind.type)) ↔
        item ∈ genvAllocatedIndices genv
      constructor
      · rintro (present | rfl)
        · exact present
        · exact allocated
      · exact Or.inl
    rw [allocatedIndices_installTypeConstructor, unchanged]
    exact disjoint
  · intro name' stamp' bound ⟨key, found⟩
    by_cases same : key = ((tag, some idx), arity)
    · subst key
      simp [finiteUpdate, FUPDATE_HOL] at found
      omega
    · have original : genv.c.lookup key = some (.typeStamp name' stamp') := by
        simpa [finiteUpdate, FUPDATE_HOL, same] using found
      exact types name' stamp' bound ⟨key, original⟩
  · intro exn bound ⟨key, found⟩
    by_cases same : key = ((tag, some idx), arity)
    · subst key
      simp [finiteUpdate, FUPDATE_HOL] at found
    · have original : genv.c.lookup key = some (.exnStamp exn) := by
        simpa [finiteUpdate, FUPDATE_HOL, same] using found
      exact exceptions exn bound ⟨key, original⟩

/-- Installing the type table consumes one reserved index; no source type
stamp has yet been added to the constructor map. -/
theorem idxRangeRel_installTypeTable {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind)) (tags : List (Nat × Nat))
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other))
    (fits : start.tidx + 1 ≤ finish.tidx) :
    idxRangeRel interp { genv with tys := finiteUpdate genv.tys start.tidx tags }
      (nextType + 1) nextExn evalState ({ start with tidx := start.tidx + 1 }, finish, other) := by
  obtain ⟨_, _, final, _, tuple, nextMatch, previous, disjoint, types, exceptions⟩ := range
  cases tuple
  refine ⟨_, _, final, other, rfl, nextMatch, previous, ?_, ?_, exceptions⟩
  · rw [allocatedIndices_installTypeTable]
    apply allDisjoint_consume (idxBlock start finish)
      (idxBlock { start with tidx := start.tidx + 1 } finish) (idxFinalBlock final)
      other (genvAllocatedIndices genv) (start.tidx, .type) disjoint
    · intro ⟨i, kind⟩ member
      change idxBlock { start with tidx := start.tidx + 1 } finish (i, kind) at member
      change idxBlock start finish (i, kind)
      cases kind <;> simp only [idxBlock] at member ⊢ <;> omega
    · change idxBlock start finish (start.tidx, .type)
      simp only [idxBlock]
      omega
    · change ¬ idxBlock { start with tidx := start.tidx + 1 } finish (start.tidx, .type)
      simp only [idxBlock]
      omega
  · intro name stamp bound found
    exact types name stamp (by omega) found

/-- Reserving a type table preserves the preliminary factored invariant and
advances both type counters. Constructor entries may then be installed in the
reserved table; their compatibility remains a separate obligation. -/
theorem factoredInvariant_installTypeTable {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (tags : List (Nat × Nat))
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (fits : start.tidx + 1 ≤ finish.tidx) :
    factoredInvariant interp transform gen
      { genv with tys := finiteUpdate genv.tys start.tidx tags }
      ({ start with tidx := start.tidx + 1 }, finish, other)
      { source with nextTypeStamp := source.nextTypeStamp + 1 } flat := by
  obtain ⟨cOk, typesOk, states, range, invs, oracle, globals, reserved, genInv, fin⟩ := valid
  have free := (idxRangeRel_type_free interp genv source.nextTypeStamp source.nextExnStamp source.evalState
    start finish other range (by omega)).1
  have growth := GlobalGrowth.installTypeTable genv start.tidx tags free
  have grownStates := stateRel_growth genv _ growth source flat states
  have nextStates : StateRel
      { genv with tys := finiteUpdate genv.tys start.tidx tags }
      { source with nextTypeStamp := source.nextTypeStamp + 1 } flat := by
    cases grownStates with
    | intro nonempty refs clock ffi => exact .intro _ _ nonempty refs clock ffi
  have nextRange := idxRangeRel_installTypeTable interp genv source.nextTypeStamp source.nextExnStamp
    source.evalState start finish other tags range fits
  have nextInvs : srcOracInvs interp transform
      { genv with tys := finiteUpdate genv.tys start.tidx tags }
      source.evalState := ⟨invs.1, srcOracEnvInvs_growth interp genv _ growth _ invs.2.1, invs.2.2⟩
  exact ⟨cOk, genvCTysOk_installTypeTable genv start.tidx tags typesOk free,
    nextStates, nextRange, nextInvs, oracle, globals, reserved, genInv, fin⟩

/-- Installing a constructor in an already reserved type preserves the
factored invariant when its key, stamp and type relation are compatible with
the existing constructor map. -/
theorem factoredInvariant_installTypeConstructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F)
    (idx tag arity : Nat) (name : ConN) (stamp : Nat) (tags : List (Nat × Nat))
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (table : genv.tys.lookup idx = some tags) (member : (tag, arity) ∈ tags)
    (older : stamp < source.nextTypeStamp)
    (free : genv.c.lookup ((tag, some idx), arity) = none)
    (fresh : ∀ key, genv.c.lookup key ≠ some (.typeStamp name stamp))
    (compatible : ∀ cn' arity' stamp', genv.c.lookup (cn', arity') = some stamp' →
      (SemanticPrimitivesHOL.ctorSameType (some (.typeStamp name stamp)) (some stamp') = true ↔
        FlatSem.ctorSameType (some (tag, some idx)) (some cn'))) :
    factoredInvariant interp transform gen
      { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) }
      (start, finish, other) source flat := by
  obtain ⟨cOk, typesOk, states, range, invs, oracle, globals, reserved, genInv, fin⟩ := valid
  have growth := GlobalGrowth.installTypeConstructor genv idx tag arity name stamp free
  have nextInvs : srcOracInvs interp transform
      { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) }
      source.evalState := ⟨invs.1, srcOracEnvInvs_growth interp genv _ growth _ invs.2.1, invs.2.2⟩
  exact ⟨genvCOk_installConstructor genv (tag, some idx) arity (.typeStamp name stamp) cOk free fresh compatible,
    genvCTysOk_installTypeConstructor genv idx tag arity name stamp tags typesOk table member,
    stateRel_growth genv _ growth source flat states,
    idxRangeRel_installTypeConstructor interp genv source.nextTypeStamp source.nextExnStamp source.evalState
      start finish other idx tag arity name stamp tags range table older,
    nextInvs, oracle, globals, reserved, genInv, fin⟩

/-- Subsequent constructors of a reserved type inherit compatibility from
an existing constructor of that type. -/
theorem factoredInvariant_installSiblingConstructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F)
    (idx tag arity anchorTag anchorArity : Nat) (name anchorName : ConN)
    (stamp : Nat) (tags : List (Nat × Nat))
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (table : genv.tys.lookup idx = some tags) (member : (tag, arity) ∈ tags)
    (older : stamp < source.nextTypeStamp)
    (anchor : genv.c.lookup ((anchorTag, some idx), anchorArity) = some (.typeStamp anchorName stamp))
    (free : genv.c.lookup ((tag, some idx), arity) = none)
    (fresh : ∀ key, genv.c.lookup key ≠ some (.typeStamp name stamp)) :
    factoredInvariant interp transform gen
      { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) }
      (start, finish, other) source flat :=
  factoredInvariant_installTypeConstructor interp transform gen genv start finish other source flat
    idx tag arity name stamp tags valid table member older free fresh
    (genvCOk_sameType_compatible genv idx tag anchorTag anchorArity name anchorName stamp valid.1 anchor)

/-- Reserving a type and installing its first constructor preserves the
factored invariant, deriving the compatibility conditions from the original
fresh index and stamp. -/
theorem factoredInvariant_allocateFirstTypeConstructor {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F)
    (tag arity : Nat) (name : ConN) (tags : List (Nat × Nat))
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (fits : start.tidx + 1 ≤ finish.tidx) (member : (tag, arity) ∈ tags) :
    factoredInvariant interp transform gen
      { { genv with tys := finiteUpdate genv.tys start.tidx tags } with
        c := finiteUpdate genv.c ((tag, some start.tidx), arity) (.typeStamp name source.nextTypeStamp) }
      ({ start with tidx := start.tidx + 1 }, finish, other)
      { source with nextTypeStamp := source.nextTypeStamp + 1 } flat := by
  classical
  let reserved := { genv with tys := finiteUpdate genv.tys start.tidx tags }
  let nextSource := { source with nextTypeStamp := source.nextTypeStamp + 1 }
  have reservedInv : factoredInvariant interp transform gen reserved
      ({ start with tidx := start.tidx + 1 }, finish, other) nextSource flat :=
    factoredInvariant_installTypeTable interp transform gen genv start finish other source flat tags valid fits
  have range := valid.2.2.2.1
  have free := (idxRangeRel_type_free interp genv source.nextTypeStamp source.nextExnStamp source.evalState
    start finish other range (by omega)).2
  have fresh := idxRangeRel_typeStamp_fresh interp genv source.nextTypeStamp source.nextExnStamp source.evalState
    start finish other range
  have table : reserved.tys.lookup start.tidx = some tags := by
    simp [reserved, finiteUpdate, FUPDATE_HOL]
  have cOk := genvCOk_installFreshTypeConstructor reserved start.tidx tag arity name source.nextTypeStamp
    reservedInv.1 free fresh
  have growth := GlobalGrowth.installTypeConstructor reserved start.tidx tag arity name source.nextTypeStamp
    (free tag arity)
  have newLookup : (finiteUpdate reserved.c ((tag, some start.tidx), arity)
      (.typeStamp name source.nextTypeStamp)).lookup ((tag, some start.tidx), arity) =
      some (.typeStamp name source.nextTypeStamp) := by
    simp [finiteUpdate, FUPDATE_HOL]
  have compatible : ∀ cn' arity' stamp', reserved.c.lookup (cn', arity') = some stamp' →
      (SemanticPrimitivesHOL.ctorSameType (some (.typeStamp name source.nextTypeStamp)) (some stamp') = true ↔
        FlatSem.ctorSameType (some (tag, some start.tidx)) (some cn')) := by
    intro cn' arity' stamp' old
    exact cOk.2.2.2.1 (tag, some start.tidx) cn' arity arity' (.typeStamp name source.nextTypeStamp) stamp'
      newLookup (growth.constructors (cn', arity') stamp' old)
  have result := factoredInvariant_installTypeConstructor interp transform gen reserved
    { start with tidx := start.tidx + 1 } finish other nextSource flat start.tidx tag arity name
    source.nextTypeStamp tags reservedInv table member (by simp [nextSource]) (free tag arity) (fresh name) compatible
  simpa [reserved, nextSource] using result

/-- Install a list of named constructor tags for one type. This proof-side
operation uses the same finite-map updates used by the allocation invariant. -/
noncomputable def installTypeConstructorList (idx stamp : Nat) :
    List (ConN × Nat × Nat) → GlobalEnv → GlobalEnv
  | [], genv => genv
  | (name, tag, arity) :: rest, genv =>
    installTypeConstructorList idx stamp rest
      { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) }

/-- An installation list cannot alter a constructor key absent from its tag
and arity projection. -/
theorem installTypeConstructorList_lookup_unchanged (idx stamp tag arity : Nat)
    (entries : List (ConN × Nat × Nat))
    (absent : (tag, arity) ∉ entries.map Prod.snd) (genv : GlobalEnv) :
    (installTypeConstructorList idx stamp entries genv).c.lookup ((tag, some idx), arity) =
      genv.c.lookup ((tag, some idx), arity) := by
  classical
  induction entries generalizing genv with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨name, newTag, newArity⟩
    have absent' : (tag, arity) ≠ (newTag, newArity) ∧ (tag, arity) ∉ rest.map Prod.snd := by
      simpa only [List.map_cons, List.mem_cons, not_or] using absent
    have different : ((tag, some idx), arity) ≠ ((newTag, some idx), newArity) := by
      intro same
      apply absent'.1
      simpa [and_assoc] using same
    simp only [installTypeConstructorList]
    rw [ih absent'.2]
    simp [finiteUpdate, FUPDATE_HOL, different]

/-- Each entry of a distinct installation list is present in the resulting
global constructor map with the source type stamp assigned to its name. -/
theorem installTypeConstructorList_lookup_entry (idx stamp : Nat) (entries : List (ConN × Nat × Nat))
    (distinct : (entries.map Prod.snd).Nodup) (name : ConN) (tag arity : Nat)
    (member : (name, tag, arity) ∈ entries) (genv : GlobalEnv) :
    (installTypeConstructorList idx stamp entries genv).c.lookup ((tag, some idx), arity) =
      some (.typeStamp name stamp) := by
  classical
  induction entries generalizing genv with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨headName, headTag, headArity⟩
    have distinct' := List.nodup_cons.mp distinct
    simp only [List.mem_cons] at member
    rcases member with same | member
    · have fields : name = headName ∧ tag = headTag ∧ arity = headArity := by simpa [and_assoc] using same
      obtain ⟨rfl, rfl, rfl⟩ := fields
      simp only [installTypeConstructorList]
      rw [installTypeConstructorList_lookup_unchanged _ _ _ _ rest distinct'.1]
      simp [finiteUpdate, FUPDATE_HOL]
    · simp only [installTypeConstructorList]
      exact ih distinct'.2 member _

/-- Each constructor entry generated by `allocTags` is installed at its
allocated flat key with the corresponding source stamp. -/
theorem installAllocatedConstructor_lookup (idx stamp : Nat) (constructors : List (ConN × List AstT))
    (name : ConN) (tag arity : Nat)
    (member : (name, tag, arity) ∈ allocatedConstructorEntries (M := ModN) constructors.reverse)
    (genv : GlobalEnv) :
    (installTypeConstructorList idx stamp (allocatedConstructorEntries (M := ModN) constructors.reverse) genv).c.lookup
      ((tag, some idx), arity) = some (.typeStamp name stamp) := by
  apply installTypeConstructorList_lookup_entry idx stamp _ _ name tag arity member genv
  rw [(allocatedConstructorEntries_projections (M := ModN) constructors.reverse).2]
  exact allocTags1_tags_nodup (M := ModN) constructors.reverse

/-- Installing a list of distinct constructors for an already allocated type
preserves the factored invariant. The anchor supplies the established type
relation and is preserved through every update. -/
theorem factoredInvariant_installConstructorList {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (idx stamp : Nat) (tags : List (Nat × Nat))
    (anchorTag anchorArity : Nat) (anchorName : ConN) (entries : List (ConN × Nat × Nat)) :
    ∀ genv : GlobalEnv,
      factoredInvariant interp transform gen genv (start, finish, other) source flat →
      genv.tys.lookup idx = some tags → stamp < source.nextTypeStamp →
      genv.c.lookup ((anchorTag, some idx), anchorArity) = some (.typeStamp anchorName stamp) →
      (entries.map Prod.fst).Nodup → (entries.map Prod.snd).Nodup →
      (∀ name tag arity, (name, tag, arity) ∈ entries → (tag, arity) ∈ tags) →
      (∀ name tag arity, (name, tag, arity) ∈ entries → genv.c.lookup ((tag, some idx), arity) = none) →
      (∀ name tag arity, (name, tag, arity) ∈ entries →
        ∀ key, genv.c.lookup key ≠ some (.typeStamp name stamp)) →
      factoredInvariant interp transform gen (installTypeConstructorList idx stamp entries genv)
        (start, finish, other) source flat := by
  classical
  induction entries with
  | nil =>
    intro genv valid _ _ _ _ _ _ _ _
    exact valid
  | cons entry rest ih =>
    rcases entry with ⟨name, tag, arity⟩
    intro genv valid table older anchor names keys members free fresh
    have names' := (List.nodup_cons.mp names)
    have keys' := (List.nodup_cons.mp keys)
    have headMember : (name, tag, arity) ∈ (name, tag, arity) :: rest := by simp
    have headFree := free name tag arity headMember
    have growth := GlobalGrowth.installTypeConstructor genv idx tag arity name stamp headFree
    let next := { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) }
    have nextValid : factoredInvariant interp transform gen next (start, finish, other) source flat :=
      factoredInvariant_installSiblingConstructor interp transform gen genv start finish other source flat
        idx tag arity anchorTag anchorArity name anchorName stamp tags valid table
        (members name tag arity headMember) older anchor headFree (fresh name tag arity headMember)
    have nextAnchor : next.c.lookup ((anchorTag, some idx), anchorArity) = some (.typeStamp anchorName stamp) :=
      growth.constructors _ _ anchor
    apply ih next nextValid table older nextAnchor names'.2 keys'.2
    · intro name' tag' arity' present
      exact members name' tag' arity' (List.mem_cons_of_mem _ present)
    · intro name' tag' arity' present
      have different : ((tag', some idx), arity') ≠ ((tag, some idx), arity) := by
        intro same
        have pair : (tag', arity') = (tag, arity) := by simpa [and_assoc] using same
        apply keys'.1
        apply List.mem_map.mpr
        exact ⟨(name', tag', arity'), present, pair⟩
      simpa [next, finiteUpdate, FUPDATE_HOL, different] using
        free name' tag' arity' (List.mem_cons_of_mem _ present)
    · intro name' tag' arity' present key
      have different : name' ≠ name := by
        intro same
        apply names'.1
        apply List.mem_map.mpr
        exact ⟨(name', tag', arity'), present, same⟩
      by_cases atKey : key = ((tag, some idx), arity)
      · subst key
        simp [next, finiteUpdate, FUPDATE_HOL, Ne.symm different]
      · simpa [next, finiteUpdate, FUPDATE_HOL, atKey] using
          fresh name' tag' arity' (List.mem_cons_of_mem _ present) key

/-- The list-level invariant applies to a suffix of the actual allocator
entries once a constructor of the type has been installed. Its distinctness
and table membership follow from the allocator. -/
theorem factoredInvariant_installAllocatedConstructors {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (idx stamp : Nat)
    (anchorTag anchorArity : Nat) (anchorName : ConN) (constructors : List (ConN × List AstT)) (skip : Nat)
    (genv : GlobalEnv)
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (table : genv.tys.lookup idx = some
      (allocTags1 constructors : Namespace ModN ConN Nat × Spt Nat × List (Nat × Nat)).2.2)
    (older : stamp < source.nextTypeStamp)
    (anchor : genv.c.lookup ((anchorTag, some idx), anchorArity) = some (.typeStamp anchorName stamp))
    (names : (constructors.map Prod.fst).Nodup)
    (free : ∀ name tag arity, (name, tag, arity) ∈ (allocatedConstructorEntries (M := ModN) constructors).drop skip →
      genv.c.lookup ((tag, some idx), arity) = none)
    (fresh : ∀ name tag arity, (name, tag, arity) ∈ (allocatedConstructorEntries (M := ModN) constructors).drop skip →
      ∀ key, genv.c.lookup key ≠ some (.typeStamp name stamp)) :
    factoredInvariant interp transform gen
      (installTypeConstructorList idx stamp ((allocatedConstructorEntries (M := ModN) constructors).drop skip) genv)
      (start, finish, other) source flat := by
  have distinct := allocatedConstructorEntries_nodup (M := ModN) constructors names
  have namesTail : (((allocatedConstructorEntries (M := ModN) constructors).drop skip).map Prod.fst).Nodup := by
    rw [List.map_drop]
    exact List.Nodup.sublist (List.drop_sublist _ _) distinct.1
  have keysTail : (((allocatedConstructorEntries (M := ModN) constructors).drop skip).map Prod.snd).Nodup := by
    rw [List.map_drop]
    exact List.Nodup.sublist (List.drop_sublist _ _) distinct.2
  apply factoredInvariant_installConstructorList interp transform gen start finish other source flat idx stamp
    (allocTags1 constructors : Namespace ModN ConN Nat × Spt Nat × List (Nat × Nat)).2.2
    anchorTag anchorArity anchorName ((allocatedConstructorEntries (M := ModN) constructors).drop skip)
    genv valid table older anchor namesTail keysTail
  · intro name tag arity member
    rw [← (allocatedConstructorEntries_projections (M := ModN) constructors).2]
    exact List.mem_map.mpr ⟨(name, tag, arity), List.mem_of_mem_drop member, rfl⟩
  · exact free
  · exact fresh

/-- Reserving a fresh type and installing all of its distinct constructor
entries preserves the factored invariant, including for an empty type. -/
theorem factoredInvariant_allocateConstructorList {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (tags : List (Nat × Nat))
    (entries : List (ConN × Nat × Nat))
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (fits : start.tidx + 1 ≤ finish.tidx)
    (names : (entries.map Prod.fst).Nodup) (keys : (entries.map Prod.snd).Nodup)
    (members : ∀ name tag arity, (name, tag, arity) ∈ entries → (tag, arity) ∈ tags) :
    factoredInvariant interp transform gen
      (installTypeConstructorList start.tidx source.nextTypeStamp entries
        { genv with tys := finiteUpdate genv.tys start.tidx tags })
      ({ start with tidx := start.tidx + 1 }, finish, other)
      { source with nextTypeStamp := source.nextTypeStamp + 1 } flat := by
  classical
  cases entries with
  | nil =>
    exact factoredInvariant_installTypeTable interp transform gen genv start finish other source flat tags valid fits
  | cons head rest =>
    rcases head with ⟨name, tag, arity⟩
    have names' := List.nodup_cons.mp names
    have keys' := List.nodup_cons.mp keys
    have headMember : (name, tag, arity) ∈ (name, tag, arity) :: rest := by simp
    let next := { { genv with tys := finiteUpdate genv.tys start.tidx tags } with
      c := finiteUpdate genv.c ((tag, some start.tidx), arity) (.typeStamp name source.nextTypeStamp) }
    have nextValid := factoredInvariant_allocateFirstTypeConstructor interp transform gen genv start finish other
      source flat tag arity name tags valid fits (members name tag arity headMember)
    have table : next.tys.lookup start.tidx = some tags := by simp [next, finiteUpdate, FUPDATE_HOL]
    have anchor : next.c.lookup ((tag, some start.tidx), arity) = some (.typeStamp name source.nextTypeStamp) := by
      simp [next, finiteUpdate, FUPDATE_HOL]
    have range := valid.2.2.2.1
    have free := (idxRangeRel_type_free interp genv source.nextTypeStamp source.nextExnStamp source.evalState
      start finish other range (by omega)).2
    have fresh := idxRangeRel_typeStamp_fresh interp genv source.nextTypeStamp source.nextExnStamp source.evalState
      start finish other range
    change factoredInvariant interp transform gen
      (installTypeConstructorList start.tidx source.nextTypeStamp rest next)
      ({ start with tidx := start.tidx + 1 }, finish, other)
      { source with nextTypeStamp := source.nextTypeStamp + 1 } flat
    apply factoredInvariant_installConstructorList interp transform gen { start with tidx := start.tidx + 1 }
      finish other { source with nextTypeStamp := source.nextTypeStamp + 1 } flat start.tidx source.nextTypeStamp
      tags tag arity name rest next nextValid table (by simp) anchor names'.2 keys'.2
    · intro name' tag' arity' present
      exact members name' tag' arity' (List.mem_cons_of_mem _ present)
    · intro name' tag' arity' present
      have different : ((tag', some start.tidx), arity') ≠ ((tag, some start.tidx), arity) := by
        intro same
        have pair : (tag', arity') = (tag, arity) := by simpa [and_assoc] using same
        apply keys'.1
        exact List.mem_map.mpr ⟨(name', tag', arity'), present, pair⟩
      simpa [next, finiteUpdate, FUPDATE_HOL, different] using free tag' arity'
    · intro name' tag' arity' present key
      have different : name' ≠ name := by
        intro same
        apply names'.1
        exact List.mem_map.mpr ⟨(name', tag', arity'), present, same⟩
      by_cases atKey : key = ((tag, some start.tidx), arity)
      · subst key
        simp [next, finiteUpdate, FUPDATE_HOL, Ne.symm different]
      · simpa [next, finiteUpdate, FUPDATE_HOL, atKey] using fresh name' key

/-- Allocating all constructors produced by `allocTags` preserves the
factored invariant. The table is reversed exactly as in the compiler pass. -/
theorem factoredInvariant_allocateTags {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (gen : EnvironmentGenerationStore) (genv : GlobalEnv)
    (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (constructors : List (ConN × List AstT))
    (valid : factoredInvariant interp transform gen genv (start, finish, other) source flat)
    (fits : start.tidx + 1 ≤ finish.tidx) (names : (constructors.map Prod.fst).Nodup) :
    factoredInvariant interp transform gen
      (installTypeConstructorList start.tidx source.nextTypeStamp
        (allocatedConstructorEntries (M := ModN) constructors.reverse)
        { genv with tys := finiteUpdate genv.tys start.tidx ((allocTags1 constructors.reverse :
          Namespace ModN ConN Nat × Spt Nat × List (Nat × Nat)).2.2.reverse) })
      ({ start with tidx := start.tidx + 1 }, finish, other)
      { source with nextTypeStamp := source.nextTypeStamp + 1 } flat := by
  have reversedNames : (constructors.reverse.map Prod.fst).Nodup := by
    rw [List.map_reverse, List.Nodup, List.pairwise_reverse]
    exact names.imp (fun h => Ne.symm h)
  have distinct := allocatedConstructorEntries_nodup (M := ModN) constructors.reverse reversedNames
  apply factoredInvariant_allocateConstructorList interp transform gen genv start finish other source flat
    (allocTags1 constructors.reverse : Namespace ModN ConN Nat × Spt Nat × List (Nat × Nat)).2.2.reverse
    (allocatedConstructorEntries (M := ModN) constructors.reverse) valid fits distinct.1 distinct.2
  intro name tag arity member
  simp only [List.mem_reverse]
  rw [← (allocatedConstructorEntries_projections (M := ModN) constructors.reverse).2]
  exact List.mem_map.mpr ⟨(name, tag, arity), member, rfl⟩

/-- Installing distinct, unused constructor keys preserves every previous
global binding throughout the whole list. -/
theorem GlobalGrowth.installConstructorList (idx stamp : Nat) (entries : List (ConN × Nat × Nat)) :
    ∀ genv : GlobalEnv, (entries.map Prod.snd).Nodup →
      (∀ name tag arity, (name, tag, arity) ∈ entries → genv.c.lookup ((tag, some idx), arity) = none) →
      GlobalGrowth genv (installTypeConstructorList idx stamp entries genv) := by
  classical
  induction entries with
  | nil =>
    intro genv _ _
    exact GlobalGrowth.refl genv
  | cons entry rest ih =>
    rcases entry with ⟨name, tag, arity⟩
    intro genv distinct free
    have distinct' := List.nodup_cons.mp distinct
    have headFree := free name tag arity (by simp)
    let next := { genv with c := finiteUpdate genv.c ((tag, some idx), arity) (.typeStamp name stamp) }
    have first := GlobalGrowth.installTypeConstructor genv idx tag arity name stamp headFree
    have remainingFree : ∀ name' tag' arity', (name', tag', arity') ∈ rest →
        next.c.lookup ((tag', some idx), arity') = none := by
      intro name' tag' arity' present
      have different : ((tag', some idx), arity') ≠ ((tag, some idx), arity) := by
        intro same
        have pair : (tag', arity') = (tag, arity) := by simpa [and_assoc] using same
        apply distinct'.1
        exact List.mem_map.mpr ⟨(name', tag', arity'), present, pair⟩
      simpa [next, finiteUpdate, FUPDATE_HOL, different] using
        free name' tag' arity' (List.mem_cons_of_mem _ present)
    exact first.trans (ih next distinct'.2 remainingFree)

/-- The fresh allocation generated by `allocTags` extends the original
global environment. -/
theorem GlobalGrowth.allocateTags {C : Type}
    (interp : Option (Value → Option (Config × C))) (genv : GlobalEnv)
    (nextType nextExn : Nat) (evalState : Option EvalState)
    (start finish : NextIndices) (other : Set (Nat × IndexKind)) (constructors : List (ConN × List AstT))
    (range : idxRangeRel interp genv nextType nextExn evalState (start, finish, other))
    (fits : start.tidx < finish.tidx) :
    GlobalGrowth genv
      (installTypeConstructorList start.tidx nextType (allocatedConstructorEntries (M := ModN) constructors.reverse)
        { genv with tys := finiteUpdate genv.tys start.tidx ((allocTags1 constructors.reverse :
          Namespace ModN ConN Nat × Spt Nat × List (Nat × Nat)).2.2.reverse) }) := by
  have free := idxRangeRel_type_free interp genv nextType nextExn evalState start finish other range fits
  let reserved := { genv with tys := finiteUpdate genv.tys start.tidx ((allocTags1 constructors.reverse :
    Namespace ModN ConN Nat × Spt Nat × List (Nat × Nat)).2.2.reverse) }
  have tableGrowth := GlobalGrowth.installTypeTable genv start.tidx
    (allocTags1 constructors.reverse : Namespace ModN ConN Nat × Spt Nat × List (Nat × Nat)).2.2.reverse free.1
  have keys : ((allocatedConstructorEntries (M := ModN) constructors.reverse).map Prod.snd).Nodup := by
    rw [(allocatedConstructorEntries_projections (M := ModN) constructors.reverse).2]
    exact allocTags1_tags_nodup (M := ModN) constructors.reverse
  have constructorGrowth := GlobalGrowth.installConstructorList start.tidx nextType
    (allocatedConstructorEntries (M := ModN) constructors.reverse) reserved keys
    (fun _ tag arity _ => free.2 tag arity)
  exact tableGrowth.trans constructorGrowth

end Flapjack.Compiler.Backend.SourceToFlat
