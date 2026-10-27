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

end Flapjack.Compiler.Backend.SourceToFlat
