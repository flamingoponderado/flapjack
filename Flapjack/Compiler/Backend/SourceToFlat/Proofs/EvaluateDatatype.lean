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

end Flapjack.Compiler.Backend.SourceToFlat
