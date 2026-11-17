module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.NamespaceProps.MapLookup
public import Flapjack.NamespaceProps.LiftLookup

@[expose] public section

/-! Type identifier conditions for declarative environments. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.InferProps
  Flapjack.Basis.Pure.MlString Flapjack.AstHOL

/-- Lookup consequence used by the canonical type-name and variable proofs. -/
private theorem nsAll2EqLookup {M N V : Type} [DecidableEq M] [DecidableEq N]
    {a b : Namespace M N V} (h : nsAll2 (fun _ x y => x = y) a b) (id : Ident M N) :
    nsLookup a id = nsLookup b id := by
  cases first : nsLookup a id with
  | none =>
    cases second : nsLookup b id with
    | none => rfl
    | some v =>
      obtain ⟨w, found, _⟩ := h.2.1 id v second
      simp [first] at found
  | some v =>
    obtain ⟨w, found, eq⟩ := h.1.1 id v first
    cases eq
    simp [found]

/-- Declarative environments agree on all namespace lookups. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "tenv_equiv_def"]
def tenvEquiv (t1 t2 : TypeEnv) : Prop :=
  nsAll2 (fun _ a b => a = b) t1.t t2.t ∧
  nsAll2 (fun _ a b => a = b) t1.c t2.c ∧
  nsAll2 (fun _ a b => a = b) t1.v t2.v

/-- Every declarative environment is equivalent to itself. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "tenv_equiv_refl"]
theorem tenvEquivRefl (tenv : TypeEnv) : tenvEquiv tenv tenv := by
  have refl {V : Type} (env : Namespace MlString MlString V) :
      nsAll2 (fun _ a b => a = b) env env := by
    constructor <;> constructor
    all_goals first | (intro id v found; exact ⟨v, found, rfl⟩) | (intro path absent; exact absent)
  exact ⟨refl tenv.t, refl tenv.c, refl tenv.v⟩

/-- Environment equivalence is symmetric. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "tenv_equiv_sym"]
theorem tenvEquivSym (t1 t2 : TypeEnv) : tenvEquiv t1 t2 → tenvEquiv t2 t1 := by
  have sym {V : Type} {a b : Namespace MlString MlString V}
      (h : nsAll2 (fun _ x y => x = y) a b) :
      nsAll2 (fun _ x y => x = y) b a := by
    obtain ⟨⟨forward, fm⟩, ⟨backward, bm⟩⟩ := h
    refine ⟨⟨?_, bm⟩, ⟨?_, fm⟩⟩
    · intro id v found
      obtain ⟨w, hw, eq⟩ := backward id v found
      exact ⟨w, hw, eq.symm⟩
    · intro id v found
      obtain ⟨w, hw, eq⟩ := forward id v found
      exact ⟨w, hw, eq.symm⟩
  intro ⟨ht, hc, hv⟩
  exact ⟨sym ht, sym hc, sym hv⟩

/-- Lifting equivalent environments under the same module preserves equivalence. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "tenv_equiv_tenvLift"]
theorem tenvEquivTenvLift (t1 t2 : TypeEnv) (m : MlString) :
    tenvEquiv t1 t2 → tenvEquiv (tenvLift m t1) (tenvLift m t2) := by
  intro h
  simpa only [tenvEquiv, tenvLift, nsAll2_nsLift] using h

/-- Equivalent environments give the same variable lookup. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "lookup_var_tenv_equiv"]
theorem lookupVarTenvEquiv (t1 t2 : TypeEnv) (n : Ident MlString MlString)
    (bvs : TenvValExp) : tenvEquiv t1 t2 → lookupVar n bvs t1 = lookupVar n bvs t2 := by
  intro ⟨_, _, hv⟩
  simp only [lookupVar, nsAll2EqLookup hv n]

mutual
/-- Equivalent type namespaces give the same result when checking names. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "check_type_names_tenv_equiv"]
theorem checkTypeNamesTenvEquiv (t1 : TenvAbbrev) (t : AstT) (t2 : TenvAbbrev) :
    nsAll2 (fun _ a b => a = b) t1 t2 ∧ checkTypeNames t1 t = true →
      checkTypeNames t2 t = true := by
  rintro ⟨heq, checked⟩
  cases t with
  | atvar name => simp [checkTypeNames]
  | attup ts =>
    simp only [checkTypeNames] at checked ⊢
    exact checkTypeNamesListTenvEquiv t1 ts t2 ⟨heq, checked⟩
  | atfun left right =>
    simp only [checkTypeNames, Bool.and_eq_true] at checked ⊢
    exact ⟨checkTypeNamesTenvEquiv t1 left t2 ⟨heq, checked.1⟩,
      checkTypeNamesTenvEquiv t1 right t2 ⟨heq, checked.2⟩⟩
  | atapp ts name =>
    simp only [checkTypeNames, Bool.and_eq_true] at checked ⊢
    rw [← nsAll2EqLookup heq name]
    exact ⟨checked.1, checkTypeNamesListTenvEquiv t1 ts t2 ⟨heq, checked.2⟩⟩
termination_by sizeOf t

private theorem checkTypeNamesListTenvEquiv (t1 : TenvAbbrev) (ts : List AstT)
    (t2 : TenvAbbrev) :
    nsAll2 (fun _ a b => a = b) t1 t2 ∧ checkTypeNamesList t1 ts = true →
      checkTypeNamesList t2 ts = true := by
  rintro ⟨heq, checked⟩
  cases ts with
  | nil => simp [checkTypeNamesList]
  | cons t ts =>
    simp only [checkTypeNamesList, Bool.and_eq_true] at checked ⊢
    exact ⟨checkTypeNamesTenvEquiv t1 t t2 ⟨heq, checked.1⟩,
      checkTypeNamesListTenvEquiv t1 ts t2 ⟨heq, checked.2⟩⟩
termination_by sizeOf ts
end

mutual
/-- Equivalent type namespaces resolve a source type identically. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_name_subst_tenv_equiv"]
theorem typeNameSubstTenvEquiv (t1 : TenvAbbrev) (t : AstT) (t2 : TenvAbbrev) :
    nsAll2 (fun _ a b => a = b) t1 t2 → typeNameSubst t1 t = typeNameSubst t2 t := by
  intro heq
  cases t with
  | atvar name => simp [typeNameSubst]
  | attup ts => simp [typeNameSubst, typeNameSubstListTenvEquiv t1 ts t2 heq]
  | atfun left right =>
    simp [typeNameSubst, typeNameSubstTenvEquiv t1 left t2 heq,
      typeNameSubstTenvEquiv t1 right t2 heq]
  | atapp ts name =>
    simp [typeNameSubst, typeNameSubstListTenvEquiv t1 ts t2 heq, nsAll2EqLookup heq name]
termination_by sizeOf t

private theorem typeNameSubstListTenvEquiv (t1 : TenvAbbrev) (ts : List AstT)
    (t2 : TenvAbbrev) : nsAll2 (fun _ a b => a = b) t1 t2 →
      typeNameSubstList t1 ts = typeNameSubstList t2 ts := by
  intro heq
  cases ts with
  | nil => simp [typeNameSubstList]
  | cons t ts =>
    simp [typeNameSubstList, typeNameSubstTenvEquiv t1 t t2 heq,
      typeNameSubstListTenvEquiv t1 ts t2 heq]
termination_by sizeOf ts
end

/-- Pattern and pattern-list typing are preserved by environment equivalence. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_p_tenv_equiv"]
theorem typePTenvEquiv :
    (∀ tvs env p t bindings, TypeP tvs env p t bindings →
      ∀ target, tenvEquiv env target → TypeP tvs target p t bindings) ∧
    (∀ tvs env ps ts bindings, TypePs tvs env ps ts bindings →
      ∀ target, tenvEquiv env target → TypePs tvs target ps ts bindings) := by
  constructor
  all_goals
    intro tvs env ps ts bindings h
    let P := fun p t bindings (_ : TypeP tvs env p t bindings) =>
      ∀ target, tenvEquiv env target → TypeP tvs target p t bindings
    let Ps := fun ps ts bindings (_ : TypePs tvs env ps ts bindings) =>
      ∀ target, tenvEquiv env target → TypePs tvs target ps ts bindings
    first
    | refine TypeP.rec (motive_1 := P) (motive_2 := Ps) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    | refine TypePs.rec (motive_1 := P) (motive_2 := Ps) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    case refine_1 =>
      intro t free target equiv
      exact .any tvs target t free
    case refine_2 =>
      intro name t free target equiv
      exact .var tvs target name t free
    case refine_3 => intro n target equiv; exact .intLit tvs target n
    case refine_4 => intro c target equiv; exact .charLit tvs target c
    case refine_5 => intro s target equiv; exact .stringLit tvs target s
    case refine_6 => intro w target equiv; exact .word8Lit tvs target w
    case refine_7 => intro w target equiv; exact .word64Lit tvs target w
    case refine_8 =>
      intro name ps types params id args bindings free arity typed lookup ih target equiv
      apply TypeP.constructor tvs target name ps types params id args bindings free arity (ih target equiv)
      rw [← nsAll2EqLookup equiv.2.1 name]
      exact lookup
    case refine_9 =>
      intro ps types bindings typed ih target equiv
      exact .tuple tvs target ps types bindings (ih target equiv)
    case refine_10 =>
      intro p t bindings typed ih target equiv
      exact .reference tvs target p t bindings (ih target equiv)
    case refine_11 =>
      intro p name t bindings typed ih target equiv
      exact .asPattern tvs target p name t bindings (ih target equiv)
    case refine_12 =>
      intro p t bindings free names typed ih target equiv
      have names' := checkTypeNamesTenvEquiv env.t t target.t ⟨equiv.1, names⟩
      have subst := typeNameSubstTenvEquiv env.t t target.t equiv.1
      have typed' := ih target equiv
      rw [subst] at typed' ⊢
      exact .annotation tvs target p t bindings free names' typed'
    case refine_13 => intro target equiv; exact .nil tvs target
    case refine_14 =>
      intro p ps t ts bindings rest head tail ihHead ihTail target equiv
      exact .cons tvs target p ps t ts bindings rest (ihHead target equiv) (ihTail target equiv)

/-- Expression, expression-list, and function typing respect environment equivalence. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_e_tenv_equiv"]
theorem typeETenvEquiv :
    (∀ env bvs e t, TypeE env bvs e t →
      ∀ target, tenvEquiv env target → TypeE target bvs e t) ∧
    (∀ env bvs es ts, TypeEs env bvs es ts →
      ∀ target, tenvEquiv env target → TypeEs target bvs es ts) ∧
    (∀ env bvs funs ts, TypeFuns env bvs funs ts →
      ∀ target, tenvEquiv env target → TypeFuns target bvs funs ts) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro env bvs es ts h
    let P := fun bvs e t (_ : TypeE env bvs e t) =>
      ∀ target, tenvEquiv env target → TypeE target bvs e t
    let Ps := fun bvs es ts (_ : TypeEs env bvs es ts) =>
      ∀ target, tenvEquiv env target → TypeEs target bvs es ts
    let Pf := fun bvs funs ts (_ : TypeFuns env bvs funs ts) =>
      ∀ target, tenvEquiv env target → TypeFuns target bvs funs ts
    let Pb := fun bvs input output clauses (_ : TypeBranches env bvs input output clauses) =>
      ∀ target, tenvEquiv env target → TypeBranches target bvs input output clauses
    first
    | refine TypeE.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    | refine TypeEs.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    | refine TypeFuns.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    case refine_1 => intro b n target equiv; exact .intLit target b n
    case refine_2 => intro b c target equiv; exact .charLit target b c
    case refine_3 => intro b s target equiv; exact .stringLit target b s
    case refine_4 => intro b w target equiv; exact .word8Lit target b w
    case refine_5 => intro b w target equiv; exact .word64Lit target b w
    case refine_6 => intro b w target equiv; exact .float64Lit target b w
    case refine_7 =>
      intro b e t free typed ih target equiv
      exact .raise target b e t free (ih target equiv)
    case refine_8 =>
      intro b e clauses t typed nonempty branches ih ihBranches target equiv
      exact .handle target b e clauses t (ih target equiv) nonempty (ihBranches target equiv)
    case refine_9 =>
      intro b name es params id args types free arity typed lookup ih target equiv
      apply TypeE.constructor target b name es params id args types free arity (ih target equiv)
      rw [← nsAll2EqLookup equiv.2.1 name]
      exact lookup
    case refine_10 =>
      intro b es types typed ih target equiv
      exact .tuple target b es types (ih target equiv)
    case refine_11 =>
      intro b name t args tvs arity free lookup target equiv
      apply TypeE.var target b name t args tvs arity free
      rw [← lookupVarTenvEquiv env target name b equiv]
      exact lookup
    case refine_12 =>
      intro b name body t1 t2 free typed ih target equiv
      exact .fn target b name body t1 t2 free (ih target equiv)
    case refine_13 =>
      intro b op es ts t typed operator free ih target equiv
      exact .app target b op es ts t (ih target equiv) operator free
    case refine_14 =>
      intro b op e1 e2 first second ih1 ih2 target equiv
      exact .log target b op e1 e2 (ih1 target equiv) (ih2 target equiv)
    case refine_15 =>
      intro b guard yes no t condition thenBranch elseBranch ih1 ih2 ih3 target equiv
      exact .if_ target b guard yes no t (ih1 target equiv) (ih2 target equiv) (ih3 target equiv)
    case refine_16 =>
      intro b e clauses t1 t2 typed nonempty branches ih ihBranches target equiv
      exact .match_ target b e clauses t1 t2 (ih target equiv) nonempty (ihBranches target equiv)
    case refine_17 =>
      intro b name e1 e2 t1 t2 value body ih1 ih2 target equiv
      exact .let_ target b name e1 e2 t1 t2 (ih1 target equiv) (ih2 target equiv)
    case refine_18 =>
      intro b funs e t bindings functions body ihF ihE target equiv
      exact .letrec target b funs e t bindings (ihF target equiv) (ihE target equiv)
    case refine_19 =>
      intro b e t free names typed ih target equiv
      have names' := checkTypeNamesTenvEquiv env.t t target.t ⟨equiv.1, names⟩
      have subst := typeNameSubstTenvEquiv env.t t target.t equiv.1
      have typed' := ih target equiv
      rw [subst] at typed' ⊢
      exact .annotation target b e t free names' typed'
    case refine_20 =>
      intro b e loc t typed ih target equiv
      exact .location target b e loc t (ih target equiv)
    case refine_21 => intro b target equiv; exact .nil target b
    case refine_22 =>
      intro b e es t ts head tail ihH ihT target equiv
      exact .cons target b e es t ts (ihH target equiv) (ihT target equiv)
    case refine_23 => intro b target equiv; exact .nil target b
    case refine_24 =>
      intro b name arg body funs bindings t1 t2 free typed tail unique ihH ihT target equiv
      exact .cons target b name arg body funs bindings t1 t2 free (ihH target equiv) (ihT target equiv) unique
    case refine_25 => intro b input output target equiv; exact .nil target b input output
    case refine_26 =>
      intro b input output p body rest bindings distinct pattern expression tail ihE ihT target equiv
      exact .cons target b input output p body rest bindings distinct
        (typePTenvEquiv.1 (numTvs b) env p input bindings pattern target equiv)
        (ihE target equiv) (ihT target equiv)

/-- Pattern-expression determinacy is preserved by environment equivalence. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_pe_determ_tenv_equiv"]
theorem typePeDetermTenvEquiv (t1 t2 : TypeEnv) (x : TenvValExp) (y : Pat) (z : Flapjack.AstHOL.Exp) :
    typePeDeterm t1 x y z ∧ tenvEquiv t1 t2 → typePeDeterm t2 x y z := by
  rintro ⟨determ, equiv⟩ ty1 bs1 ty2 bs2 ⟨hp1, he1, hp2, he2⟩
  have reverse := tenvEquivSym t1 t2 equiv
  apply determ ty1 bs1 ty2 bs2
  exact ⟨typePTenvEquiv.1 0 t2 y ty1 bs1 hp1 t1 reverse,
    typeETenvEquiv.1 t2 x z ty1 he1 t1 reverse,
    typePTenvEquiv.1 0 t2 y ty2 bs2 hp2 t1 reverse,
    typeETenvEquiv.1 t2 x z ty2 he2 t1 reverse⟩

/-- Every type identifier in the declarative environment belongs to the set. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_tenv_def"]
noncomputable def setTidsTenv (tids : Nat → Prop) (tenv : TypeEnv) : Prop :=
  nsAll (fun _ entry => setTidsSubset tids entry.2) tenv.t ∧
  nsAll (fun _ entry => (∀ t ∈ entry.2.1, setTidsSubset tids t) ∧ tids entry.2.2) tenv.c ∧
  nsAll (fun _ entry => setTidsSubset tids entry.2) tenv.v

/-- The source's determinacy condition for bindings below the canonical bound. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_pe_determ_canon_def"]
def typePeDetermCanon (n : Nat) (env : TypeEnv) (localEnv : TenvValExp)
    (p : Pat) (e : Flapjack.AstHOL.Exp) : Prop :=
  ∀ t1 bindings1 t2 bindings2,
    TypeP 0 env p t1 bindings1 ∧ TypeE env localEnv e t1 ∧
    (∀ entry ∈ bindings1, setTidsSubset (fun id => id < n) entry.2) ∧
    TypeP 0 env p t2 bindings2 ∧ TypeE env localEnv e t2 ∧
    (∀ entry ∈ bindings2, setTidsSubset (fun id => id < n) entry.2) →
    bindings1 = bindings2

/-- Canonical pattern-expression determinacy respects environment equivalence. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_pe_determ_canon_tenv_equiv"]
theorem typePeDetermCanonTenvEquiv (n : Nat) (t1 t2 : TypeEnv) (x : TenvValExp)
    (y : Pat) (z : Flapjack.AstHOL.Exp) :
    typePeDetermCanon n t1 x y z ∧ tenvEquiv t1 t2 → typePeDetermCanon n t2 x y z := by
  rintro ⟨determ, equiv⟩ ty1 bs1 ty2 bs2 ⟨hp1, he1, ids1, hp2, he2, ids2⟩
  have reverse := tenvEquivSym t1 t2 equiv
  apply determ ty1 bs1 ty2 bs2
  exact ⟨typePTenvEquiv.1 0 t2 y ty1 bs1 hp1 t1 reverse,
    typeETenvEquiv.1 t2 x z ty1 he1 t1 reverse, ids1,
    typePTenvEquiv.1 0 t2 y ty2 bs2 hp2 t1 reverse,
    typeETenvEquiv.1 t2 x z ty2 he2 t1 reverse, ids2⟩

/-- Extending two environments preserves their common type-ID bound. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_tenv_extend_dec_tenv"]
theorem setTidsTenvExtendDecTenv (s : Nat → Prop) (t : TypeEnv)
    (s' : Nat → Prop) (t' : TypeEnv) :
    setTidsTenv (fun id => s' id ∨ s id) t' ∧
      setTidsTenv (fun id => s' id ∨ s id) t →
      setTidsTenv (fun id => s' id ∨ s id) (extendDecTenv t' t) := by
  rintro ⟨⟨ht', hc', hv'⟩, ⟨ht, hc, hv⟩⟩
  have append {V : Type} (p : Ident MlString MlString → V → Prop)
      (a b : Namespace MlString MlString V) (ha : nsAll p a) (hb : nsAll p b) :
      nsAll p (nsAppend a b) := by
    intro id value found
    cases a with
    | bind av am =>
      cases b with
      | bind bv bm =>
        cases id with
        | short name =>
          cases h : av.lookup name with
          | none => exact hb (.short name) value (by simpa [nsAppend, nsLookup, List.lookup_append, h] using found)
          | some v => exact ha (.short name) value (by simpa [nsAppend, nsLookup, List.lookup_append, h] using found)
        | long name rest =>
          cases h : am.lookup name with
          | none => exact hb (.long name rest) value (by simpa [nsAppend, nsLookup, List.lookup_append, h] using found)
          | some env => exact ha (.long name rest) value (by simpa [nsAppend, nsLookup, List.lookup_append, h] using found)
  exact ⟨append _ _ _ ht' ht, append _ _ _ hc' hc, append _ _ _ hv' hv⟩

/-- Renaming an environment maps its permitted type identifiers pointwise. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_tenv_remap"]
theorem setTidsTenvRemap (tids : Nat → Prop) (tenv : TypeEnv) (f : Nat → Nat) :
    setTidsTenv tids tenv →
      setTidsTenv (fun id => ∃ old, tids old ∧ f old = id) (remapTenv f tenv) := by
  intro ⟨ht, hc, hv⟩
  have rename (t : SemanticT) (h : setTidsSubset tids t) :
      setTidsSubset (fun id => ∃ old, tids old ∧ f old = id) (tsTidRename f t) := by
    intro id hid
    rw [setTidsTsTidRename] at hid
    obtain ⟨old, hold, heq⟩ := hid
    exact ⟨old, h old hold, heq⟩
  simp only [setTidsTenv, remapTenv]
  refine ⟨?_, ?_, ?_⟩
  · rw [nsAll_nsMap]
    intro id entry found
    exact rename _ (ht id entry found)
  · rw [nsAll_nsMap]
    intro id entry found
    obtain ⟨hargs, hid⟩ := hc id entry found
    constructor
    · intro t mem
      obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp mem
      exact rename old (hargs old oldMem)
    · exact ⟨entry.2.2, hid, rfl⟩
  · rw [nsAll_nsMap]
    intro id entry found
    exact rename _ (hv id entry found)

/-- Renaming commutes with extending declarative environments. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "remap_tenv_extend_dec_tenv"]
theorem remapTenvExtendDecTenv (f : Nat → Nat) (t t' : TypeEnv) :
    remapTenv f (extendDecTenv t t') =
      extendDecTenv (remapTenv f t) (remapTenv f t') := by
  cases t
  cases t'
  simp [remapTenv, extendDecTenv, nsMap_nsAppend]

/-- Enlarging the permitted set preserves the type's identifier condition. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_subset_mono"]
theorem setTidsSubsetMono (tids : Nat → Prop) (t : SemanticT) (tids' : Nat → Prop) :
    setTidsSubset tids t ∧ (∀ id, tids id → tids' id) → setTidsSubset tids' t := by
  rintro ⟨ht, hsub⟩ id hid
  exact hsub id (ht id hid)

/-- Enlarging the permitted set preserves the environment's identifier condition. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "set_tids_tenv_mono"]
theorem setTidsTenvMono (tids : Nat → Prop) (tenv : TypeEnv) (tids' : Nat → Prop) :
    setTidsTenv tids tenv ∧ (∀ id, tids id → tids' id) → setTidsTenv tids' tenv := by
  rintro ⟨⟨ht, hc, hv⟩, hsub⟩
  refine ⟨?_, ?_, ?_⟩
  · intro id entry h
    exact setTidsSubsetMono tids entry.2 tids' ⟨ht id entry h, hsub⟩
  · intro id entry h
    obtain ⟨hall, hid⟩ := hc id entry h
    exact ⟨fun t mem => setTidsSubsetMono tids t tids' ⟨hall t mem, hsub⟩, hsub _ hid⟩
  · intro id entry h
    exact setTidsSubsetMono tids entry.2 tids' ⟨hv id entry h, hsub⟩

mutual
/-- Canonical declaration typing with sequentially allocated type identifiers. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_d_canon"]
inductive TypeDCanon : Nat → TypeEnv → Dec → Nat → TypeEnv → Prop where
  | value (n tvs : Nat) (env : TypeEnv) (p : Pat) (e : Flapjack.AstHOL.Exp)
      (t : SemanticT) (bindings : List (MlString × SemanticT)) (loc : Flapjack.Misc.Location.Locs)
      (value : isValue e = true) (distinct : (patBindings p).Nodup)
      (pattern : TypeP tvs env p t bindings) (expression : TypeE env (bindTvar tvs .empty) e t)
      (principal : ∀ tvs' bindings' t',
        TypeP tvs' env p t' bindings' ∧ TypeE env (bindTvar tvs' .empty) e t' ∧
          (∀ entry ∈ bindings', setTidsSubset (fun id => id < n) entry.2) →
          every2 tschemeInst ((tenvAddTvs tvs' bindings').map Prod.snd)
            ((tenvAddTvs tvs bindings).map Prod.snd)) :
      TypeDCanon n env (.dlet loc p e) 0 ⟨alistToNs (tenvAddTvs tvs bindings), nsEmpty, nsEmpty⟩
  | monomorphic (n : Nat) (env : TypeEnv) (p : Pat) (e : Flapjack.AstHOL.Exp)
      (t : SemanticT) (bindings : List (MlString × SemanticT)) (loc : Flapjack.Misc.Location.Locs)
      (restricted : isValue e = false ∧ typePeDetermCanon n env .empty p e)
      (distinct : (patBindings p).Nodup) (pattern : TypeP 0 env p t bindings)
      (expression : TypeE env .empty e t) :
      TypeDCanon n env (.dlet loc p e) 0 ⟨alistToNs (tenvAddTvs 0 bindings), nsEmpty, nsEmpty⟩
  | recursive (n : Nat) (env : TypeEnv) (funs : List (MlString × MlString × Flapjack.AstHOL.Exp))
      (bindings : List (MlString × SemanticT)) (tvs : Nat) (loc : Flapjack.Misc.Location.Locs)
      (typed : TypeFuns env (bindVarList 0 bindings (bindTvar tvs .empty)) funs bindings)
      (principal : ∀ tvs' bindings',
        TypeFuns env (bindVarList 0 bindings' (bindTvar tvs' .empty)) funs bindings' ∧
          (∀ entry ∈ bindings', setTidsSubset (fun id => id < n) entry.2) →
          every2 tschemeInst ((tenvAddTvs tvs' bindings').map Prod.snd)
            ((tenvAddTvs tvs bindings).map Prod.snd)) :
      TypeDCanon n env (.dletrec loc funs) 0 ⟨alistToNs (tenvAddTvs tvs bindings), nsEmpty, nsEmpty⟩
  | datatype (n : Nat) (ids : List Nat) (env : TypeEnv) (defs : TypeDef)
      (newTypes : TenvAbbrev) (loc : Flapjack.Misc.Location.Locs)
      (bound : (TlistNum :: TboolNum :: primTypeNums).foldr max 0 < n)
      (allocated : ids = (List.range defs.length).map (fun i => i + n))
      (valid : checkCtorTenv (nsAppend newTypes env.t) defs)
      (types : newTypes = alistToNs ((defs.zip ids).map fun ((params, name, _), id) =>
        (name, (params, .app (params.map SemanticT.var) id)))) :
      TypeDCanon n env (.dtype loc defs) defs.length
        ⟨nsEmpty, buildCtorTenv (nsAppend newTypes env.t) defs ids, newTypes⟩
  | abbreviation (n : Nat) (env : TypeEnv) (tvs : List MlString) (name : MlString)
      (t : AstT) (loc : Flapjack.Misc.Location.Locs) (free : checkFreevarsAst tvs t = true)
      (names : checkTypeNames env.t t = true) (distinct : tvs.Nodup) :
      TypeDCanon n env (.dtabbrev loc tvs name t) 0
        ⟨nsEmpty, nsEmpty, nsSing name (tvs, typeNameSubst env.t t)⟩
  | exception (n : Nat) (env : TypeEnv) (name : MlString) (ts : List AstT) (loc : Flapjack.Misc.Location.Locs)
      (free : ts.all (checkFreevarsAst []) = true) (names : ts.all (checkTypeNames env.t) = true) :
      TypeDCanon n env (.dexn loc name ts) 0
        ⟨nsEmpty, nsSing name ([], ts.map (typeNameSubst env.t), TexnNum), nsEmpty⟩
  | module_ (n : Nat) (env : TypeEnv) (name : MlString) (ds : List Dec)
      (count : Nat) (newEnv : TypeEnv) (typed : TypeDsCanon n env ds count newEnv) :
      TypeDCanon n env (.dmod name ds) count (tenvLift name newEnv)
  | local_ (n : Nat) (env : TypeEnv) (privateDs publicDs : List Dec)
      (env1 env2 : TypeEnv) (count1 count2 : Nat)
      (first : TypeDsCanon n env privateDs count1 env1)
      (second : TypeDsCanon (n + count1) (extendDecTenv env1 env) publicDs count2 env2) :
      TypeDCanon n env (.dlocal privateDs publicDs) (count1 + count2) env2

/-- Canonical typing for declaration lists. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_d_canon"]
inductive TypeDsCanon : Nat → TypeEnv → List Dec → Nat → TypeEnv → Prop where
  | nil (n : Nat) (env : TypeEnv) : TypeDsCanon n env [] 0 ⟨nsEmpty, nsEmpty, nsEmpty⟩
  | cons (n : Nat) (env : TypeEnv) (d : Dec) (ds : List Dec) (env1 env2 : TypeEnv)
      (count1 count2 : Nat) (head : TypeDCanon n env d count1 env1)
      (tail : TypeDsCanon (n + count1) (extendDecTenv env1 env) ds count2 env2) :
      TypeDsCanon n env (d :: ds) (count1 + count2) (extendDecTenv env2 env1)
end

/-- A type-ID renaming fixes every primitive identifier. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "good_remap_def"]
def goodRemap (f : Nat → Nat) : Prop :=
  (TlistNum :: TboolNum :: primTypeNums).map f = TlistNum :: TboolNum :: primTypeNums

/-- Extend a renaming on a selected set by a shifted second function. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "extend_bij_def"]
noncomputable def extendBij (f g : Nat → Nat) (ids : Nat → Prop) (n v : Nat) : Nat := by
  classical
  exact if ids v then n + g v else f v

/-- The source's two identity laws for extending a renaming. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "extend_bij_id"]
theorem extendBijId (f g : Nat → Nat) (s : Nat → Prop) (n : Nat) :
    (extendBij f f s 0 = f) ∧ (extendBij f g (fun _ => False) n = f) := by
  classical
  constructor <;> funext v <;> simp [extendBij]

/-- Two consecutive extensions combine into one union extension. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "extend_bij_compose"]
theorem extendBijCompose (f g h : Nat → Nat) (ids jds : Nat → Prop) (n m : Nat) :
    extendBij (extendBij f g ids n) h jds (n + m) =
      extendBij f (extendBij g h jds m) (fun v => ids v ∨ jds v) n := by
  classical
  funext v
  by_cases hi : ids v <;> by_cases hj : jds v <;> simp [extendBij, hi, hj, Nat.add_assoc]

/-- Extending away from the primitives preserves a good renaming. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "good_remap_extend_bij"]
theorem goodRemapExtendBij (f g : Nat → Nat) (ids : Nat → Prop) (n : Nat) :
    goodRemap f ∧ primTids false ids → goodRemap (extendBij f g ids n) := by
  classical
  rintro ⟨good, prim⟩
  unfold goodRemap at good ⊢
  calc
    (TlistNum :: TboolNum :: primTypeNums).map (extendBij f g ids n) =
        (TlistNum :: TboolNum :: primTypeNums).map f := by
      apply List.map_congr_left
      intro id mem
      have absent : ¬ ids id := by
        intro h
        have := (prim id mem).1 h
        contradiction
      simp [extendBij, absent]
    _ = TlistNum :: TboolNum :: primTypeNums := good

end Flapjack.Compiler.Inference.TypeDCanon
