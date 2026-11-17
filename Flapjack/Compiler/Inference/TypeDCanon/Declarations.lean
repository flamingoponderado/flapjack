module

public import Flapjack.Compiler.Inference.TypeDCanon.BindingTids
public import Flapjack.Compiler.Inference.TypeDCanon.Bijection
public import Flapjack.Compiler.Inference.TypeDCanon.DetermRemap
public import Flapjack.Compiler.Inference.TypeDCanon.ConstructorBounds
public import Flapjack.NamespaceProps.EmptyLookup
public import Flapjack.NamespaceProps.All
public import Flapjack.NamespaceProps.Append
public import Flapjack.TypeSysProps.Constructor

@[expose] public section

/-! Canonical allocation of declaration type identifiers. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack Flapjack.TypeSystemHOL Flapjack.AstHOL Flapjack.NamespaceHOL
  Flapjack.Compiler.Inference.InferProps
  Flapjack.Compiler.Inference.TypeDCanon

/-- Induction motive for the declaration conjunct of the theorem below. -/
private def dGoal (extra : Bool) (env : TypeEnv) (d : Dec) (ids : Set Nat) (out : TypeEnv) : Prop :=
  ∀ (tids : Set Nat) (f : Nat → Nat) (n : Nat) (mapped : TypeEnv),
    extra = true ∧ Disjoint ids tids ∧ setTidsTenv tids env ∧
    Set.BijOn f tids (fun id => id < n) ∧ primTids true tids ∧ goodRemap f ∧
    tenvEquiv (remapTenv f env) mapped →
      ∃ (g : Nat → Nat) (mappedOut : TypeEnv),
        setTidsTenv (tids ∪ ids : Set Nat) out ∧ primTids false ids ∧ ids.Finite ∧
        Set.BijOn g ids (fun id => id < ids.ncard) ∧
        TypeDCanon n mapped d ids.ncard mappedOut ∧
        tenvEquiv (remapTenv (extendBij f g ids n) out) mappedOut

/-- Induction motive for the declaration-list conjunct of the theorem below. -/
private def dsGoal (extra : Bool) (env : TypeEnv) (ds : List Dec) (ids : Set Nat) (out : TypeEnv) : Prop :=
  ∀ (tids : Set Nat) (f : Nat → Nat) (n : Nat) (mapped : TypeEnv),
    extra = true ∧ Disjoint ids tids ∧ setTidsTenv tids env ∧
    Set.BijOn f tids (fun id => id < n) ∧ primTids true tids ∧ goodRemap f ∧
    tenvEquiv (remapTenv f env) mapped →
      ∃ (g : Nat → Nat) (mappedOut : TypeEnv),
        setTidsTenv (tids ∪ ids : Set Nat) out ∧ primTids false ids ∧ ids.Finite ∧
        Set.BijOn g ids (fun id => id < ids.ncard) ∧
        TypeDsCanon n mapped ds ids.ncard mappedOut ∧
        tenvEquiv (remapTenv (extendBij f g ids n) out) mappedOut

/-- Environment extension preserves equivalence; HOL proves this inline using
namespace append. This private helper has no separate HOL declaration. -/
private theorem equivExtend (a a' b b' : TypeEnv)
    (first : tenvEquiv a b) (second : tenvEquiv a' b') :
    tenvEquiv (extendDecTenv a a') (extendDecTenv b b') := by
  obtain ⟨ht, hc, hv⟩ := first
  obtain ⟨bt, bc, bv⟩ := second
  have decEq : Classical.typeDecidableEq Basis.Pure.MlString.MlString =
      inferInstanceAs (DecidableEq Basis.Pure.MlString.MlString) := Subsingleton.elim _ _
  change nsAll2 (fun _ a b => a = b) a.t b.t at ht
  change nsAll2 (fun _ a b => a = b) a.c b.c at hc
  change nsAll2 (fun _ a b => a = b) a.v b.v at hv
  change nsAll2 (fun _ a b => a = b) a'.t b'.t at bt
  change nsAll2 (fun _ a b => a = b) a'.c b'.c at bc
  change nsAll2 (fun _ a b => a = b) a'.v b'.v at bv
  unfold tenvEquiv extendDecTenv
  rw [← decEq] at *
  exact ⟨nsAll2NsAppend _ _ _ _ _ ⟨ht, bt⟩,
    nsAll2NsAppend _ _ _ _ _ ⟨hc, bc⟩, nsAll2NsAppend _ _ _ _ _ ⟨hv, bv⟩⟩

/-- Visible pointwise agreement of two maps gives namespace equivalence.
HOL uses this lookup argument inline, without a separate declaration. -/
private theorem equivMapPair {M N V W : Type} [DecidableEq M] [DecidableEq N]
    (f g : V → W) (env : Namespace M N V)
    (agree : ∀ id v, nsLookup env id = some v → f v = g v) :
    nsAll2 (fun _ a b => a = b) (nsMap f env) (nsMap g env) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro id v found
    rw [nsLookup_nsMap] at found
    cases source : nsLookup env id with
    | none => simp [source] at found
    | some value =>
      simp [source] at found
      subst v
      exact ⟨g value, by simp [nsLookup_nsMap, source], agree id value source⟩
  · intro path absent
    rw [nsLookupMod_nsMap] at absent ⊢
    cases source : nsLookupMod env path <;> simp [source] at absent ⊢
  · intro id v found
    rw [nsLookup_nsMap] at found
    cases source : nsLookup env id with
    | none => simp [source] at found
    | some value =>
      simp [source] at found
      subst v
      exact ⟨f value, by simp [nsLookup_nsMap, source], agree id value source⟩
  · intro path absent
    rw [nsLookupMod_nsMap] at absent ⊢
    cases source : nsLookupMod env path <;> simp [source] at absent ⊢

/-- Renamings agreeing on an environment's identifiers yield equivalent
environments; the HOL proof establishes this inline. -/
private theorem equivRemapAgree (f g : Nat → Nat) (s : Nat → Prop) (env : TypeEnv)
    (agree : ∀ id, s id → f id = g id) (bound : setTidsTenv s env) :
    tenvEquiv (remapTenv f env) (remapTenv g env) := by
  obtain ⟨types, constructors, values⟩ := bound
  refine ⟨?_, ?_, ?_⟩
  · apply equivMapPair
    intro id entry found
    have h := types id entry found
    have fixedType := (tsTidRenameEqF f entry.2 g).2 (fun id member => agree id (h id member))
    simp [fixedType]

  · apply equivMapPair
    intro id entry found
    have ⟨typesBound, idBound⟩ := constructors id entry found
    have fixedTypes : entry.2.1.map (tsTidRename f) = entry.2.1.map (tsTidRename g) := by
      apply List.map_congr_left
      intro typ member
      exact (tsTidRenameEqF f typ g).2 (fun id occurs => agree id (typesBound typ member id occurs))
    simp [fixedTypes, agree _ idBound]
  · apply equivMapPair
    intro id entry found
    have h := values id entry found
    have fixedType := (tsTidRenameEqF f entry.2 g).2 (fun id member => agree id (h id member))
    simp [fixedType]

/-- Transitivity for equality-related namespaces, used inline in HOL's
environment lookup argument and not a separately claimed HOL port. -/
private theorem nsAll2EqTrans {M N V : Type} [DecidableEq M] [DecidableEq N]
    (a b c : Namespace M N V)
    (ab : nsAll2 (fun _ x y => x = y) a b) (bc : nsAll2 (fun _ x y => x = y) b c) :
    nsAll2 (fun _ x y => x = y) a c := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro id v found
    obtain ⟨w, hw, rfl⟩ := ab.1.1 id v found
    exact bc.1.1 id _ hw
  · intro path absent
    exact ab.1.2 path (bc.1.2 path absent)
  · intro id v found
    obtain ⟨w, hw, rfl⟩ := bc.2.1 id v found
    exact ab.2.1 id _ hw
  · intro path absent
    exact bc.2.2 path (ab.2.2 path absent)

/-- Transitivity of the environment relation, a local proof convenience for
the source's inline lookup reasoning. -/
private theorem equivTrans (a b c : TypeEnv) (ab : tenvEquiv a b) (bc : tenvEquiv b c) :
    tenvEquiv a c :=
  ⟨nsAll2EqTrans a.t b.t c.t ab.1 bc.1,
    nsAll2EqTrans a.c b.c c.c ab.2.1 bc.2.1,
    nsAll2EqTrans a.v b.v c.v ab.2.2 bc.2.2⟩

/-- Lists of type variables contain no type identifiers. This is a local
unfolding of the HOL definitions, not a separate HOL theorem. -/
private theorem tidsVars (xs : List Basis.Pure.MlString.MlString) (id : Nat) :
    ¬ setTidsList (xs.map SemanticT.var) id := by
  induction xs with
  | nil => simp [setTidsList]
  | cons x xs ih => simp [setTidsList, setTids, ih]

/-- Identifier renaming leaves type variables unchanged; HOL simplifies this
directly in the datatype case. -/
private theorem renameVars (f : Nat → Nat) (xs : List Basis.Pure.MlString.MlString) :
    tsTidRenameList f (xs.map SemanticT.var) = xs.map SemanticT.var := by
  induction xs with
  | nil => simp [tsTidRenameList]
  | cons x xs ih => simp [tsTidRenameList, tsTidRename, ih]

/-- Extract the checks used by HOL's inline constructor argument traversal.
This is a local elimination lemma, not a separate HOL declaration. -/
private theorem ctorNamesChecked (env : TenvAbbrev) (defs : TypeDef)
    (valid : checkCtorTenv env defs) : ∀ decl ∈ defs, ∀ ctor ∈ decl.2.2,
      ∀ ty ∈ ctor.2, checkTypeNames env ty = true := by
  induction defs with
  | nil => simp
  | cons d ds ih =>
    rcases d with ⟨tvs, name, ctors⟩
    simp only [checkCtorTenv] at valid
    intro decl mem ctor cMem ty tMem
    rcases List.mem_cons.mp mem with same | mem
    · subst decl
      exact (valid.2.2.1 ctor cMem ty tMem).2
    · exact ih valid.2.2.2.2 decl mem ctor cMem ty tMem

/-- Map a constructor environment when its individual source types commute
with renaming. HOL proves this list traversal inline in the datatype case. -/
private theorem mapBuildCtor (oldEnv newEnv : TenvAbbrev) (f : Nat → Nat)
    (defs : TypeDef) (ids : List Nat) (lengths : defs.length = ids.length)
    (agree : ∀ decl ∈ defs, ∀ ctor ∈ decl.2.2, ∀ ty ∈ ctor.2,
      tsTidRename f (typeNameSubst oldEnv ty) = typeNameSubst newEnv ty) :
    nsMap (fun entry => (entry.1, entry.2.1.map (tsTidRename f), f entry.2.2))
      (buildCtorTenv (α := Basis.Pure.MlString.MlString) oldEnv defs ids) =
      buildCtorTenv newEnv defs (ids.map f) := by
  induction defs generalizing ids with
  | nil =>
    cases ids <;> simp [buildCtorTenv, alistToNs, nsMap] at lengths ⊢
  | cons decl defs ih =>
    rcases decl with ⟨tvs, name, ctors⟩
    cases ids with
    | nil => simp at lengths
    | cons id ids =>
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      have tailAgree : ∀ decl ∈ defs, ∀ ctor ∈ decl.2.2, ∀ ty ∈ ctor.2,
          tsTidRename f (typeNameSubst oldEnv ty) = typeNameSubst newEnv ty := by
        intro decl mem
        exact agree decl (by simp [mem])
      simp only [List.map_cons, buildCtorTenv, nsMap_nsAppend]
      rw [ih ids lengths tailAgree]
      simp only [nsMap, alistToNs, List.map_nil, List.map_reverse, List.map_map]
      congr 2
      apply congrArg List.reverse
      apply List.map_congr_left
      intro ctor member
      rcases ctor with ⟨ctorName, args⟩
      simp only [Function.comp_def, List.map_map]
      congr 2
      apply congrArg (fun xs => (xs, f id))
      apply List.map_congr_left
      intro ty tyMem
      exact agree (tvs, name, ctors) (by simp) (ctorName, args) member ty tyMem

/-- Every source declaration and declaration list can be typed with canonical
consecutive identifiers. The finite-ID conclusions make `Set.ncard` agree
with HOL `CARD` wherever its value is observed in the result. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_d_type_d_canon"]
theorem typeDTypeDCanon :
    (∀ (extra : Bool) (env : TypeEnv) (d : Dec) (ids : Set Nat) (out : TypeEnv),
      TypeD extra env d ids out →
      ∀ (tids : Set Nat) (f : Nat → Nat) (n : Nat) (mapped : TypeEnv),
        extra = true ∧ Disjoint ids tids ∧ setTidsTenv tids env ∧
        Set.BijOn f tids (fun id => id < n) ∧ primTids true tids ∧ goodRemap f ∧
        tenvEquiv (remapTenv f env) mapped →
          ∃ (g : Nat → Nat) (mappedOut : TypeEnv),
            setTidsTenv (tids ∪ ids : Set Nat) out ∧ primTids false ids ∧ ids.Finite ∧
            Set.BijOn g ids (fun id => id < ids.ncard) ∧
            TypeDCanon n mapped d ids.ncard mappedOut ∧
            tenvEquiv (remapTenv (extendBij f g ids n) out) mappedOut) ∧
    (∀ (extra : Bool) (env : TypeEnv) (ds : List Dec) (ids : Set Nat) (out : TypeEnv),
      TypeDs extra env ds ids out →
      ∀ (tids : Set Nat) (f : Nat → Nat) (n : Nat) (mapped : TypeEnv),
        extra = true ∧ Disjoint ids tids ∧ setTidsTenv tids env ∧
        Set.BijOn f tids (fun id => id < n) ∧ primTids true tids ∧ goodRemap f ∧
        tenvEquiv (remapTenv f env) mapped →
          ∃ (g : Nat → Nat) (mappedOut : TypeEnv),
            setTidsTenv (tids ∪ ids : Set Nat) out ∧ primTids false ids ∧ ids.Finite ∧
            Set.BijOn g ids (fun id => id < ids.ncard) ∧
            TypeDsCanon n mapped ds ids.ncard mappedOut ∧
            tenvEquiv (remapTenv (extendBij f g ids n) out) mappedOut) := by
  change (∀ extra env d ids out, TypeD extra env d ids out → dGoal extra env d ids out) ∧
    (∀ extra env ds ids out, TypeDs extra env ds ids out → dsGoal extra env ds ids out)
  constructor <;> intro extra env d ids out typed
  all_goals
    first
    | apply TypeD.rec (motive_1 := fun env d ids out _ => dGoal extra env d ids out)
        (motive_2 := fun env ds ids out _ => dsGoal extra env ds ids out)
    | apply TypeDs.rec (motive_1 := fun env d ids out _ => dGoal extra env d ids out)
        (motive_2 := fun env ds ids out _ => dsGoal extra env ds ids out)
    case datatype =>
      intro env defs ids newTypes loc distinct fresh valid arity types tids f n mapped h
      rcases h with ⟨extraTrue, disjoint, envBound, bij, prim, good, equiv⟩
      obtain ⟨finiteIds, cardIds, bijIds, indexIds⟩ := listIdxOfBij ids distinct
      have noPrim : primTids false (fun id => id ∈ ids) := by
        intro id member
        change (id ∈ ids) ↔ false = true
        simp only [Bool.false_eq_true, iff_false]
        intro present
        exact fresh id present (by simpa [TlistNum, TboolNum] using member)
      have primitiveBound : (TlistNum :: TboolNum :: primTypeNums).foldr max 0 < n := by
        have fixed := mapFixedOnMembers f (TlistNum :: TboolNum :: primTypeNums) good
        have each : ∀ id ∈ TlistNum :: TboolNum :: primTypeNums, id < n := by
          intro id mem
          have inDomain := (prim id mem).2 rfl
          have inRange := bij.1 inDomain
          change f id < n at inRange
          simpa [fixed id mem] using inRange
        simp [primTypeNums, TlistNum, TboolNum, TarrayNum, TcharNum, TexnNum, TfnNum,
          TintNum, TrefNum, TstringNum, TtupNum, TvectorNum, Tword64Num, Tword8Num,
          Tword8arrayNum, TdoubleNum] at each ⊢
        omega
      let newIds := (List.range defs.length).map (fun i => i + n)
      let mappedTypes : TenvAbbrev := alistToNs ((defs.zip newIds).map fun ((params, name, _), id) =>
        (name, (params, SemanticT.app (params.map SemanticT.var) id)))
      have newTypesBound : nsAll (fun _ entry =>
          setTidsSubset (fun id => tids id ∨ id ∈ ids) entry.2) newTypes := by
        rw [types]
        have decEq : Classical.typeDecidableEq Basis.Pure.MlString.MlString =
            inferInstanceAs (DecidableEq Basis.Pure.MlString.MlString) := Subsingleton.elim _ _
        rw [← decEq]
        apply nsAllAlistToNs (fun _ entry => setTidsSubset (fun id => tids id ∨ id ∈ ids) entry.2)
          ((defs.zip ids).map fun ((params, name, _), id) =>
            (name, (params, SemanticT.app (params.map SemanticT.var) id)))
        intro entry mem
        obtain ⟨⟨⟨params, name, ctors⟩, id⟩, zipped, rfl⟩ := List.mem_map.mp mem
        have idMem : id ∈ ids := (List.of_mem_zip zipped).2
        intro candidate occurs
        simp only [setTids] at occurs
        rcases occurs with equal | impossible
        · exact Or.inr (equal ▸ idMem)
        · exact False.elim (tidsVars params candidate impossible)
      have oldTypesBound : nsAll (fun _ entry =>
          setTidsSubset (fun id => tids id ∨ id ∈ ids) entry.2) env.t := by
        intro id entry found candidate occurs
        exact Or.inl (envBound.1 id entry found candidate occurs)
      have combinedTypeBound : nsAll (fun _ entry =>
          setTidsSubset (fun id => tids id ∨ id ∈ ids) entry.2) (nsAppend newTypes env.t) := by
        have decEq : Classical.typeDecidableEq Basis.Pure.MlString.MlString =
            inferInstanceAs (DecidableEq Basis.Pure.MlString.MlString) := Subsingleton.elim _ _
        rw [← decEq] at newTypesBound oldTypesBound ⊢
        exact nsAll_nsAppend _ _ _ ⟨newTypesBound, oldTypesBound⟩
      have ctorBound : nsAll (fun _ entry =>
          (∀ t ∈ entry.2.1, setTidsSubset (fun id => tids id ∨ id ∈ ids) t) ∧
            (tids entry.2.2 ∨ entry.2.2 ∈ ids))
          (buildCtorTenv (α := Basis.Pure.MlString.MlString) (nsAppend newTypes env.t) defs ids) := by
        have decEq : Classical.typeDecidableEq Basis.Pure.MlString.MlString =
            inferInstanceAs (DecidableEq Basis.Pure.MlString.MlString) := Subsingleton.elim _ _
        rw [← decEq]
        exact buildCtorTenvTypeIdentities (M := Basis.Pure.MlString.MlString)
          (nsAppend newTypes env.t) defs ids tids ⟨prim, combinedTypeBound, arity.symm⟩
      have outputBound : setTidsTenv (fun id => tids id ∨ id ∈ ids)
          ⟨nsEmpty, buildCtorTenv (nsAppend newTypes env.t) defs ids, newTypes⟩ := by
        exact ⟨newTypesBound, ctorBound, by simp [nsAll, nsLookup_nsEmpty]⟩
      let ext := extendBij f ids.idxOf (fun id => id ∈ ids) n
      have allocated : ∀ i (hi : i < ids.length), ext ids[i] = n + i := by
        intro i hi
        simp [ext, extendBij, List.getElem_mem hi, indexIds i hi]
      have mappedTypesEq : nsMap (fun entry => (entry.1, tsTidRename ext entry.2)) newTypes = mappedTypes := by
        rw [types]
        simp only [nsMap, alistToNs, mappedTypes, List.map_nil]
        congr 1
        apply List.ext_getElem
        · simp [newIds, arity]
        · intro i hi hi'
          simp only [List.getElem_map, List.getElem_zip] at *
          have idBound : i < ids.length := by simpa [List.length_zip, arity] using hi
          have defBound : i < defs.length := by omega
          have mappedId : newIds[i]'(by simpa [newIds] using defBound) = i + n := by
            simp [newIds]
          cases hdef : defs[i] with
          | mk params rest =>
            cases rest with
            | mk name ctors =>
              simp [tsTidRename, renameVars, allocated i idBound, mappedId, Nat.add_comm]
      have extGood : goodRemap ext := goodRemapExtendBij f ids.idxOf (fun id => id ∈ ids) n ⟨good, noPrim⟩
      have agreeOld : ∀ id, tids id → ext id = f id := by
        intro id member
        have absent : id ∉ ids := fun present => Set.disjoint_left.1 disjoint present member
        simp [ext, extendBij, absent]
      have extEnvEquiv : tenvEquiv (remapTenv ext env) mapped :=
        equivTrans _ _ _ (equivRemapAgree ext f tids env agreeOld envBound) equiv
      have combinedEquiv : nsAll2 (fun _ a b => a = b)
          (nsMap (fun entry => (entry.1, tsTidRename ext entry.2)) (nsAppend newTypes env.t))
          (nsAppend mappedTypes mapped.t) := by
        rw [nsMap_nsAppend, mappedTypesEq]
        have same : nsAll2 (fun _ a b => a = b) mappedTypes mappedTypes :=
          (tenvEquivRefl ⟨nsEmpty, nsEmpty, mappedTypes⟩).1
        have old := extEnvEquiv.1
        change nsAll2 (fun _ a b => a = b)
          (nsMap (fun entry => (entry.1, tsTidRename ext entry.2)) env.t) mapped.t at old
        have decEq : Classical.typeDecidableEq Basis.Pure.MlString.MlString =
            inferInstanceAs (DecidableEq Basis.Pure.MlString.MlString) := Subsingleton.elim _ _
        rw [← decEq] at same old ⊢
        exact nsAll2NsAppend _ _ _ _ _ ⟨same, old⟩
      have checkedNames : ∀ t, checkTypeNames (nsAppend newTypes env.t) t = true →
          checkTypeNames (nsAppend mappedTypes mapped.t) t = true := by
        intro t old
        exact checkTypeNamesTenvEquiv _ t _
          ⟨combinedEquiv, (checkTypeNamesTsTidRename (nsAppend newTypes env.t) t ext).1 old⟩
      have mappedValid : checkCtorTenv (nsAppend mappedTypes mapped.t) defs := by
        apply Flapjack.TypeSysProps.checkCtorTenvChangeTenvT (nsAppend newTypes env.t) defs _
        refine ⟨?_, valid⟩
        intro ctor _ all ty member
        exact checkedNames ty (all ty member)
      have idsMapped : ids.map ext = newIds := by
        apply List.ext_getElem
        · simp [newIds, arity]
        · intro i hi hi'
          have idBound : i < ids.length := by simpa using hi
          have defBound : i < defs.length := by omega
          simp [newIds, allocated i idBound, Nat.add_comm]
      have substAgree : ∀ decl ∈ defs, ∀ ctor ∈ decl.2.2, ∀ ty ∈ ctor.2,
          tsTidRename ext (typeNameSubst (nsAppend newTypes env.t) ty) =
            typeNameSubst (nsAppend mappedTypes mapped.t) ty := by
        intro decl declMem ctor ctorMem ty tyMem
        have old := ctorNamesChecked (nsAppend newTypes env.t) defs valid decl declMem ctor ctorMem ty tyMem
        rw [tsTidRenameTypeNameSubst (nsAppend newTypes env.t) ty ext env ⟨extGood, old⟩]
        exact typeNameSubstTenvEquiv _ ty _ combinedEquiv
      have ctorEq := mapBuildCtor (nsAppend newTypes env.t) (nsAppend mappedTypes mapped.t)
        ext defs ids arity.symm substAgree
      rw [idsMapped] at ctorEq
      refine ⟨ids.idxOf, ⟨nsEmpty, buildCtorTenv (nsAppend mappedTypes mapped.t) defs newIds, mappedTypes⟩,
        outputBound, noPrim, finiteIds, ?_, ?_, ?_⟩
      · change Set.BijOn ids.idxOf {id | id ∈ ids} (fun id => id < ({id | id ∈ ids} : Set Nat).ncard)
        rw [cardIds]
        exact bijIds
      · change TypeDCanon n mapped (.dtype loc defs) ({id | id ∈ ids} : Set Nat).ncard _
        rw [cardIds, arity]
        exact TypeDCanon.datatype n newIds mapped defs mappedTypes loc primitiveBound rfl mappedValid rfl
      · have envEq : remapTenv ext
            ⟨nsEmpty, buildCtorTenv (nsAppend newTypes env.t) defs ids, newTypes⟩ =
            ⟨nsEmpty, buildCtorTenv (nsAppend mappedTypes mapped.t) defs newIds, mappedTypes⟩ := by
          simp [remapTenv, nsMap, nsEmpty, mappedTypesEq, ctorEq]
        rw [show extendBij f ids.idxOf (fun id => id ∈ ids) n = ext from rfl, envEq]
        exact tenvEquivRefl _
    case value =>
      intro tvs env p e t bindings loc isVal distinct pattern expression principal
      change dGoal extra env (.dlet loc p e) (∅ : Set Nat) _
      intro tids f n mapped h
      rcases h with ⟨extraTrue, _, bound, bij, prim, good, equiv⟩
      have bindingBounds := typePeBindingsTids tids env tvs p e t bindings
        ⟨prim, bound, pattern, expression, principal extraTrue⟩
      have renamedPattern := (typePTsTidRename f good).1 tvs env p t bindings pattern
      have renamedExpression := (typeETsTidRename f good).1 env (bindTvar tvs .empty) e t expression
      simp only [remapTenvEBindTvar, remapTenvE] at renamedExpression
      have canonicalPattern := typePTenvEquiv.1 tvs (remapTenv f env) p _ _ renamedPattern mapped equiv
      have canonicalExpression := typeETenvEquiv.1 (remapTenv f env) (bindTvar tvs .empty) e _
        renamedExpression mapped equiv
      have canonicalPrincipal : ∀ tvs' bindings' t',
          TypeP tvs' mapped p t' bindings' ∧
          TypeE mapped (bindTvar tvs' .empty) e t' ∧
          (∀ entry ∈ bindings', setTidsSubset (fun id => id < n) entry.2) →
          every2 tschemeInst ((tenvAddTvs tvs' bindings').map Prod.snd)
            ((tenvAddTvs tvs (bindings.map (fun entry => (entry.1, tsTidRename f entry.2)))).map Prod.snd) := by
        intro tvs' bindings' t' ⟨pattern', expression', bindingsBound⟩
        let inv := holLinv f tids
        have goodInv : goodRemap inv := goodRemapBij f tids (fun id => id < n) ⟨good, prim, bij⟩
        have inverseEnv := remapTenvLinv f tids (fun id => id < n) env ⟨bij, bound⟩
        have patternMapped := typePTenvEquiv.1 tvs' mapped p t' bindings' pattern'
          (remapTenv f env) (tenvEquivSym _ _ equiv)
        have expMapped := typeETenvEquiv.1 mapped (bindTvar tvs' .empty) e t' expression'
          (remapTenv f env) (tenvEquivSym _ _ equiv)
        have invPattern := (typePTsTidRename inv goodInv).1 tvs' (remapTenv f env) p t' bindings' patternMapped
        have invExpression := (typeETsTidRename inv goodInv).1 (remapTenv f env) (bindTvar tvs' .empty) e t' expMapped
        simp only [remapTenvEBindTvar, remapTenvE] at invExpression
        have origPattern := typePTenvEquiv.1 tvs' _ p _ _ invPattern env inverseEnv
        have origExpression := typeETenvEquiv.1 _ (bindTvar tvs' .empty) e _ invExpression env inverseEnv
        have original := principal extraTrue tvs' (bindings'.map (fun entry => (entry.1, tsTidRename inv entry.2)))
          (tsTidRename inv t') ⟨origPattern, origExpression⟩
        have rightInv : ∀ y, y < n → f (inv y) = y := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := bij.2.2 hy
          have inj : holInj f tids (fun id => id < n) :=
            ⟨fun _ hx => bij.1 hx, fun _ _ h eq => bij.2.1 h.1 h.2 eq⟩
          exact congrArg f (holLinvDef f tids (fun id => id < n) inj x hx)
        have restored : ∀ entry ∈ bindings', tsTidRename f (tsTidRename inv entry.2) = entry.2 := by
          intro entry mem
          rw [tsTidRenameCompose]
          apply (tsTidRenameEqId _ _).2
          intro id occurs
          exact rightInv id (bindingsBound entry mem id occurs)
        have transport {xs ys : List (Nat × SemanticT)} (rel : every2 tschemeInst xs ys) :
            every2 tschemeInst (xs.map (fun x => (x.1, tsTidRename f x.2)))
              (ys.map (fun x => (x.1, tsTidRename f x.2))) := by
          induction rel with
          | nil => exact .nil
          | @cons x y xs ys head tail ih =>
            exact .cons (tschemeInstRename f x.1 y.1 x.2 y.2 head) ih
        have moved := transport original
        simp only [tenvAddTvs, List.map_map, Function.comp_def] at moved ⊢
        have restoredList :
            bindings'.map (fun entry => (tvs', tsTidRename f (tsTidRename inv entry.2))) =
              bindings'.map (fun entry => (tvs', entry.2)) := by
          apply List.map_congr_left
          intro entry mem
          simp [restored entry mem]
        rw [← restoredList]
        exact moved
      let renamedBindings := bindings.map (fun entry => (entry.1, tsTidRename f entry.2))
      refine ⟨id, ⟨alistToNs (tenvAddTvs tvs renamedBindings), nsEmpty, nsEmpty⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Set.union_empty, setTidsTenv]
        refine ⟨?_, ?_, ?_⟩
        · simp [nsAll, nsLookup_nsEmpty]
        · simp [nsAll, nsLookup_nsEmpty]
        · intro ident entry found
          cases ident with
          | short key =>
            change (tenvAddTvs tvs bindings).lookup key = some entry at found
            obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp found
            have member : (key, entry) ∈ tenvAddTvs tvs bindings := by rw [equal]; simp
            obtain ⟨original, originalMem, originalEq⟩ := List.mem_map.mp member
            rcases original with ⟨origName, origType⟩
            change (origName, (tvs, origType)) = (key, entry) at originalEq
            cases originalEq
            exact bindingBounds _ _ originalMem
          | long mod rest => simp [alistToNs, nsLookup] at found
      · intro _ _
        change False ↔ false = true
        simp
      · exact Set.finite_empty
      · refine ⟨?_, ?_, ?_⟩
        · intro _ absent
          exact False.elim absent
        · intro _ absent
          exact False.elim absent
        · intro _ bound
          change _ < (∅ : Set Nat).ncard at bound
          simp at bound
      · simpa [renamedBindings] using
          TypeDCanon.value n tvs mapped p e (tsTidRename f t) renamedBindings loc
            isVal distinct canonicalPattern canonicalExpression canonicalPrincipal
      · have extEq : extendBij f id (∅ : Set Nat) n = f := (extendBijId f id (∅ : Set Nat) n).2
        simpa [remapTenv, nsMap, nsEmpty, alistToNs, tenvAddTvs, renamedBindings,
          List.map_map, Function.comp_def, extEq] using
          tenvEquivRefl ⟨alistToNs (tenvAddTvs tvs renamedBindings), nsEmpty, nsEmpty⟩
    case monomorphic =>
      intro env p e t bindings loc restricted distinct pattern expression
      change dGoal extra env (.dlet loc p e) (∅ : Set Nat) _
      intro tids f n mapped h
      rcases h with ⟨extraTrue, _, bound, bij, prim, good, equiv⟩
      obtain ⟨notValue, determ⟩ := restricted extraTrue
      have bindingBounds := typePeBindingsTidsZero tids env p e t bindings
        ⟨prim, bound, pattern, expression, determ⟩
      have canonicalDeterm : typePeDetermCanon n mapped .empty p e :=
        typePeDetermCanonTenvEquiv n (remapTenv f env) mapped .empty p e
          ⟨typePeDetermRemap env p e f tids n ⟨determ, good, prim, bij, bound⟩, equiv⟩
      have renamedPattern := (typePTsTidRename f good).1 0 env p t bindings pattern
      have renamedExpression := (typeETsTidRename f good).1 env .empty e t expression
      simp only [remapTenvE] at renamedExpression
      have canonicalPattern := typePTenvEquiv.1 0 (remapTenv f env) p _ _ renamedPattern mapped equiv
      have canonicalExpression := typeETenvEquiv.1 (remapTenv f env) .empty e _ renamedExpression mapped equiv
      let renamedBindings := bindings.map (fun entry => (entry.1, tsTidRename f entry.2))
      refine ⟨id, ⟨alistToNs (tenvAddTvs 0 renamedBindings), nsEmpty, nsEmpty⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Set.union_empty, setTidsTenv]
        refine ⟨?_, ?_, ?_⟩
        · simp [nsAll, nsLookup_nsEmpty]
        · simp [nsAll, nsLookup_nsEmpty]
        · intro ident entry found
          cases ident with
          | short key =>
            change (tenvAddTvs 0 bindings).lookup key = some entry at found
            obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp found
            have member : (key, entry) ∈ tenvAddTvs 0 bindings := by rw [equal]; simp
            obtain ⟨original, originalMem, originalEq⟩ := List.mem_map.mp member
            rcases original with ⟨origName, origType⟩
            change (origName, (0, origType)) = (key, entry) at originalEq
            cases originalEq
            exact bindingBounds _ _ originalMem
          | long mod rest => simp [alistToNs, nsLookup] at found
      · intro _ _
        change False ↔ false = true
        simp
      · exact Set.finite_empty
      · refine ⟨?_, ?_, ?_⟩
        · intro _ absent
          exact False.elim absent
        · intro _ absent
          exact False.elim absent
        · intro _ bound
          change _ < (∅ : Set Nat).ncard at bound
          simp at bound
      · simpa [renamedBindings] using
          TypeDCanon.monomorphic n mapped p e (tsTidRename f t) renamedBindings loc
            ⟨notValue, canonicalDeterm⟩ distinct canonicalPattern canonicalExpression
      · have extEq : extendBij f id (∅ : Set Nat) n = f := (extendBijId f id (∅ : Set Nat) n).2
        simpa [remapTenv, nsMap, nsEmpty, alistToNs, tenvAddTvs, renamedBindings,
          List.map_map, Function.comp_def, extEq] using
          tenvEquivRefl ⟨alistToNs (tenvAddTvs 0 renamedBindings), nsEmpty, nsEmpty⟩
    case recursive =>
      intro env funs bindings tvs loc typedFuns principal
      change dGoal extra env (.dletrec loc funs) (∅ : Set Nat) _
      intro tids f n mapped h
      rcases h with ⟨extraTrue, _, bound, bij, prim, good, equiv⟩
      have sourcePrincipal : ∀ tvs' bindings',
          TypeFuns env (bindVarList 0 bindings' (bindTvar tvs' .empty)) funs bindings' →
          every2 tschemeInst (bindings'.map (fun entry => (tvs', entry.2)))
            (bindings.map (fun entry => (tvs, entry.2))) := by
        intro tvs' bindings' typed'
        simpa [tenvAddTvs, List.map_map, Function.comp_def] using principal extraTrue tvs' bindings' typed'
      have bindingBounds := typeFunsBindingsTids tids env tvs funs bindings
        ⟨typedFuns, bound, prim, sourcePrincipal⟩
      have renamedFuns := (typeETsTidRename f good).2.2 env
        (bindVarList 0 bindings (bindTvar tvs .empty)) funs bindings typedFuns
      simp only [remapTenvEBindVarList, remapTenvEBindTvar, remapTenvE] at renamedFuns
      have canonicalFuns := typeETenvEquiv.2.2 (remapTenv f env) _ funs _ renamedFuns mapped equiv
      have canonicalPrincipal : ∀ tvs' bindings',
          TypeFuns mapped (bindVarList 0 bindings' (bindTvar tvs' .empty)) funs bindings' ∧
          (∀ entry ∈ bindings', setTidsSubset (fun id => id < n) entry.2) →
          every2 tschemeInst ((tenvAddTvs tvs' bindings').map Prod.snd)
            ((tenvAddTvs tvs (bindings.map (fun entry => (entry.1, tsTidRename f entry.2)))).map Prod.snd) := by
        intro tvs' bindings' ⟨typed', bindingsBound⟩
        let inv := holLinv f tids
        have goodInv : goodRemap inv := goodRemapBij f tids (fun id => id < n) ⟨good, prim, bij⟩
        have inverseEnv := remapTenvLinv f tids (fun id => id < n) env ⟨bij, bound⟩
        have funsMapped := typeETenvEquiv.2.2 mapped _ funs bindings' typed'
          (remapTenv f env) (tenvEquivSym _ _ equiv)
        have invFuns := (typeETsTidRename inv goodInv).2.2 (remapTenv f env)
          (bindVarList 0 bindings' (bindTvar tvs' .empty)) funs bindings' funsMapped
        simp only [remapTenvEBindVarList, remapTenvEBindTvar, remapTenvE] at invFuns
        have origFuns := typeETenvEquiv.2.2 _ _ funs _ invFuns env inverseEnv
        have original := principal extraTrue tvs' (bindings'.map (fun entry => (entry.1, tsTidRename inv entry.2))) origFuns
        have rightInv : ∀ y, y < n → f (inv y) = y := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := bij.2.2 hy
          have inj : holInj f tids (fun id => id < n) :=
            ⟨fun _ hx => bij.1 hx, fun _ _ h eq => bij.2.1 h.1 h.2 eq⟩
          exact congrArg f (holLinvDef f tids (fun id => id < n) inj x hx)
        have restored : ∀ entry ∈ bindings', tsTidRename f (tsTidRename inv entry.2) = entry.2 := by
          intro entry mem
          rw [tsTidRenameCompose]
          apply (tsTidRenameEqId _ _).2
          intro id occurs
          exact rightInv id (bindingsBound entry mem id occurs)
        have transport {xs ys : List (Nat × SemanticT)} (rel : every2 tschemeInst xs ys) :
            every2 tschemeInst (xs.map (fun x => (x.1, tsTidRename f x.2)))
              (ys.map (fun x => (x.1, tsTidRename f x.2))) := by
          induction rel with
          | nil => exact .nil
          | @cons x y xs ys head tail ih =>
            exact .cons (tschemeInstRename f x.1 y.1 x.2 y.2 head) ih
        have moved := transport original
        simp only [tenvAddTvs, List.map_map, Function.comp_def] at moved ⊢
        have restoredList :
            bindings'.map (fun entry => (tvs', tsTidRename f (tsTidRename inv entry.2))) =
              bindings'.map (fun entry => (tvs', entry.2)) := by
          apply List.map_congr_left
          intro entry mem
          simp [restored entry mem]
        rw [← restoredList]
        exact moved
      let renamedBindings := bindings.map (fun entry => (entry.1, tsTidRename f entry.2))
      refine ⟨id, ⟨alistToNs (tenvAddTvs tvs renamedBindings), nsEmpty, nsEmpty⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Set.union_empty, setTidsTenv]
        refine ⟨?_, ?_, ?_⟩
        · simp [nsAll, nsLookup_nsEmpty]
        · simp [nsAll, nsLookup_nsEmpty]
        · intro ident entry found
          cases ident with
          | short key =>
            change (tenvAddTvs tvs bindings).lookup key = some entry at found
            obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp found
            have member : (key, entry) ∈ tenvAddTvs tvs bindings := by rw [equal]; simp
            obtain ⟨original, originalMem, originalEq⟩ := List.mem_map.mp member
            rcases original with ⟨origName, origType⟩
            change (origName, (tvs, origType)) = (key, entry) at originalEq
            cases originalEq
            exact bindingBounds _ originalMem
          | long mod rest => simp [alistToNs, nsLookup] at found
      · intro _ _
        change False ↔ false = true
        simp
      · exact Set.finite_empty
      · refine ⟨?_, ?_, ?_⟩
        · intro _ absent
          exact False.elim absent
        · intro _ absent
          exact False.elim absent
        · intro _ bound
          change _ < (∅ : Set Nat).ncard at bound
          simp at bound
      · simpa [renamedBindings] using
          TypeDCanon.recursive n mapped funs renamedBindings tvs loc canonicalFuns canonicalPrincipal
      · have extEq : extendBij f id (∅ : Set Nat) n = f := (extendBijId f id (∅ : Set Nat) n).2
        simpa [remapTenv, nsMap, nsEmpty, alistToNs, tenvAddTvs, renamedBindings,
          List.map_map, Function.comp_def, extEq] using
          tenvEquivRefl ⟨alistToNs (tenvAddTvs tvs renamedBindings), nsEmpty, nsEmpty⟩
    case abbreviation =>
      intro env tvs name t loc free names distinct
      change dGoal extra env (.dtabbrev loc tvs name t) (∅ : Set Nat) _
      intro tids f n mapped h
      rcases h with ⟨_, _, bound, _, prim, good, equiv⟩
      have checked : checkTypeNames mapped.t t = true := by
        apply checkTypeNamesTenvEquiv (remapTenv f env).t t mapped.t
        exact ⟨equiv.1, (checkTypeNamesTsTidRename env.t t f).1 names⟩
      have typeBound : setTidsSubset tids (typeNameSubst env.t t) :=
        setTidsSubsetTypeNameSubst env.t t tids ⟨prim, bound.1⟩
      have equalTypes : tsTidRename f (typeNameSubst env.t t) = typeNameSubst mapped.t t := by
        rw [tsTidRenameTypeNameSubst env.t t f env ⟨good, names⟩]
        exact typeNameSubstTenvEquiv (remapTenv f env).t t mapped.t equiv.1
      refine ⟨id, ⟨nsEmpty, nsEmpty, nsSing name (tvs, typeNameSubst mapped.t t)⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Set.union_empty, setTidsTenv]
        refine ⟨?_, ?_, ?_⟩
        · have decEq : Classical.typeDecidableEq Basis.Pure.MlString.MlString =
              inferInstanceAs (DecidableEq Basis.Pure.MlString.MlString) := Subsingleton.elim _ _
          rw [← decEq]
          exact (nsAllNsSing _ _ _).2 typeBound
        · simp [nsAll, nsLookup_nsEmpty]
        · simp [nsAll, nsLookup_nsEmpty]
      · intro _ _
        change False ↔ false = true
        simp
      · exact Set.finite_empty
      · refine ⟨?_, ?_, ?_⟩
        · intro _ absent
          exact False.elim absent
        · intro _ absent
          exact False.elim absent
        · intro _ bound
          change _ < (∅ : Set Nat).ncard at bound
          simp at bound
      · simpa using TypeDCanon.abbreviation n mapped tvs name t loc free checked distinct
      · have extEq : extendBij f id (∅ : Set Nat) n = f := (extendBijId f id (∅ : Set Nat) n).2
        simpa [remapTenv, nsMap, nsEmpty, nsSing, extEq, equalTypes] using
          tenvEquivRefl ⟨nsEmpty, nsEmpty, nsSing name (tvs, typeNameSubst mapped.t t)⟩
    case module_ =>
      intro env name ds ids out typed ih tids f n mapped h
      obtain ⟨g, mappedOut, bound, prim, finite, bij, canon, equiv⟩ := ih tids f n mapped h
      refine ⟨g, tenvLift name mappedOut, ?_, prim, finite, bij,
        TypeDCanon.module_ n mapped name ds (show Set Nat from ids).ncard mappedOut canon, ?_⟩
      · simpa [setTidsTenv, tenvLift, Flapjack.NamespaceHOL.nsAll_nsLift] using bound
      · have lifted := tenvEquivTenvLift _ _ name equiv
        simpa [remapTenv, tenvLift, Flapjack.NamespaceHOL.nsMap,
          Flapjack.NamespaceHOL.nsLift] using lifted
    case local_ =>
      intro env privateDs publicDs env1 env2 ids1 ids2 first second distinct ih1 ih2 tids f n mapped h
      rcases h with ⟨extraTrue, disjoint, envBound, bij, prim, good, equiv⟩
      have disj1 : Disjoint (show Set Nat from ids1) tids := by
        apply Set.disjoint_left.2
        intro id h1 ht
        exact Set.disjoint_left.1 disjoint (Or.inl h1) ht
      have disj2 : Disjoint (show Set Nat from ids2) (tids ∪ (show Set Nat from ids1)) := by
        apply Set.disjoint_left.2
        intro id h2 ht
        rcases ht with ht | h1
        · exact Set.disjoint_left.1 disjoint (Or.inr h2) ht
        · exact distinct id h1 h2
      obtain ⟨g, mapped1, bound1, prim1, finite1, bij1, canon1, equiv1⟩ :=
        ih1 tids f n mapped ⟨extraTrue, disj1, envBound, bij, prim, good, equiv⟩
      let allIds : Set Nat := tids ∪ (show Set Nat from ids1)
      let f1 := extendBij f g ids1 n
      have boundEnv : setTidsTenv allIds (extendDecTenv env1 env) := by
        apply setTidsTenvExtendDecTenv ids1 env tids env1
        refine ⟨bound1, ?_⟩
        exact setTidsTenvMono tids env allIds ⟨envBound, fun id member => Or.inl member⟩
      have primAll : primTids true allIds := by
        intro id member
        simp only [iff_true]
        exact Or.inl ((prim id member).2 rfl)
      have good1 : goodRemap f1 := goodRemapExtendBij f g ids1 n ⟨good, prim1⟩
      have bijAll : Set.BijOn f1 allIds (fun id => id < n + (show Set Nat from ids1).ncard) := by
        apply bijExtendBij tids (show Set Nat from ids1) f g n
        exact ⟨fun id ht hi => Set.disjoint_left.1 disj1 hi ht, bij, bij1⟩
      have agreeOld : ∀ id, tids id → f1 id = f id := by
        intro id member
        have absent : ¬ ids1 id := fun present => Set.disjoint_left.1 disj1 present member
        simp [f1, extendBij, absent]
      have oldEquiv := equivTrans _ _ _ (equivRemapAgree f1 f tids env agreeOld envBound) equiv
      have combinedEquiv : tenvEquiv (remapTenv f1 (extendDecTenv env1 env))
          (extendDecTenv mapped1 mapped) := by
        rw [remapTenvExtendDecTenv]
        exact equivExtend _ _ _ _ equiv1 oldEquiv
      obtain ⟨g2, mapped2, bound2, prim2, finite2, bij2, canon2, equiv2⟩ :=
        ih2 allIds f1 (n + (show Set Nat from ids1).ncard) (extendDecTenv mapped1 mapped)
          ⟨extraTrue, disj2, boundEnv, bijAll, primAll, good1, combinedEquiv⟩
      have disj12 : Disjoint (show Set Nat from ids1) (show Set Nat from ids2) := by
        apply Set.disjoint_left.2
        intro id h1 h2
        exact distinct id h1 h2
      have cardUnion : (show Set Nat from unionTypeIds ids1 ids2).ncard =
          (show Set Nat from ids1).ncard + (show Set Nat from ids2).ncard :=
        disjointCardUnion _ _ ⟨finite1, finite2, disj12⟩
      refine ⟨extendBij g g2 ids2 (show Set Nat from ids1).ncard, mapped2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change setTidsTenv (tids ∪ ((show Set Nat from ids1) ∪ (show Set Nat from ids2)) : Set Nat) env2
        have unionEq : allIds ∪ (show Set Nat from ids2) =
            tids ∪ ((show Set Nat from ids1) ∪ (show Set Nat from ids2)) := by
          exact Set.union_assoc tids (show Set Nat from ids1) (show Set Nat from ids2)
        rw [← unionEq]
        exact bound2
      · intro id member
        change (ids1 id ∨ ids2 id) ↔ false = true
        have h1 := prim1 id member
        have h2 := prim2 id member
        simp only [Bool.false_eq_true, iff_false] at h1 h2 ⊢
        intro present
        rcases present with present | present
        · exact h1 present
        · exact h2 present
      · exact finite1.union finite2
      · have combined := bijExtendBij (show Set Nat from ids1) (show Set Nat from ids2)
          g g2 (show Set Nat from ids1).ncard
          ⟨distinct, bij1, bij2⟩
        change Set.BijOn (extendBij g g2 ids2 (show Set Nat from ids1).ncard)
          (fun id => ids1 id ∨ ids2 id) (fun id => id < (show Set Nat from unionTypeIds ids1 ids2).ncard)
        rw [cardUnion]
        exact combined
      · rw [cardUnion]
        exact TypeDCanon.local_ n mapped privateDs publicDs mapped1 mapped2 _ _ canon1 canon2
      · have comp : extendBij f (extendBij g g2 ids2 (show Set Nat from ids1).ncard)
            (unionTypeIds ids1 ids2) n =
            extendBij f1 g2 ids2 (n + (show Set Nat from ids1).ncard) := by
          exact (extendBijCompose f g g2 ids1 ids2 n (show Set Nat from ids1).ncard).symm
        rw [comp]
        exact equiv2
    case exception =>
      intro env name ts loc free names
      change dGoal extra env (.dexn loc name ts) (∅ : Set Nat) _
      intro tids f n mapped h
      rcases h with ⟨_, _, bound, _, prim, good, equiv⟩
      have checked : ts.all (checkTypeNames mapped.t) = true := by
        rw [List.all_eq_true] at names ⊢
        intro t mem
        apply checkTypeNamesTenvEquiv (remapTenv f env).t t mapped.t
        exact ⟨equiv.1, (checkTypeNamesTsTidRename env.t t f).1 (names t mem)⟩
      have typeBound : ∀ t ∈ ts, setTidsSubset tids (typeNameSubst env.t t) := by
        intro t _
        exact setTidsSubsetTypeNameSubst env.t t tids ⟨prim, bound.1⟩
      have exnBound : tids TexnNum := (prim TexnNum (by simp [primTypeNums])).2 rfl
      have fixedExn : f TexnNum = TexnNum :=
        mapFixedOnMembers f (TlistNum :: TboolNum :: primTypeNums) good TexnNum (by simp [primTypeNums])
      have equalTypes : (ts.map (typeNameSubst env.t)).map (tsTidRename f) =
          ts.map (typeNameSubst mapped.t) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro t mem
        change tsTidRename f (typeNameSubst env.t t) = typeNameSubst mapped.t t
        rw [tsTidRenameTypeNameSubst env.t t f env ⟨good, (List.all_eq_true.mp names) t mem⟩]
        exact typeNameSubstTenvEquiv (remapTenv f env).t t mapped.t equiv.1
      refine ⟨id, ⟨nsEmpty, nsSing name ([], ts.map (typeNameSubst mapped.t), TexnNum), nsEmpty⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Set.union_empty, setTidsTenv]
        refine ⟨?_, ?_, ?_⟩
        · simp [nsAll, nsLookup_nsEmpty]
        · have decEq : Classical.typeDecidableEq Basis.Pure.MlString.MlString =
              inferInstanceAs (DecidableEq Basis.Pure.MlString.MlString) := Subsingleton.elim _ _
          rw [← decEq, nsAllNsSing]
          refine ⟨?_, exnBound⟩
          intro ty mem
          obtain ⟨t, tmem, rfl⟩ := List.mem_map.mp mem
          exact typeBound t tmem
        · simp [nsAll, nsLookup_nsEmpty]
      · intro _ _
        change False ↔ false = true
        simp
      · exact Set.finite_empty
      · refine ⟨?_, ?_, ?_⟩
        · intro _ absent
          exact False.elim absent
        · intro _ absent
          exact False.elim absent
        · intro _ bound
          change _ < (∅ : Set Nat).ncard at bound
          simp at bound
      · simpa using TypeDCanon.exception n mapped name ts loc free checked
      · have extEq : extendBij f id (∅ : Set Nat) n = f := (extendBijId f id (∅ : Set Nat) n).2
        simpa [remapTenv, nsMap, nsEmpty, nsSing, extEq, equalTypes, fixedExn] using
          tenvEquivRefl ⟨nsEmpty, nsSing name ([], ts.map (typeNameSubst mapped.t), TexnNum), nsEmpty⟩
    case cons =>
      intro env d ds env1 env2 ids1 ids2 head tail distinct ih1 ih2 tids f n mapped h
      rcases h with ⟨extraTrue, disjoint, envBound, bij, prim, good, equiv⟩
      have disj1 : Disjoint (show Set Nat from ids1) tids := by
        apply Set.disjoint_left.2
        intro id h1 ht
        exact Set.disjoint_left.1 disjoint (Or.inl h1) ht
      have disj2 : Disjoint (show Set Nat from ids2) (tids ∪ (show Set Nat from ids1)) := by
        apply Set.disjoint_left.2
        intro id h2 ht
        rcases ht with ht | h1
        · exact Set.disjoint_left.1 disjoint (Or.inr h2) ht
        · exact distinct id h1 h2
      obtain ⟨g, mapped1, bound1, prim1, finite1, bij1, canon1, equiv1⟩ :=
        ih1 tids f n mapped ⟨extraTrue, disj1, envBound, bij, prim, good, equiv⟩
      let allIds : Set Nat := tids ∪ (show Set Nat from ids1)
      let f1 := extendBij f g ids1 n
      have boundEnv : setTidsTenv allIds (extendDecTenv env1 env) := by
        apply setTidsTenvExtendDecTenv ids1 env tids env1
        refine ⟨bound1, ?_⟩
        exact setTidsTenvMono tids env allIds ⟨envBound, fun id member => Or.inl member⟩
      have primAll : primTids true allIds := by
        intro id member
        simp only [iff_true]
        exact Or.inl ((prim id member).2 rfl)
      have good1 : goodRemap f1 := goodRemapExtendBij f g ids1 n ⟨good, prim1⟩
      have bijAll : Set.BijOn f1 allIds (fun id => id < n + (show Set Nat from ids1).ncard) := by
        apply bijExtendBij tids (show Set Nat from ids1) f g n
        exact ⟨fun id ht hi => Set.disjoint_left.1 disj1 hi ht, bij, bij1⟩
      have agreeOld : ∀ id, tids id → f1 id = f id := by
        intro id member
        have absent : ¬ ids1 id := fun present => Set.disjoint_left.1 disj1 present member
        simp [f1, extendBij, absent]
      have oldEquiv := equivTrans _ _ _ (equivRemapAgree f1 f tids env agreeOld envBound) equiv
      have combinedEquiv : tenvEquiv (remapTenv f1 (extendDecTenv env1 env))
          (extendDecTenv mapped1 mapped) := by
        rw [remapTenvExtendDecTenv]
        exact equivExtend _ _ _ _ equiv1 oldEquiv
      obtain ⟨g2, mapped2, bound2, prim2, finite2, bij2, canon2, equiv2⟩ :=
        ih2 allIds f1 (n + (show Set Nat from ids1).ncard) (extendDecTenv mapped1 mapped)
          ⟨extraTrue, disj2, boundEnv, bijAll, primAll, good1, combinedEquiv⟩
      have disj12 : Disjoint (show Set Nat from ids1) (show Set Nat from ids2) := by
        apply Set.disjoint_left.2
        intro id h1 h2
        exact distinct id h1 h2
      have cardUnion : (show Set Nat from unionTypeIds ids1 ids2).ncard =
          (show Set Nat from ids1).ncard + (show Set Nat from ids2).ncard :=
        disjointCardUnion _ _ ⟨finite1, finite2, disj12⟩
      refine ⟨extendBij g g2 ids2 (show Set Nat from ids1).ncard, (extendDecTenv mapped2 mapped1), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change setTidsTenv (tids ∪ ((show Set Nat from ids1) ∪ (show Set Nat from ids2)) : Set Nat) (extendDecTenv env2 env1)
        have unionEq : allIds ∪ (show Set Nat from ids2) =
            tids ∪ ((show Set Nat from ids1) ∪ (show Set Nat from ids2)) := by
          exact Set.union_assoc tids (show Set Nat from ids1) (show Set Nat from ids2)
        rw [← unionEq]
        apply setTidsTenvExtendDecTenv ids2 env1 allIds env2
        refine ⟨bound2, ?_⟩
        exact setTidsTenvMono allIds env1 (allIds ∪ (show Set Nat from ids2) : Set Nat)
          ⟨bound1, fun id member => Or.inl member⟩
      · intro id member
        change (ids1 id ∨ ids2 id) ↔ false = true
        have h1 := prim1 id member
        have h2 := prim2 id member
        simp only [Bool.false_eq_true, iff_false] at h1 h2 ⊢
        intro present
        rcases present with present | present
        · exact h1 present
        · exact h2 present
      · exact finite1.union finite2
      · have combined := bijExtendBij (show Set Nat from ids1) (show Set Nat from ids2)
          g g2 (show Set Nat from ids1).ncard
          ⟨distinct, bij1, bij2⟩
        change Set.BijOn (extendBij g g2 ids2 (show Set Nat from ids1).ncard)
          (fun id => ids1 id ∨ ids2 id) (fun id => id < (show Set Nat from unionTypeIds ids1 ids2).ncard)
        rw [cardUnion]
        exact combined
      · rw [cardUnion]
        exact TypeDsCanon.cons n mapped d ds mapped1 mapped2 _ _ canon1 canon2
      · have comp : extendBij f (extendBij g g2 ids2 (show Set Nat from ids1).ncard)
            (unionTypeIds ids1 ids2) n =
            extendBij f1 g2 ids2 (n + (show Set Nat from ids1).ncard) := by
          exact (extendBijCompose f g g2 ids1 ids2 n (show Set Nat from ids1).ncard).symm
        rw [remapTenvExtendDecTenv, comp]
        have agreeFirst : ∀ id, allIds id → extendBij f1 g2 ids2 (n + (show Set Nat from ids1).ncard) id = f1 id := by
          intro id member
          have absent : ¬ ids2 id := fun present => Set.disjoint_left.1 disj2 present member
          simp [extendBij, absent]
        have firstEquiv := equivTrans _ _ _
          (equivRemapAgree _ f1 allIds env1 agreeFirst bound1) equiv1
        exact equivExtend _ _ _ _ equiv2 firstEquiv
    case nil =>
      intro env
      change dsGoal extra env [] (∅ : Set Nat) _
      intro tids f n mapped h
      refine ⟨id, ⟨Flapjack.NamespaceHOL.nsEmpty, Flapjack.NamespaceHOL.nsEmpty,
        Flapjack.NamespaceHOL.nsEmpty⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setTidsTenv, Flapjack.NamespaceHOL.nsAll,
          Flapjack.NamespaceHOL.nsLookup_nsEmpty]
      · intro _ _
        change False ↔ false = true
        simp
      · exact Set.finite_empty
      · refine ⟨?_, ?_, ?_⟩
        · intro _ absent
          exact False.elim absent
        · intro _ absent
          exact False.elim absent
        · intro _ bound
          change _ < (∅ : Set Nat).ncard at bound
          simp at bound
      · simpa using TypeDsCanon.nil n mapped
      · simpa [remapTenv, Flapjack.NamespaceHOL.nsMap, Flapjack.NamespaceHOL.nsEmpty] using
          tenvEquivRefl ⟨Flapjack.NamespaceHOL.nsEmpty, Flapjack.NamespaceHOL.nsEmpty,
            Flapjack.NamespaceHOL.nsEmpty⟩
    all_goals exact typed

end Flapjack.Compiler.Inference.TypeDCanon
