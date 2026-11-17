module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant
public import Flapjack.HolArb
public import Flapjack.TypeSoundInvariants
public import Flapjack.NamespaceProps.MapLookup

@[expose] public section

/-! Identifier-set prerequisites for the initial inference environment. -/
namespace Flapjack.Compiler.Inference.InferProps
open Flapjack.Compiler.Inference Flapjack.NamespaceHOL Flapjack.TypeSystemHOL

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "ienv_ok_def"]
def ienvOk (uvars : Nat → Prop) (ienv : Infer.Env) : Prop :=
  Infer.ienvValOk uvars ienv.infV ∧ Flapjack.TypeSoundInvariants.tenvCtorOk ienv.infC ∧
    Flapjack.TypeSoundInvariants.tenvAbbrevOk ienv.infT

mutual
/-- Type identifiers appearing in a declarative type. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "set_tids_def"]
def setTids : SemanticT → Nat → Prop
  | .app ts name => fun id => id = name ∨ setTidsList ts id
  | _ => fun _ => False
termination_by t => sizeOf t

/-- List union for the `BIGUNION` clause of `setTids`; this is local
infrastructure, not a separate HOL declaration. -/
def setTidsList : List SemanticT → Nat → Prop
  | [] => fun _ => False
  | t :: ts => fun id => setTids t id ∨ setTidsList ts id
termination_by ts => sizeOf ts
end

mutual
/-- Rename every type identifier in a declarative type. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "ts_tid_rename_def"]
def tsTidRename (f : Nat → Nat) : SemanticT → SemanticT
  | .app ts id => .app (tsTidRenameList f ts) (f id)
  | t => t
termination_by t => sizeOf t

/-- List traversal for the source renaming's `MAP` clause. -/
def tsTidRenameList (f : Nat → Nat) : List SemanticT → List SemanticT
  | [] => []
  | t :: ts => tsTidRename f t :: tsTidRenameList f ts
termination_by ts => sizeOf ts
end

/-- The recursive traversal is the source's list map. -/
theorem tsTidRenameList_eq_map (f : Nat → Nat) (ts : List SemanticT) :
    tsTidRenameList f ts = ts.map (tsTidRename f) := by
  induction ts with
  | nil => simp [tsTidRenameList]
  | cons t ts ih => simp [tsTidRenameList, ih]

mutual
private theorem tsTidRenameIdApply (t : SemanticT) : tsTidRename id t = t := by
  cases t with
  | var name => simp [tsTidRename]
  | varDb n => simp [tsTidRename]
  | app ts name => simp [tsTidRename, tsTidRenameIdList ts]
termination_by sizeOf t

private theorem tsTidRenameIdList (ts : List SemanticT) : tsTidRenameList id ts = ts := by
  cases ts with
  | nil => simp [tsTidRenameList]
  | cons t ts => simp [tsTidRenameList, tsTidRenameIdApply t, tsTidRenameIdList ts]
termination_by sizeOf ts
end

/-- Renaming with the identity function leaves every type unchanged. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "ts_tid_rename_I"]
theorem tsTidRenameId : tsTidRename id = id := by
  funext t
  exact tsTidRenameIdApply t

mutual
/-- Renaming maps precisely the set of identifiers occurring in a type. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "set_tids_ts_tid_rename"]
theorem setTidsTsTidRename (f : Nat → Nat) (t : SemanticT) :
    setTids (tsTidRename f t) = (fun id => ∃ old, setTids t old ∧ f old = id) := by
  funext id
  apply propext
  cases t with
  | var name => simp [tsTidRename, setTids]
  | varDb n => simp [tsTidRename, setTids]
  | app ts name =>
    simp only [tsTidRename, setTids, setTidsTsTidRenameList f ts]
    constructor
    · rintro (h | ⟨old, hold, heq⟩)
      · exact ⟨name, Or.inl rfl, h.symm⟩
      · exact ⟨old, Or.inr hold, heq⟩
    · rintro ⟨old, (h | h), heq⟩
      · subst old
        exact Or.inl heq.symm
      · exact Or.inr ⟨old, h, heq⟩
termination_by sizeOf t

private theorem setTidsTsTidRenameList (f : Nat → Nat) (ts : List SemanticT) :
    setTidsList (tsTidRenameList f ts) =
      (fun id => ∃ old, setTidsList ts old ∧ f old = id) := by
  funext id
  apply propext
  cases ts with
  | nil => simp [tsTidRenameList, setTidsList]
  | cons t ts =>
    simp only [tsTidRenameList, setTidsList, setTidsTsTidRename f t,
      setTidsTsTidRenameList f ts]
    constructor
    · rintro (⟨old, h, heq⟩ | ⟨old, h, heq⟩)
      · exact ⟨old, Or.inl h, heq⟩
      · exact ⟨old, Or.inr h, heq⟩
    · rintro ⟨old, (h | h), heq⟩
      · exact Or.inl ⟨old, h, heq⟩
      · exact Or.inr ⟨old, h, heq⟩
termination_by sizeOf ts
end

/-- Rename type identifiers throughout a declarative environment. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "remap_tenv_def"]
def remapTenv (f : Nat → Nat) (tenv : TypeEnv) : TypeEnv :=
  ⟨nsMap (fun entry => (entry.1, tsTidRename f entry.2)) tenv.v,
   nsMap (fun entry => (entry.1, entry.2.1.map (tsTidRename f), f entry.2.2)) tenv.c,
   nsMap (fun entry => (entry.1, tsTidRename f entry.2)) tenv.t⟩

/-- Identity renaming preserves every declarative environment. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "remap_tenv_I"]
theorem remapTenvId : remapTenv id = id := by
  funext tenv
  cases tenv
  simp [remapTenv, tsTidRenameId, Prod.eta]
  exact ⟨nsMapId _, nsMapId _, nsMapId _⟩

mutual
/-- Convert semantic types back to inference types, retaining HOL's `ARB`
for named type variables. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "unconvert_t_def"]
noncomputable def unconvertT : SemanticT → InferT
  | .varDb n => .varDb n
  | .app ts name => .app (unconvertTList ts) name
  | .var _ => .uvar (Flapjack.holArb Nat)
termination_by t => sizeOf t

/-- List traversal for the `MAP` clause of `unconvertT`; this is local
infrastructure, not a separate HOL declaration. -/
noncomputable def unconvertTList : List SemanticT → List InferT
  | [] => []
  | t :: ts => unconvertT t :: unconvertTList ts
termination_by ts => sizeOf ts
end

mutual
/-- Type identifiers appearing in an inference type, as a set predicate. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "inf_set_tids_def"]
def infSetTids : InferT → Nat → Prop
  | .app ts name => fun id => id = name ∨ infSetTidsList ts id
  | _ => fun _ => False
termination_by t => sizeOf t

/-- The union over a list of types in the `BIGUNION` clause; this is local
infrastructure, not a separate HOL declaration. -/
def infSetTidsList : List InferT → Nat → Prop
  | [] => fun _ => False
  | t :: ts => fun id => infSetTids t id ∨ infSetTidsList ts id
termination_by ts => sizeOf ts
end

mutual
/-- Converting a declarative type preserves its complete type-identifier set. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "inf_set_tids_unconvert"]
theorem infSetTidsUnconvert (t : SemanticT) : infSetTids (unconvertT t) = setTids t := by
  cases t with
  | var name => simp [unconvertT, infSetTids, setTids]
  | varDb n => simp [unconvertT, infSetTids, setTids]
  | app ts name =>
    funext id
    apply propext
    simp only [unconvertT, infSetTids, setTids]
    rw [infSetTidsUnconvertList ts]
termination_by sizeOf t

/-- List induction used to prove the original identifier-set equality. -/
private theorem infSetTidsUnconvertList (ts : List SemanticT) :
    infSetTidsList (unconvertTList ts) = setTidsList ts := by
  cases ts with
  | nil => simp [unconvertTList, infSetTidsList, setTidsList]
  | cons t ts =>
    funext id
    apply propext
    simp only [unconvertTList, infSetTidsList, setTidsList]
    rw [infSetTidsUnconvert t, infSetTidsUnconvertList ts]
termination_by sizeOf ts
end

/-- Every identifier appearing in the type belongs to the given set. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "set_tids_subset_def"]
def setTidsSubset (tids : Nat → Prop) (t : SemanticT) : Prop :=
  ∀ id, setTids t id → tids id

/-- The primitive type identifiers are either all included or all excluded. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "prim_tids_def"]
def primTids (contain : Bool) (tids : Nat → Prop) : Prop :=
  ∀ id ∈ TlistNum :: TboolNum :: primTypeNums, tids id ↔ contain = true

/-- Any count at least the initial identifier includes all primitive IDs. -/
@[hol "cakeml/compiler/inference/inferPropsScript.sml" "start_type_id_prim_tids_count"]
theorem startTypeIdPrimTidsCount (n : Nat) :
    Infer.startTypeId ≤ n → primTids true (fun id => id < n) := by
  intro bound id member
  simp only [iff_true]
  simp [primTypeNums, TlistNum, TboolNum, TarrayNum, TcharNum, TexnNum, TfnNum,
    TintNum, TrefNum, TstringNum, TtupNum, TvectorNum, Tword64Num, Tword8Num,
    Tword8arrayNum, TdoubleNum] at member
  simp [Infer.startTypeId] at bound
  omega

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "inf_set_tids_subset_def"]
def infSetTidsSubset (tids : Nat → Prop) (t : InferT) : Prop :=
  ∀ id, infSetTids t id → tids id

@[hol "cakeml/compiler/inference/inferPropsScript.sml" "inf_set_tids_ienv_def"]
noncomputable def infSetTidsIenv (tids : Nat → Prop) (ienv : Infer.Env) : Prop :=
  nsAll (fun _ entry => infSetTidsSubset tids (unconvertT entry.2)) ienv.infT ∧
  nsAll (fun _ entry => (∀ t ∈ entry.2.1, infSetTidsSubset tids (unconvertT t)) ∧
    tids entry.2.2) ienv.infC ∧
  nsAll (fun _ entry => infSetTidsSubset tids entry.2) ienv.infV

end Flapjack.Compiler.Inference.InferProps
