module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.Compiler.Inference.Infer.EnvironmentInvariant
public import Flapjack.HolArb
public import Flapjack.TypeSoundInvariants

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
