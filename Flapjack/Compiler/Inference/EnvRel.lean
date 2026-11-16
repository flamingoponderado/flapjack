module

public import Flapjack.Compiler.Inference.InferProps
public import Flapjack.TypeSystemHOL.Declarations

@[expose] public section

/-! Conversions used by the inference/declarative environment relation. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

mutual
/-- Inference-to-declarative conversion. HOL specifies only the de Bruijn and
    application clauses; the unification-variable case is an arbitrary value. -/
noncomputable def convertT : InferT → SemanticT
  | .varDb n => .varDb n
  | .app ts tc => .app (convertTList ts) tc
  | .uvar _ => by
      letI : Nonempty SemanticT := ⟨.varDb 0⟩
      exact Flapjack.holArb SemanticT
termination_by t => sizeOf t

/-- Structural list recursion for the source MAP clause. -/
noncomputable def convertTList : List InferT → List SemanticT
  | [] => []
  | t :: ts => convertT t :: convertTList ts
termination_by ts => sizeOf ts
end

private theorem convertTListMap (ts : List InferT) : convertTList ts = ts.map convertT := by
  induction ts with
  | nil => simp [convertTList]
  | cons t ts ih => simp [convertTList, ih]

/-- The complete source equations; HOL imposes no unification-variable clause. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "convert_t_def"]
theorem convertTEqn :
    (∀ n, convertT (.varDb n) = .varDb n) ∧
    (∀ ts tc, convertT (.app ts tc) = .app (ts.map convertT) tc) := by
  constructor
  · intro n; simp [convertT]
  · intro ts tc; simp [convertT, convertTListMap]

mutual
/-- Structural induction for closed declarative type conversion. -/
private theorem convertUnconvertType (t : SemanticT) (n : Nat)
    (h : checkFreevars n [] t = true) : convertT (unconvertT t) = t := by
  cases t with
  | var name => simp [checkFreevars] at h
  | varDb k => simp [unconvertT, convertT]
  | app ts tc =>
    have hl : checkFreevarsList n [] ts = true := by simpa [checkFreevars] using h
    simp [unconvertT, convertT, convertUnconvertList ts n hl]
termination_by sizeOf t

/-- List induction for closed declarative type conversion. -/
private theorem convertUnconvertList (ts : List SemanticT) (n : Nat)
    (h : checkFreevarsList n [] ts = true) : convertTList (unconvertTList ts) = ts := by
  cases ts with
  | nil => simp [convertTList, unconvertTList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at h
    simp [unconvertTList, convertTList, convertUnconvertType t n h.1,
      convertUnconvertList ts n h.2]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "check_freevars_empty_convert_unconvert_id"]
theorem checkFreevarsEmptyConvertUnconvertId (t : SemanticT) (n : Nat)
    (h : checkFreevars n [] t = true) : convertT (unconvertT t) = t :=
  convertUnconvertType t n h

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "tenv_to_ienv_def"]
noncomputable def tenvToIenv (env : TypeEnv) : Infer.Env :=
  ⟨nsMap (fun entry => (entry.1, unconvertT entry.2)) env.v, env.c, env.t⟩

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "tenv_to_ienv_lift"]
theorem tenvToIenvLift (mn : Flapjack.Basis.Pure.MlString.MlString) (tenv : TypeEnv) :
    tenvToIenv (tenvLift mn tenv) = Infer.liftIenv mn (tenvToIenv tenv) := by
  cases tenv
  simp [tenvToIenv, tenvLift, Infer.liftIenv, nsLift, nsMap]

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "tenv_to_ienv_extend"]
theorem tenvToIenvExtend (tenv1 tenv2 : TypeEnv) :
    tenvToIenv (extendDecTenv tenv2 tenv1) =
      Infer.extendDecIenv (tenvToIenv tenv2) (tenvToIenv tenv1) := by
  cases tenv1 with
  | mk v1 c1 t1 =>
    cases tenv2 with
    | mk v2 c2 t2 =>
      cases v1 with
      | bind values1 modules1 =>
        cases v2 with
        | bind values2 modules2 =>
          simp [tenvToIenv, extendDecTenv, Infer.extendDecIenv, nsAppend, nsMap, List.map_append]

mutual
/-- Closed declarative types convert to inference types with no unification variables.
    The source also quantifies an unused polymorphic `z`; it is vacuous in
    both premise and conclusion. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "check_freevars_to_check_t"]
theorem checkFreevarsToCheckT (t : SemanticT) (n : Nat)
    (h : checkFreevars n [] t = true) :
    Infer.checkT n (fun _ => False) (unconvertT t) := by
  cases t with
  | var name => simp [checkFreevars] at h
  | varDb k => simpa [checkFreevars, unconvertT] using h
  | app ts name =>
    have hl : checkFreevarsList n [] ts = true := by simpa [checkFreevars] using h
    simpa [unconvertT] using checkFreevarsListToCheckT ts n hl
termination_by sizeOf t

/-- Structural list induction for the source type conversion theorem. -/
private theorem checkFreevarsListToCheckT (ts : List SemanticT) (n : Nat)
    (h : checkFreevarsList n [] ts = true) :
    Infer.checkTList n (fun _ => False) (unconvertTList ts) := by
  cases ts with
  | nil => simp [unconvertTList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at h
    simp only [unconvertTList, Infer.checkTList_cons]
    exact ⟨checkFreevarsToCheckT t n h.1, checkFreevarsListToCheckT ts n h.2⟩
termination_by sizeOf ts
end

mutual
/-- Structural induction for the source empty-substitution theorem. -/
private theorem inferTypeSubstNilType (t : SemanticT) (n : Nat)
    (h : checkFreevars n [] t = true) : Infer.inferTypeSubst [] t = unconvertT t := by
  cases t with
  | var name => simp [checkFreevars] at h
  | varDb k => simp [Infer.inferTypeSubst, unconvertT]
  | app ts name =>
    have hl : checkFreevarsList n [] ts = true := by simpa [checkFreevars] using h
    simp [Infer.inferTypeSubst, unconvertT, inferTypeSubstNilList ts n hl]
termination_by sizeOf t

/-- List recursion used by the empty-substitution type induction. -/
private theorem inferTypeSubstNilList (ts : List SemanticT) (n : Nat)
    (h : checkFreevarsList n [] ts = true) :
    Infer.inferTypeSubstList [] ts = unconvertTList ts := by
  cases ts with
  | nil => simp [Infer.inferTypeSubstList, unconvertTList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at h
    simp [Infer.inferTypeSubstList, unconvertTList,
      inferTypeSubstNilType t n h.1, inferTypeSubstNilList ts n h.2]
termination_by sizeOf ts
end

/-- Empty named substitution agrees with unconvert on closed types and lists. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "infer_type_subst_nil"]
theorem inferTypeSubstNil (n : Nat) :
    (∀ t, checkFreevars n [] t = true → Infer.inferTypeSubst [] t = unconvertT t) ∧
    (∀ ts : List SemanticT, (∀ t ∈ ts, checkFreevars n [] t = true) →
      ts.map (Infer.inferTypeSubst []) = ts.map unconvertT) := by
  constructor
  · exact fun t h => inferTypeSubstNilType t n h
  · intro ts h
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [inferTypeSubstNilType t n h.1, ih h.2]

/-- Lookup in the empty local type environment always fails. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "lookup_varE_empty"]
theorem lookupVarEEmpty (id : Ident Flapjack.Basis.Pure.MlString.MlString
    Flapjack.Basis.Pure.MlString.MlString) : lookupVarE id .empty = none := by
  cases id <;> rfl

end Flapjack.Compiler.Inference.EnvRel
