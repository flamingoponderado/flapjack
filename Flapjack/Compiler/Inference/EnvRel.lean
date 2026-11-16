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

mutual
/-- Structural induction for closed inference-type conversion. -/
private theorem closedConvertType (t : InferT) (n : Nat)
    (h : Infer.checkT n (fun _ => False) t) :
    checkFreevars n [] (convertT t) = true ∧ unconvertT (convertT t) = t := by
  cases t with
  | uvar v => simp at h
  | varDb v =>
    constructor
    · simpa [convertT, checkFreevars] using h
    · simp [convertT, unconvertT]
  | app ts tc =>
    have hl : Infer.checkTList n (fun _ => False) ts := (Infer.checkT_app n tc _ ts).mp h
    have result := closedConvertList ts n hl
    constructor
    · simpa [convertT, checkFreevars] using result.1
    · simpa [convertT, unconvertT] using congrArg (fun xs => InferT.app xs tc) result.2
termination_by sizeOf t

/-- List induction for the closed inference-type conversion. -/
private theorem closedConvertList (ts : List InferT) (n : Nat)
    (h : Infer.checkTList n (fun _ => False) ts) :
    checkFreevarsList n [] (convertTList ts) = true ∧
      unconvertTList (convertTList ts) = ts := by
  cases ts with
  | nil => simp [convertTList, checkFreevarsList, unconvertTList]
  | cons t ts =>
    have hs := (Infer.checkTList_cons n _ t ts).mp h
    have first := closedConvertType t n hs.1
    have rest := closedConvertList ts n hs.2
    simp [convertTList, checkFreevarsList, unconvertTList, first.1, first.2, rest.1, rest.2]
termination_by sizeOf ts
end

/-- The source has an unused universally quantified set `n`; it is omitted. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "check_t_to_check_freevars"]
theorem checkTToCheckFreevars (tvs : Nat) (t : InferT)
    (h : Infer.checkT tvs (fun _ => False) t) : checkFreevars tvs [] (convertT t) = true :=
  (closedConvertType t tvs h).1

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "check_convert_freevars"]
theorem checkConvertFreevars (tvs : Nat) (uvs : Nat → Prop) (t : InferT)
    (checked : Infer.checkT tvs uvs t) (empty : uvs = (fun _ => False)) :
    checkFreevars tvs [] (convertT t) = true := by
  subst uvs
  exact (closedConvertType t tvs checked).1

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "check_t_empty_unconvert_convert_id"]
theorem checkTEmptyUnconvertConvertId (t : InferT) (n : Nat)
    (h : Infer.checkT n (fun _ => False) t) : unconvertT (convertT t) = t :=
  (closedConvertType t n h).2

mutual
/-- Structural induction for the source conversion-shift theorem. -/
private theorem convertIncType (t : InferT) (bound amount : Nat)
    (h : Infer.checkT bound (fun _ => False) t) :
    convertT (Infer.inferDeBruijnInc amount t) = deBruijnInc 0 amount (convertT t) := by
  cases t with
  | uvar v => simp at h
  | varDb v => simp [Infer.inferDeBruijnInc, convertT, deBruijnInc]
  | app ts tc =>
    have hl := (Infer.checkT_app bound tc _ ts).mp h
    simp [Infer.inferDeBruijnInc, convertT, deBruijnInc, convertIncList ts bound amount hl]
termination_by sizeOf t

/-- List induction for the conversion-shift theorem. -/
private theorem convertIncList (ts : List InferT) (bound amount : Nat)
    (h : Infer.checkTList bound (fun _ => False) ts) :
    convertTList (Infer.inferDeBruijnIncList amount ts) =
      deBruijnIncList 0 amount (convertTList ts) := by
  cases ts with
  | nil => simp [Infer.inferDeBruijnIncList, convertTList, deBruijnIncList]
  | cons t ts =>
    have hs := (Infer.checkTList_cons bound _ t ts).mp h
    simp [Infer.inferDeBruijnIncList, convertTList, deBruijnIncList,
      convertIncType t bound amount hs.1, convertIncList ts bound amount hs.2]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "convert_inc"]
theorem convertInc (t : InferT) (tvs bound : Nat)
    (h : Infer.checkT bound (fun _ => False) t) :
    convertT (Infer.inferDeBruijnInc tvs t) = deBruijnInc 0 tvs (convertT t) :=
  convertIncType t bound tvs h

mutual
/-- Structural induction for shifting beyond the free-variable bound. -/
private theorem incConvertType (t : InferT) (bound amount : Nat)
    (h : Infer.checkT bound (fun _ => False) t) :
    deBruijnInc bound amount (convertT t) = convertT t := by
  cases t with
  | uvar v => simp at h
  | varDb v =>
    have hv : v < bound := by simpa using h
    simp [convertT, deBruijnInc, hv]
  | app ts tc =>
    have hl := (Infer.checkT_app bound tc _ ts).mp h
    simp [convertT, deBruijnInc, incConvertList ts bound amount hl]
termination_by sizeOf t

/-- List induction for shifting beyond the free-variable bound. -/
private theorem incConvertList (ts : List InferT) (bound amount : Nat)
    (h : Infer.checkTList bound (fun _ => False) ts) :
    deBruijnIncList bound amount (convertTList ts) = convertTList ts := by
  cases ts with
  | nil => simp [convertTList, deBruijnIncList]
  | cons t ts =>
    have hs := (Infer.checkTList_cons bound _ t ts).mp h
    simp [convertTList, deBruijnIncList, incConvertType t bound amount hs.1,
      incConvertList ts bound amount hs.2]
termination_by sizeOf ts
end

@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "inc_convert_t"]
theorem incConvertT :
    (∀ (t : InferT) bound amount, Infer.checkT bound (fun _ => False) t →
      deBruijnInc bound amount (convertT t) = convertT t) ∧
    (∀ (ts : List InferT) bound amount,
      (∀ t ∈ ts, Infer.checkT bound (fun _ => False) t) →
      ts.map (fun t => deBruijnInc bound amount (convertT t)) = ts.map convertT) := by
  constructor
  · intro t bound amount h
    exact incConvertType t bound amount h
  · intro ts bound amount h
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [incConvertType t bound amount h.1, ih h.2]

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

mutual
/-- Structural induction for converting declarative substitutions. -/
private theorem unconvertDbSubstType (t : SemanticT) (subst : List SemanticT) (bound : Nat)
    (h : checkFreevars bound [] t = true) :
    unconvertT (deBruijnSubst 0 subst t) =
      Infer.inferDeBruijnSubst (subst.map unconvertT) (unconvertT t) := by
  cases t with
  | var name => simp [checkFreevars] at h
  | varDb k =>
    by_cases hk : k < subst.length
    · simp [deBruijnSubst, unconvertT, Infer.inferDeBruijnSubst, hk]
    · simp [deBruijnSubst, unconvertT, Infer.inferDeBruijnSubst, hk]
  | app ts tc =>
    have hl : checkFreevarsList bound [] ts = true := by simpa [checkFreevars] using h
    simp [deBruijnSubst, unconvertT, Infer.inferDeBruijnSubst,
      unconvertDbSubstList ts subst bound hl]
termination_by sizeOf t

/-- Structural list induction for converting declarative substitutions. -/
private theorem unconvertDbSubstList (ts : List SemanticT) (subst : List SemanticT) (bound : Nat)
    (h : checkFreevarsList bound [] ts = true) :
    unconvertTList (deBruijnSubstList 0 subst ts) =
      Infer.inferDeBruijnSubstList (subst.map unconvertT) (unconvertTList ts) := by
  cases ts with
  | nil => simp [deBruijnSubstList, unconvertTList, Infer.inferDeBruijnSubstList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at h
    simp [deBruijnSubstList, unconvertTList, Infer.inferDeBruijnSubstList,
      unconvertDbSubstType t subst bound h.1, unconvertDbSubstList ts subst bound h.2]
termination_by sizeOf ts
end

/-- The source also quantifies an unused polymorphic `fvs`; it is vacuous. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "unconvert_db_subst"]
theorem unconvertDbSubst (t : SemanticT) (subst : List SemanticT) (bound : Nat)
    (h : checkFreevars bound [] t = true) :
    unconvertT (deBruijnSubst 0 subst t) =
      Infer.inferDeBruijnSubst (subst.map unconvertT) (unconvertT t) :=
  unconvertDbSubstType t subst bound h

mutual
/-- Structural induction used to relate the two de Bruijn substitutions. -/
private theorem deBruijnSubstConvertType (t : InferT) (n : Nat) (subst : List InferT)
    (h : Infer.checkT n (fun _ => False) t) :
    deBruijnSubst 0 (subst.map convertT) (convertT t) =
      convertT (Infer.inferDeBruijnSubst subst t) := by
  cases t with
  | uvar v => simp at h
  | varDb k =>
    by_cases hk : k < subst.length
    · simp [convertT, deBruijnSubst, Infer.inferDeBruijnSubst, hk]
    · simp [convertT, deBruijnSubst, Infer.inferDeBruijnSubst, hk]
  | app ts tc =>
    have hl := (Infer.checkT_app n tc _ ts).mp h
    simp [convertT, deBruijnSubst, Infer.inferDeBruijnSubst,
      deBruijnSubstConvertList ts n subst hl]
termination_by sizeOf t

/-- List recursion for the de Bruijn substitution correspondence. -/
private theorem deBruijnSubstConvertList (ts : List InferT) (n : Nat) (subst : List InferT)
    (h : Infer.checkTList n (fun _ => False) ts) :
    deBruijnSubstList 0 (subst.map convertT) (convertTList ts) =
      convertTList (Infer.inferDeBruijnSubstList subst ts) := by
  cases ts with
  | nil => simp [convertTList, deBruijnSubstList, Infer.inferDeBruijnSubstList]
  | cons t ts =>
    have hs := (Infer.checkTList_cons n _ t ts).mp h
    simp [convertTList, deBruijnSubstList, Infer.inferDeBruijnSubstList,
      deBruijnSubstConvertType t n subst hs.1, deBruijnSubstConvertList ts n subst hs.2]
termination_by sizeOf ts
end

/-- Conversion commutes with de Bruijn substitution for checked types and lists. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "deBruijn_subst_convert"]
theorem deBruijnSubstConvert (n : Nat) (subst : List InferT) :
    (∀ t, Infer.checkT n (fun _ => False) t →
      deBruijnSubst 0 (subst.map convertT) (convertT t) =
        convertT (Infer.inferDeBruijnSubst subst t)) ∧
    (∀ ts : List InferT, (∀ t ∈ ts, Infer.checkT n (fun _ => False) t) →
      ts.map (deBruijnSubst 0 (subst.map convertT) ∘ convertT) =
        ts.map (convertT ∘ Infer.inferDeBruijnSubst subst)) := by
  constructor
  · exact fun t h => deBruijnSubstConvertType t n subst h
  · intro ts h
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at h
      simp [deBruijnSubstConvertType t n subst h.1, ih h.2]

/-- Lookup in the empty local type environment always fails. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "lookup_varE_empty"]
theorem lookupVarEEmpty (id : Ident Flapjack.Basis.Pure.MlString.MlString
    Flapjack.Basis.Pure.MlString.MlString) : lookupVarE id .empty = none := by
  cases id <;> rfl

end Flapjack.Compiler.Inference.EnvRel
