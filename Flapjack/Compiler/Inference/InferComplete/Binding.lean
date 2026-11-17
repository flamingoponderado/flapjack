module

public import Flapjack.Compiler.Inference.InferComplete.NamedSubst
public import Flapjack.Misc.FindIndex.Membership
public import Flapjack.Misc.ListEl
public import Flapjack.TypeSysProps.Abbrev

@[expose] public section

/-! Substitution reindexing for inference environment completeness. -/
namespace Flapjack.Compiler.Inference.InferComplete
open Flapjack Flapjack.Misc Flapjack.Basis.Pure.MlString
local instance : Nonempty MlString := ⟨ofString ""⟩

private theorem lookupIndexed (names : List MlString) (key : MlString) (offset : Nat) :
    (names.zip ((List.range' offset names.length).map InferT.varDb)).lookup key =
      (findIndex key names offset).map InferT.varDb := by
  induction names generalizing offset with
  | nil => rfl
  | cons name names ih =>
    by_cases same : name = key
    · subst key; simp [findIndex, List.range']
    · have different : (key == name) = false := by simp [Ne.symm same]
      simpa [findIndex, same, List.range', List.lookup, different] using ih (offset + 1)
private theorem lookupIndex0 (names : List MlString) (key : MlString) :
    (names.zip ((List.range names.length).map InferT.varDb)).lookup key =
      (findIndex key names 0).map InferT.varDb := by
  simpa [List.range_eq_range'] using lookupIndexed names key 0

private theorem namedCase (name : MlString) (fvs fvs' : List MlString) (subst : List InferT) (fallback : Nat)
    (member : name ∈ fvs') (included : ∀ n ∈ fvs', n ∈ fvs) :
    Infer.inferDeBruijnSubst subst
      (Infer.inferTypeSubst (fvs.zip ((List.range fvs.length).map InferT.varDb)) (.var name)) =
    Infer.inferDeBruijnSubst
      ((List.range fvs'.length).map fun n =>
        Infer.inferDeBruijnSubst subst
          (match findIndex (holEl n fvs') fvs 0 with
           | none => .app [] fallback
           | some t => .varDb t))
      (Infer.inferTypeSubst (fvs'.zip ((List.range fvs'.length).map InferT.varDb)) (.var name)) := by
  obtain ⟨i, findI, boundI, elI⟩ := findIndex_mem fvs' name 0 member
  obtain ⟨j, findJ, boundJ, elJ⟩ := findIndex_mem fvs name 0 (included name member)
  simp only [Nat.zero_add] at findI findJ
  simp only [Infer.inferTypeSubst, lookupIndex0, findI, findJ, Option.map_some, Option.getD_some,
    Infer.inferDeBruijnSubst]
  simp [boundI, elI, findJ, Infer.inferDeBruijnSubst]
open Flapjack.TypeSystemHOL

private noncomputable def reindex (fvs fvs' : List MlString) (subst : List InferT) (fallback : Nat) : List InferT :=
  (List.range fvs'.length).map fun n =>
    Infer.inferDeBruijnSubst subst
      (match findIndex (holEl n fvs') fvs 0 with
       | none => .app [] fallback
       | some t => .varDb t)

mutual
private theorem bindingCore (t : SemanticT) (fvs fvs' : List MlString)
    (subst : List InferT) (fallback : Nat)
    (free : checkFreevars 0 fvs' t = true) (included : ∀ n ∈ fvs', n ∈ fvs) :
    Infer.inferDeBruijnSubst subst
      (Infer.inferTypeSubst (fvs.zip ((List.range fvs.length).map InferT.varDb)) t) =
    Infer.inferDeBruijnSubst (reindex fvs fvs' subst fallback)
      (Infer.inferTypeSubst (fvs'.zip ((List.range fvs'.length).map InferT.varDb)) t) := by
  cases t with
  | var name =>
    have member : name ∈ fvs' := by simpa [checkFreevars] using free
    exact namedCase name fvs fvs' subst fallback member included
  | varDb n => simp [checkFreevars] at free
  | app ts id =>
    have all : checkFreevarsList 0 fvs' ts = true := by simpa [checkFreevars] using free
    simp [Infer.inferTypeSubst, Infer.inferDeBruijnSubst,
      bindingListCore ts fvs fvs' subst fallback all included]
termination_by sizeOf t

private theorem bindingListCore (ts : List SemanticT) (fvs fvs' : List MlString)
    (subst : List InferT) (fallback : Nat)
    (free : checkFreevarsList 0 fvs' ts = true) (included : ∀ n ∈ fvs', n ∈ fvs) :
    Infer.inferDeBruijnSubstList subst
      (Infer.inferTypeSubstList (fvs.zip ((List.range fvs.length).map InferT.varDb)) ts) =
    Infer.inferDeBruijnSubstList (reindex fvs fvs' subst fallback)
      (Infer.inferTypeSubstList (fvs'.zip ((List.range fvs'.length).map InferT.varDb)) ts) := by
  cases ts with
  | nil => simp [Infer.inferTypeSubstList, Infer.inferDeBruijnSubstList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at free
    simp [Infer.inferTypeSubstList, Infer.inferDeBruijnSubstList,
      bindingCore t fvs fvs' subst fallback free.1 included,
      bindingListCore ts fvs fvs' subst fallback free.2 included]
termination_by sizeOf ts
end

/-- Reindex substitutions from a contained name list into the enclosing list. -/
@[hol "cakeml/compiler/inference/proofs/inferCompleteScript.sml" "env_rel_binding_lemma2"]
theorem envRelBindingLemma2 (fallback : Nat) (t : SemanticT) (fvs fvs' : List MlString) (subst : List InferT) :
    checkFreevars 0 fvs' t = true ∧ (∀ n ∈ fvs', n ∈ fvs) ∧ fvs'.Nodup →
    Infer.inferDeBruijnSubst subst
      (Infer.inferTypeSubst (fvs.zip ((List.range fvs.length).map InferT.varDb)) t) =
    Infer.inferDeBruijnSubst
      ((List.range fvs'.length).map fun n =>
        Infer.inferDeBruijnSubst subst
          (match findIndex (holEl n fvs') fvs 0 with
           | none => .app [] fallback
           | some t => .varDb t))
      (Infer.inferTypeSubst (fvs'.zip ((List.range fvs'.length).map InferT.varDb)) t) := by
  intro ⟨free, included, _⟩
  exact bindingCore t fvs fvs' subst fallback free included
end Flapjack.Compiler.Inference.InferComplete
