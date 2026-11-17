module

public import Flapjack.Compiler.Inference.InferEComplete
public import Flapjack.Compiler.Inference.InferProps.Freevars
public import Flapjack.Misc.ListLookup

@[expose] public section

/-! Checks for named substitution in inference types. -/
namespace Flapjack.Compiler.Inference.InferEComplete
open Flapjack Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.Infer Flapjack.Basis.Pure.MlString

mutual
private theorem substCheck (t : SemanticT) (n : Nat) (names : List MlString) (values : List InferT)
    (lengths : values.length = names.length) (checks : ∀ x ∈ values, checkT n (fun _ => False) x)
    (free : checkFreevars n names t = true) :
    checkT n (fun _ => False) (inferTypeSubst (names.zip values) t) := by
  cases t with
  | var name =>
    have mem : name ∈ names := by simpa [checkFreevars] using free
    obtain ⟨value, found⟩ := Flapjack.Misc.lookupZipExists names values lengths.symm name mem
    obtain ⟨before, after, zipped, _⟩ := List.lookup_eq_some_iff.mp found
    have pairMem : (name, value) ∈ names.zip values := by rw [zipped]; simp
    have valMem : value ∈ values := (List.of_mem_zip pairMem).2
    simpa [inferTypeSubst, found] using checks value valMem
  | varDb index =>
    have bound : index < n := by simpa [checkFreevars] using free
    simpa [inferTypeSubst] using bound
  | app ts id =>
    have all : checkFreevarsList n names ts = true := by simpa [checkFreevars] using free
    simpa [inferTypeSubst] using substCheckList ts n names values lengths checks all
termination_by sizeOf t

private theorem substCheckList (ts : List SemanticT) (n : Nat) (names : List MlString) (values : List InferT)
    (lengths : values.length = names.length) (checks : ∀ x ∈ values, checkT n (fun _ => False) x)
    (free : checkFreevarsList n names ts = true) :
    checkTList n (fun _ => False) (inferTypeSubstList (names.zip values) ts) := by
  cases ts with
  | nil => simp [inferTypeSubstList]
  | cons t ts =>
    simp only [checkFreevarsList, Bool.and_eq_true] at free
    simp only [inferTypeSubstList, checkTList_cons]
    exact ⟨substCheck t n names values lengths checks free.1,
      substCheckList ts n names values lengths checks free.2⟩
termination_by sizeOf ts
end

/-- Checked substitutions preserve checks on types and type lists. -/
@[hol "cakeml/compiler/inference/proofs/infer_eCompleteScript.sml" "infer_type_subst_check_t_less"]
theorem inferTypeSubstCheckTLess (values : List InferT) (names : List MlString) (n : Nat) :
    values.length = names.length ∧ (∀ x ∈ values, checkT n (fun _ => False) x) →
      (∀ t, checkFreevars n names t = true → checkT n (fun _ => False) (inferTypeSubst (names.zip values) t)) ∧
      (∀ (ts : List SemanticT), ts.all (checkFreevars n names) = true →
        ∀ x ∈ ts.map (inferTypeSubst (names.zip values)), checkT n (fun _ => False) x) := by
  intro ⟨lengths, checks⟩
  constructor
  · intro t free
    exact substCheck t n names values lengths checks free
  · intro ts free x mem
    obtain ⟨t, member, rfl⟩ := List.mem_map.mp mem
    exact substCheck t n names values lengths checks (List.all_eq_true.mp free t member)
end Flapjack.Compiler.Inference.InferEComplete
