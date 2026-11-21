module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMti
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! backendProofScript.sml 201-217: closure programs without multi-argument
syntax obey every positive application-arity bound. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack.Compiler.Backend.ClosLang Flapjack.Compiler.Backend.ClosProps

mutual
/-- Flapjack structural induction for one expression; HOL proves the theorem
below with `obeys_max_app_ind` directly. -/
private theorem noMti_obeys (m : Nat) (hm : 0 < m) : ∀ e : Exp, noMti e → obeysMaxApp m e
  | .var .. => fun _ => by simp [obeysMaxApp]
  | .ifThenElse _ a b c => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact ⟨noMti_obeys m hm a h.1, noMti_obeys m hm b h.2.1, noMti_obeys m hm c h.2.2⟩
  | .let _ xs body => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact ⟨noMtiList_obeys m hm xs h.1, noMti_obeys m hm body h.2⟩
  | .raise _ body => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact noMti_obeys m hm body h
  | .tick _ body => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact noMti_obeys m hm body h
  | .handle _ a b => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact ⟨noMti_obeys m hm a h.1, noMti_obeys m hm b h.2⟩
  | .call .. => fun h => by simp [noMti] at h
  | .app _ _ fn args => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact ⟨by omega, noMti_obeys m hm fn h.2.2.2, noMtiList_obeys m hm args h.2.2.1⟩
  | .fn _ _ _ _ body => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact noMti_obeys m hm body h.2.2.2
  | .letrec _ _ _ fns body => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact ⟨noMtiFuns_obeys m hm fns h.2.2.2, noMti_obeys m hm body h.1⟩
  | .op _ _ args => fun h => by
      simp only [noMti] at h
      simp only [obeysMaxApp]
      exact noMtiList_obeys m hm args h
termination_by e => sizeOf e

private theorem noMtiList_obeys (m : Nat) (hm : 0 < m) :
    ∀ es : List Exp, noMtiList es → obeysMaxAppList m es
  | [] => fun _ => by simp [obeysMaxAppList]
  | e :: es => fun h => by
      simp only [noMtiList] at h
      simp only [obeysMaxAppList]
      exact ⟨noMti_obeys m hm e h.1, noMtiList_obeys m hm es h.2⟩
termination_by es => sizeOf es

private theorem noMtiFuns_obeys (m : Nat) (hm : 0 < m) :
    ∀ fs : List (Nat × Exp), noMtiFuns fs → obeysMaxAppFuns m fs
  | [] => fun _ => by simp [obeysMaxAppFuns]
  | (_, body) :: fs => fun h => by
      simp only [noMtiFuns] at h
      simp only [obeysMaxAppFuns]
      exact ⟨noMti_obeys m hm body h.2.1, noMtiFuns_obeys m hm fs h.2.2⟩
termination_by fs => sizeOf fs
end

/-- Exact HOL `no_mti_IMP_obeys_max_app` (`backendProofScript.sml:201-211`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "no_mti_IMP_obeys_max_app"]
theorem noMti_imp_obeysMaxApp :
    ∀ (m : Nat) (exp : Exp), 0 < m ∧ noMti exp → obeysMaxApp m exp :=
  fun m exp h => noMti_obeys m h.1 exp h.2

/-- HOL `EVERY_no_mti_IMP_obeys_max_app` (`backendProofScript.sml:213-217`).
The captured statement `∀(e3 :α). 0 < m ∧ EVERY no_mti exps ⇒ EVERY
(obeys_max_app m) exps` quantifies `e3` over an independent type variable and
never uses it; HOL types are nonempty, so that quantifier is vacuous and is
omitted here (a Lean quantifier over an empty type would make the statement
trivially true). `EVERY P l` is membership quantification. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "EVERY_no_mti_IMP_obeys_max_app"]
theorem every_noMti_imp_obeysMaxApp (m : Nat) (exps : List Exp) :
    0 < m ∧ (∀ e ∈ exps, noMti e) → ∀ e ∈ exps, obeysMaxApp m e :=
  fun h e he => noMti_imp_obeysMaxApp m e ⟨h.1, h.2 e he⟩

end Flapjack.Compiler.Backend.BackendProof
