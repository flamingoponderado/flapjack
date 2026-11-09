import Flapjack.Compiler.Backend.ClosToBvl.Layout
import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

/-! Syntactic invariants of the closure-to-BVL entry-point chain. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.ClosProps

/-- Chaining preserves and reflects the function-location predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_every_Fn_SOME" 8596]
theorem chainExps_fnLocationSome_iff (start : Nat) (expressions : List ClosLang.Exp) :
    everyFnLocationSome ((chainExps start expressions).map (fun (_, _, body) => body)) ↔
      everyFnLocationSome expressions := by
  induction expressions generalizing start with
  | nil => simp [chainExps, everyFnLocationSome, fnLocationSomeExp]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps, everyFnLocationSome]
    | cons second tail =>
      have step := ih (start + 1)
      simp [chainExps, everyFnLocationSome, fnLocationSomeExp, step]

/-- Chaining preserves and reflects the function-variable predicate. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_every_Fn_vs_SOME"]
theorem chainExps_fnVarsSome_iff (start : Nat) (expressions : List ClosLang.Exp) :
    everyFnVarsSome ((chainExps start expressions).map (fun (_, _, body) => body)) ↔
      everyFnVarsSome expressions := by
  induction expressions generalizing start with
  | nil => simp [chainExps, everyFnVarsSome, fnVarsSomeExp]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps, everyFnVarsSome]
    | cons second tail =>
      have step := ih (start + 1)
      simp [chainExps, everyFnVarsSome, fnVarsSomeExp, step]

/-- Chaining preserves function-location annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_every_Fn_SOME" 9248]
theorem chainExps_everyFnSome (expressions : List ClosLang.Exp) (start : Nat) :
    everyFnLocationSome expressions →
    everyFnLocationSome ((chainExps start expressions).map (fun (_, _, body) => body)) := by
  exact (chainExps_fnLocationSome_iff start expressions).2

/-- Chaining preserves the source maximum application arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_obeys_max_app"]
theorem chainExps_obeysMaxApp (maxApp : Nat) (expressions : List ClosLang.Exp) (start : Nat) :
    (∀ e ∈ expressions, obeysMaxApp maxApp e) →
    ∀ e ∈ (chainExps start expressions).map (fun (_, _, body) => body), obeysMaxApp maxApp e := by
  induction expressions generalizing start with
  | nil => simp [chainExps, obeysMaxApp, obeysMaxAppList]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps]
    | cons second tail =>
      intro premise
      have head := premise first (by simp)
      have step := ih (start + 1) (fun e member => premise e (by simp [member]))
      simpa [chainExps, obeysMaxApp, obeysMaxAppList] using And.intro head step

/-- Chaining does not introduce label operations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_no_Labels"]
theorem chainExps_noLabels (expressions : List ClosLang.Exp) (start : Nat) :
    (∀ e ∈ expressions, noLabels e) →
    ∀ e ∈ (chainExps start expressions).map (fun (_, _, body) => body), noLabels e := by
  induction expressions generalizing start with
  | nil => simp [chainExps, noLabels, noLabelsList]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps]
    | cons second tail =>
      intro premise
      have head := premise first (by simp)
      have step := ih (start + 1) (fun e member => premise e (by simp [member]))
      simpa [chainExps, noLabels, noLabelsList] using And.intro head step

end Flapjack.Compiler.Backend.ClosToBvl
