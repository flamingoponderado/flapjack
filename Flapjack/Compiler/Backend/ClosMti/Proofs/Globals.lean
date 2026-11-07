import Flapjack.Compiler.Backend.ClosMti.Proofs.Syntactic
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals

/-! Global-write and closure-safety invariants for argument collection. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosProps
open Flapjack.Compiler.Backend.FlatProps (unionGlobalBag)

/-- Collecting function arguments preserves the global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_args_preserves_set_globals"]
theorem collectArgs_preserves_setGlobals (maxApp count : Nat) (expression : Exp)
    (arity : Nat) (body : Exp) (run : collectArgs maxApp count expression = (arity, body)) :
    setGlobals body = setGlobals expression := by
  cases expression with
  | fn name location vars n inner =>
    cases location with
    | some location => simp only [collectArgs, Prod.mk.injEq] at run; obtain ⟨rfl, rfl⟩ := run; rfl
    | none =>
      cases vars with
      | some vars => simp only [collectArgs, Prod.mk.injEq] at run; obtain ⟨rfl, rfl⟩ := run; rfl
      | none =>
        simp only [collectArgs] at run
        split at run
        · simpa [setGlobals] using collectArgs_preserves_setGlobals maxApp (count + n) inner arity body run
        · cases run; rfl
  | _ => simp only [collectArgs, Prod.mk.injEq] at run; obtain ⟨rfl, rfl⟩ := run; rfl
termination_by sizeOf expression

/-- Collecting function arguments preserves closure safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_args_preserves_esgc_free"]
theorem collectArgs_preserves_esgcFree (maxApp count : Nat) (expression : Exp)
    (arity : Nat) (body : Exp)
    (premises : collectArgs maxApp count expression = (arity, body) ∧ esgcFree expression) :
    esgcFree body := by
  obtain ⟨run, valid⟩ := premises
  cases expression with
  | fn name location vars n inner =>
    simp only [esgcFree] at valid
    apply setGlobalsEmptyEsgcFree
    have same : setGlobals body = setGlobals inner := by
      simpa [setGlobals] using collectArgs_preserves_setGlobals maxApp count (.fn name location vars n inner) arity body run
    exact same.trans valid
  | _ =>
    simp only [collectArgs, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact valid

/-- Collecting applications preserves the combined global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_apps_preserves_set_globals"]
theorem collectApps_preserves_setGlobals (maxApp : Nat) (args : List Exp) (expression : Exp)
    (collected : List Exp) (head : Exp)
    (run : collectApps maxApp args expression = (collected, head)) :
    unionGlobalBag (elistGlobals args) (setGlobals expression) =
      unionGlobalBag (elistGlobals collected) (setGlobals head) := by
  cases expression with
  | app trace location inner more =>
    cases location with
    | some location =>
      simp only [collectApps, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      rfl
    | none =>
      simp only [collectApps] at run
      split at run
      · have ih := collectApps_preserves_setGlobals maxApp (args ++ more) inner collected head run
        rw [← ih, elistGlobals_append]
        simp only [setGlobals]
        funext key
        simp [unionGlobalBag, Flapjack.bagUnion, Nat.add_assoc, Nat.add_comm]
      · cases run
        rfl
  | _ =>
    simp only [collectApps, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    rfl
termination_by sizeOf expression

/-- Collecting applications preserves closure safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_apps_preserves_esgc_free"]
theorem collectApps_preserves_esgcFree (maxApp : Nat) (args : List Exp) (expression : Exp)
    (collected : List Exp) (head : Exp)
    (premises : collectApps maxApp args expression = (collected, head) ∧
      (∀ e ∈ args, esgcFree e) ∧ esgcFree expression) :
    (∀ e ∈ collected, esgcFree e) ∧ esgcFree head := by
  obtain ⟨run, argsValid, valid⟩ := premises
  cases expression with
  | app trace location inner more =>
    cases location with
    | some location =>
      simp only [collectApps, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨argsValid, valid⟩
    | none =>
      simp only [collectApps] at run
      split at run
      · simp only [esgcFree] at valid
        have moreValid : ∀ e ∈ more, esgcFree e := (esgcFreeList_iff more).mp valid.2
        have allValid : ∀ e ∈ args ++ more, esgcFree e := by
          intro e member
          rcases List.mem_append.mp member with member | member
          · exact argsValid e member
          · exact moreValid e member
        exact collectApps_preserves_esgcFree maxApp (args ++ more) inner collected head ⟨run, allValid, valid.1⟩
      · cases run
        exact ⟨argsValid, valid⟩
  | _ =>
    simp only [collectApps, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨argsValid, valid⟩
termination_by sizeOf expression
end Flapjack.Compiler.Backend.ClosMti
