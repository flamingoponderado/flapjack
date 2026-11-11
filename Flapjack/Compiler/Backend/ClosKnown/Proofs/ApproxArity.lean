module

public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity

@[expose] public section

/-! Application-arity invariants for known-function approximations. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open Flapjack ClosLang ClosProps

/-- Inlined bodies in an approximation obey the application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "val_approx_obeys_max_app_def"]
def valApproxObeysMaxApp (limit : Nat) : ValApprox → Prop
  | .clos _ _ body _ => obeysMaxApp limit body
  | .tuple _ values => ∀ value ∈ values, valApproxObeysMaxApp limit value
  | _ => True
termination_by a => sizeOf a
decreasing_by
  all_goals
    have := List.sizeOf_lt_of_mem ‹_›
    simp_wf
    omega

/-- Every stored global approximation obeys the bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "globals_approx_obeys_max_app_def"]
def globalsApproxObeysMaxApp (limit : Nat) (g : Spt ValApprox) : Prop :=
  ∀ n a, sptLookup n g = some a → valApproxObeysMaxApp limit a

/-- A body selected for inlining obeys the approximation's application bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_obeys_max_app"]
theorem decideInlineObeysMaxApp {L : Type} (limit : Nat) (c : Config) (approx : ValApprox)
    (loc : Option L) (arity : Nat) (e : Exp)
    (h : valApproxObeysMaxApp limit approx ∧ decideInlineHOL c approx loc arity = .letInline e) :
    obeysMaxApp limit e := by
  obtain ⟨safe, decision⟩ := h
  cases approx <;> simp [decideInlineHOL] at decision
  case closNoInline target n => split at decision <;> simp_all
  case clos target n body size =>
    split at decision <;> simp_all [valApproxObeysMaxApp]
    split at decision <;> simp_all

/-- Non-inlineable recursive closures obey every application-arity bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "clos_gen_no_inline_obeys_max_app"]
theorem closGenNoInline_obeysMaxApp (limit : Nat) (xs : List (Nat × Exp)) (n x : Nat) :
    ∀ approx ∈ closGenNoInline x n xs, valApproxObeysMaxApp limit approx := by
  induction xs generalizing n with
  | nil => simp [closGenNoInline]
  | cons p xs ih =>
    cases p
    simpa [closGenNoInline, valApproxObeysMaxApp] using ih (n + 1)

end Flapjack.Compiler.Backend.ClosKnown
