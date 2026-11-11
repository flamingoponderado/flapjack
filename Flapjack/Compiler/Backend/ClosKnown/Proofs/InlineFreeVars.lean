module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.FreeVars
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGlobalSafety
public import Flapjack.Compiler.Backend.ClosKnown.Inline.Free.Correct
public import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeCorrect

@[expose] public section

/-! Free-variable bounds of closure bodies selected for inlining. -/
namespace Flapjack.Compiler.Backend.ClosKnown.InlineFreeVars
open ClosLang ClosProps ClosCall

/-- The closedness test on a function bounds its body's free variables by
the function arity. This is Flapjack infrastructure connecting the source
closedness traversal to the closure semantics. -/
theorem closedFunctionBodyBound (arity : Nat) (body : Exp)
    (h : closedHOL (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none arity body) = true) :
    fvMax arity [body] := by
  exact (closedFn_fv (Flapjack.Basis.Pure.MlString.ofString "") none none arity body).mp h

/-- A selected inline body is a closure approximation whose free variables
are all supplied by the application's arguments. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "decide_inline_LetInline_IMP_Clos_fv_max"]
theorem decideInlineLetInlineFvMax {L : Type} (c : Config) (approx : ValApprox) (loc : Option L)
    (arity : Nat) (body : Exp) (decision : decideInlineHOL c approx loc arity = .letInline body) :
    ∃ m size, approx = .clos m arity body size ∧ fvMax arity [body] := by
  obtain ⟨m, size, rfl⟩ := decideInlineLetInlineImpClos c approx loc arity body decision
  refine ⟨m, size, rfl, closedFunctionBodyBound arity body ?_⟩
  simp only [decideInlineHOL] at decision
  split at decision
  next initial =>
    split at decision
    next checks => exact checks.2.2
    next => contradiction
  next => contradiction

end Flapjack.Compiler.Backend.ClosKnown.InlineFreeVars
