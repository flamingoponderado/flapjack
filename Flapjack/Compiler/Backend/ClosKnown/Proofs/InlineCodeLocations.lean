module

public import Flapjack.Compiler.Backend.ClosKnown.Inline
public import Flapjack.Compiler.Backend.ClosKnown.Fuel
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGlobalSafety
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

@[expose] public section

/-! Code-location facts required for known-function inlining. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps

mutual
/-- The singleton version of the closure-presence argument; this structural
helper has no standalone HOL declaration. -/
theorem containsClosuresExp_codeLocations (e : Exp)
    (safe : containsClosuresExpHOL e = false) : codeLocationsExp e = [] := by
  cases e with
  | var t n => rfl
  | fn name loc vs arity body => simp [containsClosuresExpHOL] at safe
  | letrec names loc vs fns body => simp [containsClosuresExpHOL] at safe
  | ifThenElse t x y z =>
    simp only [containsClosuresExpHOL, Bool.or_eq_false_iff] at safe
    simp [codeLocationsExp, containsClosuresExp_codeLocations x safe.1.1,
      containsClosuresExp_codeLocations y safe.1.2, containsClosuresExp_codeLocations z safe.2]
  | «let» t xs body =>
    simp only [containsClosuresExpHOL, Bool.or_eq_false_iff] at safe
    simp [codeLocationsExp, containsClosures_codeLocations xs safe.1,
      containsClosuresExp_codeLocations body safe.2]
  | raise t x | tick t x =>
    exact containsClosuresExp_codeLocations x (by simpa [containsClosuresExpHOL] using safe)
  | handle t x y =>
    simp only [containsClosuresExpHOL, Bool.or_eq_false_iff] at safe
    simp [codeLocationsExp, containsClosuresExp_codeLocations x safe.1,
      containsClosuresExp_codeLocations y safe.2]
  | call t ticks dest xs | op t dest xs =>
    exact containsClosures_codeLocations xs (by simpa [containsClosuresExpHOL] using safe)
  | app t loc x xs =>
    simp only [containsClosuresExpHOL, Bool.or_eq_false_iff] at safe
    simp [codeLocationsExp, containsClosuresExp_codeLocations x safe.1,
      containsClosures_codeLocations xs safe.2]
termination_by sizeOf e

/-- A closure-free expression list contains no code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "contains_closures_code_locs"]
theorem containsClosures_codeLocations (xs : List Exp)
    (safe : containsClosuresHOL xs = false) : codeLocations xs = [] := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [containsClosuresHOL, Bool.or_eq_false_iff] at safe
    simp [codeLocations, containsClosuresExp_codeLocations x safe.1,
      containsClosures_codeLocations xs safe.2]
termination_by sizeOf xs
end

/-- Inlining only selects a body without closure-code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "code_locs_decide_inline"]
theorem decideInline_codeLocations {L : Type} (c : Config) (approx : ValApprox) (loc : Option L)
    (arity : Nat) (body : Exp) (decision : decideInlineHOL c approx loc arity = .letInline body) :
    codeLocations [body] = [] := by
  obtain ⟨m, size, rfl⟩ := decideInlineLetInlineImpClos c approx loc arity body decision
  simp only [decideInlineHOL] at decision
  split at decision
  next _ =>
    split at decision
    next checks => exact containsClosures_codeLocations [body] checks.2.1
    next => contradiction
  next => contradiction

/-- Inserting ticks leaves the code-location list unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "code_locs_mk_Ticks"]
theorem ticks_codeLocations (trace : BackendCommon.Tra) (index n : Nat) (e : Exp) :
    codeLocations [ticks trace index n e] = codeLocations [e] := by
  induction n generalizing index e with
  | zero => rfl
  | succ n ih =>
    simpa [ticks, codeLocations, codeLocationsExp] using
      ih (index + 1) (.tick (BackendCommon.mkCons trace index) e)

end Flapjack.Compiler.Backend.ClosKnown
