import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxValue
import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Misc.Sptree

/-! Global approximation invariant for closure known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem

/-- The closure state's finite maps roundtrip through their lookup view. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Every approximation present for an initialized global describes its value. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_def"
  (fmap_as_finite_support := [refs, code])]
def stateGlobalsApprox {C F : Type} (s : State C F) (g : Spt ValApprox) : Prop :=
  ∀ k v a, getGlobal k s.globals = some (some v) ∧ sptLookup k g = some a →
    ValApproxVal a v

/-- Updating the clock preserves the global approximation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_clock_fupd"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxClock {C F : Type} (s : State C F) (g : Spt ValApprox)
    (f : Nat → Nat) : stateGlobalsApprox {s with clock := f s.clock} g ↔
      stateGlobalsApprox s g := Iff.rfl

/-- Decrementing the clock preserves the global approximation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_dec_clock"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxDecClock {C F : Type} (n : Nat) (s : State C F) (g : Spt ValApprox) :
    stateGlobalsApprox (decClock n s) g ↔ stateGlobalsApprox s g := Iff.rfl

/-- Updating references preserves the global approximation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_refsfupd"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxRefs {C F : Type} (s : State C F) (g : Spt ValApprox)
    (f : HolFiniteMapExact Nat (Ref Value) → HolFiniteMapExact Nat (Ref Value)) :
    stateGlobalsApprox {s with refs := f s.refs} g ↔ stateGlobalsApprox s g := Iff.rfl

/-- Updating the FFI, including changing its carrier, preserves the invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_ffifupd"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxFfi {C F G : Type} (s : State C F) (g : Spt ValApprox)
    (f : HolFfiState F → HolFfiState G) :
    stateGlobalsApprox (⟨s.globals, s.refs, f s.ffi, s.clock, s.compile,
      s.compileOracle, s.code, s.maxApp⟩ : State C G) g ↔ stateGlobalsApprox s g := Iff.rfl

/-- Updating code preserves the global approximation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_codeupd"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxCode {C F : Type} (s : State C F) (g : Spt ValApprox)
    (f : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    stateGlobalsApprox {s with code := f s.code} g ↔ stateGlobalsApprox s g := Iff.rfl

/-- Updating the compile oracle preserves the global approximation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_coupd"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxOracle {C F : Type} (s : State C F) (g : Spt ValApprox)
    (f : CompileOracle C → CompileOracle C) :
    stateGlobalsApprox {s with compileOracle := f s.compileOracle} g ↔ stateGlobalsApprox s g := Iff.rfl

/-- Restricting an approximation map preserves its agreement with globals. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_globals_approx_subspt"
  (fmap_as_finite_support := [refs, code])]
theorem stateGlobalsApproxSubspt {C F : Type} (g0 g : Spt ValApprox) (s : State C F)
    (h : sptSubspt g0 g ∧ stateGlobalsApprox s g) : stateGlobalsApprox s g0 := by
  intro k value approx ⟨found, lookup⟩
  have member : sptMem k g0 := (sptMem_iff_lookup k g0).2 ⟨approx, lookup⟩
  have equal := (h.1 k member).2
  exact h.2 k value approx ⟨found, equal.trans lookup⟩

end Flapjack.Compiler.Backend.ClosKnown
