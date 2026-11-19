module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.State
public import Flapjack.HolRef

@[expose] public section

/-!
# Initial-state projections of HOL `bvlProps`

Counterpart of `cakeml/compiler/backend/semantics/bvlPropsScript.sml:157-175`:
`initial_state_simp` and `initial_state_with_simp`.
-/

namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem

namespace InitialStateCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InitialStateCarrier

/-- Every initial-state field equals the argument that supplied it. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "initial_state_simp"
  (fmap_as_finite_support := [refs])]
theorem initialState_simp {C F : Type} (ffi : HolFfiState F) (code : Spt (Nat × Bvl.Exp))
    (oracle : CompileOracle C) (compiler : Compiler C) (clock : Nat) :
    (initialState ffi code oracle compiler clock :
      Flapjack.Compiler.Backend.BvlSem.State C F).code = code ∧
      (initialState ffi code oracle compiler clock).ffi = ffi ∧
      (initialState ffi code oracle compiler clock).clock = clock ∧
      (initialState ffi code oracle compiler clock).compile = compiler ∧
      (initialState ffi code oracle compiler clock).compileOracle = oracle ∧
      (initialState ffi code oracle compiler clock).refs = HolFiniteMapExact.empty ∧
      (initialState ffi code oracle compiler clock).globals = [] := by
  simp [initialState]

/-- Replacing the clock or the code of an initial state keeps it initial. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "initial_state_with_simp"
  (fmap_as_finite_support := [refs])]
theorem initialState_with_simp {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C) (compiler : Compiler C)
    (clock : Nat) (clock1 : Nat) (code1 : Spt (Nat × Bvl.Exp)) :
    ({ initialState ffi code oracle compiler clock with clock := clock1 } :
        Flapjack.Compiler.Backend.BvlSem.State C F) =
        initialState ffi code oracle compiler clock1 ∧
      { initialState ffi code oracle compiler clock with code := code1 } =
        initialState ffi code1 oracle compiler clock := by
  simp [initialState]

end Flapjack.Compiler.Backend.BvlProps
