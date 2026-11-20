module

public import Flapjack.Compiler.Backend.Semantics.BviProps.AdjustOracle
public import Flapjack.HolRef

@[expose] public section

/-!
# Adjusted-oracle predicates of HOL `bviProps`

Counterpart of `cakeml/compiler/backend/semantics/bviPropsScript.sml:743-766`:
`adj_orac_ok_def`, `adj_orac_rel_def` and `adj_orac_simps`. The projection-form
`adjustOracleOk` in `AdjustOracle.lean` stays untagged infrastructure; the
tagged definitions below follow HOL's binder and premise shape, and the
untagged `adjustOracleOkHOL_iff` relates the two.
-/

namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

namespace AdjustOracleHOLCarrier
/-- Canonical BVI reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end AdjustOracleHOLCarrier

/-- The adjusted callback agrees with the original at every oracle entry. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "adj_orac_ok_def"
  (fmap_as_finite_support := [refs])]
def adjustOracleOkHOL {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) : Prop :=
  ∀ (n : Nat) (x : C) (y : List (Nat × Nat × Bvi.Exp)),
    state.compileOracle n = (x, y) →
      (state.compile x y).map (fun (bytes, data, config) => (bytes, data, f config)) =
        compiler (f x) y

/-- A target state is the source state with its callback adjusted, provided
the callbacks agree at every oracle entry. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "adj_orac_rel_def"
  (fmap_as_finite_support := [refs])]
def adjustOracleRel {C D F : Type} (compiler : Compiler D) (f : C → D)
    (source : BviState C F) (target : BviState D F) : Prop :=
  adjustOracleOkHOL compiler f source ∧ target = adjustOracle compiler f source

/-- Flapjack helper: the source-shaped callback agreement is the projection
form used by the untagged adjustment lemmas. -/
theorem adjustOracleOkHOL_iff {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) :
    adjustOracleOkHOL compiler f state ↔ adjustOracleOk compiler f state := by
  constructor
  · intro ok n
    exact ok n (state.compileOracle n).1 (state.compileOracle n).2 rfl
  · intro ok n x y found
    simp only [adjustOracleOk] at ok
    have applied := ok n
    simp only [found] at applied
    simpa using applied

/-- The adjusted state keeps every runtime field, commutes with clock changes
and preserves callback agreement. -/
@[hol "cakeml/compiler/backend/semantics/bviPropsScript.sml" "adj_orac_simps"
  (fmap_as_finite_support := [refs])]
theorem adjustOracle_simps {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) (n k : Nat) :
    (adjustOracle compiler f state).clock = state.clock ∧
      (adjustOracle compiler f state).code = state.code ∧
      (adjustOracle compiler f state).refs = state.refs ∧
      (adjustOracle compiler f state).global = state.global ∧
      (adjustOracle compiler f state).ffi = state.ffi ∧
      decClock n (adjustOracle compiler f state) = adjustOracle compiler f (decClock n state) ∧
      { adjustOracle compiler f state with clock := k } =
        adjustOracle compiler f { state with clock := k } ∧
      (adjustOracleOkHOL compiler f (decClock n state) ↔ adjustOracleOkHOL compiler f state) ∧
      (adjustOracleOkHOL compiler f { state with clock := k } ↔
        adjustOracleOkHOL compiler f state) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rfl
  · rfl

end Flapjack.Compiler.Backend.BviProps
