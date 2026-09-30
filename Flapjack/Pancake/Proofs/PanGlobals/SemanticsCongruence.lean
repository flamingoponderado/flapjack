import Flapjack.Pancake.Semantics.PanSem.Semantics

namespace Flapjack

open Pancake.PanLang PanSemStateFiniteExact

/-- Flapjack-specific assembly helper, with no standalone HOL original.
The HOL semantics uses only the result and FFI event list of each clocked
entry call. Equality of these observations therefore preserves failure,
the entire termination choice predicate, and the divergence prefix set.
This conditional congruence is infrastructure, not a pass-correctness port
or the premise-free HOL `semantics_empty_locals` theorem. -/
theorem panGlobals_semantics_of_clock_observations {width : Nat} {σ : Type}
    [NeZero width] (first second : PanSemStateFiniteExact width σ) (start : MlS)
    (observations : ∀ clock,
      let a := evaluateHOLFiniteState { first with clock := clock } (.call none start [])
      let b := evaluateHOLFiniteState { second with clock := clock } (.call none start [])
      (a.1, a.2.ffi.ioEvents) = (b.1, b.2.ffi.ioEvents)) :
    semantics first start = semantics second start := by
  classical
  have hresult (clock : Nat) :
      (evaluateHOLFiniteState { first with clock := clock } (.call none start [])).1 =
      (evaluateHOLFiniteState { second with clock := clock } (.call none start [])).1 :=
    (Prod.mk.inj (observations clock)).1
  have hevents (clock : Nat) :
      (evaluateHOLFiniteState { first with clock := clock } (.call none start [])).2.ffi.ioEvents =
      (evaluateHOLFiniteState { second with clock := clock } (.call none start [])).2.ffi.ioEvents :=
    (Prod.mk.inj (observations clock)).2
  unfold semantics
  dsimp only
  simp only [hresult, hevents]
  congr 3
  funext res
  apply propext
  constructor
  · rintro ⟨clock, post, result, outcome, heval, houtcome, hres⟩
    let output := evaluateHOLFiniteState { second with clock := clock } (.call none start [])
    have hr := hresult clock
    have he := hevents clock
    rw [heval] at hr he
    refine ⟨clock, output.2, output.1, outcome, (Prod.eta output).symm, ?_, ?_⟩
    · change _ at hr
      rw [← hr]
      exact houtcome
    · change _ at he
      rw [← he]
      exact hres
  · rintro ⟨clock, post, result, outcome, heval, houtcome, hres⟩
    let output := evaluateHOLFiniteState { first with clock := clock } (.call none start [])
    have hr := hresult clock
    have he := hevents clock
    rw [heval] at hr he
    refine ⟨clock, output.2, output.1, outcome, (Prod.eta output).symm, ?_, ?_⟩
    · change _ at hr
      rw [hr]
      exact houtcome
    · change _ at he
      rw [he]
      exact hres

end Flapjack
