module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift

@[expose] public section

/-! Clocked simulation consequences for the proof-side observational semantics.
The evaluator and state carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- A non-timeout initial evaluation is unchanged by additional clock, apart
from the final clock field. -/
theorem evaluate_initial_addClock {C F : Type} (ffi : HolFfiState F) (maxApp clock extra : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (program : List ClosLang.Exp) (result : Result (List Value) Value)
    (final : State C F) (run : evaluate program [] (initialState ffi maxApp code oracle compiler clock) = (result, final))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate program [] (initialState ffi maxApp code oracle compiler (clock + extra)) =
      (result, { final with clock := final.clock + extra }) := by
  have shifted := evaluate_addClock.1 program [] (initialState ffi maxApp code oracle compiler clock)
    final result extra run notTimeout
  simpa [initialState] using shifted

/-- Monotone clock-indexed traces with a forward clock-extension simulation
have the same lazy-list limit. -/
theorem clocked_traces_lub_eq {α : Type} (source target : Nat → List α)
    (sourceMono : ∀ k l, k ≤ l → source k <+: source l)
    (targetMono : ∀ k l, k ≤ l → target k <+: target l)
    (simulation : ∀ clock, ∃ extra, source clock = target (clock + extra)) :
    HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (source clock)) =
      HolLList.buildLprefixLub (fun trace => ∃ clock, trace = HolLList.fromList (target clock)) := by
  apply HolLList.IMP_build_lprefix_lub_EQ
  · intro x y ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    subst x; subst y
    rcases Nat.le_total k l with h | h
    · exact Or.inl ((HolLList.lprefix_fromList _ _).2 (sourceMono k l h))
    · exact Or.inr ((HolLList.lprefix_fromList _ _).2 (sourceMono l k h))
  · intro x y ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    subst x; subst y
    rcases Nat.le_total k l with h | h
    · exact Or.inl ((HolLList.lprefix_fromList _ _).2 (targetMono k l h))
    · exact Or.inr ((HolLList.lprefix_fromList _ _).2 (targetMono l k h))
  · intro trace ⟨clock, h⟩
    subst trace
    obtain ⟨extra, equal⟩ := simulation clock
    refine ⟨HolLList.fromList (target (clock + extra)), ⟨clock + extra, rfl⟩, ?_⟩
    apply (HolLList.lprefix_fromList _ _).2
    rw [equal]
    exact List.prefix_refl _
  · intro trace ⟨clock, h⟩
    subst trace
    obtain ⟨extra, equal⟩ := simulation clock
    refine ⟨HolLList.fromList (source clock), ⟨clock, rfl⟩, ?_⟩
    apply (HolLList.lprefix_fromList _ _).2
    rw [equal]
    exact targetMono clock (clock + extra) (Nat.le_add_right clock extra)

end Flapjack.Compiler.Backend.ClosSem
