import Flapjack.Translator.Monadic.MonadBase.ListPrimitives

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Flapjack helper with no separate HOL original: an in-range `Msub` read
succeeds with Lean's bounds-checked element. Used instead of the HOL
`Msub_eqn` rendering, whose statement reads the held total HOL `EL`. -/
theorem mSub_success_getElem {α ε : Type} (e : ε) :
    ∀ (ls : List α) (n : Nat) (h : n < ls.length), mSub e n ls = .success ls[n]
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => by simp [mSub]
  | _ :: tail, n + 1, h => by
      simp only [mSub, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      exact mSub_success_getElem e tail n (by simpa using h)

end Flapjack.RegAlloc
