import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact

/-- Local proof infrastructure for the Loop helper's clock induction. The
successful entry cut preserves the clock; the reviewed `evaluate_clock` bound
then makes a nonzero body result's decremented clock strictly smaller than the
original input clock. HOL uses this argument inside `evaluate_apply_colour_Loop_helper`
at 1027-1033 and 1077-1083; it is not a separately named HOL declaration. -/
theorem loopBodyRecursiveClockLt {width : Nat} [NeZero width] {C F : Type}
    (names : WordLangCutsetsHOL) (body : WordLangProgHOL (BitVec width))
    (st entry out : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (hcut : cutState names st = some entry)
    (hrun : evaluate body entry = (res, out)) (hne : out.clock ≠ 0) :
    (decClock out).clock < st.clock := by
  have hentry := (cutState_clock_termdep names st entry hcut).1
  have hbody := (evaluate_clock body entry res out hrun).1
  simp only [decClock]
  omega

/-- Local proof infrastructure for the Loop helper's oracle composition.
Given an actual non-Error body run after an entry cut, any oracle requested by
the recursive iteration can be installed in the body's output by choosing a
new original-input oracle. The entry cut and all other output fields stay
exact. This composes `cutState_withPermute` and `permute_swap_lemma`, matching
the internal HOL argument at 1041-1048 and 1089-1096; no independent HOL
declaration names the composition, hence no tag. -/
theorem loopBodyOracleStitch {width : Nat} [NeZero width] {C F : Type}
    (names : WordLangCutsetsHOL) (body : WordLangProgHOL (BitVec width))
    (st entry out : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (wanted : Nat → Nat → Nat)
    (hcut : cutState names st = some entry)
    (hrun : evaluate body entry = (res, out)) (hne : res ≠ some .error) :
    ∃ initial, cutState names { st with permute := initial } =
        some { entry with permute := initial } ∧
      evaluate body { entry with permute := initial } =
        (res, { out with permute := wanted }) ∧
      decClock { out with permute := wanted } = { decClock out with permute := wanted } := by
  have hswap := permute_swap_lemma body entry wanted
  rw [hrun] at hswap
  obtain ⟨initial, hbody⟩ := hswap hne
  refine ⟨initial, ?_, hbody, rfl⟩
  rw [cutState_withPermute, hcut]
  rfl

end Flapjack.WordAlloc
