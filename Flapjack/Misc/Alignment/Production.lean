import Flapjack.Misc.Alignment
import Flapjack.Pancake.Semantics.CrepSem.Log2ZeroParametric

/-!
# HOL `byte_align` against the Flapjack alignment renderings

Flapjack infrastructure relating the exact HOL `byte_align` (`holByteAlign`, over the specified
`LOG2`) to the untagged production `panByteAlignHOL` (which uses `Nat.log2`) and to the
`Log2ZeroParametric` model family. At widths of at least 8 all agree. At every width the HOL
definition is the parametric model at `log2Zero := holLOG2 0`, the one unconstrained HOL value;
no value of it is assumed.
-/

namespace Flapjack

theorem holByteAlign_eq_log2Zero {width : Nat} [NeZero width] (w : BitVec width) :
    holByteAlign w = panByteAlignHOLLog2Zero (holLOG2 0) w := by
  unfold holByteAlign panByteAlignHOLLog2Zero
  rw [holAlign_eq_div]
  by_cases hb : width / 8 = 0
  · simp only [hb, if_true]
  · simp only [hb, if_false, holLOG2_eq_log2 (Nat.pos_of_ne_zero hb)]

theorem holByteAlign_eq_panByteAlignHOL {width : Nat} [NeZero width] (hwidth : 8 ≤ width)
    (w : BitVec width) : holByteAlign w = panByteAlignHOL w := by
  rw [holByteAlign_eq_log2Zero, panByteAlignHOLLog2Zero_eq_panByteAlignHOL hwidth]

end Flapjack
