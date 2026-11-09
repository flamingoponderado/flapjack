module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.HolArb
public import Flapjack.Basis.Pure.MlString.CharWord

@[expose] public section

/-! HOL's partially specified literal selectors and primitive conversions. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Extract an integer literal; other values have HOL's unspecified result. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "the_Litv_IntLit_def"]
noncomputable def theLitvInt : Value → Int
  | .litv (.intLit i) => i
  | _ => Flapjack.holArb Int

/-- Extract a byte literal; other values have HOL's unspecified result. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "the_Litv_Word8_def"]
noncomputable def theLitvWord8 : Value → BitVec 8
  | .litv (.word8 w) => w
  | _ => Flapjack.holArb (BitVec 8)

/-- Extract a 64-bit word literal; other values have HOL's unspecified result. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "the_Litv_Word64_def"]
noncomputable def theLitvWord64 : Value → BitVec 64
  | .litv (.word64 w) => w
  | _ => Flapjack.holArb (BitVec 64)

/-- Extract a floating-point bit pattern; other values have HOL's unspecified result. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "the_Litv_Float64_def"]
noncomputable def theLitvFloat64 : Value → BitVec 64
  | .litv (.float64 w) => w
  | _ => Flapjack.holArb (BitVec 64)

/-- Extract a character literal; other values have HOL's unspecified result. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "the_Litv_Char_def"]
noncomputable def theLitvChar : Value → HolChar
  | .litv (.char c) => c
  | _ => Flapjack.holArb HolChar

/-- Convert a value between primitive types, with the original character-range
exception and unspecified literal selectors. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_conversion_def"]
noncomputable def doConversion (v : Value) : PrimType → PrimType → Option (Sum Value Value)
  | .wordT .w8, .intT => some (.inr (.litv (.intLit (theLitvWord8 v).toNat)))
  | .wordT .w64, .intT => some (.inr (.litv (.intLit (theLitvWord64 v).toNat)))
  | .intT, .wordT .w8 => some (.inr (.litv (.word8 (BitVec.ofInt 8 (theLitvInt v)))))
  | .intT, .wordT .w64 => some (.inr (.litv (.word64 (BitVec.ofInt 64 (theLitvInt v)))))
  | .charT, .intT => some (.inr (.litv (.intLit (theLitvChar v).toNat)))
  | .intT, .charT =>
    let i := theLitvInt v
    if i < 0 ∨ i > 255 then some (.inl chrExnV)
    else some (.inr (.litv (.char (BitVec.ofNat 8 i.natAbs))))
  | .charT, .wordT .w8 => some (.inr (.litv (.word8 (charToWord8 (theLitvChar v)))))
  | .wordT .w8, .charT => some (.inr (.litv (.char (word8ToChar (theLitvWord8 v)))))
  | .float64T, .wordT .w64 => some (.inr (.litv (.word64 (theLitvFloat64 v))))
  | .wordT .w64, .float64T => some (.inr (.litv (.float64 (theLitvWord64 v))))
  | _, _ => none

end Flapjack.SemanticPrimitivesHOL
