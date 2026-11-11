import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.Compiler.Backend.ClosLang.GeneratedSize

/-! Datatype-generated closure-value sizes used in original HOL proofs. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack

mutual
/-- The value component of the generated HOL closure-value size equations. -/
def valueSizeHOL : Value → Nat
  | .number _ => 1
  | .word64 word => 1 + word.toNat
  | .block tag values => 1 + (tag + valueListSizeHOL values)
  | .byteVector bytes => 1 + listSizeHOL BitVec.toNat bytes
  | .refPtr flag index => 1 + (boolSizeHOL flag + index)
  | .closure loc env args arity body =>
      1 + (optionSizeHOL id loc + (valueListSizeHOL env +
        (valueListSizeHOL args + (arity + ClosLang.expSizeHOL body))))
  | .recclosure loc env args fns index =>
      1 + (optionSizeHOL id loc + (valueListSizeHOL env +
        (valueListSizeHOL args + (listSizeHOL (pairSizeHOL id ClosLang.expSizeHOL) fns + index))))
/-- The list component of the generated HOL closure-value size equations. -/
def valueListSizeHOL : List Value → Nat
  | [] => 0
  | value :: rest => 1 + (valueSizeHOL value + valueListSizeHOL rest)
end
end Flapjack.Compiler.Backend.ClosSem
