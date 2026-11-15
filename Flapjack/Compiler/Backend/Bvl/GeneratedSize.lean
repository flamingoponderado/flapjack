import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Compiler.Backend.ClosLang.GeneratedSize

/-! HOL-generated BVL expression sizes used by evaluator induction. -/
namespace Flapjack.Compiler.Backend.Bvl
open Flapjack

mutual
/-- The generated HOL BVL expression size includes constructor payload sizes.
HOL generates this function from the datatype, so it has no source declaration
to tag. It supplies the size bounds in the original evaluator induction rule. -/
def expSizeHOL : Exp → Nat
  | .var n => 1 + n
  | .ifThenElse a b c => 1 + (expSizeHOL a + (expSizeHOL b + expSizeHOL c))
  | .let xs b => 1 + (expListSizeHOL xs + expSizeHOL b)
  | .raise b | .tick b => 1 + expSizeHOL b
  | .handle a b => 1 + (expSizeHOL a + expSizeHOL b)
  | .call ticks dest xs => 1 + (ticks + (optionSizeHOL id dest + expListSizeHOL xs))
  | .force loc n => 1 + (loc + n)
  | .op op xs => 1 + (ClosLang.opSizeHOL op + expListSizeHOL xs)

/-- The generated HOL expression-list size, equal to `list_size exp_size`. -/
def expListSizeHOL : List Exp → Nat
  | [] => 0
  | e :: es => 1 + (expSizeHOL e + expListSizeHOL es)
end

end Flapjack.Compiler.Backend.Bvl
