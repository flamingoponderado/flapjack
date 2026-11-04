import Flapjack.RiscV.PipelineDiagnostics

/-!
# Word-to-Stack frame containment

`word_to_stack$compile_prog` (`word_to_stackScript.sml:586-593`) sizes a
function's frame from `max_var prog DIV 2 + 1 - reg_count` of the program it
is lowering -- the output of `word_alloc`.  Flapjack used to recover that
number by running a second, complete allocation of a differently prepared
program (`cakeWordStackVarCount` on the unflattened body), which has no
counterpart upstream and can come out either above or below the real one.

When it comes out below, the register allocator's own stack slots fall
outside the frame that is allocated for them.  The fixture below is a
differential-fuzz case, minimized: original Pancake accepts it, Flapjack
accepts it, and its `main` spills far enough that the two numbers disagree
(the second allocation says 9, the lowered program needs 11).  The check is
the invariant itself, so it stays meaningful if either number changes.
-/

namespace Flapjack.Test.CakeFrameContainment

open Flapjack Flapjack.RiscV Flapjack.Parser

def spillingSource : String :=
    "fun 1 add1(1 a, 1 b) { return a + b; }\n" ++
    "fun {1,1} pair(1 a, 1 b) { return <a, b>; }\n" ++
    "exception E : 1;\n" ++
    "fun 1 main() {\n" ++
    "  var 1 x = 1000;\n" ++
    "  var 1 y115 = add1(((3 | 3) #>> 2), x);\n" ++
    "  var 1 y717 = add1(((y115 #>> 1) << (2 & 2)), (1000 ^ y115));\n" ++
    "  var 1 y98 = add1((ld8 (1000 + 12 + 8)), 0);\n" ++
    "  var 1 y209 = (ld8 1016);\n" ++
    "  var 1 y600 = add1((ld8 1000), (lds 1 (1008)));\n" ++
    "  var {1,1} p938 = pair(y209, y98);\n" ++
    "  try\n" ++
    "    y98 = add1(p938.1, 0)\n" ++
    "  catch E => y600 {\n" ++
    "      while (x > 0) {\n" ++
    "      }\n" ++
    "  }\n" ++
    "  if (p938.0 > ((7 + 1) #>> 7)) {\n" ++
    "    @foo(((lds 1 ((0 + 1000))) << (ld8 (1008 + 1000))), y717, (lds 1 (((0 + 8) + 4))), ((ld8 (1000 + 24 + 1000)) #>> 7));\n" ++
    "  }\n" ++
    "  return add1(((lds 1 (1000 + 12)) ^ (0 & 1)), (p938.1 << p938.0));\n" ++
    "}\n"

end Flapjack.Test.CakeFrameContainment
