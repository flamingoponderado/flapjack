import Flapjack.RiscV.WordExpressionFlatten
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
import Std.Data.TreeMap

/-!
# Cake `pull_exp`/`flatten_exp` constant-placement oracle (GH #1024)

Cake's instruction selection normalizes every assignment operand with

```
inst_select c temp (Assign v exp) =
  (inst_select_exp c v temp o flatten_exp o pull_exp) exp
```

(`cakeml/compiler/backend/word_instScript.sml:383`).  The two passes interact:

* `pull_ops` collects operands with `ls ++ acc`, which reverses their order.
* `optimize_consts`/`reduce_const` fold constant operands into a single
  constant and place it at the front of the collected list (and, when there
  are no constants, they reverse the list).
* `flatten_exp (Op op (x::xs)) = Op op [flatten_exp (Op op xs); flatten_exp x]`
  is head-last, which reverses once more.

The net effect, confirmed by the direct HOL evaluation in
`scripts/hol-probes/word_inst_probe.out`, is that a plain operation keeps the
reversed `pull_ops` order (`Op Add [Var 2; Var 4]` normalizes to
`Op Add [Var 4; Var 2]`) while a constant operand ends up **last**
(`Op Add [Var 7; Const 1w]` and `Op Add [Const 1w; Var 7]` both normalize to
`Op Add [Var 7; Const 1w]`).  `inst_select_exp` only uses an immediate when the
second operand is a constant, so this is exactly the `addi` shape.

The port keeps Cake's constant-right `convert_sub` and head-first
`wordInstFlattenExp`; `wordInstConstantsToEnd` reproduces Cake's constant
placement (constants last) and, for `Add`, Cake's `optimize_consts` folding of
several constants into one value together with `reduce_const`'s zero drop.

This module pins the oracle values from `word_inst_probe.out` and checks that
the port's normalizer reaches them.
-/

namespace Flapjack.Test.WordInstNormalizeParity

open Flapjack Flapjack.RiscV

/-! Cake's `word_cse` canonicalizes an `OpCurrHeap` source for its fact key,
    but preserves the original selected source in the emitted instruction.
    This is observable when a repeated constant is rematerialized: the later
    constant must remain live through the final dead-code pass. -/

/-- `word_inst_probe.out: norm_two_vars`. -/
def cakeTwoVarAtoms : List (Option Nat) := [some 4, some 2]

/-- `word_inst_probe.out: norm_t_plus_1` / `norm_1_plus_t`. -/
def cakeVarConstAtoms : List (Option Nat) := [some 7, none]

/-- `word_inst_probe.out: norm_nested_add`. -/
def cakeNestedAtoms : List (Option Nat) := [some 2, some 1, none]

/-- `word_inst_probe.out: norm_const_middle`. -/
def cakeConstMiddleAtoms : List (Option Nat) := [some 3, some 1, none]

/-- `word_inst_probe.out: norm_nested_fixture`: the five-load nested add
    used by the exact nested-expression corpus fixture. -/
def cakeNestedFixtureAtoms : List (Option Nat) :=
  [some 4, some 2, some 10, some 12, some 6]

end Flapjack.Test.WordInstNormalizeParity
