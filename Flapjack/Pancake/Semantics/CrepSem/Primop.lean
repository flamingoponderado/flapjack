import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.HolRef
import Flapjack.PanValues
import Flapjack.Pancake.Semantics.PanSem

/-!
The HOL `crepSemScript.sml` primitive operator acts on `word_lab` cells, not
the wrapper-erased raw words used by Flapjack's compatibility runtime handler.
-/

namespace Flapjack

/-- HOL `crepSem$crep_primop`: AddCarry accepts exactly three word cells and
    returns the result and carry-out as two word cells. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "crep_primop_def"]
def crepPrimopHOL {width : Nat} [NeZero width] :
    PrimOp → List (PanWordLab (BitVec width)) →
      Option (List (PanWordLab (BitVec width)))
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, overflow) := wordAddCarryHOL left right carry
      some [.word result, .word overflow]
  | _, _ => none

/-- Exact port of HOL `crep_primop_def` (`cakeml/pancake/semantics/crepSemScript.sml:221`)
    over the exact `word_lab` carrier `HolWordLab` (`panSemScript.sml:17`,
    `word_lab = Word ('a word)`).

    HOL `crep_primop AddCarry args = if LENGTH args = 3 /\ EVERY isWord args then`
    `let l = theWord (EL 0 args); r = theWord (EL 1 args); ci = theWord (EL 2 args);`
    `(res, co) = word_add_carry l r ci in SOME [Word res; Word co] else NONE`.

    Because `word_lab` is one-constructor, `EVERY isWord` is automatic and the
    only surviving side condition is the exact-three arity, rendered as the
    `.word` triple pattern. This is UNTAGGED pending coordinator source review:
    the existing `crepPrimopHOL` is the `PanWordLab` rendering of the same HOL
    definition; this `HolWordLab` version lets `pan_primop_crep_primop` be
    stated with exact HOL shape (no `toPanWordLab` map). -/
def crepPrimopHOLExact {width : Nat} [NeZero width] :
    PrimOp → List (HolWordLab width) → Option (List (HolWordLab width))
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, overflow) := wordAddCarryHOL left right carry
      some [.word result, .word overflow]
  | _, _ => none

end Flapjack
