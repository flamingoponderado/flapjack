import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.HolRef
import Flapjack.PanValues
import Flapjack.Pancake.Semantics.PanSem

/-!
The HOL `crepSemScript.sml` primitive operator acts on `word_lab` cells, not
the wrapper-erased raw words used by Flapjack's compatibility runtime handler.
-/

namespace Flapjack

/-- Exact port of HOL `crep_primop_def` (`cakeml/pancake/semantics/crepSemScript.sml:221`)
    over the exact `word_lab` carrier `HolWordLab` (`panSemScript.sml:17`,
    `word_lab = Word ('a word)`).

    HOL `crep_primop AddCarry args = if LENGTH args = 3 /\ EVERY isWord args then`
    `let l = theWord (EL 0 args); r = theWord (EL 1 args); ci = theWord (EL 2 args);`
    `(res, co) = word_add_carry l r ci in SOME [Word res; Word co] else NONE`.

    Because `word_lab` is one-constructor, `EVERY isWord` is automatic and the
    only surviving side condition is the exact-three arity, rendered as the
    `.word` triple pattern. -/
@[hol "cakeml/pancake/semantics/crepSemScript.sml" "crep_primop_def"]
def crepPrimopHOLExact {width : Nat} [NeZero width] :
    PrimOp → List (HolWordLab width) → Option (List (HolWordLab width))
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, overflow) := wordAddCarryHOL left right carry
      some [.word result, .word overflow]
  | _, _ => none

/-- Executable `PanWordLab` rendering of HOL `crepSem$crep_primop`.

    This is NOT the canonical exact port: `crepPrimopHOLExact` above is the
    tagged `crep_primop_def` (over the exact `word_lab` carrier `HolWordLab`).
    The executed Crep evaluator (`Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean`)
    still calls this `PanWordLab` version, mapping payloads with
    `HolWordLab.toPanWordLab`; `crepPrimopHOL_eq_map_toPanWordLab` below is the
    proved conversion equation. Routing the evaluator through
    `crepPrimopHOLExact` is tracked by `flapjack-4ac.5.16.9.1.1`. -/
def crepPrimopHOL {width : Nat} [NeZero width] :
    PrimOp → List (PanWordLab (BitVec width)) →
      Option (List (PanWordLab (BitVec width)))
  | .addCarry, [.word left, .word right, .word carry] =>
      let (result, overflow) := wordAddCarryHOL left right carry
      some [.word result, .word overflow]
  | _, _ => none

/-- The executable `PanWordLab` rendering `crepPrimopHOL` agrees with the exact
    `crepPrimopHOLExact` after mapping payloads with `HolWordLab.toPanWordLab`.
    This is the conversion equation that keeps the untagged production rendering
    on the executed path equivalent to the tagged exact declaration. -/
theorem crepPrimopHOL_eq_map_toPanWordLab {width : Nat} [NeZero width]
    (operator : PrimOp) (arguments : List (HolWordLab width)) :
    crepPrimopHOL operator (arguments.map HolWordLab.toPanWordLab) =
      (crepPrimopHOLExact operator arguments).map
        (List.map HolWordLab.toPanWordLab) := by
  cases operator
  cases arguments with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              cases rest with
              | nil =>
                  cases first <;> cases second <;> cases third <;>
                    simp [crepPrimopHOL, crepPrimopHOLExact, HolWordLab.toPanWordLab]
              | cons _ _ => rfl

end Flapjack
