import Flapjack.HolRef
import Flapjack.Pancake.PanLang.Prog
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.Semantics.PanProps

/-!
The source-level lemmas from CakeML's `pan_to_wordProofScript.sml`.
This is the counterpart module for theorem ports from that HOL proof script.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact port of HOL `pan_exps_of_nested_seq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:1018`).  Enumerating
    the expressions of a nested sequence is the concatenation of the
    per-statement expression lists.  This is a concrete proof consumer of the
    exact PanProps `expsOfHOL` port. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "pan_exps_of_nested_seq"]
theorem panExpsOfNestedSeqHOL {width : Nat} [NeZero width]
    (statements : List (Flapjack.Pancake.PanLang.ProgHOL width)) :
    expsOfHOL (Flapjack.Pancake.PanLang.nestedSeqHOL statements) =
      (statements.map expsOfHOL).flatten := by
  induction statements with
  | nil => rfl
  | cons statement statements ih =>
      simp only [Flapjack.Pancake.PanLang.nestedSeqHOL, expsOfHOL, List.map_cons,
        List.flatten_cons, ih]

/-- The Bool predicate `λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2` used by
    HOL `good_panops_def`: a `Panop` expression must carry exactly two
    arguments; every other expression satisfies it vacuously.  This is the
    `every_exp` predicate argument, not a separate HOL declaration, so it
    carries no `@[hol]` tag. -/
def panopArityTwoHOL {width : Nat} [NeZero width] : ExpHOL width → Bool
  | .panop _ es => decide (es.length = 2)
  | _ => true

/-- Exact port of HOL `good_panops`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:1108-1113`):
    `good_panops (Function fi) = EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒
    LENGTH es = 2)) (exps_of fi.body)`;
    `good_panops (Decl sh v exp) = every_exp (…) exp`; the catch-all is `T`.
    The `EVERY`-fold and `every_exp` are rendered by the reviewed exact
    `everyExpHOL`, and `exps_of` by the reviewed exact `expsOfHOL`. -/
@[hol "cakeml/pancake/proofs/pan_to_wordProofScript.sml" "good_panops_def"
  (words_as_type_indexed_bitvec)]
def goodPanopsHOL {width : Nat} [NeZero width] : DeclHOL width → Bool
  | .function fi => everyExpListHOL panopArityTwoHOL (expsOfHOL fi.body)
  | .decl _ _ exp => everyExpHOL panopArityTwoHOL exp
  | _ => true

end Flapjack
