import Flapjack.Compiler.Backend.RegAlloc.Carriers

namespace Flapjack.RegAlloc

/-- Literal `tag_col` (`reg_allocScript.sml:939-942`): the colour of a fixed
tag, and `0` for `Atemp`/`Stemp`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "tag_col_def"]
def tagCol : Tag → Nat
  | .Fixed n => n
  | _ => 0

/-- Literal `unbound_colour` (`reg_allocScript.sml:947-956`): the first colour
`≥ col` not met while scanning the list. Total on arbitrary lists; the
original's "assuming input is sorted" comment is not a premise. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "unbound_colour_def"]
def unboundColour (col : Nat) : List Nat → Nat
  | [] => col
  | x :: xs =>
    if col < x then col
    else if x = col then unboundColour (col + 1) xs
    else unboundColour col xs

/-- Literal `extract_tag` (`reg_allocScript.sml:1299-1303`), written in HOL as
a `case` on the tag: a fixed tag's colour, else `0`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "extract_tag_def"]
def extractTag (t : Tag) : Nat :=
  match t with
  | .Fixed m => m
  | _ => 0

end Flapjack.RegAlloc
