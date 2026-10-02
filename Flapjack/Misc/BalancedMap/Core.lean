import Flapjack.HolRef

/-!
Literal core of the pinned HOL balanced-map script. The cached size is a
constructor field, including on malformed trees; it is never silently repaired.
Lean `Ordering.lt/eq/gt` renders HOL `Less/Equal/Greater` constructor for
constructor. Lookup accepts an arbitrary comparator, with no ordering premise.
This carrier is a prerequisite for CSE knowledge; production still uses its
existing tree map until the remaining balanced-map ports and wiring are reviewed.
-/

namespace Flapjack.Misc.BalancedMap

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanced_map"]
inductive Map (κ ν : Type) where
  | tip : Map κ ν
  | bin (cachedSize : Nat) (key : κ) (value : ν) (left right : Map κ ν) : Map κ ν
  deriving Repr, DecidableEq

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "ratio_def"]
def ratio : Nat := 2

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "delta_def"]
def delta : Nat := 3

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "size_def"]
def size {κ ν : Type} : Map κ ν → Nat
  | .tip => 0
  | .bin n _ _ _ _ => n

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "bin_def"]
def bin {κ ν : Type} (key : κ) (value : ν) (left right : Map κ ν) : Map κ ν :=
  .bin (size left + size right + 1) key value left right

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "null_def"]
def null {κ ν : Type} : Map κ ν → Bool
  | .tip => true
  | .bin _ _ _ _ _ => false

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "lookup_def"]
def lookup {κ ν : Type} (cmp : κ → κ → Ordering) (key : κ) : Map κ ν → Option ν
  | .tip => none
  | .bin _ key' value left right =>
    match cmp key key' with
    | .lt => lookup cmp key left
    | .gt => lookup cmp key right
    | .eq => some value

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "member_def"]
def member {κ ν : Type} (cmp : κ → κ → Ordering) (key : κ) : Map κ ν → Bool
  | .tip => false
  | .bin _ key' _ left right =>
    match cmp key key' with
    | .lt => member cmp key left
    | .gt => member cmp key right
    | .eq => true

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "empty_def"]
def empty {κ ν : Type} : Map κ ν := .tip

@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "singleton_def"]
def singleton {κ ν : Type} (key : κ) (value : ν) : Map κ ν :=
  .bin 1 key value .tip .tip

end Flapjack.Misc.BalancedMap
