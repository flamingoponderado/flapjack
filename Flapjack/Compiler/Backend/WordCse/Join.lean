import Flapjack.Compiler.Backend.WordCse.Knowledge
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Misc.BalancedMap.Insert
import Flapjack.Misc.Sptree.InterEq

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack

/-- Literal original accumulator traversal: insert this node conditionally,
then traverse the right subtree and finally the left subtree. All cached sizes,
keys and values of arbitrary input trees retain their original carriers. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "bm_inter_eq_acc_def"]
def bmInterEqAcc {α : Type} [DecidableEq α] (second : Misc.BalancedMap.Map (List Nat) α) :
    Misc.BalancedMap.Map (List Nat) α → Misc.BalancedMap.Map (List Nat) α →
      Misc.BalancedMap.Map (List Nat) α
  | .tip, accumulator => accumulator
  | .bin _ key value left right, accumulator =>
      bmInterEqAcc second left
        (bmInterEqAcc second right
          (if Misc.BalancedMap.lookup listCmp key second = some value then
            Misc.BalancedMap.insert listCmp key value accumulator else accumulator))

@[hol "cakeml/compiler/backend/word_cseScript.sml" "bm_inter_eq_def"]
def bmInterEq {α : Type} [DecidableEq α] (first second : Misc.BalancedMap.Map (List Nat) α) :
    Misc.BalancedMap.Map (List Nat) α :=
  bmInterEqAcc second first Misc.BalancedMap.empty

/-- Original five-field join: latest is reset, the ordered store list is
filtered against the second list's first lookup, and both fact trees use the
literal accumulator intersection. Actual ordered-map join correspondence and
whole CSE correctness remain separately open. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "merge_data_def"]
def mergeData (first second : Knowledge) : Knowledge :=
  { toCanonical := sptInterEq first.toCanonical second.toCanonical
    toLatest := .ln
    getsMem := first.getsMem.filter (fun entry => decide (second.getsMem.lookup entry.1 = some entry.2))
    instrsMem := bmInterEq first.instrsMem second.instrsMem
    loadsMem := bmInterEq first.loadsMem second.loadsMem }

end Flapjack.Compiler.Backend.WordCse
