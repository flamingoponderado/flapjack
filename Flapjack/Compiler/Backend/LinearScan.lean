import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Misc.Option

/-!
# linear_scan definitions

Counterpart of `cakeml/compiler/backend/reg_alloc/linear_scanScript.sml`.
This module holds the pure live-tree and interval definitions
(`linear_scanScript.sml:17-312`). They are proof-side ports: the executed
allocator still uses `Flapjack/RiscV/LinearScan*.lean`, whose migration is
separate work.

Carrier conventions: HOL `num_set` is `NumSet`, `int num_map` is `Spt Int`,
HOL `int` is Lean `Int`, and HOL `num set` (the result of `domain`, `set` and
`UNION`) is a predicate `Nat → Prop`. Proof-only HOL `bool` definitions whose
bodies quantify (`check_number_property`, `check_startlive_prop`,
`check_intervals`) or whose parameter is an arbitrary HOL predicate are
`Prop`-valued; the executable comparison parameter of `numset_list_add_if` is a
Lean `Bool` function, as are the executed HOL comparisons it is applied to.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc

/-- HOL `linear_scan$live_tree` (`linear_scanScript.sml:17-22`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "live_tree"]
inductive LiveTree where
  | writes (names : List Nat)
  | reads (names : List Nat)
  | branch (left right : LiveTree)
  | seq (left right : LiveTree)
  deriving Repr, DecidableEq

/-- Left-to-right insertion of unit entries (`linear_scanScript.sml:25-28`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "numset_list_insert_def"]
def numsetListInsert : List Nat → NumSet → NumSet
  | [], t => t
  | x :: xs, t => numsetListInsert xs (sptInsert x () t)

/-- Right-fold insertion (`linear_scanScript.sml:30-33`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "numset_list_insert_nottailrec_def"]
def numsetListInsertNottailrec : List Nat → NumSet → NumSet
  | [], t => t
  | x :: xs, t => sptInsert x () (numsetListInsertNottailrec xs t)

/-- Live-tree view of a clash tree (`linear_scanScript.sml:35-58`). Cut sets
are listed through `MAP FST (toAList _)`. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_live_tree_def"]
def getLiveTree : ClashTree → LiveTree
  | .delta wr rd => .seq (.reads rd) (.writes wr)
  | .set cutset =>
      let cutlist := (sptToAList cutset).map Prod.fst
      .reads cutlist
  | .branch optcutset ct1 ct2 =>
      let lt1 := getLiveTree ct1
      let lt2 := getLiveTree ct2
      match optcutset with
      | some cutset =>
          let cutlist := (sptToAList cutset).map Prod.fst
          .seq (.reads cutlist) (.branch lt1 lt2)
      | none => .branch lt1 lt2
  | .seq ct1 ct2 =>
      let lt2 := getLiveTree ct2
      let lt1 := getLiveTree ct1
      .seq lt1 lt2

/-- Colouring checker over a live tree (`linear_scanScript.sml:60-88`). As in
HOL, `Writes` checks the written names and then discards that check's
output; `Seq` checks its right child first. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "check_live_tree_def"]
def checkLiveTree (f : Nat → Nat) : LiveTree → NumSet → NumSet →
    Option (NumSet × NumSet)
  | .writes l, live, flive =>
      match checkPartialCol f l live flive with
      | none => none
      | some _ =>
          let livein := numsetListDelete l live
          let flivein := numsetListDelete (l.map f) flive
          some (livein, flivein)
  | .reads l, live, flive => checkPartialCol f l live flive
  | .branch lt1 lt2, live, flive =>
      match checkLiveTree f lt1 live flive with
      | none => none
      | some (livein1, flivein1) =>
          match checkLiveTree f lt2 live flive with
          | none => none
          | some (livein2, _flivein2) =>
              checkPartialCol f
                ((sptToAList (sptDifference livein2 livein1)).map Prod.fst)
                livein1 flivein1
  | .seq lt1 lt2, live, flive =>
      match checkLiveTree f lt2 live flive with
      | none => none
      | some (livein2, flivein2) => checkLiveTree f lt1 livein2 flivein2

/-- Backward liveness over a live tree (`linear_scanScript.sml:90-106`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "get_live_backward_def"]
def getLiveBackward : LiveTree → NumSet → NumSet
  | .writes l, live => numsetListDelete l live
  | .reads l, live => numsetListInsert l live
  | .branch lt1 lt2, live =>
      let live1 := getLiveBackward lt1 live
      let live2 := getLiveBackward lt2 live
      numsetListInsert ((sptToAList (sptDifference live2 live1)).map Prod.fst) live1
  | .seq lt1 lt2, live => getLiveBackward lt1 (getLiveBackward lt2 live)

/-- Prefix the names live at entry with a `Writes`
(`linear_scanScript.sml:108-113`). The `live = LN` test is equality of raw
sparse trees, as in HOL. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "fix_domination_def"]
def fixDomination (lt : LiveTree) : LiveTree :=
  let live := getLiveBackward lt .ln
  if live = .ln then lt
  else .seq (.writes ((sptToAList live).map Prod.fst)) lt

/-- Conditional interval-bound update (`linear_scanScript.sml:115-127`): an
absent key is always inserted, a present one only when `P v v'` holds. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "numset_list_add_if_def"]
def numsetListAddIf : List Nat → Int → Spt Int → (Int → Int → Bool) → Spt Int
  | [], _v, s, _P => s
  | x :: xs, v, s, P =>
      match sptLookup x s with
      | some v' =>
          if P v v' then numsetListAddIf xs v (sptInsert x v s) P
          else numsetListAddIf xs v s P
      | none => numsetListAddIf xs v (sptInsert x v s) P

/-- HOL `numset_list_add_if l v s $<=` (`linear_scanScript.sml:129-131`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "numset_list_add_if_lt_def"]
def numsetListAddIfLt (l : List Nat) (v : Int) (s : Spt Int) : Spt Int :=
  numsetListAddIf l v s (fun a b => decide (a ≤ b))

/-- HOL `numset_list_add_if l v s (\a b. b <= a)`
(`linear_scanScript.sml:133-135`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "numset_list_add_if_gt_def"]
def numsetListAddIfGt (l : List Nat) (v : Int) (s : Spt Int) : Spt Int :=
  numsetListAddIf l v s (fun a b => decide (b ≤ a))

/-- Number of leaves of a live tree, as an integer
(`linear_scanScript.sml:137-151`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "size_of_live_tree_def"]
def sizeOfLiveTree : LiveTree → Int
  | .writes _ => 1
  | .reads _ => 1
  | .branch lt1 lt2 => sizeOfLiveTree lt1 + sizeOfLiveTree lt2
  | .seq lt1 lt2 => sizeOfLiveTree lt1 + sizeOfLiveTree lt2

/-- Backward interval numbering (`linear_scanScript.sml:153-169`). Both
compound cases number the right child first. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_def"]
def getIntervals : LiveTree → Int → Spt Int → Spt Int → Int × Spt Int × Spt Int
  | .writes l, n, intBeg, intEnd =>
      (n - 1, numsetListAddIfLt l n intBeg, numsetListAddIfGt l n intEnd)
  | .reads l, n, intBeg, intEnd =>
      (n - 1, intBeg, numsetListAddIfGt l n intEnd)
  | .branch lt1 lt2, n, intBeg, intEnd =>
      let (n2, intBeg2, intEnd2) := getIntervals lt2 n intBeg intEnd
      getIntervals lt1 n2 intBeg2 intEnd2
  | .seq lt1 lt2, n, intBeg, intEnd =>
      let (n2, intBeg2, intEnd2) := getIntervals lt2 n intBeg intEnd
      getIntervals lt1 n2 intBeg2 intEnd2

/-- Interval numbering that also tracks live names
(`linear_scanScript.sml:173-191`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "get_intervals_withlive_def"]
def getIntervalsWithlive : LiveTree → Int → Spt Int → Spt Int → NumSet →
    Int × Spt Int × Spt Int
  | .writes l, n, intBeg, intEnd, _live =>
      (n - 1, numsetListAddIfLt l n intBeg, numsetListAddIfGt l n intEnd)
  | .reads l, n, intBeg, intEnd, _live =>
      (n - 1, numsetListDelete l intBeg, numsetListAddIfGt l n intEnd)
  | .branch lt1 lt2, n, intBeg, intEnd, live =>
      let (n2, intBeg2, intEnd2) := getIntervalsWithlive lt2 n intBeg intEnd live
      let (n1, intBeg1, intEnd1) :=
        getIntervalsWithlive lt1 n2 (sptDifference intBeg2 live) intEnd2 live
      (n1, sptDifference intBeg1
        (sptUnion (getLiveBackward lt1 live) (getLiveBackward lt2 live)), intEnd1)
  | .seq lt1 lt2, n, intBeg, intEnd, live =>
      let (n2, intBeg2, intEnd2) := getIntervalsWithlive lt2 n intBeg intEnd live
      let (n1, intBeg1, intEnd1) :=
        getIntervalsWithlive lt1 n2 intBeg2 intEnd2 (getLiveBackward lt2 live)
      (n1, intBeg1, intEnd1)

/-- `P` holds after every leaf, with the leaf's number and outgoing live set
(`linear_scanScript.sml:193-215`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "check_number_property_def"]
def checkNumberProperty (P : Int → NumSet → Prop) : LiveTree → Int → NumSet → Prop
  | .writes l, n, live =>
      let nOut := n - 1
      let liveOut := numsetListDelete l live
      P nOut liveOut
  | .reads l, n, live =>
      let nOut := n - 1
      let liveOut := numsetListInsert l live
      P nOut liveOut
  | .branch lt1 lt2, n, live =>
      let r2 := checkNumberProperty P lt2 n live
      let r1 := checkNumberProperty P lt1 (n - sizeOfLiveTree lt2) live
      r1 ∧ r2
  | .seq lt1 lt2, n, live =>
      let r2 := checkNumberProperty P lt2 n live
      let r1 := checkNumberProperty P lt1 (n - sizeOfLiveTree lt2)
        (getLiveBackward lt2 live)
      r1 ∧ r2

/-- `check_number_property` that also checks `P` after each `Branch`
(`linear_scanScript.sml:217-239`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "check_number_property_strong_def"]
def checkNumberPropertyStrong (P : Int → NumSet → Prop) :
    LiveTree → Int → NumSet → Prop
  | .writes l, n, live =>
      let nOut := n - 1
      let liveOut := numsetListDelete l live
      P nOut liveOut
  | .reads l, n, live =>
      let nOut := n - 1
      let liveOut := numsetListInsert l live
      P nOut liveOut
  | .branch lt1 lt2, n, live =>
      let r2 := checkNumberPropertyStrong P lt2 n live
      let r1 := checkNumberPropertyStrong P lt1 (n - sizeOfLiveTree lt2) live
      r1 ∧ r2 ∧ P (n - sizeOfLiveTree (.branch lt1 lt2))
        (getLiveBackward (.branch lt1 lt2) live)
  | .seq lt1 lt2, n, live =>
      let r2 := checkNumberPropertyStrong P lt2 n live
      let r1 := checkNumberPropertyStrong P lt1 (n - sizeOfLiveTree lt2)
        (getLiveBackward lt2 live)
      r1 ∧ r2

/-- Written names start no later than their write and end no earlier
(`linear_scanScript.sml:241-260`). `option_CASE (lookup r beg) ndef (\x.x)`
is the `match` on the lookup. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "check_startlive_prop_def"]
def checkStartliveProp : LiveTree → Int → Spt Int → Spt Int → Int → Prop
  | .writes l, n, beg, end_, ndef =>
      ∀ r, r ∈ l →
        (match sptLookup r beg with
          | none => ndef
          | some x => x) ≤ n ∧
        (∃ v, sptLookup r end_ = some v ∧ n ≤ v)
  | .reads _, _n, _beg, _end, _ndef => True
  | .branch lt1 lt2, n, beg, end_, ndef =>
      let r2 := checkStartliveProp lt2 n beg end_ ndef
      let r1 := checkStartliveProp lt1 (n - sizeOfLiveTree lt2) beg end_ ndef
      r1 ∧ r2
  | .seq lt1 lt2, n, beg, end_, ndef =>
      let r2 := checkStartliveProp lt2 n beg end_ ndef
      let r1 := checkStartliveProp lt1 (n - sizeOfLiveTree lt2) beg end_ ndef
      r1 ∧ r2

/-- The set of names in a live tree (`linear_scanScript.sml:262-267`). HOL
`set l` is list membership and `UNION` pointwise disjunction. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "live_tree_registers_def"]
def liveTreeRegisters : LiveTree → Nat → Prop
  | .writes l => fun r => r ∈ l
  | .reads l => fun r => r ∈ l
  | .branch lt1 lt2 => fun r => liveTreeRegisters lt1 r ∨ liveTreeRegisters lt2 r
  | .seq lt1 lt2 => fun r => liveTreeRegisters lt1 r ∨ liveTreeRegisters lt2 r

/-- Closed-interval intersection (`linear_scanScript.sml:269-271`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "interval_intersect_def"]
def intervalIntersect : Int × Int → Int × Int → Prop
  | (l1, r1), (l2, r2) => l1 ≤ r2 ∧ l2 ≤ r1

/-- Closed-interval membership (`linear_scanScript.sml:273-275`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "point_inside_interval_def"]
def pointInsideInterval : Int × Int → Int → Prop
  | (l, r), n => l ≤ n ∧ n ≤ r

/-- Intersecting intervals of distinct names get distinct colours
(`linear_scanScript.sml:277-284`). HOL `THE` is `holThe`; as in HOL, nothing
is known about `THE NONE` (an end missing for a name with a beginning). As in
HOL (`(num -> α) -> ...`), the colouring's codomain is arbitrary. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "check_intervals_def"]
def checkIntervals {α : Type} (f : Nat → α) (intBeg intEnd : Spt Int) : Prop :=
  ∀ r1 r2,
    sptDomain intBeg r1 ∧ sptDomain intBeg r2 ∧
    intervalIntersect (holThe (sptLookup r1 intBeg), holThe (sptLookup r1 intEnd))
      (holThe (sptLookup r2 intBeg), holThe (sptLookup r2 intEnd)) ∧
    f r1 = f r2 →
    r1 = r2

/-- Interval numbering directly over a clash tree
(`linear_scanScript.sml:286-305`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "get_intervals_ct_aux_def"]
def getIntervalsCtAux : ClashTree → Int → Spt Int → Spt Int → NumSet →
    Int × Spt Int × Spt Int × NumSet
  | .delta wr rd, n, intBeg, intEnd, live =>
      (n - 2, numsetListAddIfLt wr n intBeg,
        numsetListAddIfGt rd (n - 1) (numsetListAddIfGt wr n intEnd),
        numsetListInsert rd (numsetListDelete wr live))
  | .set cutset, n, intBeg, intEnd, live =>
      (n - 1, intBeg, numsetListAddIfGt ((sptToAList cutset).map Prod.fst) n intEnd,
        sptUnion cutset live)
  | .branch optcutset ct1 ct2, n, intBeg, intEnd, live =>
      let (n2, intBeg2, intEnd2, live2) := getIntervalsCtAux ct2 n intBeg intEnd live
      let (n1, intBeg1, intEnd1, live1) := getIntervalsCtAux ct1 n2 intBeg2 intEnd2 live
      match optcutset with
      | none => (n1, intBeg1, intEnd1, sptUnion live1 live2)
      | some cutset =>
          (n1 - 1, intBeg1,
            numsetListAddIfGt ((sptToAList cutset).map Prod.fst) n1 intEnd1,
            sptUnion cutset (sptUnion live1 live2))
  | .seq ct1 ct2, n, intBeg, intEnd, live =>
      let (n2, intBeg2, intEnd2, live2) := getIntervalsCtAux ct2 n intBeg intEnd live
      getIntervalsCtAux ct1 n2 intBeg2 intEnd2 live2

/-- Intervals of a clash tree, closing the names live at entry
(`linear_scanScript.sml:307-312`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_ct_def"]
def getIntervalsCt (ct : ClashTree) : Int × Spt Int × Spt Int :=
  let (n, intBeg, intEnd, live) := getIntervalsCtAux ct 0 .ln .ln .ln
  let listlive := (sptToAList live).map Prod.fst
  (n - 1, numsetListAddIfLt listlive n intBeg, numsetListAddIfGt listlive n intEnd)

end Flapjack.LinearScan
