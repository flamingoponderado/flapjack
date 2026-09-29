import Flapjack.Pancake.LoopToWord

/-!
# Original HOL parity for the total exact `loop_to_word$comp`

The original definition is `comp_def` at
`cakeml/pancake/loop_to_wordScript.sml:56-150`. The expected observations are
direct HOL-EVAL results from `scripts/hol-probes/loop_to_word_comp_probe.out`
(23 rows), `scripts/hol-probes/loop_to_word_comp_recursive_probe.out` (4 rows),
and `scripts/hol-probes/loop_to_word_comp_call_probe.out` (3 rows); all 30 of
those rows are replayed here through the total exact `compHOL` over the exact
`HolLoopProg` and `WordLangProgHOL` carriers, using the exact program, label,
context, and live-set inputs of each probe.

The program, label, operand, and emitted-string fields are compared
structurally (no wildcards). The `mk_new_cutset` results are compared by their
exact finite support: `cutsetIs` checks that every expected key is present and
that the tree size equals the key count, so each expected cut-set is pinned to
a concrete key set. `Spt` trees are not canonical, so structural tree equality
with a hand-written `sptInsert` list is neither claimed nor used.
-/

namespace Flapjack.Test.LoopToWordCompHOLParity

open Flapjack Flapjack.LoopToWord

/-- Probe labels `(7, 11)`. -/
def compLabels : Nat × Nat := (7, 11)

/-- Source variable keys 10-14 map to their dense word-register names. -/
def compContext : Spt Nat :=
  sptInsert 14 28 (sptInsert 13 26 (sptInsert 12 24
    (sptInsert 11 22 (sptInsert 10 20 .ln))))

/-- The loop `live_in` fixture `insert 10 () LN` of the recursive probe. -/
def compLiveIn : Spt Unit := sptInsert 10 () .ln

/-- The loop `live_out` fixture `insert 11 () LN` of the recursive probe. -/
def compLiveOut : Spt Unit := sptInsert 11 () .ln

/-- The call `live` fixture `insert 12 () LN` of the call probe. -/
def compCallLive : Spt Unit := sptInsert 12 () .ln

/-- The `If` live fixture `insert 12 () LN` of the recursive probe. -/
def compIfLive : Spt Unit := sptInsert 12 () .ln

/-- The call-handler live fixture `insert 13 () LN` of the call probe
(the `comp`-ignored fourth field of the handler tuple). -/
def compHandlerLive : Spt Unit := sptInsert 13 () .ln

/-- The FFI fixture `FFI «foo» 10 11 12 13 (insert 6 () LN)`. -/
def loopLangFfiRow : HolLoopProg 8 :=
  .ffi (Flapjack.Basis.Pure.MlString.ofString "foo") 10 11 12 13 (sptInsert 6 () .ln)

/-- `cutsetIs t keys` holds when the cut-set `t` has exactly the keys `keys`:
each key is present and the tree size equals the number of keys. -/
def cutsetIs (tree : Spt Unit) (keys : List Nat) : Bool :=
  (keys.all (fun key => (sptLookup key tree).isSome)) && (sptSize tree == keys.length)

attribute [local simp] Flapjack.LoopToWord.compHOL.eq_def findVarHOL compExpHOL
  compContext compLabels compLiveIn compLiveOut compCallLive compIfLive compHandlerLive
  loopLangFfiRow
attribute [local simp] sptLookup_sptInsert_same sptLookup_sptInsert_ne

example : Flapjack.LoopToWord.compHOL (width := 8) compContext .skip compLabels =
    (.skip, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.assign 10 (.var 10)) compLabels =
      (.assign 20 (.var 20), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.primitive [10, 11] .addCarry [12, 13, 14]) compLabels =
      (.seq (.assign 1 (.var 28))
        (.seq (.inst (.arith (.addCarry 3 24 26 1)))
          (.seq (.assign 22 (.var 1)) (.assign 20 (.var 3)))), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.primitive [10] .addCarry [12, 13, 14]) compLabels =
      (.skip, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.arith (.longMul 10 11 12 13)) compLabels =
      (.inst (.arith (.longMul 20 22 24 26)), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.arith (.longDiv 10 11 12 13 14)) compLabels =
      (.inst (.arith (.longDiv 20 22 24 26 28)), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.arith (.div 10 12 13)) compLabels =
      (.inst (.arith (.div 20 24 26)), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.store (.var 10) 11) compLabels =
      (.store (.var 20) 22, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.setGlobal (5 : BitVec 5) (.var 10)) compLabels =
      (.set (.temp (5 : BitVec 5)) (.var 20), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.load32 12 13) compLabels =
      (.inst (.mem .load32 26 (.addr 24 (BitVec.ofNat 8 0))), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.loadByte 13 12) compLabels =
      (.inst (.mem .load8 24 (.addr 26 (BitVec.ofNat 8 0))), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.store32 12 14) compLabels =
      (.inst (.mem .store32 28 (.addr 24 (BitVec.ofNat 8 0))), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.storeByte 13 11) compLabels =
      (.inst (.mem .store8 22 (.addr 26 (BitVec.ofNat 8 0))), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.break 5) compLabels = (.break 5, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.continue 6) compLabels = (.continue 6, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.raise 10) compLabels = (.raise 20, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.return [10, 11, 12]) compLabels =
      (.return 0 [20, 22, 24], compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    .tick compLabels = (.tick, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    .fail compLabels = (.skip, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.locValue 10 3) compLabels =
      (.locValue 20 3, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.shMem .load 10 (.var 12)) compLabels =
      (.shareInst .load 20 (.var 24), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.seq (.assign 10 (.var 11)) (.assign 12 (.const (5 : BitVec 8)))) compLabels =
      (.seq (.assign 20 (.var 22)) (.assign 24 (.const (5 : BitVec 8))), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.ite .equal 10 (.reg 11)
      (.assign 12 (.const (5 : BitVec 8))) (.assign 13 (.var 14)) compIfLive) compLabels =
      (.seq (.ite .equal 20 (.reg 22)
        (.assign 24 (.const (5 : BitVec 8))) (.assign 26 (.var 28))) .tick,
        compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.loop compLiveIn (.assign 12 (.var 13)) compLiveOut) compLabels =
      (.seq .tick (.seq (.loop (mkNewCutsetHOL compContext compLiveIn)
        (.assign 24 (.var 26)) (mkNewCutsetHOL compContext compLiveOut)) .tick),
        compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.mark (.assign 10 (.var 14))) compLabels =
      (.assign 20 (.var 28), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.call none (some 5) [10, 11] none) compLabels =
      (.call none (some 5) [0, 20, 22] none, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.call (some ([12, 13], compCallLive)) (some 5) [10, 11] none) compLabels =
      (.call (some ([24, 26], (mkNewCutsetHOL compContext compCallLive, .ln), .skip,
        compLabels)) (some 5) [20, 22] none, (7, 12)) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.call (some ([12, 13], compCallLive)) (some 5) [10, 11]
      (some (14, .assign 10 (.var 11), .assign 12 (.const (5 : BitVec 8)), compHandlerLive)))
      compLabels =
      (.seq (.call
        (some ([24, 26], (mkNewCutsetHOL compContext compCallLive, .ln),
          .assign 24 (.const (5 : BitVec 8)), compLabels))
        (some 5) [20, 22] (some (28, .assign 20 (.var 22), (7, 12)))) .tick,
        (7, 13)) := by simp

/-- All 30 rows of the three direct HOL probes, replayed through the total
exact `compHOL` with the exact probe inputs; `mk_new_cutset` results are pinned
by their exact key sets through `cutsetIs`. -/
def compHOLProbeChecks : List Bool :=
  [ (match Flapjack.LoopToWord.compHOL (width := 8) compContext .skip compLabels with
      | (.skip, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.assign 10 (.var 10)) compLabels with
      | (.assign 20 (.var 20), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.primitive [10, 11] .addCarry [12, 13, 14]) compLabels with
      | (.seq (.assign 1 (.var 28))
          (.seq (.inst (.arith (.addCarry 3 24 26 1)))
            (.seq (.assign 22 (.var 1)) (.assign 20 (.var 3)))), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.primitive [10] .addCarry [12, 13, 14]) compLabels with
      | (.skip, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.primitive [10, 11] .addCarry [12, 13]) compLabels with
      | (.skip, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.arith (.longMul 10 11 12 13)) compLabels with
      | (.inst (.arith (.longMul 20 22 24 26)), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.arith (.longDiv 10 11 12 13 14)) compLabels with
      | (.inst (.arith (.longDiv 20 22 24 26 28)), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.arith (.div 10 12 13)) compLabels with
      | (.inst (.arith (.div 20 24 26)), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.store (.var 10) 11) compLabels with
      | (.store (.var 20) 22, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.setGlobal (5 : BitVec 5) (.var 10)) compLabels with
      | (.set (.temp (5 : BitVec 5)) (.var 20), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.load32 12 13) compLabels with
      | (.inst (.mem .load32 26 (.addr 24 (BitVec.ofNat 8 0))), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.loadByte 13 12) compLabels with
      | (.inst (.mem .load8 24 (.addr 26 (BitVec.ofNat 8 0))), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.store32 12 14) compLabels with
      | (.inst (.mem .store32 28 (.addr 24 (BitVec.ofNat 8 0))), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.storeByte 13 11) compLabels with
      | (.inst (.mem .store8 22 (.addr 26 (BitVec.ofNat 8 0))), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.break 5) compLabels with
      | (.break 5, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.continue 6) compLabels with
      | (.continue 6, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.raise 10) compLabels with
      | (.raise 20, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.return [10, 11, 12]) compLabels with
      | (.return 0 [20, 22, 24], (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext .tick compLabels with
      | (.tick, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext .fail compLabels with
      | (.skip, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.locValue 10 3) compLabels with
      | (.locValue 20 3, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        loopLangFfiRow compLabels with
      | (.ffi name 20 22 24 26 (cutset, .ln), (7, 11)) =>
        decide (name = Flapjack.Basis.Pure.MlString.ofString "foo") && cutsetIs cutset [0]
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.shMem .load 10 (.var 12)) compLabels with
      | (.shareInst .load 20 (.var 24), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.seq (.assign 10 (.var 11)) (.assign 12 (.const (5 : BitVec 8)))) compLabels with
      | (.seq (.assign 20 (.var 22)) (.assign 24 (.const (5 : BitVec 8))), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.ite .equal 10 (.reg 11)
          (.assign 12 (.const (5 : BitVec 8))) (.assign 13 (.var 14)) compIfLive) compLabels with
      | (.seq (.ite .equal 20 (.reg 22)
          (.assign 24 (.const (5 : BitVec 8))) (.assign 26 (.var 28))) .tick,
          (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.loop compLiveIn (.assign 12 (.var 13)) compLiveOut) compLabels with
      | (.seq .tick (.seq (.loop cutIn (.assign 24 (.var 26)) cutOut) .tick),
          (7, 11)) => cutsetIs cutIn [0, 20] && cutsetIs cutOut [0, 22]
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.mark (.assign 10 (.var 14))) compLabels with
      | (.assign 20 (.var 28), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.call none (some 5) [10, 11] none) compLabels with
      | (.call none (some 5) [0, 20, 22] none, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.call (some ([12, 13], compCallLive)) (some 5) [10, 11] none) compLabels with
      | (.call (some ([24, 26], (cutset, .ln), .skip, (7, 11))) (some 5)
          [20, 22] none, (7, 12)) => cutsetIs cutset [0, 24]
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.call (some ([12, 13], compCallLive)) (some 5) [10, 11]
          (some (14, .assign 10 (.var 11), .assign 12 (.const (5 : BitVec 8)), compHandlerLive)))
          compLabels with
      | (.seq (.call (some ([24, 26], (cutset, .ln),
          .assign 24 (.const (5 : BitVec 8)), (7, 11))) (some 5) [20, 22]
          (some (28, .assign 20 (.var 22), (7, 12)))) .tick, (7, 13)) =>
        cutsetIs cutset [0, 24]
      | _ => false) ]

#guard compHOLProbeChecks.all id

def runChecks : IO Bool := do
  let passed := compHOLProbeChecks.all id
  if passed then
    IO.println "PASS LoopToWord total compHOL exact HOL EVAL rows (30 rows, cutsets pinned)"
  else
    IO.println "FAIL LoopToWord total compHOL exact HOL EVAL rows (30 rows, cutsets pinned)"
  pure passed

end Flapjack.Test.LoopToWordCompHOLParity
