import Flapjack.Pancake.LoopToWord

/-!
# Original HOL parity for the total exact `loop_to_word$comp`

The original definition is `comp_def` at
`cakeml/pancake/loop_to_wordScript.sml:56-152`. The expected observations are
direct HOL-EVAL results from `scripts/hol-probes/loop_to_word_comp_probe.out`,
`scripts/hol-probes/loop_to_word_comp_recursive_probe.out`, and
`scripts/hol-probes/loop_to_word_comp_call_probe.out`, replayed here through the
total exact `compHOL` over the exact `HolLoopProg` and `WordLangProgHOL` carriers.
-/

namespace Flapjack.Test.LoopToWordCompHOLParity

open Flapjack Flapjack.LoopToWord

/-- Probe labels `(7, 11)`. -/
def compLabels : Nat × Nat := (7, 11)

/-- Source variable keys 10-14 map to their dense word-register names. -/
def compContext : Spt Nat :=
  sptInsert 14 28 (sptInsert 13 26 (sptInsert 12 24
    (sptInsert 11 22 (sptInsert 10 20 .ln))))

/-- `insert 10 () (insert 11 () LN)`, the loop cut-set fixture. -/
def compLive : Spt Unit := sptInsert 11 () (sptInsert 10 () .ln)

/-- The FFI fixture `FFI «foo» 10 11 12 13 (insert 6 () LN)`. -/
def loopLangFfiRow : HolLoopProg 8 :=
  .ffi (Flapjack.Basis.Pure.MlString.ofString "foo") 10 11 12 13 (sptInsert 6 () .ln)

attribute [local simp] Flapjack.LoopToWord.compHOL.eq_def findVarHOL compExpHOL
  compContext compLabels compLive loopLangFfiRow
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
    (.return [10, 11, 12]) compLabels =
      (.return 0 [20, 22, 24], compLabels) := by simp

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
      (.assign 12 (.const (5 : BitVec 8))) (.assign 13 (.var 14)) compLive) compLabels =
      (.seq (.ite .equal 20 (.reg 22)
        (.assign 24 (.const (5 : BitVec 8))) (.assign 26 (.var 28))) .tick,
        compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.loop compLive (.assign 12 (.var 13)) compLive) compLabels =
      (.seq .tick (.seq (.loop (mkNewCutsetHOL compContext compLive)
        (.assign 24 (.var 26)) (mkNewCutsetHOL compContext compLive)) .tick),
        compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.mark (.assign 10 (.var 14))) compLabels =
      (.assign 20 (.var 28), compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.call none (some 5) [10, 11] none) compLabels =
      (.call none (some 5) [0, 20, 22] none, compLabels) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.call (some ([12, 13], compLive)) (some 5) [10, 11] none) compLabels =
      (.call (some ([24, 26], (mkNewCutsetHOL compContext compLive, .ln), .skip,
        compLabels)) (some 5) [20, 22] none, (7, 12)) := by simp

example : Flapjack.LoopToWord.compHOL (width := 8) compContext
    (.call (some ([12, 13], compLive)) (some 5) [10, 11]
      (some (14, .assign 10 (.var 11), .assign 12 (.const (5 : BitVec 8)), compLive)))
      compLabels =
      (.seq (.call
        (some ([24, 26], (mkNewCutsetHOL compContext compLive, .ln),
          .assign 24 (.const (5 : BitVec 8)), compLabels))
        (some 5) [20, 22] (some (28, .assign 20 (.var 22), (7, 12)))) .tick,
        (7, 13)) := by simp

/-- Every row of the three direct HOL probes on the exact carrier. -/
def compHOLProbeChecks : List Bool :=
  [ (match Flapjack.LoopToWord.compHOL (width := 8) compContext
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
        (.load32 12 13) compLabels with
      | (.inst (.mem .load32 26 (.addr 24 _)), (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.return [10, 11, 12]) compLabels with
      | (.return 0 [20, 22, 24], (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        loopLangFfiRow compLabels with
      | (.ffi _ 20 22 24 26 (cutset, .ln), (7, 11)) => (sptLookup 0 cutset).isSome
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
        (.call none (some 5) [10, 11] none) compLabels with
      | (.call none (some 5) [0, 20, 22] none, (7, 11)) => true
      | _ => false),
    (match Flapjack.LoopToWord.compHOL (width := 8) compContext
        (.call (some ([12, 13], compLive)) (some 5) [10, 11] none) compLabels with
      | (.call (some ([24, 26], (cutset, .ln), .skip, (7, 11))) (some 5)
          [20, 22] none, (7, 12)) => (sptLookup 0 cutset).isSome
      | _ => false) ]

def runChecks : IO Bool := do
  let passed := compHOLProbeChecks.all id
  if passed then
    IO.println "PASS LoopToWord total compHOL exact HOL EVAL rows"
  else
    IO.println "FAIL LoopToWord total compHOL exact HOL EVAL rows"
  pure passed

end Flapjack.Test.LoopToWordCompHOLParity
