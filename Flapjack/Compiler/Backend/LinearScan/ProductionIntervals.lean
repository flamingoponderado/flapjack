import Flapjack.Compiler.Backend.LinearScan.ProductionState

/-!
Array-backed interval construction for the linear-scan allocator. These
Flapjack-specific definitions simulate the source definitions over converted
states; the compiler has not yet been switched to this implementation.
-/
namespace Flapjack.LinearScan.Production

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

abbrev FastM (α : Type) := M ProductionState α StateException

def numsetListAddIfLt : List Nat → Int → FastM Unit
  | [], _ => ret ()
  | r :: rs, v =>
      bind (intBegSub r) fun begr =>
        if 0 < begr then
          ignoreBind (updateIntBeg r v) (numsetListAddIfLt rs v)
        else if v ≤ begr then
          ignoreBind (updateIntBeg r v) (numsetListAddIfLt rs v)
        else numsetListAddIfLt rs v

def numsetListAddIfGt : List Nat → Int → FastM Unit
  | [], _ => ret ()
  | r :: rs, v =>
      bind (intEndSub r) fun begr =>
        if 0 < begr then
          ignoreBind (updateIntEnd r v) (numsetListAddIfGt rs v)
        else if begr ≤ v then
          ignoreBind (updateIntEnd r v) (numsetListAddIfGt rs v)
        else numsetListAddIfGt rs v

theorem numsetListAddIfLt_correct (rs : List Nat) (v : Int) :
    Simulates (numsetListAddIfLt rs v) (numsetListAddIfLtMonad rs v) := by
  induction rs with
  | nil => exact simulates_ret ()
  | cons r rs ih =>
    simp only [numsetListAddIfLt, numsetListAddIfLtMonad]
    apply simulates_bind _ _ _ _ (intBegSub_correct r)
    intro begr
    by_cases h : 0 < begr
    · simp only [if_pos h]
      exact simulates_ignoreBind _ _ _ _ (updateIntBeg_correct r v) ih
    · by_cases h' : v ≤ begr
      · simp only [if_neg h, if_pos h']
        exact simulates_ignoreBind _ _ _ _ (updateIntBeg_correct r v) ih
      · simpa only [if_neg h, if_neg h'] using ih

theorem numsetListAddIfGt_correct (rs : List Nat) (v : Int) :
    Simulates (numsetListAddIfGt rs v) (numsetListAddIfGtMonad rs v) := by
  induction rs with
  | nil => exact simulates_ret ()
  | cons r rs ih =>
    simp only [numsetListAddIfGt, numsetListAddIfGtMonad]
    apply simulates_bind _ _ _ _ (intEndSub_correct r)
    intro begr
    by_cases h : 0 < begr
    · simp only [if_pos h]
      exact simulates_ignoreBind _ _ _ _ (updateIntEnd_correct r v) ih
    · by_cases h' : begr ≤ v
      · simp only [if_neg h, if_pos h']
        exact simulates_ignoreBind _ _ _ _ (updateIntEnd_correct r v) ih
      · simpa only [if_neg h, if_neg h'] using ih

def getIntervalsAux : ClashTree → Int → NumSet → FastM (Int × NumSet)
  | .delta wr rd, n, live =>
      ignoreBind (numsetListAddIfLt wr n)
        (ignoreBind (numsetListAddIfGt wr n)
          (ignoreBind (numsetListAddIfGt rd (n - 1))
            (ret (n - 2, numsetListInsert rd (numsetListDelete wr live)))))
  | .set cutset, n, live =>
      ignoreBind (numsetListAddIfGt ((sptToAList cutset).map Prod.fst) n)
        (ret (n - 1, sptUnion cutset live))
  | .branch optcutset ct1 ct2, n, live =>
      bind (getIntervalsAux ct2 n live) fun (n2, live2) =>
        bind (getIntervalsAux ct1 n2 live) fun (n1, live1) =>
          match optcutset with
          | none => ret (n1, sptUnion live1 live2)
          | some cutset =>
              ignoreBind (numsetListAddIfGt ((sptToAList cutset).map Prod.fst) n1)
                (ret (n1 - 1, sptUnion cutset (sptUnion live1 live2)))
  | .seq ct1 ct2, n, live =>
      bind (getIntervalsAux ct2 n live) fun (n2, live2) =>
        getIntervalsAux ct1 n2 live2

theorem getIntervalsAux_correct (tree : ClashTree) (n : Int) (live : NumSet) :
    Simulates (getIntervalsAux tree n live) (getIntervalsCtMonadAux tree n live) := by
  induction tree generalizing n live with
  | delta wr rd =>
    simp only [getIntervalsAux, getIntervalsCtMonadAux]
    exact simulates_ignoreBind _ _ _ _ (numsetListAddIfLt_correct wr n)
      (simulates_ignoreBind _ _ _ _ (numsetListAddIfGt_correct wr n)
        (simulates_ignoreBind _ _ _ _ (numsetListAddIfGt_correct rd (n - 1))
          (simulates_ret _)))
  | set cutset =>
    simp only [getIntervalsAux, getIntervalsCtMonadAux]
    exact simulates_ignoreBind _ _ _ _ (numsetListAddIfGt_correct _ n) (simulates_ret _)
  | branch opt left right ihLeft ihRight =>
    simp only [getIntervalsAux, getIntervalsCtMonadAux]
    apply simulates_bind _ _ _ _ (ihRight n live)
    rintro ⟨n2, live2⟩
    apply simulates_bind _ _ _ _ (ihLeft n2 live)
    rintro ⟨n1, live1⟩
    cases opt with
    | none => exact simulates_ret _
    | some cutset =>
      exact simulates_ignoreBind _ _ _ _ (numsetListAddIfGt_correct _ n1) (simulates_ret _)
  | seq left right ihLeft ihRight =>
    simp only [getIntervalsAux, getIntervalsCtMonadAux]
    apply simulates_bind _ _ _ _ (ihRight n live)
    rintro ⟨n2, live2⟩
    exact ihLeft n2 live2

def getIntervals (tree : ClashTree) : FastM Int :=
  bind (getIntervalsAux tree 0 .ln) fun (n, live) =>
    ignoreBind (numsetListAddIfLt ((sptToAList live).map Prod.fst) n)
      (ignoreBind (numsetListAddIfGt ((sptToAList live).map Prod.fst) n)
        (ret (n - 1)))

theorem getIntervals_correct (tree : ClashTree) :
    Simulates (getIntervals tree) (getIntervalsCtMonad tree) := by
  simp only [getIntervals, getIntervalsCtMonad]
  apply simulates_bind _ _ _ _ (getIntervalsAux_correct tree 0 .ln)
  rintro ⟨n, live⟩
  exact simulates_ignoreBind _ _ _ _ (numsetListAddIfLt_correct _ n)
    (simulates_ignoreBind _ _ _ _ (numsetListAddIfGt_correct _ n) (simulates_ret _))

end Flapjack.LinearScan.Production
