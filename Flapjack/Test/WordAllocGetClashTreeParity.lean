import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg
import Flapjack.Compiler.Backend.WordAlloc.ProductionBufferClashTree

namespace Flapjack.Test.WordAllocGetClashTreeParity

open Flapjack.WordAlloc
open Flapjack.RegAlloc

/-! Direct original HOL rows replaying every probe row in
`scripts/hol-probes/word_alloc_get_clash_tree_probe.out`. These are regression
observations over the exact positive-width `WordLangProgHOL (BitVec 8)` program
carrier, the literal `ClashTree` receiver, and explicit `Spt Unit` num_set trees,
not an independent cross-language equivalence theorem. -/

private abbrev setA : NumSet := sptFromAList [(1, ()), (2, ())]
private abbrev setB : NumSet := sptFromAList [(3, ())]
-- HOL-exact paired fixtures for the rows whose original inputs are b = [3, 4]
-- (Alloc/Install/FFI) and a = [1], b = [2] (Loop/Break/Continue); see
-- scripts/hol-probes/word_alloc_get_clash_tree_probeScript.sml.
private abbrev setB34 : NumSet := sptFromAList [(3, ()), (4, ())]
private abbrev setA1 : NumSet := sptFromAList [(1, ())]
private abbrev setB2 : NumSet := sptFromAList [(2, ())]

-- gct_skip=T
example : getClashTree (.skip : WordLangProgHOL (BitVec 8)) [] = .delta [] [] := by
  decide +kernel

-- gct_move=T
example : getClashTree (.move 3 [(1, 2), (3, 4)] : WordLangProgHOL (BitVec 8)) [] =
    .delta [1, 3] [2, 4] := by decide +kernel

-- gct_inst=T
example : getClashTree
    (.inst (.arith (.binop .add 1 2 (.reg 3))) : WordLangProgHOL (BitVec 8)) [] =
    .delta [1] [2, 3] := by decide +kernel

-- gct_assign=T
example : getClashTree
    (.assign 1 (.op .add [.var 2, .var 3]) : WordLangProgHOL (BitVec 8)) [] =
    .delta [1] [2, 3] := by decide +kernel

-- gct_get=T
example : getClashTree (.get 1 .nextFree : WordLangProgHOL (BitVec 8)) [] =
    .delta [1] [] := by decide +kernel

-- gct_store=T
example : getClashTree (.store (.var 2) 3 : WordLangProgHOL (BitVec 8)) [] =
    .delta [] [3, 2] := by decide +kernel

-- gct_seq=T
example : getClashTree (.seq .skip .tick : WordLangProgHOL (BitVec 8)) [] =
    .seq (.delta [] []) (.delta [] []) := by decide +kernel

-- gct_if_reg=T
example : getClashTree
    (.ite .equal 1 (.reg 2) .skip .tick : WordLangProgHOL (BitVec 8)) [] =
    .seq (.delta [] [1, 2]) (.branch none (.delta [] []) (.delta [] [])) := by
  decide +kernel

-- gct_if_imm=T
example : getClashTree
    (.ite .equal 1 (.imm (7 : BitVec 8)) .skip .tick : WordLangProgHOL (BitVec 8)) [] =
    .seq (.delta [] [1]) (.branch none (.delta [] []) (.delta [] [])) := by
  decide +kernel

-- gct_mustterminate=T
example : getClashTree (.mustTerminate .skip : WordLangProgHOL (BitVec 8)) [] =
    .delta [] [] := by decide +kernel

-- gct_alloc=T
example : getClashTree (.alloc 5 (setA, setB34) : WordLangProgHOL (BitVec 8)) [] =
    .seq (.delta [] [5]) (.set (sptUnion setA setB34)) := by decide +kernel

-- gct_install=T
example : getClashTree (.install 1 2 3 4 (setA, setB34) : WordLangProgHOL (BitVec 8)) [] =
    .seq (.delta [] [4, 3, 2, 1])
      (.seq (.set (sptUnion setA setB34)) (.delta [1] [])) := by decide +kernel

-- gct_codebufferwrite=T
example : getClashTree (.codeBufferWrite 1 2 : WordLangProgHOL (BitVec 8)) [] =
    .delta [] [2, 1] := by decide +kernel

-- gct_databufferwrite=T
example : getClashTree (.dataBufferWrite 1 2 : WordLangProgHOL (BitVec 8)) [] =
    .delta [] [2, 1] := by decide +kernel

-- Executed producer replay of those same original HOL observations. These
-- explicit ordered lists detect a reversal even though set membership agrees.
example : Flapjack.wordClashTree (.codeBufferWrite 1 2 : WordProg (BitVec 8)) [] =
    .delta [] [2, 1] := by simp only [Flapjack.wordClashTree]

example : Flapjack.wordClashTree (.dataBufferWrite 1 2 : WordProg (BitVec 8)) [] =
    .delta [] [2, 1] := by simp only [Flapjack.wordClashTree]

-- gct_ffi=T
example : getClashTree
    (.ffi (.implode [65]) 1 2 3 4 (setA, setB34) : WordLangProgHOL (BitVec 8)) [] =
    .seq (.delta [] [1, 2, 3, 4]) (.set (sptUnion setA setB34)) := by decide +kernel

-- gct_raise=T
example : getClashTree (.raise 1 : WordLangProgHOL (BitVec 8)) [] = .delta [] [1] := by
  decide +kernel

-- gct_return=T
example : getClashTree (.return 1 [2, 3] : WordLangProgHOL (BitVec 8)) [] =
    .delta [] [1, 2, 3] := by decide +kernel

-- gct_tick=T
example : getClashTree (.tick : WordLangProgHOL (BitVec 8)) [] = .delta [] [] := by
  decide +kernel

-- gct_locvalue=T
example : getClashTree (.locValue 1 2 : WordLangProgHOL (BitVec 8)) [] =
    .delta [1] [] := by decide +kernel

-- gct_set=T
example : getClashTree (.set .nextFree (.var 2) : WordLangProgHOL (BitVec 8)) [] =
    .delta [] [2] := by decide +kernel

-- gct_opcurrheap=T
example : getClashTree (.opCurrHeap .add 1 2 : WordLangProgHOL (BitVec 8)) [] =
    .delta [1] [2] := by decide +kernel

-- gct_storeconsts=T
example : getClashTree (.storeConsts 1 2 3 4 [] : WordLangProgHOL (BitVec 8)) [] =
    .delta [1, 2, 3, 4] [3, 4] := by decide +kernel

-- gct_shareinst_store=T
example : getClashTree (.shareInst .store 5 (.var 2) : WordLangProgHOL (BitVec 8)) [] =
    .delta [] [5, 2] := by decide +kernel

-- gct_shareinst_other=T
example : getClashTree (.shareInst .load 5 (.var 2) : WordLangProgHOL (BitVec 8)) [] =
    .delta [5] [2] := by decide +kernel

-- gct_loop=T
example : getClashTree (.loop setA1 .skip setB2 : WordLangProgHOL (BitVec 8)) [] =
    .seq (.set setA1) (.seq (.set setB2) (.seq (.delta [] []) (.set setA1))) := by
  decide +kernel

-- gct_break_none=T
example : getClashTree (.break 2 : WordLangProgHOL (BitVec 8)) [] = .set .ln := by
  decide +kernel

-- gct_break_some=T
example : getClashTree (.break 0 : WordLangProgHOL (BitVec 8)) [(setA1, setB2)] =
    .set setB2 := by decide +kernel

-- gct_continue_none=T
example : getClashTree (.continue 2 : WordLangProgHOL (BitVec 8)) [] = .set .ln := by
  decide +kernel

-- gct_continue_some=T
example : getClashTree (.continue 0 : WordLangProgHOL (BitVec 8)) [(setA1, setB2)] =
    .set setA1 := by decide +kernel

-- gct_call_none=T
example : getClashTree (.call none none [3, 4] none : WordLangProgHOL (BitVec 8)) [] =
    .set (sptInsert 3 () (sptInsert 4 () .ln)) := by decide +kernel

-- gct_call_ret=T
example :
    let cutset := sptUnion setA setB
    let argsSet := sptInsert 3 () (sptInsert 4 () .ln)
    let liveSet := sptUnion cutset argsSet
    getClashTree
      (.call (some ([7, 8], (setA, setB), .skip, 0, 0)) none [3, 4] none
        : WordLangProgHOL (BitVec 8)) [] =
      .seq (.set liveSet)
        (.seq (.set (sptInsert 7 () (sptInsert 8 () cutset))) (.delta [] [])) := by
  decide +kernel

-- gct_call_ret_handler=T
example :
    let cutset := sptUnion setA setB
    let argsSet := sptInsert 3 () (sptInsert 4 () .ln)
    let liveSet := sptUnion cutset argsSet
    getClashTree
      (.call (some ([7, 8], (setA, setB), .skip, 0, 0)) none [3, 4]
        (some (9, .tick, 0, 0)) : WordLangProgHOL (BitVec 8)) [] =
      .branch (some liveSet)
        (.seq (.set (sptInsert 7 () (sptInsert 8 () cutset))) (.delta [] []))
        (.seq (.set (sptInsert 9 () cutset)) (.delta [] [])) := by
  decide +kernel

/-- Runtime PASS lines mirroring `CompilerParity`'s other parity registrations;
the same propositions are already kernel-checked above. -/
def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("getClashTree Skip",
        decide (getClashTree (.skip : WordLangProgHOL (BitVec 8)) [] = .delta [] [])),
      ("getClashTree Move",
        decide (getClashTree (.move 3 [(1, 2), (3, 4)] : WordLangProgHOL (BitVec 8)) [] =
          .delta [1, 3] [2, 4])),
      ("getClashTree Inst",
        decide (getClashTree
          (.inst (.arith (.binop .add 1 2 (.reg 3))) : WordLangProgHOL (BitVec 8)) [] =
          .delta [1] [2, 3])),
      ("getClashTree Assign",
        decide (getClashTree
          (.assign 1 (.op .add [.var 2, .var 3]) : WordLangProgHOL (BitVec 8)) [] =
          .delta [1] [2, 3])),
      ("getClashTree Get",
        decide (getClashTree (.get 1 .nextFree : WordLangProgHOL (BitVec 8)) [] =
          .delta [1] [])),
      ("getClashTree Store",
        decide (getClashTree (.store (.var 2) 3 : WordLangProgHOL (BitVec 8)) [] =
          .delta [] [3, 2])),
      ("getClashTree Seq",
        decide (getClashTree (.seq .skip .tick : WordLangProgHOL (BitVec 8)) [] =
          .seq (.delta [] []) (.delta [] []))),
      ("getClashTree If Reg",
        decide (getClashTree
          (.ite .equal 1 (.reg 2) .skip .tick : WordLangProgHOL (BitVec 8)) [] =
          .seq (.delta [] [1, 2]) (.branch none (.delta [] []) (.delta [] [])))),
      ("getClashTree If Imm",
        decide (getClashTree
          (.ite .equal 1 (.imm (7 : BitVec 8)) .skip .tick
            : WordLangProgHOL (BitVec 8)) [] =
          .seq (.delta [] [1]) (.branch none (.delta [] []) (.delta [] [])))),
      ("getClashTree MustTerminate",
        decide (getClashTree (.mustTerminate .skip : WordLangProgHOL (BitVec 8)) [] =
          .delta [] [])),
      ("getClashTree Alloc",
        decide (getClashTree (.alloc 5 (setA, setB34) : WordLangProgHOL (BitVec 8)) [] =
          .seq (.delta [] [5]) (.set (sptUnion setA setB34)))),
      ("getClashTree Install",
        decide (getClashTree (.install 1 2 3 4 (setA, setB34)
            : WordLangProgHOL (BitVec 8)) [] =
          .seq (.delta [] [4, 3, 2, 1])
            (.seq (.set (sptUnion setA setB34)) (.delta [1] [])))),
      ("getClashTree CodeBufferWrite",
        decide (getClashTree (.codeBufferWrite 1 2 : WordLangProgHOL (BitVec 8)) [] =
          .delta [] [2, 1])),
      ("getClashTree DataBufferWrite",
        decide (getClashTree (.dataBufferWrite 1 2 : WordLangProgHOL (BitVec 8)) [] =
          .delta [] [2, 1])),
      ("getClashTree FFI",
        decide (getClashTree
          (.ffi (.implode [65]) 1 2 3 4 (setA, setB34) : WordLangProgHOL (BitVec 8)) [] =
          .seq (.delta [] [1, 2, 3, 4]) (.set (sptUnion setA setB34)))),
      ("getClashTree Raise",
        decide (getClashTree (.raise 1 : WordLangProgHOL (BitVec 8)) [] = .delta [] [1])),
      ("getClashTree Return",
        decide (getClashTree (.return 1 [2, 3] : WordLangProgHOL (BitVec 8)) [] =
          .delta [] [1, 2, 3])),
      ("getClashTree Tick",
        decide (getClashTree (.tick : WordLangProgHOL (BitVec 8)) [] = .delta [] [])),
      ("getClashTree LocValue",
        decide (getClashTree (.locValue 1 2 : WordLangProgHOL (BitVec 8)) [] =
          .delta [1] [])),
      ("getClashTree Set",
        decide (getClashTree (.set .nextFree (.var 2) : WordLangProgHOL (BitVec 8)) [] =
          .delta [] [2])),
      ("getClashTree OpCurrHeap",
        decide (getClashTree (.opCurrHeap .add 1 2 : WordLangProgHOL (BitVec 8)) [] =
          .delta [1] [2])),
      ("getClashTree StoreConsts",
        decide (getClashTree (.storeConsts 1 2 3 4 [] : WordLangProgHOL (BitVec 8)) [] =
          .delta [1, 2, 3, 4] [3, 4])),
      ("getClashTree ShareInst Store",
        decide (getClashTree (.shareInst .store 5 (.var 2) : WordLangProgHOL (BitVec 8)) [] =
          .delta [] [5, 2])),
      ("getClashTree ShareInst other",
        decide (getClashTree (.shareInst .load 5 (.var 2) : WordLangProgHOL (BitVec 8)) [] =
          .delta [5] [2])),
      ("getClashTree Loop",
        decide (getClashTree (.loop setA1 .skip setB2 : WordLangProgHOL (BitVec 8)) [] =
          .seq (.set setA1) (.seq (.set setB2) (.seq (.delta [] []) (.set setA1))))),
      ("getClashTree Break none",
        decide (getClashTree (.break 2 : WordLangProgHOL (BitVec 8)) [] = .set .ln)),
      ("getClashTree Break some",
        decide (getClashTree (.break 0 : WordLangProgHOL (BitVec 8)) [(setA1, setB2)] =
          .set setB2)),
      ("getClashTree Continue none",
        decide (getClashTree (.continue 2 : WordLangProgHOL (BitVec 8)) [] = .set .ln)),
      ("getClashTree Continue some",
        decide (getClashTree (.continue 0 : WordLangProgHOL (BitVec 8)) [(setA1, setB2)] =
          .set setA1)),
      ("getClashTree Call none",
        decide (getClashTree (.call none none [3, 4] none
            : WordLangProgHOL (BitVec 8)) [] =
          .set (sptInsert 3 () (sptInsert 4 () .ln)))),
      ("getClashTree Call ret",
        let cutset := sptUnion setA setB
        let argsSet := sptInsert 3 () (sptInsert 4 () .ln)
        let liveSet := sptUnion cutset argsSet
        decide (getClashTree
          (.call (some ([7, 8], (setA, setB), .skip, 0, 0)) none [3, 4] none
            : WordLangProgHOL (BitVec 8)) [] =
          .seq (.set liveSet)
            (.seq (.set (sptInsert 7 () (sptInsert 8 () cutset))) (.delta [] [])))),
      ("getClashTree Call ret handler",
        let cutset := sptUnion setA setB
        let argsSet := sptInsert 3 () (sptInsert 4 () .ln)
        let liveSet := sptUnion cutset argsSet
        decide (getClashTree
          (.call (some ([7, 8], (setA, setB), .skip, 0, 0)) none [3, 4]
            (some (9, .tick, 0, 0)) : WordLangProgHOL (BitVec 8)) [] =
          .branch (some liveSet)
            (.seq (.set (sptInsert 7 () (sptInsert 8 () cutset))) (.delta [] []))
            (.seq (.set (sptInsert 9 () cutset)) (.delta [] [])))) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.WordAllocGetClashTreeParity
