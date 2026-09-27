import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.PanToCrep.CompileProg

/-!
# Original-domain parity for `pan_to_crep$compile` (`compile_def`)

The expected cases come from the direct HOL-EVAL fixture
`scripts/hol-probes/compile_def_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:139-305`.
-/

namespace Flapjack.Test.CompileDefParity

open Flapjack
open Flapjack.Basis.Pure.MlString

def context : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0, bytesInWord := 1 }

def finiteMapContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE (FUPDATE FEMPTY ("p", (.one, [3]))) ("p", (.one, [5]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 5 }

def fixedWidthHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE_LIST FEMPTY
      [("p", (.one, [0])), ("x", (.one, [1])), ("y", (.one, [2]))]
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 2 }

def emptyHOLContext : PanToCrepHOLContext Nat :=
  { vars := FEMPTY, funcs := FEMPTY, eids := FEMPTY, vmax := 0 }

def emptyOneHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE FEMPTY ("empty_one", (.one, []))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 0 }

def highTailHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE_LIST FEMPTY
      [("ptr1", (.one, [4, 100])), ("len1", (.one, [5])),
       ("ptr2", (.one, [6])), ("len2", (.one, [7]))]
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 100 }

def highTailExtCall : Prog Nat :=
  .extCall "f" (.var .local "ptr1") (.var .local "len1")
    (.var .local "ptr2") (.var .local "len2")

def sharedHighTailHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE FEMPTY ("x", (.one, [1, 99]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 99 }

def sharedHighTailExtCall : Prog Nat :=
  .extCall "f" (.var .local "x") (.var .local "x")
    (.var .local "x") (.var .local "x")

def extraNamesHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE FEMPTY ("extra_names", (.one, [4, 5]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 5 }

def missingNamesHOLContext : PanToCrepHOLContext Nat :=
  { vars := FUPDATE FEMPTY ("missing_names", (.comb [.one, .one], [4]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 4 }

def pairLoad : Prog Nat :=
  .return (.load (.comb [.one, .one]) (.var .local "p"))

def riscv64PairContext : PanToCrepHOLContext (BitVec 64) :=
  { vars := FUPDATE_LIST FEMPTY
      [("p", (.one, [0])), ("x", (.one, [1])), ("y", (.one, [2]))]
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 2 }

def riscv64PairLoad : Prog (BitVec 64) :=
  .return (.load (.comb [.one, .one]) (.var .local "p"))

def riscv64PairStore : Prog (BitVec 64) :=
  .store (.var .local "p") (.rStruct [.var .local "x", .var .local "y"])

def riscv64EmptyStructReturn : Prog (BitVec 64) :=
  .return (.rStruct [])

def riscv64EmptyHOLContext : PanToCrepHOLContext (BitVec 64) :=
  { vars := FEMPTY, funcs := FEMPTY, eids := FEMPTY, vmax := 0 }

def riscv64ShadowContext : PanToCrepHOLContext (BitVec 64) :=
  { vars := FUPDATE (FUPDATE FEMPTY ("p", (.one, [3]))) ("p", (.one, [5]))
    funcs := FEMPTY
    eids := FEMPTY
    vmax := 5 }

def riscv64ShadowReturn : Prog (BitVec 64) :=
  .return (.var .local "p")

def isEmptyRiscv64Return : CrepProg (BitVec 64) → Bool
  | .return [] => true
  | _ => false

def isRiscv64ShadowReturn : CrepProg (BitVec 64) → Bool
  | .return [.var 5] => true
  | _ => false

#guard isEmptyRiscv64Return
  (compileProgRiscV riscv64EmptyHOLContext riscv64EmptyStructReturn)
#guard isRiscv64ShadowReturn
  (compileProgRiscV riscv64ShadowContext riscv64ShadowReturn)


def isRiscv64PairLoad : CrepProg (BitVec 64) → Bool
  | .return [.load (.var 0), .load (.op .add [.var 0, .const stride])] =>
      stride == (8 : BitVec 64)
  | _ => false

#guard isRiscv64PairLoad (compileProgRiscV riscv64PairContext riscv64PairLoad)

def isRiscv64PairStore : CrepProg (BitVec 64) → Bool
  | .dec 3 (.var 0) (.dec 4 (.var 1) (.dec 5 (.var 2)
      (.seq (.store (.var 3) (.var 4))
        (.seq (.store (.op .add [.var 3, .const stride]) (.var 5)) .skip)))) =>
      stride == (8 : BitVec 64)
  | _ => false

#guard isRiscv64PairStore
  (compileProgRiscV riscv64PairContext riscv64PairStore)

def pairStore : Prog Nat :=
  .store (.var .local "p") (.rStruct [.var .local "x", .var .local "y"])

def emptyStructReturn : Prog Nat := .return (.rStruct [])

def isFixedPairLoad8 : CrepProg Nat → Bool
  | .return [.load (.var 0), .load (.op .add [.var 0, .const 8])] => true
  | _ => false

def isFixedPairStore8 : CrepProg Nat → Bool
  | .dec 3 (.var 0) (.dec 4 (.var 1) (.dec 5 (.var 2)
      (.seq (.store (.var 3) (.var 4))
        (.seq (.store (.op .add [.var 3, .const 8]) (.var 5)) .skip)))) => true
  | _ => false

def finiteMapParityGuard : Bool :=
  match compileProgHOL finiteMapContext (.return (.var .local "p")) with
  | .return [.var 5] => true
  | _ => false

def emptyOneGlobalContext : CompileContext Nat :=
  { vars := [("empty_one", (.one, []))], functions := [], exceptions := [],
    maxVar := 0, bytesInWord := 1 }

def extraNamesGlobalContext : CompileContext Nat :=
  { vars := [("extra_names", (.one, [4, 5]))], functions := [], exceptions := [],
    maxVar := 5, bytesInWord := 1 }

def missingNamesGlobalContext : CompileContext Nat :=
  { vars := [("missing_names", (.comb [.one, .one], [4]))],
    functions := [], exceptions := [], maxVar := 4, bytesInWord := 1 }

def missingGlobalCall : Prog Nat :=
  .call (some (some (.global, "missing"), none)) "f" []

def emptyOneGlobalCall : Prog Nat :=
  .call (some (some (.global, "empty_one"), none)) "f" []

def extraNamesGlobalCall : Prog Nat :=
  .call (some (some (.global, "extra_names"), none)) "f" []

def missingNamesGlobalCall : Prog Nat :=
  .call (some (some (.global, "missing_names"), none)) "f" []

def validLocalContext : CompileContext Nat :=
  { vars := [("pair", (.comb [.one, .one], [0, 1]))], functions := [],
    exceptions := [], maxVar := 1, bytesInWord := 1 }

def emptyOneLocalContext : CompileContext Nat :=
  { vars := [("empty_one", (.one, []))], functions := [], exceptions := [],
    maxVar := 0, bytesInWord := 1 }

def extraNamesLocalContext : CompileContext Nat :=
  { vars := [("extra_names", (.one, [4, 5]))], functions := [], exceptions := [],
    maxVar := 5, bytesInWord := 1 }

def missingNamesLocalContext : CompileContext Nat :=
  { vars := [("missing_names", (.comb [.one, .one], [4]))],
    functions := [], exceptions := [], maxVar := 4, bytesInWord := 1 }

def missingLocalCall : Prog Nat :=
  .call (some (some (.local, "missing"), none)) "f" []

def emptyOneLocalCall : Prog Nat :=
  .call (some (some (.local, "empty_one"), none)) "f" []

def extraNamesLocalCall : Prog Nat :=
  .call (some (some (.local, "extra_names"), none)) "f" []

def missingNamesLocalCall : Prog Nat :=
  .call (some (some (.local, "missing_names"), none)) "f" []

def validLocalCall : Prog Nat :=
  .call (some (some (.local, "pair"), none)) "f" []

def isTailCallToF : CrepProg Nat → Bool
  | .call none "f" [] => true
  | _ => false

def isValidPairCallToF : CrepProg Nat → Bool
  | .call (some ([0, 1], none)) "f" [] => true
  | _ => false

def isExtraNamesCallToF : CrepProg Nat → Bool
  | .call (some ([4, 5], none)) "f" [] => true
  | _ => false

def isMissingNamesCallToF : CrepProg Nat → Bool
  | .call (some ([4], none)) "f" [] => true
  | _ => false

def isSkip : CrepProg Nat → Bool
  | .skip => true
  | _ => false

def isHighTailExtCall : CrepProg Nat → Bool
  | .dec 101 (.var 4) (.dec 102 (.var 5) (.dec 103 (.var 6)
      (.dec 104 (.var 7) (.extCall "f" 101 102 103 104)))) => true
  | _ => false

def isSharedHighTailExtCall : CrepProg Nat → Bool
  | .dec 100 (.var 1) (.dec 101 (.var 1) (.dec 102 (.var 1)
      (.dec 103 (.var 1) (.extCall "f" 100 101 102 103)))) => true
  | _ => false

def isReturnSeven : CrepProg Nat → Bool
  | .return [.const 7] => true
  | _ => false

def isEmptyReturn : CrepProg Nat → Bool
  | .return [] => true
  | _ => false

def isBreak : CrepProg Nat → Bool
  | .break 0 => true
  | _ => false

def isContinue : CrepProg Nat → Bool
  | .continue 0 => true
  | _ => false

def isSeqSkipTick : CrepProg Nat → Bool
  | .seq .skip .tick => true
  | _ => false

def nativeProgramParityGuard : Bool :=
  isSkip (compileProgHOL emptyHOLContext (.skip : Prog Nat)) &&
  isReturnSeven (compileProgHOL emptyHOLContext (.return (.const 7))) &&
  isEmptyReturn (compileProgHOL emptyHOLContext emptyStructReturn) &&
  isBreak (compileProgHOL emptyHOLContext (.break : Prog Nat)) &&
  isContinue (compileProgHOL emptyHOLContext (.continue : Prog Nat)) &&
  isSeqSkipTick (compileProgHOL emptyHOLContext (.seq .skip (.tick : Prog Nat))) &&
  isHighTailExtCall (compileProgHOL highTailHOLContext highTailExtCall) &&
  isSharedHighTailExtCall
    (compileProgHOL sharedHighTailHOLContext sharedHighTailExtCall) &&
  isTailCallToF (compileProgHOL emptyHOLContext missingGlobalCall) &&
  isTailCallToF (compileProgHOL emptyOneHOLContext emptyOneGlobalCall) &&
  isExtraNamesCallToF (compileProgHOL extraNamesHOLContext extraNamesGlobalCall) &&
  isMissingNamesCallToF (compileProgHOL missingNamesHOLContext missingNamesGlobalCall)

def finiteMapLoadStoreParityGuard : Bool :=
  isFixedPairLoad8 (compileProgHOL fixedWidthHOLContext pairLoad) &&
  isFixedPairStore8 (compileProgHOL fixedWidthHOLContext pairStore)

def parityGuard : Bool :=
  isSkip (compileProg context (.skip : Prog Nat)) &&
  isReturnSeven (compileProg context (.return (.const 7))) &&
  isEmptyReturn (compileProg context emptyStructReturn) &&
  isBreak (compileProg context (.break : Prog Nat)) &&
  isContinue (compileProg context (.continue : Prog Nat)) &&
  isSeqSkipTick (compileProg context (.seq .skip (.tick : Prog Nat))) &&
  isTailCallToF (compileProg context missingGlobalCall) &&
  isTailCallToF (compileProg emptyOneGlobalContext emptyOneGlobalCall) &&
  isExtraNamesCallToF (compileProg extraNamesGlobalContext extraNamesGlobalCall) &&
  isMissingNamesCallToF (compileProg missingNamesGlobalContext missingNamesGlobalCall) &&
  isTailCallToF (compileProg context missingLocalCall) &&
  isTailCallToF (compileProg emptyOneLocalContext emptyOneLocalCall) &&
  isExtraNamesCallToF (compileProg extraNamesLocalContext extraNamesLocalCall) &&
  isMissingNamesCallToF (compileProg missingNamesLocalContext missingNamesLocalCall) &&
  isValidPairCallToF (compileProg validLocalContext validLocalCall) &&
  finiteMapParityGuard && nativeProgramParityGuard &&
    finiteMapLoadStoreParityGuard

example : compileProg context missingGlobalCall = .call none "f" [] := by
  simp [missingGlobalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, context, lookupInfo]

example : compileProg context emptyStructReturn = .return [] := by
  simp [emptyStructReturn, compileProg, compileExp, compileExp.compileExpList,
    Shape.shapeSize]

example :
    compileProg emptyOneGlobalContext emptyOneGlobalCall = .call none "f" [] := by
  simp [emptyOneGlobalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, emptyOneGlobalContext, lookupInfo]

example :
    compileProg extraNamesGlobalContext extraNamesGlobalCall =
      .call (some ([4, 5], none)) "f" [] := by
  simp [extraNamesGlobalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, extraNamesGlobalContext, lookupInfo]

example :
    compileProg missingNamesGlobalContext missingNamesGlobalCall =
      .call (some ([4], none)) "f" [] := by
  simp [missingNamesGlobalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, missingNamesGlobalContext, lookupInfo]

/-! Local-kind mirrors.  Cake's rule looks the destination up in
`ctxt.vars` and discards the `rk` tag, so a Local call and its Global twin
emit the same list; the HOL fixture `compile_def_probe.out` records both. -/

example : compileProg context missingLocalCall = .call none "f" [] := by
  simp [missingLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, context, lookupInfo]

example :
    compileProg emptyOneLocalContext emptyOneLocalCall = .call none "f" [] := by
  simp [emptyOneLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, emptyOneLocalContext, lookupInfo]

example :
    compileProg extraNamesLocalContext extraNamesLocalCall =
      .call (some ([4, 5], none)) "f" [] := by
  simp [extraNamesLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, extraNamesLocalContext, lookupInfo]

example :
    compileProg missingNamesLocalContext missingNamesLocalCall =
      .call (some ([4], none)) "f" [] := by
  simp [missingNamesLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, missingNamesLocalContext, lookupInfo]

example :
    compileProg validLocalContext validLocalCall =
      .call (some ([0, 1], none)) "f" [] := by
  simp [validLocalCall, compileProg, compileArgs, callDestinationNames,
    wrapRt, validLocalContext, lookupInfo]

#eval parityGuard
#guard parityGuard
#guard finiteMapParityGuard
#guard nativeProgramParityGuard
#guard finiteMapLoadStoreParityGuard

/-! The direct HOL rows `struct_skip`, `struct_break`, `struct_continue`,
`struct_tick`, `struct_annot`, and `struct_seq` in `compile_def_probe.out`
exercise the first exact-carrier `compile_def` slice. The support premise
admits only those constructors, so unsupported constructors are not silently
treated as successful compiler cases. -/

open Flapjack.Pancake.PanLang

def exactSkipSupported : CompileProgStructuralFragmentHOL
    (ProgHOL.skip : ProgHOL 8) := .skip

def exactControlSeqSupported : CompileProgStructuralFragmentHOL
    (ProgHOL.seq ProgHOL.skip (ProgHOL.seq ProgHOL.break ProgHOL.continue) : ProgHOL 8) :=
  .seq .skip (.seq .break .continue)

def exactTickSupported : CompileProgStructuralFragmentHOL
    (ProgHOL.tick : ProgHOL 8) := .tick

def exactBreakSupported : CompileProgStructuralFragmentHOL
    (ProgHOL.break : ProgHOL 8) := .break

def exactContinueSupported : CompileProgStructuralFragmentHOL
    (ProgHOL.continue : ProgHOL 8) := .continue

def exactAnnotSupported : CompileProgStructuralFragmentHOL
    (ProgHOL.annot (.implode []) (.implode []) : ProgHOL 8) := .annot _ _

def exactStructuralSliceParity : Bool :=
  let compiledSkip := compileProgStructuralFragmentHOL exactSkipSupported
  let controls := compileProgStructuralFragmentHOL exactControlSeqSupported
  let compiledTick := compileProgStructuralFragmentHOL exactTickSupported
  let compiledBreak := compileProgStructuralFragmentHOL exactBreakSupported
  let compiledContinue := compileProgStructuralFragmentHOL exactContinueSupported
  let annot := compileProgStructuralFragmentHOL exactAnnotSupported
  (match compiledSkip with | .skip => true | _ => false) &&
    (match controls with
    | .seq .skip (.seq (.break 0) (.continue 0)) => true
    | _ => false) &&
    (match compiledTick with | .tick => true | _ => false) &&
    (match compiledBreak with | .break 0 => true | _ => false) &&
    (match compiledContinue with | .continue 0 => true | _ => false) &&
    (match annot with | .skip => true | _ => false)

#guard exactStructuralSliceParity

def exactReturnContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 0

private def exactStoreBridgeContext : PanToCrepContextExact 8 where
  vars := HolFiniteMapExact.empty
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 0

private def exactStoreLengthMismatchContext : PanToCrepContextExact 8 where
  vars := (HolFiniteMapExact.empty.update
      (ofString "ad", (.one, [3]))).update
    (ofString "value", (.one, []))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 3

private def exactStoreAddressName : MlS := ofString "ad"

private def exactStoreValueName : MlS := ofString "value"

example :
    crepProgOfHOL (compileProgExactHOLW exactStoreBridgeContext
        (.store (expToHOL (.const (3 : BitVec 8)))
          (expToHOL (.const (4 : BitVec 8))))) =
      compileProgRiscV exactStoreBridgeContext.toProduction
        (.store (.const 3) (.const 4)) := by
  apply compileProgExactHOLW_store_success_bridge
    (exactAddress := .const 3)
    (exactAddressRest := [])
    (exactAddressShape := .one)
    (exactValues := [.const 4])
    (exactValueShape := .one)
    (productionAddress := .const 3)
    (productionAddressRest := [])
    (productionAddressShape := .one)
    (productionValues := [.const 4])
    (productionValueShape := .one)
  all_goals simp [exactStoreBridgeContext, compileExpExactHOLW,
    compileExpHOL, expToHOL, shapeOfHOL, crepExpOfHOL,
    PanToCrepContextExact.toProduction]

example :
    crepProgOfHOL (compileProgExactHOLW exactStoreBridgeContext
        (.store (expToHOL (.rStruct [] : Exp (BitVec 8)))
          (expToHOL (.const (4 : BitVec 8))))) =
      compileProgRiscV exactStoreBridgeContext.toProduction
        (.store (.rStruct []) (.const 4)) := by
  apply compileProgExactHOLW_store_output_bridge
    (exactAddresses := []) (exactAddressShape := .comb [])
    (exactValues := [.const 4]) (exactValueShape := .one)
    (productionAddresses := []) (productionAddressShape := .comb [])
    (productionValues := [.const 4]) (productionValueShape := .one)
  all_goals simp [compileExpExactHOLW, compileExpExactHOLWList, expToHOL,
    compileExpHOL, compileExpHOL.compileExpListHOL, shapeOfHOL, crepExpOfHOL]

example :
  crepProgOfHOL (compileProgExactHOLW exactStoreLengthMismatchContext
        (.store (expToHOL (.var .local
          (toStringOfBytes exactStoreAddressName) : Exp (BitVec 8)))
          (expToHOL (.var .local
            (toStringOfBytes exactStoreValueName) : Exp (BitVec 8))))) =
      compileProgRiscV exactStoreLengthMismatchContext.toProduction
        (.store (.var .local (toStringOfBytes exactStoreAddressName))
          (.var .local (toStringOfBytes exactStoreValueName))) := by
  have hnameNe : ofString "value" ≠ ofString "ad" := by decide
  apply compileProgExactHOLW_store_output_bridge
    (exactAddresses := [.var 3]) (exactAddressShape := .one)
    (exactValues := []) (exactValueShape := .one)
    (productionAddresses := [.var 3]) (productionAddressShape := .one)
    (productionValues := []) (productionValueShape := .one)
  · simp [compileExpExactHOLW, expToHOL, exactStoreLengthMismatchContext,
      exactStoreAddressName, HolFiniteMapExact.lookup_update, FUPDATE,
      ofString_toStringOfBytes, hnameNe]
  · simp [compileExpExactHOLW, expToHOL, exactStoreLengthMismatchContext,
      exactStoreValueName, HolFiniteMapExact.lookup_update, FUPDATE,
      ofString_toStringOfBytes]
  · have hlookup : exactStoreLengthMismatchContext.toProduction.vars
        (toStringOfBytes exactStoreAddressName) = some (.one, [3]) := by
      rw [PanToCrepContextExact.toProduction_vars_lookup]
      simp [exactStoreLengthMismatchContext, exactStoreAddressName,
        HolFiniteMapExact.lookup_update, FUPDATE, hnameNe, shapeOfHOL]
    simp [compileExpHOL, FLOOKUP, hlookup]
  · have hlookup : exactStoreLengthMismatchContext.toProduction.vars
        (toStringOfBytes exactStoreValueName) = some (.one, []) := by
      rw [PanToCrepContextExact.toProduction_vars_lookup]
      simp [exactStoreLengthMismatchContext, exactStoreValueName,
        HolFiniteMapExact.lookup_update, FUPDATE, shapeOfHOL]
    simp [compileExpHOL, FLOOKUP, hlookup]
  · simp [crepExpOfHOL]
  · rfl
  · simp [shapeOfHOL]

def exactLocalAssignContext (destinationNames sourceNames : List Nat) :
    CompileExpContextExact 8 where
  vars := (HolFiniteMapExact.empty.update
      (ofString "dst", (.one, destinationNames))).update
      (ofString "src", (.one, sourceNames))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 10

def exactMalformedStoreContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update
    (ofString "bad", (.comb [.one, .one], [9]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 0

def exactRaiseContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty.update
    (ofString "E", BitVec.ofNat 8 12)
  vmax := 0

/-- Context combining a successful wrapped-result destination `dst` with a
    found handler EID `E`, for the wrapped-result handler-present-eid bridge. -/
def exactWrappedHandlerContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update (ofString "dst", (.one, [7]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty.update (ofString "E", BitVec.ofNat 8 12)
  vmax := 0

def exactMalformedRaiseContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update
    (ofString "bad", (.comb [.one, .one], [9]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty.update
    (ofString "E", BitVec.ofNat 8 12)
  vmax := 0

def exactExtCallContext : CompileExpContextExact 8 where
  vars := (((HolFiniteMapExact.empty.update
      (ofString "configuration", (.one, [4, 100]))).update
      (ofString "configurationLength", (.one, [5]))).update
      (ofString "array", (.one, [6]))).update
      (ofString "arrayLength", (.one, [7]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 0

def exactMalformedExtCallContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update
    (ofString "configuration", (.comb [.one], [4]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 0

def exactExtCallConstantContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 400

def exactDecCallContext (vmax : Nat) : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := vmax

def exactCallResultContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty
  funcs := HolFiniteMapExact.empty.update
    (ofString "f", ([], .comb [.one, .one]))
  eids := HolFiniteMapExact.empty
  vmax := 10

def exactCallWrappedResultContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update
    (ofString "pair", (.comb [.one, .one], [30, 31]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 50

def exactCallWrappedEmptyOneContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update (ofString "empty_one", (.one, []))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 50

def exactCallWrappedHandlerPresentContext : CompileExpContextExact 8 where
  vars := (HolFiniteMapExact.empty.update
      (ofString "pair", (.comb [.one, .one], [30, 31]))).update
      (ofString "exn", (.comb [.one, .one], [20, 21]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty.update (ofString "E", BitVec.ofNat 8 12)
  vmax := 50

def exactCallWrappedFallbackHandlerPresentContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update
    (ofString "exn", (.comb [.one, .one], [20, 21]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty.update (ofString "E", BitVec.ofNat 8 12)
  vmax := 50

def exactCallWrappedFallbackHandlerMissingContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update
    (ofString "exn", (.comb [.one, .one], [20, 21]))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 50

def exactCallHandlerPresentContext : CompileExpContextExact 8 where
  vars := HolFiniteMapExact.empty.update
    (ofString "exn", (.comb [.one, .one], [20, 21]))
  funcs := HolFiniteMapExact.empty.update
    (ofString "f", ([], .one))
  eids := HolFiniteMapExact.empty.update
    (ofString "E", BitVec.ofNat 8 12)
  vmax := 10

def returnValuesMatch (expected : List (CrepExp (BitVec 8))) : CrepProgHOL 8 → Bool
  | .return actual => actual.map crepExpOfHOL == expected
  | _ => false

def exactReturnClauseParity : Bool :=
  returnValuesMatch [.const 7]
    (compileReturnExactHOLW exactReturnContext (.const 7)) &&
  returnValuesMatch []
    (compileReturnExactHOLW exactReturnContext (.rstruct [])) &&
  returnValuesMatch [.const 1, .const 2]
    (compileReturnExactHOLW exactReturnContext (.rstruct [.const 1, .const 2]))

#guard exactReturnClauseParity

def exactStoreClauseParity : Bool :=
  (match compileStore32ExactHOLW exactReturnContext (.const 1) (.const 2) with
   | .store32 (.const 1) (.const 2) => true
   | _ => false) &&
  (match compileStore32ExactHOLW exactReturnContext (.rstruct []) (.const 2) with
   | .skip => true
   | _ => false) &&
  (match compileStoreByteExactHOLW exactReturnContext (.const 3) (.const 4) with
   | .storeByte (.const 3) (.const 4) => true
   | _ => false) &&
  (match compileStoreByteExactHOLW exactReturnContext (.const 3) (.rstruct []) with
   | .skip => true
   | _ => false)

#guard exactStoreClauseParity

def exactIfWhileClauseParity : Bool :=
  (match compileIfExactHOLW exactReturnContext (.const 1) .skip (.break 0) with
   | .ite (.const 1) .skip (.break 0) => true
   | _ => false) &&
  (match compileIfExactHOLW exactReturnContext (.rstruct []) .skip .skip with
   | .skip => true
   | _ => false) &&
  (match compileWhileExactHOLW exactReturnContext (.const 2) (.break 0) with
   | .while (.const 2) (.break 0) => true
   | _ => false) &&
  (match compileWhileExactHOLW exactReturnContext (.rstruct []) .skip with
   | .skip => true
   | _ => false)

#guard exactIfWhileClauseParity

def exactGlobalFallbackParity : Bool :=
  (match compileGlobalAssignExactHOLW exactReturnContext (ofString "g") (.const 5) with
   | .skip => true
   | _ => false) &&
  (match compileGlobalShMemLoadExactHOLW exactReturnContext .op8 (ofString "g")
      (.const 3) with
   | .skip => true
   | _ => false)

#guard exactGlobalFallbackParity

def exactLocalAssignClauseParity : Bool :=
  (match compileLocalAssignExactHOLW
      (exactLocalAssignContext [7] [8]) (ofString "dst") (.var .local (ofString "src")) with
   | .seq (.assign 7 (.var 8)) .skip => true
   | _ => false) &&
  (match compileLocalAssignExactHOLW
      (exactLocalAssignContext [7] [7]) (ofString "dst") (.var .local (ofString "src")) with
   | .dec 11 (.var 7) (.seq (.assign 7 (.var 11)) .skip) => true
   | _ => false) &&
  (match compileLocalAssignExactHOLW exactReturnContext (ofString "dst")
      (.var .local (ofString "src")) with
   | .skip => true
   | _ => false) &&
  (match compileLocalAssignExactHOLW
      (exactLocalAssignContext [7, 8] [9]) (ofString "dst")
      (.var .local (ofString "src")) with
   | .skip => true
   | _ => false)

#guard exactLocalAssignClauseParity

def exactPrimitiveClauseParity : Bool :=
  (match compilePrimitiveExactHOLW
      (exactLocalAssignContext [7] [8]) (ofString "dst") .addCarry
      [.const 1, .var .local (ofString "src")] with
   | .dec 11 (.const 1) (.dec 12 (.var 8) (.primitive [7] .addCarry [11, 12])) => true
   | _ => false) &&
  (match compilePrimitiveExactHOLW exactReturnContext (ofString "dst") .addCarry
      [.const 1, .var .local (ofString "src")] with
   | .skip => true
   | _ => false)

#guard exactPrimitiveClauseParity

def exactStoreClauseFullParity : Bool :=
  (match compileStoreExactHOLW exactReturnContext (.const 3) (.const 4) with
   | .dec 1 (.const 3) (.dec 2 (.const 4) (.seq (.store (.var 1) (.var 2)) .skip)) => true
   | _ => false) &&
  (match compileStoreExactHOLW exactReturnContext (.const 3)
      (.rstruct [.const 4, .const 5]) with
   | .dec 1 (.const 3) (.dec 2 (.const 4) (.dec 3 (.const 5)
       (.seq (.store (.var 1) (.var 2))
         (.seq (.store (.op .add [.var 1, .const 1]) (.var 3)) .skip)))) => true
   | _ => false) &&
  (match compileStoreExactHOLW exactReturnContext (.rstruct []) (.const 4) with
   | .skip => true
   | _ => false) &&
  (match compileStoreExactHOLW exactMalformedStoreContext (.const 3)
      (.var .local (ofString "bad")) with
   | .skip => true
   | _ => false)

#guard exactStoreClauseFullParity

def exactRaiseClauseParity : Bool :=
  (match compileRaiseExactHOLW exactRaiseContext (ofString "E") (.const 9) with
   | .seq (.dec 1 (.const 9) (.seq (.storeGlob 0 (.var 1)) .skip)) (.raise 12) => true
   | _ => false) &&
  (match compileRaiseExactHOLW exactRaiseContext (ofString "E")
      (.rstruct [.const 1, .const 2]) with
   | .seq (.dec 1 (.const 1) (.dec 2 (.const 2)
       (.seq (.storeGlob 0 (.var 1)) (.seq (.storeGlob 1 (.var 2)) .skip))))
       (.raise 12) => true
   | _ => false) &&
  (match compileRaiseExactHOLW exactReturnContext (ofString "missing") (.const 9) with
   | .skip => true
   | _ => false) &&
  (match compileRaiseExactHOLW exactMalformedRaiseContext (ofString "E")
      (.var .local (ofString "bad")) with
   | .skip => true
   | _ => false)

#guard exactRaiseClauseParity

/-- The success case of the full exact-to-production Raise bridge exercises
    its codec premise on the source Raise clause, including its local Dec,
    global save, and final Raise output. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactRaiseContext
      (.raise (ofString "E") (expToHOL (.const (BitVec.ofNat 8 9))))) =
    compileProgRiscV exactRaiseContext.toProduction
      (.raise "E" (.const (BitVec.ofNat 8 9))) := by
  apply compileProgExactHOLW_raise_bridge
  simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
    List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The same bridge retains the missing exception-id fallback. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactReturnContext
      (.raise (ofString "missing") (expToHOL (.const (BitVec.ofNat 8 9))))) =
    compileProgRiscV exactReturnContext.toProduction
      (.raise "missing" (.const (BitVec.ofNat 8 9))) := by
  apply compileProgExactHOLW_raise_bridge
  simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
    List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The bridge also retains the malformed expression shape/length fallback. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactMalformedRaiseContext
      (.raise (ofString "E")
        (expToHOL (.var .local "bad")))) =
    compileProgRiscV exactMalformedRaiseContext.toProduction
      (.raise "E" (.var .local "bad")) := by
  apply compileProgExactHOLW_raise_bridge
  simp [compileExpExactHOLW.eq_2, expToHOL.eq_2, compileExpHOL.eq_2,
    PanToCrepContextExact.toProduction, exactMalformedRaiseContext,
    HolFiniteMapExact.lookup_update, FUPDATE, FLOOKUP, crepExpOfHOL,
    shapeOfHOL]

/-- The local-Assign bridge retains the missing-variable `Skip` fallback. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactReturnContext
      (.assign .local (ofString "dst") (expToHOL (.const (BitVec.ofNat 8 5))))) =
    compileProgRiscV exactReturnContext.toProduction
      (.assign .local "dst" (.const (BitVec.ofNat 8 5))) := by
  apply compileProgExactHOLW_local_assign_bridge
  simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
    List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The local-Assign bridge retains the destination/source length-mismatch
    `Skip` fallback. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7, 8] [9])
      (.assign .local (ofString "dst") (expToHOL (.const (BitVec.ofNat 8 5))))) =
    compileProgRiscV (exactLocalAssignContext [7, 8] [9]).toProduction
      (.assign .local "dst" (.const (BitVec.ofNat 8 5))) := by
  apply compileProgExactHOLW_local_assign_bridge
  simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
    List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The local-Assign bridge covers the disjoint direct `nested_seq` branch. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.assign .local (ofString "dst")
        (expToHOL (.var .local "src")))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.assign .local "dst" (.var .local "src")) := by
  apply compileProgExactHOLW_local_assign_bridge
  simp [compileExpExactHOLW.eq_2, expToHOL.eq_2, compileExpHOL.eq_2,
    PanToCrepContextExact.toProduction, exactLocalAssignContext,
    HolFiniteMapExact.lookup_update, FUPDATE, FLOOKUP, crepExpOfHOL,
    shapeOfHOL]

/-- The local-Assign bridge covers the interfering-variable fresh-temporary
    branch. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [7])
      (.assign .local (ofString "dst")
        (expToHOL (.var .local "src")))) =
    compileProgRiscV (exactLocalAssignContext [7] [7]).toProduction
      (.assign .local "dst" (.var .local "src")) := by
  apply compileProgExactHOLW_local_assign_bridge
  simp [compileExpExactHOLW.eq_2, expToHOL.eq_2, compileExpHOL.eq_2,
    PanToCrepContextExact.toProduction, exactLocalAssignContext,
    HolFiniteMapExact.lookup_update, FUPDATE, FLOOKUP, crepExpOfHOL,
    shapeOfHOL]

/-- The Primitive bridge retains the missing-variable `Skip` fallback. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactReturnContext
      (.primitive (ofString "dst") .addCarry [])) =
    compileProgRiscV exactReturnContext.toProduction
      (.primitive "dst" .addCarry []) := by
  apply compileProgExactHOLW_primitive_bridge (arguments := [])
  intro expression hmem
  simp at hmem

/-- The Primitive bridge covers the present-variable temporaries branch with an
    empty argument list. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.primitive (ofString "dst") .addCarry [])) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.primitive "dst" .addCarry []) := by
  apply compileProgExactHOLW_primitive_bridge (arguments := [])
  intro expression hmem
  simp at hmem

/-- The Primitive bridge covers a non-empty argument list through the paired
    expression codec. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.primitive (ofString "dst") .addCarry
        [expToHOL (.const (BitVec.ofNat 8 5))])) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.primitive "dst" .addCarry [.const (BitVec.ofNat 8 5)]) := by
  apply compileProgExactHOLW_primitive_bridge (arguments := [.const (BitVec.ofNat 8 5)])
  intro expression hmem
  simp only [List.mem_singleton] at hmem
  subst hmem
  simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
    List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The recursive `Dec` bridge (`pan_to_crepScript.sml:141-152`) closes the
    missing-variable `Skip` fallback, the compiled-shape store, and the
    recursive body under the extended context for a concrete `.skip` body. The
    recursive hypothesis is supplied at the two extended contexts. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.dec (ofString "dst") (shapeToHOL .one)
        (expToHOL (.const (BitVec.ofNat 8 5))) .skip)) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.dec "dst" .one (.const (BitVec.ofNat 8 5)) (progOfHOL .skip)) := by
  apply compileProgExactHOLW_dec_bridge
  · rfl
  · rfl
  · simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]
  · simp [compileProgExactHOLW, compileProgHOL, progOfHOL, crepProgOfHOL]

/-- The recursive `DecCall` bridge (`pan_to_crepScript.sml:262-272`) closes the
    declared-shape return-slot allocation, the byte-range decoding of the
    `MlString` callee, and the recursive body under the extended context for a
    concrete empty argument list and `.skip` body. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.decCall (ofString "dst") (shapeToHOL .one) (ofString "f")
        (([] : List (Exp (BitVec 8))).map expToHOL) .skip)) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.decCall "dst" .one "f" [] (progOfHOL .skip)) := by
  apply compileProgExactHOLW_decCall_bridge
  · rfl
  · rfl
  · intro expression hmem
    simp at hmem
  · decide
  · simp [compileProgExactHOLW, compileProgHOL, progOfHOL, crepProgOfHOL]

/-- The tail-call bridge (`pan_to_crepScript.sml:221-225`) for a name-ranged
    callee and a concrete single-argument list. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.call none (ofString "f")
        (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.call none "f" [.const 5]) := by
  apply compileProgExactHOLW_call_none_bridge
  · decide
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The result-carrying `Call` bridge (`pan_to_crepScript.sml:226-232`) for a
    name-ranged callee whose `funcs` entry is absent (empty result-name list)
    and a concrete single-argument list. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.call (some (none, none)) (ofString "f")
        (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.call (some (none, none)) "f" [.const 5]) := by
  apply compileProgExactHOLW_call_result_no_handler_bridge
  · decide
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The wrapped-result `Call` bridge (`pan_to_crepScript.sml:252-261`) for a
    name-ranged callee whose destination `wrap_rt` lookup succeeds with a
    non-empty name list and a concrete single-argument list. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.call (some (some (.local, ofString "dst"), none)) (ofString "f")
        (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.call (some (some (.local, "dst"), none)) "f" [.const 5]) := by
  refine compileProgExactHOLW_call_wrapped_result_no_handler_bridge
    (context := exactLocalAssignContext [7] [8]) (kind := .local)
    (resultName := "dst") (function := "f") (arguments := [.const 5])
    (resultShape := .one) (resultNames := [7]) ?_ (by decide) ?_
  · rfl
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The wrapped-result fallback `Call` bridge (`pan_to_crepScript.sml:252-261`)
    for a name-ranged callee whose destination `wrap_rt` lookup fails (absent
    variable) and a concrete single-argument list. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.call (some (some (.local, ofString "missing"), none)) (ofString "f")
        (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.call (some (some (.local, "missing"), none)) "f" [.const 5]) := by
  refine compileProgExactHOLW_call_wrapped_result_fallback_no_handler_bridge
    (context := exactLocalAssignContext [7] [8]) (kind := .local)
    (resultName := "missing") (function := "f") (arguments := [.const 5])
    ?_ (by decide) ?_
  · rfl
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The result-arm Call handler-missing-eid bridge
    (`pan_to_crepScript.sml:233-235`) for a name-ranged callee and exception
    whose `eids` table lacks the exception, with a concrete single-argument
    list. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.call (some (none, some (ofString "F", ofString "e", .skip))) (ofString "f")
        (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.call (some (none, some ("F", "e", .skip))) "f" [.const 5]) := by
  refine compileProgExactHOLW_call_handler_missing_eid_bridge
    (context := exactLocalAssignContext [7] [8]) (function := "f")
    (exceptionName := "F") (exceptionVariable := "e") (arguments := [.const 5])
    (body := .skip) ?_ (by decide) (by decide) ?_
  · rfl
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The result-arm Call handler-present-eid bridge
    (`pan_to_crepScript.sml:233-239`): the `eids` table binds `"E"` to code `12`,
    so the handler is kept and the callee return names are zero-initialized. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactRaiseContext
      (.call (some (none, some (ofString "E", ofString "e", .skip))) (ofString "f")
        (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV exactRaiseContext.toProduction
      (.call (some (none, some ("E", "e", progOfHOL ProgHOL.skip))) "f" [.const 5]) := by
  refine compileProgExactHOLW_call_handler_present_eid_bridge
    (context := exactRaiseContext) (function := "f") (exceptionName := "E")
    (exceptionVariable := "e") (arguments := [.const 5]) (body := .skip)
    (exceptionCode := BitVec.ofNat 8 12) ?_ (by decide) (by decide) ?_ ?_
  · simp [exactRaiseContext, FUPDATE]
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]
  · simp [compileProgExactHOLW, compileProgHOL, progOfHOL, crepProgOfHOL]

/-- The wrapped-result Call handler-missing-eid bridge
    (`pan_to_crepScript.sml:252-261`): the destination `wrap_rt` lookup succeeds
    but the `eids` table lacks the exception, so the handler is dropped while the
    destination names are retained as result metadata. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.call
        (some (some (.local, ofString "dst"), some (ofString "F", ofString "e", .skip)))
        (ofString "f") (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.call
        (some (some (.local, "dst"), some ("F", "e", progOfHOL ProgHOL.skip)))
        "f" [.const 5]) := by
  refine compileProgExactHOLW_call_wrapped_result_handler_missing_eid_bridge
    (context := exactLocalAssignContext [7] [8]) (kind := .local)
    (resultName := "dst") (function := "f") (exceptionName := "F")
    (exceptionVariable := "e") (arguments := [.const 5]) (body := .skip)
    (resultShape := .one) (resultNames := [7]) ?_ ?_ (by decide) (by decide) ?_
  · rfl
  · rfl
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The wrapped-result handler-present-eid bridge
    (`pan_to_crepScript.sml:252-261`) keeps the destination names and sequences
    `exp_hdl` with the recursively compiled handler body. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactWrappedHandlerContext
      (.call
        (some (some (.local, ofString "dst"), some (ofString "E", ofString "e", .skip)))
        (ofString "f") (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV exactWrappedHandlerContext.toProduction
      (.call
        (some (some (.local, "dst"), some ("E", "e", progOfHOL ProgHOL.skip)))
        "f" [.const 5]) := by
  refine compileProgExactHOLW_call_wrapped_result_handler_present_eid_bridge
    (context := exactWrappedHandlerContext) (kind := .local)
    (resultName := "dst") (function := "f") (exceptionName := "E")
    (exceptionVariable := "e") (arguments := [.const 5]) (body := .skip)
    (resultShape := .one) (resultNames := [7]) (exceptionCode := BitVec.ofNat 8 12)
    ?_ ?_ (by decide) (by decide) ?_ ?_
  · simp [exactWrappedHandlerContext, FUPDATE, wrapRtHOL]
  · simp [exactWrappedHandlerContext, FUPDATE]
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]
  · simp [compileProgExactHOLW, compileProgHOL, progOfHOL, crepProgOfHOL]

/-- The wrapped-result fallback handler-missing-eid bridge
    (`pan_to_crepScript.sml:252-261`) drops both handler and metadata and emits a
    flattened tail call. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactRaiseContext
      (.call
        (some (some (.local, ofString "dst"), some (ofString "F", ofString "e", .skip)))
        (ofString "f") (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV exactRaiseContext.toProduction
      (.call
        (some (some (.local, "dst"), some ("F", "e", progOfHOL ProgHOL.skip)))
        "f" [.const 5]) := by
  refine compileProgExactHOLW_call_wrapped_result_fallback_handler_missing_eid_bridge
    (context := exactRaiseContext) (kind := .local) (resultName := "dst")
    (function := "f") (exceptionName := "F") (exceptionVariable := "e")
    (arguments := [.const 5]) (body := .skip) ?_ ?_ (by decide) (by decide) ?_
  · rfl
  · simp [exactRaiseContext, FUPDATE]
    decide
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]

/-- The wrapped-result fallback handler-present-eid bridge
    (`pan_to_crepScript.sml:252-261`) keeps the handler but supplies an empty
    return-name list. -/
example :
    crepProgOfHOL (compileProgExactHOLW exactRaiseContext
      (.call
        (some (some (.local, ofString "dst"), some (ofString "E", ofString "e", .skip)))
        (ofString "f") (([.const 5] : List (Exp (BitVec 8))).map expToHOL))) =
    compileProgRiscV exactRaiseContext.toProduction
      (.call
        (some (some (.local, "dst"), some ("E", "e", progOfHOL ProgHOL.skip)))
        "f" [.const 5]) := by
  refine compileProgExactHOLW_call_wrapped_result_fallback_handler_present_eid_bridge
    (context := exactRaiseContext) (kind := .local) (resultName := "dst")
    (function := "f") (exceptionName := "E") (exceptionVariable := "e")
    (arguments := [.const 5]) (body := .skip) (exceptionCode := BitVec.ofNat 8 12)
    ?_ ?_ (by decide) (by decide) ?_ ?_
  · rfl
  · rfl
  · intro expression hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL.eq_1, shapeOfHOL]
  · simp [compileProgExactHOLW, compileProgHOL, progOfHOL, crepProgOfHOL]

/-- The `ExtCall` success bridge (`pan_to_crepScript.sml:274-290`) closes the
    four `One`-shaped operand bindings and the maximum-variable temporary base
    for concrete constant operands. -/
example :
    crepProgOfHOL (compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.extCall (ofString "f") (expToHOL (.const 5)) (expToHOL (.const 6))
        (expToHOL (.const 7)) (expToHOL (.const 8)))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (.extCall "f" (.const 5) (.const 6) (.const 7) (.const 8)) := by
  refine compileProgExactHOLW_extCall_success_bridge
    (context := exactLocalAssignContext [7] [8]) (function := "f")
    (configuration := .const 5) (configurationLength := .const 6)
    (array := .const 7) (arrayLength := .const 8) (hfunction := by decide)
    (exactConfiguration := .const 5) (exactConfigurationRest := [])
    (exactConfigurationLength := .const 6) (exactConfigurationLengthRest := [])
    (exactArray := .const 7) (exactArrayRest := [])
    (exactArrayLength := .const 8) (exactArrayLengthRest := [])
    (productionConfiguration := .const 5) (productionConfigurationRest := [])
    (productionConfigurationLength := .const 6) (productionConfigurationLengthRest := [])
    (productionArray := .const 7) (productionArrayRest := [])
    (productionArrayLength := .const 8) (productionArrayLengthRest := [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    simp only [compileExpExactHOLW.eq_1, expToHOL.eq_1, compileExpHOL.eq_1,
      List.map_cons, List.map_nil, crepExpOfHOL]

def exactShMemStoreClauseParity : Bool :=
  (match compileShMemStoreExactHOLW
      (exactLocalAssignContext [7] [8]) .op8 (.var .local (ofString "src")) (.const 3) with
   | .dec 9 (.const 3) (.shMem .store8 9 (.var 8)) => true
   | _ => false) &&
  (match compileShMemStoreExactHOLW exactReturnContext .op8 (.rstruct []) (.const 3) with
   | .skip => true
   | _ => false) &&
  (match compileShMemStoreExactHOLW exactReturnContext .op8 (.const 4) (.rstruct []) with
   | .skip => true
   | _ => false)

#guard exactShMemStoreClauseParity

/-! The exact and production compiler clauses agree on HOL's positional
    `ShMemStore value address` operands, including the fresh index coming from
    variables in the first (stored-value) operand. -/
def exactShMemStoreProductionBridgeParity : Bool :=
  let context := exactLocalAssignContext [1] [8]
  let value := Exp.var .local "src"
  let address := Exp.var .local "dst"
  match
      (crepProgOfHOL (compileProgExactHOLW context
          (.shMemStore .op8 (expToHOL value) (expToHOL address))),
        compileProgRiscV context.toProduction (.shMemStore .op8 value address)) with
  | (.dec 9 (.var 1) (.shMem .store8 9 (.var 8)),
      .dec 9 (.var 1) (.shMem .store8 9 (.var 8))) => true
  | _ => false

#guard exactShMemStoreProductionBridgeParity

def exactShMemLoadClauseParity : Bool :=
  (match compileShMemLoadExactHOLW (exactLocalAssignContext [7] [8]) .op8
      (ofString "dst") (.const 3) with
   | .shMem .load8 7 (.const 3) => true
   | _ => false) &&
  (match compileShMemLoadExactHOLW exactReturnContext .op8
      (ofString "dst") (.const 3) with
   | .skip => true
   | _ => false) &&
  (match compileShMemLoadExactHOLW (exactLocalAssignContext [7] [8]) .op8
      (ofString "dst") (.rstruct []) with
   | .skip => true
   | _ => false)

#guard exactShMemLoadClauseParity

example :
    crepProgOfHOL (compileProgExactHOLW
      (exactLocalAssignContext [7] [8])
      (.shMemLoad .op8 .local (ofString "dst") (expToHOL (.const (3 : BitVec 8))))) =
    compileProgRiscV (exactLocalAssignContext [7] [8]).toProduction
      (progOfHOL
        (.shMemLoad .op8 .local (ofString "dst") (expToHOL (.const (3 : BitVec 8))))) := by
  apply compileProgExactHOLW_local_shmem_load_bridge
  · simp [ExpByteRanged]
  · simp [compileExpExactHOLW, compileExpHOL, expToHOL, crepExpOfHOL, shapeOfHOL]

def exactDecClauseParity : Bool :=
  (match compileDecExactHOLW exactReturnContext (ofString "x") .one (.const 4)
      (fun bodyContext => compileReturnExactHOLW bodyContext
        (.var .local (ofString "x"))) with
   | .dec 1 (.const 4) (.return [.var 1]) => true
   | _ => false) &&
  (match compileDecExactHOLW exactReturnContext (ofString "pair") (.comb [.one, .one])
      (.rstruct [.const 1, .const 2]) (fun _ => .tick) with
   | .dec 1 (.const 1) (.dec 2 (.const 2) .tick) => true
   | _ => false) &&
  (match compileDecExactHOLW exactReturnContext (ofString "x")
      (.named (ofString "wrong")) (.const 4)
      (fun bodyContext =>
        match bodyContext.vars.lookup (ofString "x") with
        | some (.one, _) => .tick
        | _ => .break 0) with
   | .dec 1 (.const 4) .tick => true
   | _ => false) &&
  (match compileDecExactHOLW exactReturnContext (ofString "x")
      (.comb [.one, .one]) (.const 4)
      (fun bodyContext =>
        match bodyContext.vars.lookup (ofString "x") with
        | some (.one, _) => .tick
        | _ => .break 0) with
   | .dec 1 (.const 4) .tick => true
   | _ => false) &&
  (match compileDecExactHOLW exactMalformedStoreContext (ofString "x") .one
      (.var .local (ofString "bad")) (fun _ => .tick) with
   | .skip => true
   | _ => false)

#guard exactDecClauseParity

/- Direct HOL `compile_def_probe.out` row `dec_declared_shape_ignored`:
   `compile_exp` returns a two-word shape even though the source Dec declares
   One, so the body must see the compiled shape and select its second field. -/
#guard match compileProgExactHOLW exactReturnContext
    (.dec (ofString "pair") .one
      (.rstruct [.const (4 : BitVec 8), .const 5])
      (.return (.rfield 1 (.var .local (ofString "pair"))))) with
  | .dec 1 (.const 4) (.dec 2 (.const 5) (.return [.var 2])) => true
  | _ => false

def exactDecCallClauseParity : Bool :=
  (match compileDecCallExactHOLW (exactDecCallContext 4) (ofString "x") .one
      (ofString "f") [.const 3]
      (fun bodyContext => compileReturnExactHOLW bodyContext
        (.var .local (ofString "x"))) with
   | .dec 5 (.const 0) (.seq (.call (some ([5], none)) function [.const 3])
       (.return [.var 5])) => function == ofString "f"
   | _ => false) &&
  (match compileDecCallExactHOLW (exactDecCallContext 10) (ofString "pair")
      (.comb [.one, .one]) (ofString "f") [.const 3, .const 4]
      (fun bodyContext => compileReturnExactHOLW bodyContext
        (.var .local (ofString "pair"))) with
   | .dec 11 (.const 0) (.dec 12 (.const 0)
       (.seq (.call (some ([11, 12], none)) function [.const 3, .const 4])
         (.return [.var 11, .var 12]))) => function == ofString "f"
   | _ => false)

#guard exactDecCallClauseParity

def exactCallNoReturnParity : Bool :=
  match compileCallNoReturnExactHOLW exactReturnContext (ofString "f")
      [.const 1, .rstruct [.const 2, .const 3]] with
  | .call none function [.const 1, .const 2, .const 3] =>
      function == ofString "f"
  | _ => false

#guard exactCallNoReturnParity

def exactCallWrappedResultNoHandlerParity : Bool :=
  match compileCallWrappedResultNoHandlerExactHOLW exactCallWrappedResultContext
      (ofString "f") (ofString "pair")
      [.const 1, .rstruct [.const 2, .const 3]] (.comb [.one, .one]) [30, 31]
      (by simp [exactCallWrappedResultContext, wrapRtHOL,
        HolFiniteMapExact.lookup_update, FUPDATE]) with
  | .call (some ([30, 31], none)) function [.const 1, .const 2, .const 3] =>
      function == ofString "f"
  | _ => false

#guard exactCallWrappedResultNoHandlerParity

def exactCallWrappedResultFallbackNoHandlerParity : Bool :=
  (match compileCallWrappedResultFallbackNoHandlerExactHOLW exactReturnContext
      (ofString "f") (ofString "missing")
      [.const 1, .rstruct [.const 2, .const 3]]
      (by simp [exactReturnContext, wrapRtHOL]) with
   | .call none function [.const 1, .const 2, .const 3] =>
       function == ofString "f"
   | _ => false) &&
  (match compileCallWrappedResultFallbackNoHandlerExactHOLW
      exactCallWrappedEmptyOneContext (ofString "f") (ofString "empty_one")
      [.const 1, .rstruct [.const 2, .const 3]]
      (by simp [exactCallWrappedEmptyOneContext, wrapRtHOL,
        HolFiniteMapExact.lookup_update, FUPDATE]) with
   | .call none function [.const 1, .const 2, .const 3] =>
       function == ofString "f"
   | _ => false)

#guard exactCallWrappedResultFallbackNoHandlerParity

def exactCallWrappedResultHandlerMissingEidParity : Bool :=
  match compileCallWrappedResultHandlerMissingEidExactHOLW
      exactCallWrappedResultContext (ofString "f") (ofString "pair")
      [.const 1, .rstruct [.const 2, .const 3]] (.comb [.one, .one]) [30, 31]
      (ofString "E") (ofString "exn") .tick
      (by simp [exactCallWrappedResultContext, wrapRtHOL,
        HolFiniteMapExact.lookup_update, FUPDATE])
      (by simp [exactCallWrappedResultContext,
        HolFiniteMapExact.lookup_empty]) with
  | .call (some ([30, 31], none)) function [.const 1, .const 2, .const 3] =>
      function == ofString "f"
  | _ => false

#guard exactCallWrappedResultHandlerMissingEidParity

def exactCallWrappedResultHandlerPresentEidParity : Bool :=
  match compileCallWrappedResultHandlerPresentEidExactHOLW
      exactCallWrappedHandlerPresentContext (ofString "f") (ofString "pair")
      [.const 1, .rstruct [.const 2, .const 3]] (.comb [.one, .one]) [30, 31]
      (ofString "E") (ofString "exn") (BitVec.ofNat 8 12)
      (by
        have hne : ofString "exn" ≠ ofString "pair" := by decide
        simp [exactCallWrappedHandlerPresentContext, wrapRtHOL,
          HolFiniteMapExact.lookup_update, FUPDATE, hne])
      (by simp [exactCallWrappedHandlerPresentContext,
        HolFiniteMapExact.lookup_update, FUPDATE])
      (fun _ => .tick) with
  | .call (some ([30, 31], some (BitVec.ofNat 8 12,
        .seq (.seq (.assign 20 (.loadGlob 0))
          (.seq (.assign 21 (.loadGlob 1)) .skip)) .tick))) function
      [.const 1, .const 2, .const 3] => function == ofString "f"
  | _ => false

#guard exactCallWrappedResultHandlerPresentEidParity

def exactCallWrappedFallbackHandlerPresentEidParity : Bool :=
  match compileCallWrappedResultFallbackHandlerPresentEidExactHOLW
      exactCallWrappedFallbackHandlerPresentContext (ofString "f")
      (ofString "missing") [.const 1, .rstruct [.const 2, .const 3]]
      (ofString "E") (ofString "exn") (BitVec.ofNat 8 12)
      (by
        have hne : ofString "exn" ≠ ofString "missing" := by decide
        simp [exactCallWrappedFallbackHandlerPresentContext, wrapRtHOL,
          HolFiniteMapExact.lookup_update, FUPDATE, hne])
      (by simp [exactCallWrappedFallbackHandlerPresentContext,
        HolFiniteMapExact.lookup_update, FUPDATE])
      (fun _ => .tick) with
  | .call (some ([], some (BitVec.ofNat 8 12,
        .seq (.seq (.assign 20 (.loadGlob 0))
          (.seq (.assign 21 (.loadGlob 1)) .skip)) .tick))) function
      [.const 1, .const 2, .const 3] => function == ofString "f"
  | _ => false

#guard exactCallWrappedFallbackHandlerPresentEidParity

def exactCallWrappedFallbackHandlerMissingEidParity : Bool :=
  match compileCallWrappedResultFallbackHandlerMissingEidExactHOLW
      exactCallWrappedFallbackHandlerMissingContext (ofString "f")
      (ofString "missing") [.const 1, .rstruct [.const 2, .const 3]]
      (ofString "E") (ofString "exn") .tick
      (by
        have hne : ofString "exn" ≠ ofString "missing" := by decide
        simp [exactCallWrappedFallbackHandlerMissingContext, wrapRtHOL,
          HolFiniteMapExact.lookup_update, FUPDATE, hne])
      (by simp [exactCallWrappedFallbackHandlerMissingContext]) with
  | .call none function [.const 1, .const 2, .const 3] =>
      function == ofString "f"
  | _ => false

#guard exactCallWrappedFallbackHandlerMissingEidParity

def exactCallResultNoHandlerParity : Bool :=
  (match compileCallResultNoHandlerExactHOLW exactCallResultContext (ofString "f")
      [.const 1, .rstruct [.const 2, .const 3]] with
   | .dec 11 (.const 0) (.dec 12 (.const 0)
       (.call (some ([11, 12], none)) function [.const 1, .const 2, .const 3])) =>
       function == ofString "f"
   | _ => false) &&
  (match compileCallResultNoHandlerExactHOLW exactReturnContext (ofString "missing")
      [.const 1, .rstruct [.const 2, .const 3]] with
   | .call (some ([], none)) function [.const 1, .const 2, .const 3] =>
       function == ofString "missing"
   | _ => false)

#guard exactCallResultNoHandlerParity

def exactCallHandlerMissingEidParity : Bool :=
  match compileCallHandlerMissingEidExactHOLW exactCallResultContext (ofString "f")
      [.const 1, .rstruct [.const 2, .const 3]] (ofString "E") (ofString "exn")
      .tick (by simp [exactCallResultContext]) with
  | .dec 11 (.const 0) (.dec 12 (.const 0)
      (.call (some ([11, 12], none)) function [.const 1, .const 2, .const 3])) =>
      function == ofString "f"
  | _ => false

#guard exactCallHandlerMissingEidParity

def exactCallHandlerPresentEidParity : Bool :=
  match compileCallHandlerPresentEidExactHOLW exactCallHandlerPresentContext
      (ofString "f") [.const 1, .rstruct [.const 2, .const 3]] (ofString "E")
      (ofString "exn") (BitVec.ofNat 8 12)
      (by simp [exactCallHandlerPresentContext, HolFiniteMapExact.lookup_update, FUPDATE])
      (fun _ => .tick) with
  | .dec 11 (.const 0)
      (.call (some ([11], some (BitVec.ofNat 8 12,
        .seq (.seq (.assign 20 (.loadGlob 0))
          (.seq (.assign 21 (.loadGlob 1)) .skip)) .tick))) function
        [.const 1, .const 2, .const 3]) =>
      function == ofString "f"
  | _ => false

#guard exactCallHandlerPresentEidParity

/-! The exact `Call` info dispatcher is checked across all three top-level
    return-type forms, plus handler lookups on both assigned-result branches.
    The HOL output rows are the direct `compile_def` evaluations in
    `scripts/hol-probes/compile_def_probe.out` (`call_no_return`,
    `call_result_no_handler_*`, and `call_wrapped_result_*`). -/

def exactCallInfoDispatchParity : Bool :=
  (match compileCallInfoExactHOLW exactReturnContext (ofString "f") none
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ _ => .skip) with
   | .call none function [.const 1, .const 2, .const 3] => function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactCallResultContext (ofString "f")
      (some (none, none)) [.const 1, .rstruct [.const 2, .const 3]]
      (fun _ _ => .skip) with
   | .dec 11 (.const 0) (.dec 12 (.const 0)
       (.call (some ([11, 12], none)) function [.const 1, .const 2, .const 3])) =>
       function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactCallResultContext (ofString "f")
      (some (none, some (ofString "E", ofString "exn", .tick)))
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ _ => .skip) with
   | .dec 11 (.const 0) (.dec 12 (.const 0)
       (.call (some ([11, 12], none)) function [.const 1, .const 2, .const 3])) =>
       function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactCallWrappedResultContext (ofString "f")
      (some (some (.local, ofString "pair"), none))
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ _ => .skip) with
   | .call (some ([30, 31], none)) function [.const 1, .const 2, .const 3] =>
       function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactReturnContext (ofString "f")
      (some (some (.local, ofString "missing"), none))
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ _ => .skip) with
   | .call none function [.const 1, .const 2, .const 3] => function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactCallWrappedResultContext (ofString "f")
      (some (some (.local, ofString "pair"),
        some (ofString "E", ofString "exn", .tick)))
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ _ => .skip) with
   | .call (some ([30, 31], none)) function [.const 1, .const 2, .const 3] =>
       function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactCallWrappedFallbackHandlerMissingContext
      (ofString "f")
      (some (some (.local, ofString "missing"),
        some (ofString "E", ofString "exn", .tick)))
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ _ => .skip) with
   | .call none function [.const 1, .const 2, .const 3] => function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactCallWrappedHandlerPresentContext
      (ofString "f")
      (some (some (.local, ofString "pair"),
        some (ofString "E", ofString "exn", .tick)))
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ body =>
        match body with | .tick => .tick | _ => .skip) with
   | .call (some ([30, 31], some (BitVec.ofNat 8 12,
       .seq (.seq (.assign 20 (.loadGlob 0))
         (.seq (.assign 21 (.loadGlob 1)) .skip)) .tick))) function
       [.const 1, .const 2, .const 3] => function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactCallHandlerPresentContext (ofString "f")
      (some (none, some (ofString "E", ofString "exn", .tick)))
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ body =>
        match body with | .tick => .tick | _ => .skip) with
   | .dec 11 (.const 0) (.call (some ([11], some
       (BitVec.ofNat 8 12, .seq (.seq (.assign 20 (.loadGlob 0))
         (.seq (.assign 21 (.loadGlob 1)) .skip)) .tick))) function
       [.const 1, .const 2, .const 3]) => function == ofString "f"
   | _ => false) &&
  (match compileCallInfoExactHOLW exactCallWrappedFallbackHandlerPresentContext
      (ofString "f")
      (some (some (.local, ofString "missing"),
        some (ofString "E", ofString "exn", .tick)))
      [.const 1, .rstruct [.const 2, .const 3]] (fun _ body =>
        match body with | .tick => .tick | _ => .skip) with
   | .call (some ([], some (BitVec.ofNat 8 12,
       .seq (.seq (.assign 20 (.loadGlob 0))
         (.seq (.assign 21 (.loadGlob 1)) .skip)) .tick))) function
       [.const 1, .const 2, .const 3] => function == ofString "f"
   | _ => false)

#guard exactCallInfoDispatchParity

def exactExtCallClauseParity : Bool :=
  (match compileExtCallExactHOLW exactExtCallContext (ofString "f")
      (.var .local (ofString "configuration"))
      (.var .local (ofString "configurationLength"))
      (.var .local (ofString "array"))
      (.var .local (ofString "arrayLength")) with
   | .dec 101 (.var 4) (.dec 102 (.var 5) (.dec 103 (.var 6)
       (.dec 104 (.var 7) (.extCall function 101 102 103 104)))) =>
       function == ofString "f"
   | _ => false) &&
  (match compileExtCallExactHOLW exactExtCallConstantContext (ofString "f")
      (.const 1) (.const 2) (.const 3) (.const 4) with
   | .dec 1 (.const 1) (.dec 2 (.const 2) (.dec 3 (.const 3)
       (.dec 4 (.const 4) (.extCall function 1 2 3 4)))) =>
       function == ofString "f"
   | _ => false) &&
  (match compileExtCallExactHOLW exactMalformedExtCallContext (ofString "f")
      (.var .local (ofString "configuration")) (.const 1) (.const 2) (.const 3) with
   | .skip => true
   | _ => false) &&
  (match compileExtCallExactHOLW exactReturnContext (ofString "f")
      (.rstruct []) (.const 1) (.const 2) (.const 3) with
   | .skip => true
   | _ => false)

#guard exactExtCallClauseParity

/-! Whole-definition checks run each top-level syntax constructor through the
    exact recursive compiler. Their expected equations correspond to the
    committed direct HOL rows in `compile_def_probe.out`; individual row names
    and corner-case details are exercised by the clause guards above. -/

def exactCompileDefRecursiveParity : Bool :=
  (match compileProgExactHOLW exactReturnContext (.skip : ProgHOL 8) with
   | .skip => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext
      (.dec (ofString "x") .one (.const 4) (.return (.var .local (ofString "x")))) with
   | .dec 1 (.const 4) (.return [.var 1]) => true | _ => false) &&
  (match compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.assign .local (ofString "dst") (.var .local (ofString "src"))) with
   | .seq (.assign 7 (.var 8)) .skip => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext
      (.assign .global (ofString "g") (.const 5)) with
   | .skip => true | _ => false) &&
  (match compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.primitive (ofString "dst") .addCarry
        [.const 1, .var .local (ofString "src")]) with
   | .dec 11 (.const 1) (.dec 12 (.var 8) (.primitive [7] .addCarry [11, 12])) => true
   | _ => false) &&
  (match compileProgExactHOLW exactReturnContext (.store (.const 3) (.const 4)) with
   | .dec 1 (.const 3) (.dec 2 (.const 4)
       (.seq (.store (.var 1) (.var 2)) .skip)) => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext (.store32 (.const 1) (.const 2)) with
   | .store32 (.const 1) (.const 2) => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext (.storeByte (.const 3) (.const 4)) with
   | .storeByte (.const 3) (.const 4) => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext
      (.seq .skip (.seq .break .continue)) with
   | .seq .skip (.seq (.break 0) (.continue 0)) => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext
      (.ite (.const 1) .skip .break) with
   | .ite (.const 1) .skip (.break 0) => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext (.while (.const 2) .break) with
   | .while (.const 2) (.break 0) => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext (.call none (ofString "f")
      [.const 1, .rstruct [.const 2, .const 3]]) with
   | .call none function [.const 1, .const 2, .const 3] => function == ofString "f"
   | _ => false) &&
  (match compileProgExactHOLW (exactDecCallContext 4)
      (.decCall (ofString "x") .one (ofString "f") [.const 3]
        (.return (.var .local (ofString "x")))) with
   | .dec 5 (.const 0) (.seq (.call (some ([5], none)) function [.const 3])
       (.return [.var 5])) => function == ofString "f" | _ => false) &&
  (match compileProgExactHOLW exactExtCallConstantContext
      (.extCall (ofString "f") (.const 1) (.const 2) (.const 3) (.const 4)) with
   | .dec 1 (.const 1) (.dec 2 (.const 2) (.dec 3 (.const 3)
       (.dec 4 (.const 4) (.extCall function 1 2 3 4)))) => function == ofString "f"
   | _ => false) &&
  (match compileProgExactHOLW exactRaiseContext (.raise (ofString "E") (.const 9)) with
   | .seq (.dec 1 (.const 9) (.seq (.storeGlob 0 (.var 1)) .skip)) (.raise 12) => true
   | _ => false) &&
  (match compileProgExactHOLW exactReturnContext (.return (.const 7)) with
   | .return [.const 7] => true | _ => false) &&
  (match compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.shMemLoad .op8 .local (ofString "dst") (.const 3)) with
   | .shMem .load8 7 (.const 3) => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext
      (.shMemLoad .op8 .global (ofString "g") (.const 3)) with
   | .skip => true | _ => false) &&
  (match compileProgExactHOLW (exactLocalAssignContext [7] [8])
      (.shMemStore .op8 (.var .local (ofString "src")) (.const 3)) with
   | .dec 9 (.const 3) (.shMem .store8 9 (.var 8)) => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext (.tick : ProgHOL 8) with
   | .tick => true | _ => false) &&
  (match compileProgExactHOLW exactReturnContext
      (.annot (ofString "tag") (ofString "text")) with
   | .skip => true | _ => false)

#guard exactCompileDefRecursiveParity

def runChecks : IO Bool := do
  if parityGuard && exactStructuralSliceParity && exactReturnClauseParity &&
      exactStoreClauseParity && exactIfWhileClauseParity && exactGlobalFallbackParity &&
      exactLocalAssignClauseParity && exactPrimitiveClauseParity && exactStoreClauseFullParity &&
      exactRaiseClauseParity && exactShMemStoreClauseParity && exactShMemLoadClauseParity &&
      exactDecClauseParity && exactDecCallClauseParity && exactCallNoReturnParity &&
      exactCallResultNoHandlerParity && exactCallHandlerMissingEidParity &&
      exactCallHandlerPresentEidParity && exactExtCallClauseParity &&
      exactCompileDefRecursiveParity then
    IO.println "PASS exact compile_def clause parity"
  else
    IO.println "FAIL compile_def parity"
  pure (parityGuard && exactStructuralSliceParity && exactReturnClauseParity &&
    exactStoreClauseParity && exactIfWhileClauseParity && exactGlobalFallbackParity &&
    exactLocalAssignClauseParity && exactPrimitiveClauseParity && exactStoreClauseFullParity &&
    exactRaiseClauseParity && exactShMemStoreClauseParity && exactShMemLoadClauseParity &&
    exactDecClauseParity && exactDecCallClauseParity && exactCallNoReturnParity &&
    exactCallResultNoHandlerParity && exactCallHandlerMissingEidParity &&
    exactCallHandlerPresentEidParity && exactExtCallClauseParity &&
    exactCompileDefRecursiveParity)

end Flapjack.Test.CompileDefParity
