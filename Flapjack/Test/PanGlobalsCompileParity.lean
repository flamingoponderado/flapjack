module

public import Flapjack.Pancake.PanGlobals
public import Flapjack.Pancake.PanGlobals.CompileExpExact

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.PanGlobals
public meta import Flapjack.Pancake.PanGlobals.CompileExpExact
@[expose] public section

namespace Flapjack.Test.PanGlobalsCompileParity

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

def compileContext : GlobalPassContext Nat :=
  { globals := [("g", (.one, 8))]
    globalsSize := 1
    maxGlobalsSize := 16
    bytesInWord := 1
    fromNat := id }

/-- Exact `ProgHOL`/`MlS` replay of the direct `pan_globals$compile_def`
    output rows in `pan_globals_compile_probe.out`. This complements the
    production-carrier checks above; it does not claim the executed production
    compiler has been textually routed through `compileProgExactHOL`. -/
def compileProgExactContext8 : PanGlobalsContextExact 8 where
  globals := {
    lookup := fun name =>
      if name = ofString "g" then some (.one, BitVec.ofNat 8 8) else none
    finiteSupport := by
      refine ⟨[ofString "g"], ?_⟩
      intro name h
      by_cases hname : name = ofString "g"
      · simp [hname]
      · simp [hname] at h
  }
  globalsSize := BitVec.ofNat 8 1
  maxGlobalsSize := BitVec.ofNat 8 16

def compileProgExactOracleGuard : Bool :=
  (match compileProgExactHOL compileProgExactContext8
      (.assign .local (ofString "x") (.const (BitVec.ofNat 8 7)) : ProgHOL 8) with
  | .assign .local name (.const value) =>
      decide (name = ofString "x") && value == BitVec.ofNat 8 7
  | _ => false) &&
  (match compileProgExactHOL compileProgExactContext8
      (.assign .global (ofString "g") (.const (BitVec.ofNat 8 7)) : ProgHOL 8) with
  | .store (.op .sub [.topAddr, .const address]) (.const value) =>
      address == BitVec.ofNat 8 8 && value == BitVec.ofNat 8 7
  | _ => false) &&
  (match compileProgExactHOL compileProgExactContext8
      (.assign .global (ofString "missing") (.const (BitVec.ofNat 8 7)) : ProgHOL 8) with
  | .skip => true
  | _ => false) &&
  (match compileProgExactHOL compileProgExactContext8
      (.seq .skip (.return (.const (BitVec.ofNat 8 7))) : ProgHOL 8) with
  | .seq .skip (.return (.const value)) => value == BitVec.ofNat 8 7
  | _ => false) &&
  (match compileProgExactHOL compileProgExactContext8
      (.call (some (some (.global, ofString "g"),
        some (ofString "E", ofString "handler", .skip))) (ofString "f")
        [.var .local (ofString "") ] : ProgHOL 8) with
  | .dec resultName .one (.const zero)
      (.dec flagName .one (.const flagZero)
        (.seq
          (.call
            (some (some (.local, callResult), some (exception, handlerName,
              .seq .skip (.assign .local assignedFlag (.const flagOne)))))
            function [.var .local argument])
          (.ite (.var .local guardFlag) .skip
            (.store (.op .sub [.topAddr, .const address]) (.var .local storeResult))))) =>
      decide (resultName = ofString "'") && decide (flagName = ofString "vn'") &&
        zero == BitVec.ofNat 8 0 && flagZero == BitVec.ofNat 8 0 &&
        decide (callResult = resultName) && decide (exception = ofString "E") &&
        decide (handlerName = ofString "handler") &&
        decide (assignedFlag = ofString "vn'") && flagOne == BitVec.ofNat 8 1 &&
        decide (function = ofString "f") && decide (argument = ofString "") &&
        decide (guardFlag = ofString "vn'") && address == BitVec.ofNat 8 8 &&
        decide (storeResult = resultName)
  | _ => false) &&
  (match compileProgExactHOL compileProgExactContext8
      (.return (.var .global (ofString "g")) : ProgHOL 8) with
  | .return (.load .one (.op .sub [.topAddr, .const address])) =>
      address == BitVec.ofNat 8 8
  | _ => false) &&
  (match compileProgExactHOL compileProgExactContext8
      (.call (some (some (.global, ofString "g"),
        some (ofString "E", ofString "handler", .skip))) (ofString "f") [] : ProgHOL 8) with
  | .dec resultName .one (.const zero)
      (.dec flagName .one (.const flagZero)
        (.seq
          (.call
            (some (some (.local, callResult), some (exception, handlerName,
              .seq .skip (.assign .local assignedFlag (.const flagOne)))))
            function [])
          (.ite (.var .local guardFlag) .skip
            (.store (.op .sub [.topAddr, .const address]) (.var .local storeResult))))) =>
      decide (resultName = ofString "") && decide (flagName = ofString "vn'") &&
        zero == BitVec.ofNat 8 0 && flagZero == BitVec.ofNat 8 0 &&
        decide (callResult = resultName) && decide (exception = ofString "E") &&
        decide (handlerName = ofString "handler") &&
        decide (assignedFlag = ofString "vn'") && flagOne == BitVec.ofNat 8 1 &&
        decide (function = ofString "f") && decide (guardFlag = ofString "vn'") &&
        address == BitVec.ofNat 8 8 && decide (storeResult = resultName)
  | _ => false)

#eval compileProgExactOracleGuard
#guard compileProgExactOracleGuard

/-! Direct parity for `pan_globals$compile_def`
    (`pan_globalsScript.sml:69`). -/
def parityGuard : Bool :=
  (match globalCompileProg compileContext
      (.assign .local "x" (.const 7)) with
  | .assign .local "x" (.const 7) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.assign .global "g" (.const 7)) with
  | .store (.op .sub [.topAddr, .const 8]) (.const 7) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.assign .global "missing" (.const 7)) with
  | .skip => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.seq .skip (.return (.const 7))) with
  | .seq .skip (.return (.const 7)) => true
  | _ => false) &&
  (match globalCompileProg compileContext
      (.return (.var .global "g")) with
  | .return (.load .one (.op .sub [.topAddr, .const 8])) => true
  | _ => false)

#eval parityGuard
#guard parityGuard

/-! In Cake's global-destination handled-call branch, the result slot is
    freshened from `""`, but the handler flag is independently freshened from
    the fixed seed `"vn'"`. This direct generated-program regression matches
    `global_destination_handler_flag` in
    `scripts/hol-probes/pan_globals_compile_probe.out`. -/
def globalHandlerFlagInput : Prog Nat :=
  .call (some (some (.global, "g"), some ("E", "handler", .skip))) "f" []

def globalHandlerFlagGuard : Bool :=
  match globalCompileProg compileContext globalHandlerFlagInput with
  | .dec "" .one (.const 0)
      (.dec "vn'" .one (.const 0)
        (.seq
          (.call
            (some (some (.local, ""), some ("E", "handler",
              .seq .skip (.assign .local "vn'" (.const 1)))))
            "f" [])
          (.ite (.var .local "vn'") .skip
            (.store (.op .sub [.topAddr, .const 8]) (.var .local ""))))) => true
  | _ => false

#eval globalHandlerFlagGuard
#guard globalHandlerFlagGuard

/-! Cake's duplicate top-level declarations retain one initializer per
    declaration, while the final `FLOOKUP` binding is the last declaration.
    This is the source-level contract exercised by
    `Flapjack/Test/OriginalPancake/dup_global.pnk`; the warning is handled by
    the static checker, and this guard pins the address/layout semantics before
    the later allocator boundary. -/
def duplicateGlobalDecls : List (Decl Nat) :=
  [.decl .one "g" (.const 7),
   .decl .one "g" (.const 7),
   .function
     { name := "main"
       inline := false
       exported := false
       params := []
       body := .return (.var .global "g")
       returnShape := .one }]

/-! Cake compiles each global initializer with only the declarations that
    precede it in source order.  A reference to a later global therefore
    takes `compile_exp`'s zero fallback, even though the final global context
    used for function bodies contains that later declaration.  This guard is
    the direct source-shaped regression for GH #1063 and mirrors
    `pan_globalsScript.sml:162-169`. -/
def laterGlobalInitializerDecls : List (Decl Nat) :=
  [.decl .one "first" (.var .global "later"),
   .decl .one "later" (.const 7),
   .function
     { name := "main"
       inline := false
       exported := false
       params := []
       body := .return (.var .global "later")
       returnShape := .one }]

end Flapjack.Test.PanGlobalsCompileParity
