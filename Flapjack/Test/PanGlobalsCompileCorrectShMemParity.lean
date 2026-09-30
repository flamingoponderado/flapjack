import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.ShMem

/-!
# pan_globals `compile_correct` `ShMemLoad`/`ShMemStore` regression

Kernel-checked regression for the exact tagged `compile_correct` `ShMemStore`
and `ShMemLoad` (Local sub-case) ports and for the `pan_globals$compile_def`
`ShMemLoad`/`ShMemStore` clauses over the exact carriers.  The statements are
conditional over arbitrary programs/states, so there is no direct HOL `EVAL`
oracle; the compiler clauses are pinned definitionally and the tagged theorems
are replayed at concrete carriers instead.
-/

namespace Flapjack.Test.PanGlobalsCompileCorrectShMemParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsCompileCorrect
open Flapjack.Basis.Pure.MlString (ofString)

/-- Probe context with the global `g` bound to a `One` shape at address `8`. -/
def probeContext : PanGlobalsContextExact 8 where
  globals :=
    { lookup := fun key => if key = ofString "g" then some (.one, 8) else none
      finiteSupport := by
        refine ⟨[ofString "g"], ?_⟩
        intro key hkey
        by_cases h : key = ofString "g"
        · simp [h]
        · simp [h] at hkey }
  globalsSize := 1
  maxGlobalsSize := 16

/-- The local `ShMemLoad` clause keeps the constructor and compiles the
    address only. -/
example (name : MlS) (address : ExpHOL 8) :
    compileProgExactHOL probeContext (.shMemLoad .opW .local name address) =
      .shMemLoad .opW .local name (compileExpExactHOL probeContext address) := by
  simp [compileProgExactHOL]

/-- The `ShMemStore` clause compiles both expressions. -/
example (address value : ExpHOL 8) :
    compileProgExactHOL probeContext (.shMemStore .opW address value) =
      .shMemStore .opW (compileExpExactHOL probeContext address)
        (compileExpExactHOL probeContext value) := by
  simp [compileProgExactHOL]

/-- The global `ShMemLoad` clause lowers to the nested
    `Dec`/`Dec`/`Seq`/`ShMemLoad`/`Store` program with the fresh `name'`
    temporary and the `top_addr - address` global slot. -/
example (address : ExpHOL 8) :
    compileProgExactHOL probeContext (.shMemLoad .opW .global (ofString "g") address) =
      .dec (ofString "g") .one (compileExpExactHOL probeContext address)
        (.dec (mlstrAppend (ofString "g") (ofString "'")) .one (.const 0)
          (.seq
            (.shMemLoad .opW .local (mlstrAppend (ofString "g") (ofString "'"))
              (.var .local (ofString "g")))
            (.store (.op .sub [.topAddr, .const (8 : BitVec 8)])
              (.var .local (mlstrAppend (ofString "g") (ofString "'")))))) := by
  have hg : probeContext.globals.lookup (ofString "g") = some (.one, 8) := by
    simp [probeContext]
  simp [compileProgExactHOL, hg]

/-- The tagged `ShMemStore` case is usable at the exact carriers. -/
example (operator : OpSize) (address value : ExpHOL 8)
    (s : PanSemStateFiniteExact 8 Unit) :
    (∀ (res : Option (PanSemResultExact 8)) (ctxt : PanGlobalsContextExact 8)
        (t s' : PanSemStateFiniteExact 8 Unit),
        panGlobalsStateRelHOLExact true ctxt s t ∧
          evaluateHOLFiniteState s (.shMemStore operator address value) = (res, s') ∧
          res ≠ some .error →
        ∃ t', evaluateHOLFiniteState t
            (compileProgExactHOL ctxt (.shMemStore operator address value)) = (res, t') ∧
          panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t') :=
  compileCorrect_ShMemStore operator address value s

/-- The tagged `ShMemLoad` Local sub-case is usable at the exact carriers. -/
example (operator : OpSize) (name : MlS) (address : ExpHOL 8)
    (s : PanSemStateFiniteExact 8 Unit) :
    (∀ (res : Option (PanSemResultExact 8)) (ctxt : PanGlobalsContextExact 8)
        (t s' : PanSemStateFiniteExact 8 Unit),
        panGlobalsStateRelHOLExact true ctxt s t ∧
          evaluateHOLFiniteState s (.shMemLoad operator .local name address) = (res, s') ∧
          res ≠ some .error →
        ∃ t', evaluateHOLFiniteState t
            (compileProgExactHOL ctxt (.shMemLoad operator .local name address)) = (res, t') ∧
          panGlobalsStateRelHOLExact (goodResHOL res) ctxt s' t') :=
  compileCorrect_ShMemLoad_local operator name address s

/-- Runtime guard: the local `ShMemLoad` compile keeps the constructor. -/
def localLoadCompileGuard : Bool :=
  match compileProgExactHOL probeContext
      (.shMemLoad .opW .local (ofString "x") (.var .local (ofString "x")) : ProgHOL 8) with
  | .shMemLoad .opW .local _ (.var .local _) => true
  | _ => false

/-- Runtime guard: the `ShMemStore` compile keeps the constructor. -/
def storeCompileGuard : Bool :=
  match compileProgExactHOL probeContext
      (.shMemStore .opW (.const (1 : BitVec 8)) (.const (2 : BitVec 8)) : ProgHOL 8) with
  | .shMemStore .opW (.const _) (.const _) => true
  | _ => false

/-- Runtime guard: the global `ShMemLoad` compile lowers to a `Dec` whose body
    is a `Dec`/`Seq`/`Store`. -/
def globalLoadCompileGuard : Bool :=
  match compileProgExactHOL probeContext
      (.shMemLoad .opW .global (ofString "g") (.const (1 : BitVec 8)) : ProgHOL 8) with
  | .dec _ .one _ (.dec _ .one _ (.seq (.shMemLoad .opW .local _ (.var .local _))
      (.store (.op .sub [.topAddr, .const _]) (.var .local _)))) => true
  | _ => false

#guard localLoadCompileGuard
#guard storeCompileGuard
#guard globalLoadCompileGuard

def runChecks : IO Bool := do
  let exactResult := localLoadCompileGuard && storeCompileGuard && globalLoadCompileGuard
  IO.println (if exactResult then
    "PASS pan_globals compile_correct ShMemLoad/ShMemStore exact-carrier parity"
    else "FAIL pan_globals compile_correct ShMemLoad/ShMemStore exact-carrier parity")
  pure exactResult

end Flapjack.Test.PanGlobalsCompileCorrectShMemParity
