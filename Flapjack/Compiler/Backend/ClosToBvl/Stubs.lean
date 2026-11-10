module

public import Flapjack.Compiler.Backend.ClosToBvl.Layout
public import Flapjack.Compiler.Backend.ClosToBvl.Constants
public import Flapjack.Compiler.Backend.BackendCommon.ClosTags
public import Flapjack.Compiler.Backend.Bvl.Boolean
public import Flapjack.Compiler.Backend.BvlJump
public import Flapjack.Misc.Sptree
public import Flapjack.Misc.Sptree.FromList

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Runtime application and initialization stubs for closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private def elem (b : Bvl.Exp) (i : Nat) : Bvl.Exp := .op (.blockOp (.elemAt i)) [b]
/-- Generate generic application code, including over- and partial application. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "generate_generic_app_def"]
def generateGenericApp (maxApp n : Nat) : Bvl.Exp :=
  let over := BvlJump.jump (elem (.var (n + 2)) 1) ((List.range maxApp).map fun numArgs =>
    .let [.call numArgs none
      ((List.range (numArgs + 1)).map (fun arg => .var (arg + 2 + n - numArgs)) ++
        [.var (n + 3), elem (.var (n + 3)) 0])]
      (mkClCall (.var 0) ((List.range (n - numArgs)).map fun i => .var (i + 3))))
  let partialNormal := Bvl.Exp.op (.blockOp (.cons BackendCommon.partialAppTag))
    ((mkEl (.op (.globOp (.global 0)) [])
       (partialAppFnLocationCode maxApp (elem (.var (n + 2)) 1) (mkConst n)) ::
      .var 0 :: .var (n + 2) :: (List.range (n + 1)).map (fun i => .var (i + 1))).reverse)
  let partialExisting := Bvl.Exp.let [.op (.intOp .sub) [mkConst 3, .op (.blockOp .lengthBlock) [.var (n + 2)]]]
    (.op (.blockOp (.consExtend BackendCommon.partialAppTag))
      ((.var (n + 3) :: mkConst 3 :: .var 0 :: .op (.intOp .add) [.var 0, mkConst (n + 4)] ::
        mkEl (.op (.globOp (.global 0)) [])
          (partialAppFnLocationCode maxApp
            (.op (.intOp .add) [.var 0, .op (.intOp .add) [mkConst (n + 1), .var 1]])
            (.op (.intOp .add) [.var 1, mkConst n])) ::
        .var 1 :: elem (.var (n + 3)) 2 :: (List.range (n + 1)).map (fun i => .var (i + 2))).reverse))
  .let [.op (.intOp .sub) [mkConst (n + 1), elem (.var (n + 1)) 1]]
    (.ifThenElse (.op (.intOp .less) [mkConst 0, .var 0]) over
      (Bvl.mkTick n (.ifThenElse (.op (.blockOp (.tagEq BackendCommon.closureTag)) [.var (n + 2)]) partialNormal partialExisting)))

/-- Test for either kind of closure, falling through to the supplied failure. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "check_closure_def"]
def checkClosure (v : Nat) (e : Bvl.Exp) : Bvl.Exp :=
  .ifThenElse (.op (.blockOp (.tagEq BackendCommon.closureTag)) [.var v]) (Bvl.boolExp true)
    (.ifThenElse (.op (.blockOp (.tagEq BackendCommon.partialAppTag)) [.var v]) (Bvl.boolExp true) e)

/-- Enumerate generic and partial-application code at their indexed locations. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "init_code_def"]
def initCode (maxApp : Nat) : Spt (Nat × Bvl.Exp) :=
  let entries := (List.range maxApp).map (fun n => (n + 2, generateGenericApp maxApp n)) ++
    ((List.range maxApp).map fun total =>
      (List.range total).map fun previous =>
        (total - previous + 1, generatePartialAppClosureFn total previous)).flatten
  sptFromList entries

/-- Allocate the partial-application label table and enter the compiled code. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "init_globals_def"]
def initGlobals (maxApp start : Nat) : Bvl.Exp :=
  let labels := ((List.range maxApp).map fun total =>
    (List.range total).map fun previous => mkLabel (partialAppFnLocation maxApp total previous)).flatten
  .let [.op (.globOp .allocGlobal) [.op (.intOp (.const 1)) []]]
    (.let [.op (.globOp (.setGlobal partialAppLabelTableLoc)) [.op (.blockOp (.cons BackendCommon.tupleTag)) labels.reverse]]
      (.call 0 (some start) []))

/-- Force a thunk, selecting direct or generic application from its arity. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "force_thunk_code_def"]
def forceThunkCode : Bvl.Exp :=
  let unit := Bvl.Exp.op (.blockOp (.cons 0)) []
  let update := Bvl.Exp.let [.op (.thunkOp (.updateThunk .evaluated)) [.var 0, .var 1]] (.var 1)
  .ifThenElse (.op (.blockOp (.equalConst (.int 0))) [elem (.var 1) 1])
    (.let [.call 0 none [unit, .var 1, elem (.var 1) 0]] update)
    (.let [.call 0 (some 0) [unit, .var 1]] update)

end Flapjack.Compiler.Backend.ClosToBvl
