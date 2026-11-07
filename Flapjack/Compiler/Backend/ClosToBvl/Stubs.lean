import Flapjack.Compiler.Backend.ClosToBvl.Layout
import Flapjack.Compiler.Backend.BvlJump
import Flapjack.Misc.Sptree

/-! Runtime application and initialization stubs for closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private def elem (b : Bvl.Exp) (i : Nat) : Bvl.Exp := .op (.blockOp (.elemAt i)) [b]
private def tickN : Nat → Bvl.Exp → Bvl.Exp
  | 0, e => e
  | n + 1, e => .tick (tickN n e)

/-- Expose the repeated tick sequence for proofs of the application stubs. -/
def genericAppTicks (n : Nat) (e : Bvl.Exp) : Bvl.Exp := tickN n e

/-- Generate generic application code, including over- and partial application. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "generate_generic_app_def"]
def generateGenericApp (maxApp n : Nat) : Bvl.Exp :=
  let over := BvlJump.jump (elem (.var (n + 2)) 1) ((List.range maxApp).map fun numArgs =>
    .let [.call numArgs none
      ((List.range (numArgs + 1)).map (fun arg => .var (arg + 2 + n - numArgs)) ++
        [.var (n + 3), elem (.var (n + 3)) 0])]
      (mkClCall (.var 0) ((List.range (n - numArgs)).map fun i => .var (i + 3))))
  let partialNormal := Bvl.Exp.op (.blockOp (.cons 31))
    ((mkEl (.op (.globOp (.global 0)) [])
       (partialAppFnLocationCode maxApp (elem (.var (n + 2)) 1) (mkConst n)) ::
      .var 0 :: .var (n + 2) :: (List.range (n + 1)).map (fun i => .var (i + 1))).reverse)
  let partialExisting := Bvl.Exp.let [.op (.intOp .sub) [mkConst 3, .op (.blockOp .lengthBlock) [.var (n + 2)]]]
    (.op (.blockOp (.consExtend 31))
      ((.var (n + 3) :: mkConst 3 :: .var 0 :: .op (.intOp .add) [.var 0, mkConst (n + 4)] ::
        mkEl (.op (.globOp (.global 0)) [])
          (partialAppFnLocationCode maxApp
            (.op (.intOp .add) [.var 0, .op (.intOp .add) [mkConst (n + 1), .var 1]])
            (.op (.intOp .add) [.var 1, mkConst n])) ::
        .var 1 :: elem (.var (n + 3)) 2 :: (List.range (n + 1)).map (fun i => .var (i + 2))).reverse))
  .let [.op (.intOp .sub) [mkConst (n + 1), elem (.var (n + 1)) 1]]
    (.ifThenElse (.op (.intOp .less) [mkConst 0, .var 0]) over
      (tickN n (.ifThenElse (.op (.blockOp (.tagEq 30)) [.var (n + 2)]) partialNormal partialExisting)))

/-- Test for either kind of closure, falling through to the supplied failure. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "check_closure_def"]
def checkClosure (v : Nat) (e : Bvl.Exp) : Bvl.Exp :=
  .ifThenElse (.op (.blockOp (.tagEq 30)) [.var v]) (.op (.blockOp (.cons 1)) [])
    (.ifThenElse (.op (.blockOp (.tagEq 31)) [.var v]) (.op (.blockOp (.cons 1)) []) e)

/-- Enumerate generic and partial-application code at their indexed locations. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "init_code_def"]
def initCode (maxApp : Nat) : Spt (Nat × Bvl.Exp) :=
  let entries := (List.range maxApp).map (fun n => (n + 2, generateGenericApp maxApp n)) ++
    ((List.range maxApp).map fun total =>
      (List.range total).map fun previous =>
        (total - previous + 1, generatePartialAppClosureFn total previous)).flatten
  (entries.foldl (fun (i, tree) e => (i + 1, sptInsert i e tree)) (0, .ln)).2

/-- Allocate the partial-application label table and enter the compiled code. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "init_globals_def"]
def initGlobals (maxApp start : Nat) : Bvl.Exp :=
  let labels := ((List.range maxApp).map fun total =>
    (List.range total).map fun previous => mkLabel (partialAppFnLocation maxApp total previous)).flatten
  .let [.op (.globOp .allocGlobal) [.op (.intOp (.const 1)) []]]
    (.let [.op (.globOp (.setGlobal 0)) [.op (.blockOp (.cons 0)) labels.reverse]]
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
