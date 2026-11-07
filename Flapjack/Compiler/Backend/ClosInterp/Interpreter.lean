import Flapjack.Compiler.Backend.ClosLang.HasInstall

/-! The closure-language interpreter attached to programs using `Install`. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.Basis.Pure.MlString ClosLang

private def v (n : Nat) : Exp := .var .none n
private def getEl (n : Nat) (x : Exp) : Exp := .op .none (.blockOp (.elemAt n)) [x]
private def cons (n : Nat) (xs : List Exp) : Exp := .op .none (.blockOp (.cons n)) xs
private def app (f x : Exp) : Exp := .app .none none f [x]
private def callInterp (env x : Exp) : Exp :=
  app (app (app (.op .none (.globOp (.global 0)) []) env) (cons 0 [])) x
private def callInterpList (env x : Exp) : Exp :=
  app (app (app (.op .none (.globOp (.global 0)) []) env) (cons 1 [])) x
private def isCase (tag len : Nat) (yes no : Exp) : Exp :=
  .ifThenElse .none (.op .none (.blockOp (.tagLenEq tag len)) [v 0]) yes no

/-- Expose the private variable constructor to proofs about the interpreter. -/
theorem interpreterVar_eq (n : Nat) : v n = .var .none n := rfl

/-- Expose the private projection constructor to proofs about the interpreter. -/
theorem interpreterGetEl_eq (n : Nat) (x : Exp) : getEl n x = .op .none (.blockOp (.elemAt n)) [x] := rfl

/-- Expose the private constructor application to proofs about the interpreter. -/
theorem interpreterCons_eq (n : Nat) (xs : List Exp) : cons n xs = .op .none (.blockOp (.cons n)) xs := rfl

/-- Expose the private unary application to proofs about the interpreter. -/
theorem interpreterApp_eq (f x : Exp) : app f x = .app .none none f [x] := rfl

/-- Expose the interpreter's recursive expression call to proofs. -/
theorem interpreterCall_eq (env x : Exp) :
    callInterp env x = .app .none none
      (.app .none none (.app .none none (.op .none (.globOp (.global 0)) []) [env])
        [.op .none (.blockOp (.cons 0)) []]) [x] := rfl

/-- Expose the interpreter's recursive expression-list call to proofs. -/
theorem interpreterCallList_eq (env x : Exp) :
    callInterpList env x = .app .none none
      (.app .none none (.app .none none (.op .none (.globOp (.global 0)) []) [env])
        [.op .none (.blockOp (.cons 1)) []]) [x] := rfl

/-- Expose the private constructor test to proofs about the interpreter. -/
theorem interpreterIsCase_eq (tag len : Nat) (yes no : Exp) :
    isCase tag len yes no = .ifThenElse .none (.op .none (.blockOp (.tagLenEq tag len)) [.var .none 0]) yes no := rfl

/-- Interpreter helper selecting a de Bruijn environment element. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "clos_interp_el_def"]
def closInterpEl : Exp :=
  .ifThenElse .none (.op .none (.blockOp (.equalConst (.int 0))) [v 1])
    (getEl 0 (v 0))
    (app (app (v 2) (.op .none (.intOp .sub) [.op .none (.intOp (.const 1)) [], v 1]))
      (getEl 1 (v 0)))

/-- Interpreter helper reversing a list. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "clos_interp_rev_def"]
def closInterpRev : Exp :=
  .ifThenElse .none (.op .none (.blockOp (.lenEq 0)) [v 1]) (v 0)
    (app (app (v 2) (getEl 1 (v 1))) (cons 0 [v 0, getEl 0 (v 1)]))

/-- The original interpreter's list and expression dispatch body. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "clos_interpreter_body_def"]
def closInterpreterBody : Exp :=
  .ifThenElse .none (v 1)
    (.ifThenElse .none (.op .none (.blockOp (.lenEq 0)) [v 0]) (v 0)
      (.let .none [callInterp (v 2) (getEl 0 (v 0)), callInterpList (v 2) (getEl 1 (v 0))]
        (cons 0 [v 1, v 0])))
    (isCase 0 2 (app (callInterp (v 2) (getEl 0 (v 0))) (callInterp (v 2) (getEl 1 (v 0))))
    (isCase 1 1 (getEl 0 (v 0))
    (isCase 2 1 (.op .none (.globOp (.global 0)) [getEl 0 (v 0)])
    (isCase 0 1 (.letrec [] none none [(1, .fn (ofString "") none none 1 closInterpEl)]
      (app (app (v 0) (getEl 0 (v 1))) (v 3)))
    (isCase 1 2 (.let .none [callInterpList (v 2) (getEl 0 (v 0))]
      (callInterp (.op .none (.blockOp .listAppend) [v 3, v 0]) (getEl 1 (v 1))))
    (isCase 2 2 (.handle .none (callInterp (v 2) (getEl 0 (v 0)))
      (callInterp (cons 0 [v 3, v 0]) (getEl 1 (v 1))))
    (isCase 0 3 (.ifThenElse .none (callInterp (v 2) (getEl 0 (v 0)))
      (callInterp (v 2) (getEl 1 (v 0))) (callInterp (v 2) (getEl 2 (v 0))))
    (isCase 3 1 (.raise .none (callInterp (v 2) (getEl 0 (v 0))))
    (isCase 4 1 (callInterp (v 2) (getEl 0 (v 0)))
    (.let .none [callInterpList (v 2) (getEl 0 (v 0))]
      (.letrec [] none none [(1, .fn (ofString "") none none 1 closInterpRev)]
        (.let .none [app (app (v 0) (v 1)) (cons 0 [])]
          (.let .none [v 3]
            (isCase 5 1 (.op .none (.blockOp (.fromList 0)) [v 1])
            (isCase 6 1 (.op .none (.blockOp (.fromList 1)) [v 1])
            (isCase 7 1 (.op .none (.blockOp (.fromList 2)) [v 1])
              (cons 0 [])))))))))))))))))

/-- The two argument interpreter closure. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "clos_interpreter_def"]
def closInterpreter : Exp :=
  .fn (ofString "env") none none 1 (.fn (ofString "exp") none none 1 closInterpreterBody)

/-- Allocate global slot zero and initialize it with the interpreter or unit. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "compile_init_def"]
def compileInit (b : Bool) : Exp :=
  .let .none [.op .none (.globOp .allocGlobal) [.op .none (.intOp (.const 1)) []],
    if b then .fn (ofString "clos_interpreter") none none 1 closInterpreter else cons 0 []]
    (.op .none (.globOp (.setGlobal 0)) [v 1])

/-- Prepend the required initializer, installing the interpreter only if used. -/
@[hol "cakeml/compiler/backend/clos_interpScript.sml" "attach_interpreter_def"]
def attachInterpreter (xs : List Exp) : List Exp :=
  compileInit (hasInstallList xs) :: xs

end Flapjack.Compiler.Backend.ClosInterp
