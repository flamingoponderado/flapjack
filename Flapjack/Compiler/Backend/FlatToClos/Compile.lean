import Flapjack.Compiler.Backend.FlatToClos.Op
import Flapjack.Compiler.Backend.ClosInterp.Interpreter
import Flapjack.Compiler.Backend.ClosInterp.Optimise

/-! Flat expressions to closure expressions, before interpreter attachment. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString

/-- First index of a name in a de Bruijn context, or the context length if absent.
This is the instance of HOL `findi` used by this pass. -/
private def nameIndex (v : Option MlString) : List (Option MlString) → Nat
  | [] => 0
  | x :: xs => if v = x then 0 else nameIndex v xs + 1

mutual
/-- Compile one expression. This is an implementation helper for the
list-valued HOL `compile`; the source's singleton results always have length
one. The two nested conversion patterns implement `dest_nop`. -/
def compileExp (m : List (Option MlString)) : FlatLang.Exp → ClosLang.Exp
  | .raise t e => .raise t (compileExp m e)
  | .lit t l => compileLit t l
  | .varLocal t v => .var t (nameIndex (some v) m)
  | .con t n es =>
      let tag := match n with | some (tag, _) => tag | none => 0
      smartCons t tag (compileExps m es).reverse
  | .app _ (.src (.fromTo .intT (.wordT .w8)))
      [.app _ (.src (.fromTo .charT .intT)) [x]] => compileExp m x
  | .app _ (.src (.fromTo .intT .charT))
      [.app _ (.src (.fromTo (.wordT .w8) .intT)) [x]] => compileExp m x
  | .app t op es => compileOp t op (compileExps m es).reverse
  | .fn t v e => .fn t none none 1 (compileExp (some v :: m) e)
  | .if_ t a b c => .ifThenElse t (compileExp m a) (compileExp m b) (compileExp m c)
  | .let_ t vo e1 e2 => .let t [compileExp m e1] (compileExp (vo :: m) e2)
  | .mat t _ _ => .op t (.intOp (.const 0)) []
  | .handle t e [(.pvar v, h)] =>
      .handle t (compileExp m e) (compileExp (some v :: m) h)
  | .handle _ e _ => compileExp m e
  | .letrec t funs e =>
      let newM := funs.map (fun (f, _, _) => some f) ++ m
      .letrec (funs.map fun (f, _, _) => joinStrings t f) none none
        (compileFuns newM funs) (compileExp newM e)

/-- Compile expressions in source order. -/
def compileExps (m : List (Option MlString)) : List FlatLang.Exp → List ClosLang.Exp
  | [] => []
  | e :: es => compileExp m e :: compileExps m es

/-- Compile recursive function bodies with the recursive environment in scope. -/
def compileFuns (m : List (Option MlString)) :
    List (MlString × MlString × FlatLang.Exp) → List (Nat × ClosLang.Exp)
  | [] => []
  | (_, v, e) :: fs => (1, compileExp (some v :: m) e) :: compileFuns m fs
end

/-- List-valued flat-to-closure translation; interpreter attachment is a
separate source definition and is not included here. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "compile_def"]
def compile (m : List (Option MlString)) (es : List FlatLang.Exp) : List ClosLang.Exp :=
  compileExps m es

/-- Compile each top-level flat declaration in an empty environment. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "compile_decs_def"]
def compileDecs (es : List FlatLang.Exp) : List ClosLang.Exp := compile [] es

/-- Compile flat declarations and attach the original interpreter initializer. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "compile_prog_def"]
def compileProg (es : List FlatLang.Exp) : List ClosLang.Exp :=
  ClosInterp.attachInterpreter (compileDecs es)

/-- Incremental compilation appends the unit expression and applies the
original interpreter-insertion optimization. -/
@[hol "cakeml/compiler/backend/flat_to_closScript.sml" "inc_compile_decs_def"]
def incCompileDecs {α : Type} (es : List FlatLang.Exp) : List ClosLang.Exp × List α :=
  let xs := compileDecs es ++ compileDecs [.con .none none []]
  (ClosInterp.insertInterp xs, [])

end Flapjack.Compiler.Backend.FlatToClos
