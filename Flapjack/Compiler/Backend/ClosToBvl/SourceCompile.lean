import Flapjack.Compiler.Backend.ClosToBvl.Constants
import Flapjack.Compiler.Backend.ClosToBvl.Layout

/-! Total closure-to-BVL expression conversion in the original source shape. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
noncomputable section

private abbrev Aux := List (Nat × Nat × Bvl.Exp)

mutual
/-- Original total singleton conversion. The recursive-group helper factors
the source's mapped traversal and preserves arities. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_exp_sing_def"]
def compileExpHOL (maxApp : Nat) : ClosLang.Exp → Aux → Bvl.Exp × Aux
  | .var _ v, aux => (.var v, aux)
  | .ifThenElse _ x y z, aux =>
      let (x, aux) := compileExpHOL maxApp x aux
      let (y, aux) := compileExpHOL maxApp y aux
      let (z, aux) := compileExpHOL maxApp z aux
      (.ifThenElse x y z, aux)
  | .let _ xs x, aux =>
      let (xs, aux) := compileExpListHOL maxApp xs aux
      let (x, aux) := compileExpHOL maxApp x aux
      (.let xs x, aux)
  | .raise _ x, aux =>
      let (x, aux) := compileExpHOL maxApp x aux
      (.raise x, aux)
  | .tick _ x, aux =>
      let (x, aux) := compileExpHOL maxApp x aux
      (.tick x, aux)
  | .handle _ x y, aux =>
      let (x, aux) := compileExpHOL maxApp x aux
      let (y, aux) := compileExpHOL maxApp y aux
      (.handle x y, aux)
  | .op _ op xs, aux =>
      let (xs, aux) := compileExpListHOL maxApp xs aux
      let result := match op with
        | .install => Bvl.Exp.call 0 none [.op .install xs]
        | .thunkOp .forceThunk => Bvl.Exp.let xs (.force (numStubs maxApp - 2) 0)
        | _ => Bvl.Exp.op (compileOp op) xs
      (result, aux)
  | .app _ loc x xs, aux =>
      let (x, aux) := compileExpHOL maxApp x aux
      let (xs, aux) := compileExpListHOL maxApp xs aux
      let result := match loc with
        | none => Bvl.Exp.let (xs ++ [x])
            (mkClCall (.var xs.length) ((List.range xs.length).map Bvl.Exp.var))
        | some loc => Bvl.Exp.call (xs.length - 1) (some (loc + numStubs maxApp)) (xs ++ [x])
      (result, aux)
  | .fn _ loc vs args x, aux =>
      let loc := loc.getD 0
      let vs := vs.getD []
      let (x, aux) := compileExpHOL maxApp x aux
      let body := Bvl.Exp.let ((List.range args).map Bvl.Exp.var ++ freeLet (.var args) vs.length) x
      let closure := Bvl.Exp.op (.blockOp (.cons 30))
        ((mkLabel (loc + numStubs maxApp) :: mkConst (args - 1) :: vs.map Bvl.Exp.var).reverse)
      (closure, (loc + numStubs maxApp, args + 1, body) :: aux)
  | .letrec _ loc vs fns x, aux =>
      let loc := loc.getD 0 + numStubs maxApp
      let vs := vs.getD []
      match fns with
      | [] => compileExpHOL maxApp x aux
      | [(args, f)] =>
          let (f, aux) := compileExpHOL maxApp f aux
          let body := Bvl.Exp.let ((List.range args).map Bvl.Exp.var ++ [.var args] ++
            freeLet (.var args) vs.length) f
          let (x, aux) := compileExpHOL maxApp x ((loc, args + 1, body) :: aux)
          let closure := Bvl.Exp.op (.blockOp (.cons 30))
            ((mkLabel loc :: mkConst (args - 1) :: vs.map Bvl.Exp.var).reverse)
          (.let [closure] x, aux)
      | f :: g :: fs =>
          let fns := f :: g :: fs
          let (compiled, aux) := compileExpFunsHOL maxApp fns aux
          let cases := compiled.map (fun (args, body) => codeForReccCase (fns.length + vs.length) args body)
          let (_, aux) := buildAux loc cases aux
          let (x, aux) := compileExpHOL maxApp x aux
          (buildReccLetsHOL (fns.map Prod.fst) vs loc fns.length x, aux)
  | .call _ ticks dest xs, aux =>
      let (xs, aux) := compileExpListHOL maxApp xs aux
      (.call ticks (some (dest + numStubs maxApp)) xs, aux)
termination_by e _ => sizeOf e
decreasing_by all_goals simp_wf <;> omega

/-- Original total expression-list conversion. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_exp_sing_def"]
def compileExpListHOL (maxApp : Nat) : List ClosLang.Exp → Aux → List Bvl.Exp × Aux
  | [], aux => ([], aux)
  | x :: xs, aux =>
      let (x, aux) := compileExpHOL maxApp x aux
      let (xs, aux) := compileExpListHOL maxApp xs aux
      (x :: xs, aux)
termination_by xs _ => sizeOf xs
decreasing_by all_goals simp_wf <;> omega

/-- Flapjack helper for mapping arities over compiled recursive bodies. -/
def compileExpFunsHOL (maxApp : Nat) : List (Nat × ClosLang.Exp) → Aux → List (Nat × Bvl.Exp) × Aux
  | [], aux => ([], aux)
  | (arity, x) :: xs, aux =>
      let (x, aux) := compileExpHOL maxApp x aux
      let (xs, aux) := compileExpFunsHOL maxApp xs aux
      ((arity, x) :: xs, aux)
termination_by xs _ => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

/-- Flapjack's singleton/list reformulation of labeled program compilation.
The original uses `compile_exps`; `Proofs/ExpsEquivalence.lean` proves the
two formulations equal, so this helper has no separate HOL reference. -/
def compileProgHOL (maxApp : Nat) (prog : List (Nat × Nat × ClosLang.Exp)) :
    List (Nat × Nat × Bvl.Exp) :=
  let (exps, aux) := compileExpListHOL maxApp (prog.map (fun (_, _, exp) => exp)) []
  (prog.zip exps).map (fun ((loc, args, _), exp) => (loc + numStubs maxApp, args, exp)) ++ aux

end
end Flapjack.Compiler.Backend.ClosToBvl
