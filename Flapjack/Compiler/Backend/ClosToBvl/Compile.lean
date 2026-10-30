import Flapjack.Compiler.Backend.ClosToBvl.Constants
import Flapjack.Compiler.Backend.ClosToBvl.Layout

/-! Checked closure-to-BVL expression conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private abbrev Aux := List (Nat × Nat × Bvl.Exp)

mutual
/-- Flapjack's checked expression converter follows the source singleton
clauses. Its recursive-layout check always succeeds for the generated input,
as proved in `Proofs/Total.lean`; HOL correspondence remains under review. -/
def compileExp? (maxApp : Nat) : ClosLang.Exp → Aux → Option (Bvl.Exp × Aux)
  | .var _ v, aux => some (.var v, aux)
  | .ifThenElse _ x y z, aux => do
      let (x, aux) ← compileExp? maxApp x aux
      let (y, aux) ← compileExp? maxApp y aux
      let (z, aux) ← compileExp? maxApp z aux
      pure (.ifThenElse x y z, aux)
  | .let _ xs x, aux => do
      let (xs, aux) ← compileExpList? maxApp xs aux
      let (x, aux) ← compileExp? maxApp x aux
      pure (.let xs x, aux)
  | .raise _ x, aux => do
      let (x, aux) ← compileExp? maxApp x aux
      pure (.raise x, aux)
  | .tick _ x, aux => do
      let (x, aux) ← compileExp? maxApp x aux
      pure (.tick x, aux)
  | .handle _ x y, aux => do
      let (x, aux) ← compileExp? maxApp x aux
      let (y, aux) ← compileExp? maxApp y aux
      pure (.handle x y, aux)
  | .op _ op xs, aux => do
      let (xs, aux) ← compileExpList? maxApp xs aux
      let result := match op with
        | .install => Bvl.Exp.call 0 none [.op .install xs]
        | .thunkOp .forceThunk => Bvl.Exp.let xs (.force (numStubs maxApp - 2) 0)
        | _ => Bvl.Exp.op (compileOp op) xs
      pure (result, aux)
  | .app _ loc x xs, aux => do
      let (x, aux) ← compileExp? maxApp x aux
      let (xs, aux) ← compileExpList? maxApp xs aux
      let result := match loc with
        | none => Bvl.Exp.let (xs ++ [x])
            (mkClCall (.var xs.length) ((List.range xs.length).map Bvl.Exp.var))
        | some loc => Bvl.Exp.call (xs.length - 1) (some (loc + numStubs maxApp)) (xs ++ [x])
      pure (result, aux)
  | .fn _ loc vs args x, aux => do
      let loc := loc.getD 0
      let vs := vs.getD []
      let (x, aux) ← compileExp? maxApp x aux
      let body := Bvl.Exp.let ((List.range args).map Bvl.Exp.var ++ freeLet (.var args) vs.length) x
      let closure := Bvl.Exp.op (.blockOp (.cons 30))
        ((mkLabel (loc + numStubs maxApp) :: mkConst (args - 1) :: vs.map Bvl.Exp.var).reverse)
      pure (closure, (loc + numStubs maxApp, args + 1, body) :: aux)
  | .letrec _ loc vs fns x, aux => do
      let loc := loc.getD 0 + numStubs maxApp
      let vs := vs.getD []
      match fns with
      | [] => compileExp? maxApp x aux
      | [(args, f)] =>
          let (f, aux) ← compileExp? maxApp f aux
          let body := Bvl.Exp.let ((List.range args).map Bvl.Exp.var ++ [.var args] ++
            freeLet (.var args) vs.length) f
          let (x, aux) ← compileExp? maxApp x ((loc, args + 1, body) :: aux)
          let closure := Bvl.Exp.op (.blockOp (.cons 30))
            ((mkLabel loc :: mkConst (args - 1) :: vs.map Bvl.Exp.var).reverse)
          pure (.let [closure] x, aux)
      | f :: g :: fs =>
          let fns := f :: g :: fs
          let (compiled, aux) ← compileExpFuns? maxApp fns aux
          let cases := compiled.map (fun (args, body) => codeForReccCase (fns.length + vs.length) args body)
          let (_, aux) := buildAux loc cases aux
          let (x, aux) ← compileExp? maxApp x aux
          let x ← buildReccLets? (fns.map Prod.fst) vs loc fns.length x
          pure (x, aux)
  | .call _ ticks dest xs, aux => do
      let (xs, aux) ← compileExpList? maxApp xs aux
      pure (.call ticks (some (dest + numStubs maxApp)) xs, aux)
termination_by e _ => sizeOf e
decreasing_by all_goals simp_wf <;> omega

/-- Checked list traversal, preserving both evaluation and auxiliary-table order. -/
def compileExpList? (maxApp : Nat) : List ClosLang.Exp → Aux → Option (List Bvl.Exp × Aux)
  | [], aux => some ([], aux)
  | x :: xs, aux => do
      let (x, aux) ← compileExp? maxApp x aux
      let (xs, aux) ← compileExpList? maxApp xs aux
      pure (x :: xs, aux)
termination_by xs _ => sizeOf xs
decreasing_by all_goals simp_wf <;> omega

/-- Traverse recursive bodies without discarding their arities. -/
def compileExpFuns? (maxApp : Nat) : List (Nat × ClosLang.Exp) → Aux → Option (List (Nat × Bvl.Exp) × Aux)
  | [], aux => some ([], aux)
  | (arity, x) :: xs, aux => do
      let (x, aux) ← compileExp? maxApp x aux
      let (xs, aux) ← compileExpFuns? maxApp xs aux
      pure ((arity, x) :: xs, aux)
termination_by xs _ => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

/-- Compile each labeled expression and append its generated auxiliary code.
The checked wrapper succeeds for every program by `compileProg_succeeds`. -/
def compileProg? (maxApp : Nat) (prog : List (Nat × Nat × ClosLang.Exp)) :
    Option (List (Nat × Nat × Bvl.Exp)) := do
  let (exps, aux) ← compileExpList? maxApp (prog.map (fun (_, _, exp) => exp)) []
  pure ((prog.zip exps).map (fun ((loc, args, _), exp) =>
    (loc + numStubs maxApp, args, exp)) ++ aux)

end Flapjack.Compiler.Backend.ClosToBvl
