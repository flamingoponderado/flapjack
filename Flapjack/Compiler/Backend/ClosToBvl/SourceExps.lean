module

public import Flapjack.Compiler.Backend.ClosToBvl.SourceCompile
public import Flapjack.Misc.ListEl

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! The original list-valued closure-to-BVL expression conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
noncomputable section

private abbrev Aux := List (Nat × Nat × Bvl.Exp)
instance sourceExpsInst1 : Nonempty Bvl.Exp := ⟨.var 0⟩

/-- Lean structural termination measure for option-valued fields. -/
theorem option_size_pos {α : Type} [SizeOf α] (x : Option α) : 0 < sizeOf x := by
  cases x <;> simp_wf <;> omega

/-- Lean structural termination measure for trace fields. -/
theorem trace_size_pos (x : BackendCommon.Tra) : 0 < sizeOf x := by
  cases x <;> simp_wf <;> omega

mutual
/-- The original list-valued conversion, including its singleton clauses. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_exps_def"]
def compileExpsHOL (maxApp : Nat) : List ClosLang.Exp → Aux → List Bvl.Exp × Aux
  | [], aux => ([], aux)
  | x :: xs, aux =>
      let (first, aux) := compileExpsSingletonHOL maxApp x aux
      let (rest, aux) := compileExpsHOL maxApp xs aux
      (first ++ rest, aux)
termination_by es _ => 2 * sizeOf es
decreasing_by all_goals simp_wf <;> omega

/-- Flapjack helper containing the source's singleton cases. -/
def compileExpsSingletonHOL (maxApp : Nat) : ClosLang.Exp → Aux → List Bvl.Exp × Aux
  | .var _ v, aux => ([.var v], aux)
  | .ifThenElse _ x y z, aux =>
      let (x, aux) := compileExpsHOL maxApp [x] aux
      let (y, aux) := compileExpsHOL maxApp [y] aux
      let (z, aux) := compileExpsHOL maxApp [z] aux
      ([.ifThenElse (Flapjack.holHd x) (Flapjack.holHd y) (Flapjack.holHd z)], aux)
  | .let _ xs x, aux =>
      let (xs, aux) := compileExpsHOL maxApp xs aux
      let (x, aux) := compileExpsHOL maxApp [x] aux
      ([.let xs (Flapjack.holHd x)], aux)
  | .raise _ x, aux =>
      let (x, aux) := compileExpsHOL maxApp [x] aux
      ([.raise (Flapjack.holHd x)], aux)
  | .tick _ x, aux =>
      let (x, aux) := compileExpsHOL maxApp [x] aux
      ([.tick (Flapjack.holHd x)], aux)
  | .handle _ x y, aux =>
      let (x, aux) := compileExpsHOL maxApp [x] aux
      let (y, aux) := compileExpsHOL maxApp [y] aux
      ([.handle (Flapjack.holHd x) (Flapjack.holHd y)], aux)
  | .op _ op xs, aux =>
      let (xs, aux) := compileExpsHOL maxApp xs aux
      let result := match op with
        | .install => Bvl.Exp.call 0 none [.op .install xs]
        | .thunkOp .forceThunk => Bvl.Exp.let xs (.force (numStubs maxApp - 2) 0)
        | _ => Bvl.Exp.op (compileOp op) xs
      ([result], aux)
  | .app _ loc x xs, aux =>
      let (x, aux) := compileExpsHOL maxApp [x] aux
      let (xs, aux) := compileExpsHOL maxApp xs aux
      let result := match loc with
        | none => Bvl.Exp.let (xs ++ x)
            (mkClCall (.var xs.length) ((List.range xs.length).map Bvl.Exp.var))
        | some loc => Bvl.Exp.call (xs.length - 1) (some (loc + numStubs maxApp)) (xs ++ x)
      ([result], aux)
  | .fn _ loc vs args x, aux =>
      let loc := loc.getD 0
      let vs := vs.getD []
      let (x, aux) := compileExpsHOL maxApp [x] aux
      let body := Bvl.Exp.let ((List.range args).map Bvl.Exp.var ++ freeLet (.var args) vs.length) (Flapjack.holHd x)
      let closure := Bvl.Exp.op (.blockOp (.cons 30))
        ((mkLabel (loc + numStubs maxApp) :: mkConst (args - 1) :: vs.map Bvl.Exp.var).reverse)
      ([closure], (loc + numStubs maxApp, args + 1, body) :: aux)
  | .letrec _ loc vs fns x, aux =>
      let loc := loc.getD 0 + numStubs maxApp
      let vs := vs.getD []
      match fns with
      | [] => compileExpsHOL maxApp [x] aux
      | [(args, f)] =>
          let (f, aux) := compileExpsHOL maxApp [f] aux
          let body := Bvl.Exp.let ((List.range args).map Bvl.Exp.var ++ [.var args] ++
            freeLet (.var args) vs.length) (Flapjack.holHd f)
          let (x, aux) := compileExpsHOL maxApp [x] ((loc, args + 1, body) :: aux)
          let closure := Bvl.Exp.op (.blockOp (.cons 30))
            ((mkLabel loc :: mkConst (args - 1) :: vs.map Bvl.Exp.var).reverse)
          ([.let [closure] (Flapjack.holHd x)], aux)
      | f :: g :: fs =>
          let fns := f :: g :: fs
          let (compiled, aux) := compileExpsFunsHOL maxApp fns aux
          let cases := List.zipWith (codeForReccCase (fns.length + vs.length)) (fns.map Prod.fst) compiled
          let (_, aux) := buildAux loc cases aux
          let (x, aux) := compileExpsHOL maxApp [x] aux
          ([buildReccLetsHOL (fns.map Prod.fst) vs loc fns.length (Flapjack.holHd x)], aux)
  | .call _ ticks dest xs, aux =>
      let (xs, aux) := compileExpsHOL maxApp xs aux
      ([.call ticks (some (dest + numStubs maxApp)) xs], aux)
termination_by e _ => 2 * sizeOf e + 1
decreasing_by
  all_goals simp_wf
  all_goals try have h : 0 < sizeOf (‹BackendCommon.Tra›) := trace_size_pos _
  all_goals try have h : 0 < sizeOf (‹Option Nat›) := option_size_pos _
  all_goals omega

/-- Flapjack helper for compiling the mapped recursive-function bodies. -/
def compileExpsFunsHOL (maxApp : Nat) : List (Nat × ClosLang.Exp) → Aux → List Bvl.Exp × Aux
  | [], aux => ([], aux)
  | (_, x) :: xs, aux =>
      let (x, aux) := compileExpsHOL maxApp [x] aux
      let (xs, aux) := compileExpsFunsHOL maxApp xs aux
      (x ++ xs, aux)
termination_by xs _ => 2 * sizeOf xs + 1
decreasing_by all_goals simp_wf <;> omega
end

/-- The singleton clause of the original list-valued conversion, with the
empty tail removed. Flapjack helper: HOL reaches it through
`compile_exp_sing_eq`. -/
private theorem compileExpsHOL_sing (maxApp : Nat) (x : ClosLang.Exp) (aux : Aux) :
    compileExpsHOL maxApp [x] aux = compileExpsSingletonHOL maxApp x aux := by
  simp [compileExpsHOL, List.append_nil]

/-- The two-element recursion step of the original list-valued conversion. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_exps_CONS"]
theorem compileExpsHOL_cons (maxApp : Nat) (xs : List ClosLang.Exp) (x : ClosLang.Exp)
    (aux : Aux) :
    compileExpsHOL maxApp (x :: xs) aux =
      let (c1, aux1) := compileExpsHOL maxApp [x] aux
      let (c2, aux2) := compileExpsHOL maxApp xs aux1
      (c1 ++ c2, aux2) := by
  cases xs with
  | nil => simp [compileExpsHOL_sing, compileExpsHOL]
  | cons y ys => simp [compileExpsHOL_sing, compileExpsHOL]

/-- The appended-expression equation of the original list-valued conversion. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_exps_SNOC"]
theorem compileExpsHOL_snoc (xs : List ClosLang.Exp) (x : ClosLang.Exp) (aux : Aux)
    (maxApp : Nat) :
    compileExpsHOL maxApp (xs ++ [x]) aux =
      let (c1, aux1) := compileExpsHOL maxApp xs aux
      let (c2, aux2) := compileExpsHOL maxApp [x] aux1
      (c1 ++ c2, aux2) := by
  induction xs generalizing aux with
  | nil => simp [compileExpsHOL]
  | cons y ys ih =>
    simp only [List.cons_append]
    simp only [compileExpsHOL]
    simp only [ih, compileExpsHOL_sing, List.append_nil, List.append_assoc]

/-- The original labeled program conversion, using its list-valued
expression compiler and retaining the source's label and auxiliary order. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_prog_def"]
def compileProgExpsHOL (maxApp : Nat) (prog : List (Nat × Nat × ClosLang.Exp)) :
    List (Nat × Nat × Bvl.Exp) :=
  let (exps, aux) := compileExpsHOL maxApp (prog.map (fun (_, _, exp) => exp)) []
  (prog.zip exps).map (fun ((loc, args, _), exp) => (loc + numStubs maxApp, args, exp)) ++ aux

end
end Flapjack.Compiler.Backend.ClosToBvl
