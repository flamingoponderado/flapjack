import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
import Flapjack.PanToCrepMaxList

/-! Infrastructure for the source's reverse/traverse/reverse clauses. -/
namespace Flapjack.Compiler.Backend.FlatPattern

/-- Expression-list compilation composes over append, combining metadata by
maximum and disjunction. This supports the order equivalence below; it is
Flapjack proof infrastructure rather than a separate HOL declaration. -/
theorem compileExps_append (cfg : Config) (xs ys : List FlatLang.Exp) :
    compileExps cfg (xs ++ ys) =
      let (i, a, xs') := compileExps cfg xs
      let (j, b, ys') := compileExps cfg ys
      (max i j, a || b, xs' ++ ys') := by
  induction xs with
  | nil =>
      cases h : compileExps cfg ys with
      | mk j rest => cases rest with | mk b ys' => simp [compileExps, h]
  | cons x xs ih =>
      cases hx : compileExp cfg x with
      | mk i rest =>
        cases rest with
        | mk a x' =>
          cases ht : compileExps cfg xs with
          | mk j rest =>
            cases rest with
            | mk b xs' =>
              cases hy : compileExps cfg ys with
              | mk k rest =>
                cases rest with
                | mk c ys' =>
                  simp [compileExps, hx, ht, hy] at ih ⊢
                  rw [ih]
                  simp [Bool.or_assoc]

/-- Compiling a reversed expression list reverses only its output list; the
maximum and global-write metadata are unchanged. HOL's `Con` and `App`
clauses use reverse/traverse/reverse, whereas the total Lean traversal uses
the equivalent direct order. This is Flapjack proof infrastructure. -/
theorem compileExps_reverse (cfg : Config) (xs : List FlatLang.Exp) :
    compileExps cfg xs.reverse =
      let (i, sg, ys) := compileExps cfg xs
      (i, sg, ys.reverse) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hx : compileExp cfg x with
      | mk i rest =>
        cases rest with
        | mk a x' =>
          cases ht : compileExps cfg xs with
          | mk j rest =>
            cases rest with
            | mk b xs' =>
              simp only [List.reverse_cons, compileExps_append, ih, ht, hx, compileExps]
              simp [Nat.max_comm, Bool.or_comm]

/-- Constructor compilation satisfies the source's reverse/traverse/reverse equation. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_exp_def"]
theorem compileExp_con_source (cfg : Config) (t : BackendCommon.Tra)
    (tag : Option (FlatLang.CtorId × FlatLang.TypeId)) (xs : List FlatLang.Exp) :
    compileExp cfg (.con t tag xs) =
      let (i, sg, ys) := compileExps cfg xs.reverse
      (i, sg, .con t tag ys.reverse) := by
  rw [compileExps_reverse]
  cases h : compileExps cfg xs with
  | mk i rest =>
    cases rest with
    | mk sg ys => simp [compileExp, h]

/-- Application compilation satisfies the source's reverse/traverse/reverse equation. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_exp_def"]
theorem compileExp_app_source (cfg : Config) (t : BackendCommon.Tra)
    (op : FlatLang.Op) (xs : List FlatLang.Exp) :
    compileExp cfg (.app t op xs) =
      let (i, sg, ys) := compileExps cfg xs.reverse
      (i, sg || opSetsGlobals op, .app t op ys.reverse) := by
  rw [compileExps_reverse]
  cases h : compileExps cfg xs with
  | mk i rest =>
    cases rest with
    | mk sg ys => simp [compileExp, h]

/-- The recursive-function helper implements HOL's map, maximum, and exists
operations on the compiled bodies. -/
theorem compileFuns_source (cfg : Config)
    (fs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp)) :
    compileFuns cfg fs =
      let ys := fs.map (fun (a, b, body) => (a, b, compileExp cfg body))
      (Flapjack.maxList (ys.map (fun (_, _, result) => result.1)),
        ys.any (fun (_, _, result) => result.2.1),
        ys.map (fun (a, b, result) => (a, b, result.2.2))) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rcases f with ⟨name, arg, body⟩
    cases h : compileExp cfg body with
    | mk i rest =>
      cases rest with
      | mk sg result =>
        simp [compileFuns, Flapjack.maxList, h, ih]

/-- Recursive-function compilation satisfies the source's map-and-aggregate
equation. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_exp_def"]
theorem compileExp_letrec_source (cfg : Config) (t : Flapjack.AstHOL.VarN)
    (fs : List (Flapjack.AstHOL.VarN × Flapjack.AstHOL.VarN × FlatLang.Exp))
    (body : FlatLang.Exp) :
    compileExp cfg (.letrec t fs body) =
      let ys := fs.map (fun (a, b, exp) => (a, b, compileExp cfg exp))
      let (i, sgx, y) := compileExp cfg body
      let j := Flapjack.maxList (ys.map (fun (_, _, result) => result.1))
      let sgfs := ys.any (fun (_, _, result) => result.2.1)
      let fs2 := ys.map (fun (a, b, result) => (a, b, result.2.2))
      (max i j, sgfs || sgx, .letrec t fs2 y) := by
  simp only [compileExp, compileFuns_source]

end Flapjack.Compiler.Backend.FlatPattern
