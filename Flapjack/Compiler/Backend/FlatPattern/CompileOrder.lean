module

public import Flapjack.Compiler.Backend.FlatPattern.CompileTotal
public import Flapjack.Compiler.Backend.BackendCommon.ConstructorTags
public import Flapjack.PanToCrepMaxList

@[expose] public section

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

/-- Supporting equivalence for the constructor traversal order. -/
private theorem compileExp_con_source (cfg : Config) (t : BackendCommon.Tra)
    (tag : Option (FlatLang.CtorId × FlatLang.TypeId)) (xs : List FlatLang.Exp) :
    compileExp cfg (.con t tag xs) =
      let (i, sg, ys) := compileExps cfg xs.reverse
      (i, sg, .con t tag ys.reverse) := by
  rw [compileExps_reverse]
  cases h : compileExps cfg xs with
  | mk i rest =>
    cases rest with
    | mk sg ys => simp [compileExp, h]

/-- Supporting equivalence for the application traversal order. -/
private theorem compileExp_app_source (cfg : Config) (t : BackendCommon.Tra)
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

/-- Supporting equivalence for recursive-function aggregation. -/
private theorem compileExp_letrec_source (cfg : Config) (t : Flapjack.AstHOL.VarN)
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

/-- The complete source equations for expression, expression-list and match
compilation. The constructor, application and recursive-function equations
also establish agreement with the source's traversal order and aggregation. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_exp_def"]
theorem compileExp_source_equations :
    (∀ vid t cfg, compileExp cfg (.varLocal t vid) = (decNameToNum vid, false, .varLocal t vid)) ∧
    (∀ x t cfg, compileExp cfg (.raise t x) =
      let (i, sg, y) := compileExp cfg x; (i, sg, .raise t y)) ∧
    (∀ x t ps cfg, compileExp cfg (.handle t x ps) =
      let (i, sgx, y) := compileExp cfg x
      let (j, sgp, ps2) := compileMatch cfg ps
      let k := max i j + 2
      let nm := encNumToName k
      let v := FlatLang.Exp.varLocal t nm
      let r := FlatLang.Exp.raise t v
      let exp := compilePats cfg sgp t k v r ps2
      (k, sgx || sgp, .handle t y [(.pvar nm, exp)])) ∧
    (∀ xs ts t cfg, compileExp cfg (.con t ts xs) =
      let (i, sg, ys) := compileExps cfg xs.reverse; (i, sg, .con t ts ys.reverse)) ∧
    (∀ x vs t cfg, compileExp cfg (.fn t vs x) =
      let (i, sg, y) := compileExp cfg x; (i, sg, .fn t vs y)) ∧
    (∀ xs t op cfg, compileExp cfg (.app t op xs) =
      let (i, sg, ys) := compileExps cfg xs.reverse; (i, sg || opSetsGlobals op, .app t op ys.reverse)) ∧
    (∀ x t ps cfg, compileExp cfg (.mat t x ps) =
      let (i, sgx, y) := compileExp cfg x
      let (j, sgp, ps2) := compileMatch cfg ps
      let k := max i j + 2
      let nm := encNumToName k
      let v := FlatLang.Exp.varLocal t nm
      let r := FlatLang.Exp.raise t (.con t (some (BackendCommon.bindTag, none)) [])
      let exp := compilePats cfg sgp t k v r ps2
      (k, sgx || sgp, .let_ t (some nm) y exp)) ∧
    (∀ x2 x1 v t cfg, compileExp cfg (.let_ t v x1 x2) =
      let (i, sg1, y1) := compileExp cfg x1
      let (j, sg2, y2) := compileExp cfg x2
      let k := v.elim 0 decNameToNum
      (max i (max j k), sg1 || sg2, .let_ t v y1 y2)) ∧
    (∀ x t fs cfg, compileExp cfg (.letrec t fs x) =
      let ys := fs.map (fun (a, b, e) => (a, b, compileExp cfg e))
      let (i, sgx, y) := compileExp cfg x
      let j := Flapjack.maxList (ys.map (fun (_, _, result) => result.1))
      let sgfs := ys.any (fun (_, _, result) => result.2.1)
      let fs2 := ys.map (fun (a, b, result) => (a, b, result.2.2))
      (max i j, sgfs || sgx, .letrec t fs2 y)) ∧
    (∀ x3 x2 x1 t cfg, compileExp cfg (.if_ t x1 x2 x3) =
      let (i, sg1, y1) := compileExp cfg x1
      let (j, sg2, y2) := compileExp cfg x2
      let (k, sg3, y3) := compileExp cfg x3
      (max i (max j k), sg1 || sg2 || sg3, FlatLang.smartIf t y1 y2 y3)) ∧
    (∀ v t cfg, compileExp cfg (.lit t v) = (0, false, .lit t v)) ∧
    (∀ cfg, compileExps cfg [] = (0, false, [])) ∧
    (∀ xs x cfg, compileExps cfg (x :: xs) =
      let (i, sgx, y) := compileExp cfg x
      let (j, sgy, ys) := compileExps cfg xs
      (max i j, sgx || sgy, y :: ys)) ∧
    (∀ cfg, compileMatch cfg [] = (0, false, [])) ∧
    (∀ x ps p cfg, compileMatch cfg ((p, x) :: ps) =
      let (i, sgx, y) := compileExp cfg x
      let j := maxDecName (FlatLang.patBindings p)
      let (k, sgp, ps2) := compileMatch cfg ps
      (max i (max j k), sgx || sgp, (p, y) :: ps2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros
  all_goals first | rfl | exact compileExp_con_source _ _ _ _ | exact compileExp_app_source _ _ _ _ | exact compileExp_letrec_source _ _ _ _

end Flapjack.Compiler.Backend.FlatPattern
