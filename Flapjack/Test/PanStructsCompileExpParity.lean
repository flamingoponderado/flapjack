import Flapjack.Pancake.PanStructs.CompileExpExact
import Flapjack.Pancake.PanStructs
import Flapjack.Pancake.Proofs.PanStructs

namespace Flapjack.Test.PanStructsCompileExpParity

/-! Direct parity for `pan_structs$compile_exp_def`
    (`pan_structsScript.sml:107`). The cases mirror the direct HOL fixture. -/
def context : StructPassContext :=
  { structs := [ ("Pair", { fields := [("left", .one),
      ("right", .comb [.one, .one])], size := 3 }) ]
    locals := [("local", .comb [.one, .one])]
    globals := [("global", .named "Pair")] }

def parityGuard : Bool :=
  (match structCompileExp context
      (.rStruct [.const 1, .const 2] : Exp Nat) with
  | .rStruct [.const 1, .const 2] => true
  | _ => false) &&
  (match structCompileExp context
      (.rField 1 (.rStruct [.const 1, .const 2]) : Exp Nat) with
  | .rField 1 (.rStruct [.const 1, .const 2]) => true
  | _ => false) &&
  (match structCompileExp context
      (.nStruct "Pair" [("right", .const 2), ("left", .const 1)] : Exp Nat) with
  | .rStruct [.const 1, .const 2] => true
  | _ => false) &&
  (match structCompileExp context
      (.nField "right" (.nStruct "Pair" []) : Exp Nat) with
  | .rField 1 (.rStruct []) => true
  | _ => false) &&
  (match structCompileExp context
      (.load (.named "Pair") (.const 0) : Exp Nat) with
  | .load (.comb [.one, .comb [.one, .one]]) (.const 0) => true
  | _ => false) &&
  (match structCompileExp context
      (.load32 (.const 0) : Exp Nat) with
  | .load32 (.const 0) => true
  | _ => false) &&
  (match structCompileExp context
      (.loadByte (.const 0) : Exp Nat) with
  | .loadByte (.const 0) => true
  | _ => false) &&
  (match structCompileExp context (.const 0 : Exp Nat) with
  | .const 0 => true
  | _ => false)

#eval parityGuard
#guard parityGuard

/- Direct parity for `pan_structs$compile_def` (`pan_structsScript.sml:157`).
   The declaration-local context is observable here: the body field lookup
   must use the source shape bound by `Dec`, while the emitted declaration
   carries the recursively compiled shape. -/
def compileProgParityGuard : Bool :=
  match structCompileProg context
      (.dec "value" (.named "Pair")
        (.nStruct "Pair" [("left", .const 1), ("right", .const 2)])
        (.return (.nField "right" (.var .local "value"))) : Prog Nat) with
  | .dec "value" (.comb [.one, .comb [.one, .one]])
      (.rStruct [.const 1, .const 2])
      (.return (.rField 1 (.var .local "value"))) => true
  | _ => false

#eval compileProgParityGuard
#guard compileProgParityGuard

/- Direct parity for `pan_structs$compile_decs_def`
   (`pan_structsScript.sml:213`).  This checks the reverse-recursive pass's
   final global context as well as each declaration's compiled shape. -/
def compileDeclsParityGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.decl (.named "Pair") "global"
      (.nStruct "Pair" [("left", .const 1), ("right", .const 2)]),
     .function
       { name := "read", inline := false, exported := false,
         params := [("pair", .named "Pair")],
         body := .return (.nField "right" (.var .local "pair")),
         returnShape := .named "Pair" },
     .exnDecl "E" (.named "Pair")]
  let initial : StructPassContext :=
    { structs := context.structs, locals := [], globals := [] }
  let (compiled, finalContext) := structCompileDecls declarations initial
  match finalContext.globals with
  | [("global", .named "Pair")] =>
      match compiled with
      | [.decl (.comb [.one, .comb [.one, .one]]) "global"
          (.rStruct [.const 1, .const 2]),
         .function declaration,
         .exnDecl "E" (.comb [.one, .comb [.one, .one]])] =>
          (match declaration.params with
          | [("pair", .comb [.one, .comb [.one, .one]])] => true
          | _ => false) &&
          (match declaration.returnShape with
          | .comb [.one, .comb [.one, .one]] => true
          | _ => false) &&
          match declaration.body with
          | .return (.rField 1 (.var .local "pair")) => true
          | _ => false
      | _ => false
  | _ => false

#eval compileDeclsParityGuard
#guard compileDeclsParityGuard

/- Cake `compile_exps_eq_map` (`pan_structsProofScript.sml:11`): the production
   list helper maps the production expression compiler over a nontrivial
   structure expression. -/
theorem structCompileExps_eq_map_fixture :
    structCompileExp.structCompileExps context
        ([.nStruct "Pair" [("right", .const 2), ("left", .const 1)]] : List (Exp Nat)) =
      [.rStruct [.const 1, .const 2]] := by
  calc
    _ = List.map (structCompileExp context)
        ([.nStruct "Pair" [("right", .const 2), ("left", .const 1)]] : List (Exp Nat)) :=
      congrFun (structCompileExps_eq_map context)
        ([.nStruct "Pair" [("right", .const 2), ("left", .const 1)]] : List (Exp Nat))
    _ = [.rStruct [.const 1, .const 2]] := by
      simp [structCompileExp, structCompileExp.structCompileFields,
        structSelectFields, context, lookupInfo]

/- Cake `old_exp_shapes_eq` (`pan_structsProofScript.sml:679`): the production
   old-shape list helper maps nontrivial source expressions pointwise. -/
theorem structOldExpShapes_eq_map_fixture :
    structOldExpShape.structOldExpShapes context
        ([.const 1, .var .local "local", .nStruct "Pair" [],
          .rStruct [.const 2, .var .global "global", .var .local "local"]] : List (Exp Nat)) =
      [.one, .comb [.one, .one], .named "Pair",
       .comb [.one, .named "Pair", .comb [.one, .one]]] := by
  rw [structOldExpShapes_eq_map]
  simp [structOldExpShape, structOldExpShape.structOldExpShapes, context, lookupInfo]

end Flapjack.Test.PanStructsCompileExpParity

namespace Flapjack.Test.PanStructsCompileExpExactParity
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Basis.Pure.MlString
private def exactContext : ContextExact :=
  { structs := [(ofString "Pair", [(ofString "left", .one),
      (ofString "right", .comb [.one, .one])])]
    locals := [(ofString "local", .comb [.one, .one])]
    globals := [(ofString "global", .named (ofString "Pair"))] }

-- Exact 8-bit inputs from pan_structs_compile_exp_probe.out.
example : compileExpExact exactContext (.rstruct [.const 1, .const 2] : ExpHOL 8) =
    .rstruct [.const 1, .const 2] := by simp +decide [compileExpExact, compileExpsExact, exactContext]
example : compileExpExact exactContext
    (.rfield 1 (.rstruct [.const 1, .const 2]) : ExpHOL 8) =
    .rfield 1 (.rstruct [.const 1, .const 2]) := by simp +decide [compileExpExact, compileExpsExact, exactContext]
example : compileExpExact exactContext
    (.nstruct (ofString "Pair") [(ofString "right", .const 2),
      (ofString "left", .const 1)] : ExpHOL 8) = .rstruct [.const 1, .const 2] := by simp +decide [compileExpExact, compileFieldsExact, exactContext, List.findSome?]
example : compileExpExact exactContext
    (.nfield (ofString "right") (.nstruct (ofString "Pair") []) : ExpHOL 8) =
    .rfield 1 (.rstruct []) := by simp +decide [compileExpExact, compileFieldsExact, oldExpShapeExact, exactContext, Flapjack.afindi, List.findSome?]
example : compileExpExact exactContext
    (.load (.named (ofString "Pair")) (.const 0) : ExpHOL 8) =
    .load (.comb [.one, .comb [.one, .one]]) (.const 0) := by
  simp only [compileExpExact, exactContext]
  rw [compileShapeExact]
  have hdrop : List.dropWhile (fun entry : MlS × List (MlS × ShapeHOL) =>
      !decide (entry.1 = ofString "Pair"))
      [(ofString "Pair", [(ofString "left", ShapeHOL.one),
        (ofString "right", ShapeHOL.comb [.one, .one])])] =
      [(ofString "Pair", [(ofString "left", ShapeHOL.one),
        (ofString "right", ShapeHOL.comb [.one, .one])])] := by rfl
  rw [hdrop]
  simp [compileShapesExact, compileShapeExact]
example : compileExpExact exactContext (.load32 (.const 0) : ExpHOL 8) =
    .load32 (.const 0) := by simp +decide [compileExpExact, exactContext]
example : compileExpExact exactContext (.loadByte (.const 0) : ExpHOL 8) =
    .loadByte (.const 0) := by simp +decide [compileExpExact, exactContext]
example : compileExpExact exactContext (.const 0 : ExpHOL 8) = .const 0 := by simp +decide [compileExpExact, exactContext]
example : compileExpsExact exactContext
    ([.nstruct (ofString "Pair") [(ofString "right", .const 2),
        (ofString "left", .const 1)], .const 3] : List (ExpHOL 8)) =
    ([.nstruct (ofString "Pair") [(ofString "right", .const 2),
        (ofString "left", .const 1)], .const 3] : List (ExpHOL 8)).map
      (compileExpExact exactContext) := by simp +decide [compileExpExact, compileExpsExact, compileFieldsExact, exactContext, List.findSome?]
example : oldExpShapesExact exactContext
    ([.var .local (ofString "local"), .var .global (ofString "global"),
      .nstruct (ofString "Pair") [], .rstruct [.const 2,
        .var .global (ofString "global"), .var .local (ofString "local")]] : List (ExpHOL 8)) =
    ([.var .local (ofString "local"), .var .global (ofString "global"),
      .nstruct (ofString "Pair") [], .rstruct [.const 2,
        .var .global (ofString "global"), .var .local (ofString "local")]] : List (ExpHOL 8)).map
      (oldExpShapeExact exactContext) := by simp +decide [oldExpShapeExact, oldExpShapesExact, exactContext, List.findSome?]
-- Defensive defaults and first-match field selection, beyond captured rows.
example : compileExpExact exactContext
    (.nstruct (ofString "missing") [] : ExpHOL 8) = .rstruct [] := by simp +decide [compileExpExact, exactContext, List.findSome?]
example : compileExpExact exactContext
    (.nstruct (ofString "Pair") [(ofString "left", .const 1),
      (ofString "left", .const 2)] : ExpHOL 8) = .rstruct [.const 1] := by simp +decide [compileExpExact, compileFieldsExact, exactContext, List.findSome?]
example : compileExpExact exactContext
    (.nfield (ofString "missing") (.nstruct (ofString "Pair") []) : ExpHOL 8) =
    .rfield 0 (.rstruct []) := by simp +decide [compileExpExact, compileFieldsExact, oldExpShapeExact, exactContext, Flapjack.afindi, List.findSome?]
end Flapjack.Test.PanStructsCompileExpExactParity
