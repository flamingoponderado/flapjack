import Flapjack.Pancake.PanStructs.OldExpShapeExact

namespace Flapjack.Test.PanStructsOldExpShapeExactParity
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Basis.Pure.MlString

private def exactContext : ContextExact :=
  { structs := [(ofString "Pair", [(ofString "left", .one),
      (ofString "right", .comb [.one, .one])])]
    locals := [(ofString "local", .comb [.one, .one])]
    globals := [(ofString "global", .named (ofString "Pair"))] }

-- Exact replay of the ten labels in old_exp_shape_probe.out (8-bit source words).
example : oldExpShapeExact exactContext (.var .local (ofString "local") : ExpHOL 8) =
    .comb [.one, .one] := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, ite_true]
example : oldExpShapeExact exactContext (.var .global (ofString "global") : ExpHOL 8) =
    .named (ofString "Pair") := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, ite_true]
example : oldExpShapeExact exactContext (.rstruct [.const 1, .const 2] : ExpHOL 8) =
    .comb [.one, .one] := by simp +decide only [oldExpShapeExact, oldExpShapesExact, exactContext]
example : oldExpShapeExact exactContext
    (.rfield 1 (.rstruct [.const 1, .const 2]) : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, oldExpShapesExact, exactContext, List.getElem?_cons, List.getElem?_nil, Option.getD, ite_true, ite_false]
example : oldExpShapeExact exactContext
    (.rfield 4 (.rstruct [.const 1]) : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, oldExpShapesExact, exactContext, List.getElem?_cons, List.getElem?_nil, Option.getD, ite_false]
example : oldExpShapeExact exactContext (.nstruct (ofString "Pair") [] : ExpHOL 8) =
    .named (ofString "Pair") := by simp +decide only [oldExpShapeExact, exactContext]
example : oldExpShapeExact exactContext
    (.nfield (ofString "right") (.nstruct (ofString "Pair") []) : ExpHOL 8) =
    .comb [.one, .one] := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, ite_true, ite_false]
example : oldExpShapeExact exactContext
    (.nfield (ofString "missing") (.nstruct (ofString "Pair") []) : ExpHOL 8) =
    .one := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, ite_true, ite_false]
example : oldExpShapeExact exactContext
    (.load (.comb [.one, .one]) (.const 0) : ExpHOL 8) = .comb [.one, .one] := by simp +decide only [oldExpShapeExact, exactContext]
example : oldExpShapeExact exactContext (.const 0 : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, exactContext]

-- First-match and missing-variable defensive defaults supplement captured rows.
example : oldExpShapeExact
    { exactContext with locals := [(ofString "x", .one),
        (ofString "x", .comb [.one])] }
    (.var .local (ofString "x") : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, ite_true]
example : oldExpShapeExact exactContext
    (.var .global (ofString "missing") : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, ite_false]
end Flapjack.Test.PanStructsOldExpShapeExactParity
