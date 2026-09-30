import Flapjack.Pancake.PanStructs.OldExpShapeExact
import Flapjack.Pancake.PanStructs

namespace Flapjack.Test.PanStructsOldExpShapeParity

/-! Direct parity for `pan_structs$old_exp_shape_def`
    (`pan_structsScript.sml:70`). -/
def context : StructPassContext :=
  { structs := [("Pair", { fields := [("left", .one),
      ("right", .comb [.one, .one])], size := 3 })]
    locals := [("local", .comb [.one, .one])]
    globals := [("global", .named "Pair")] }

def parityGuard : Bool :=
  (match structOldExpShape context (.var .local "local" : Exp Nat) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structOldExpShape context (.var .global "global" : Exp Nat) with
  | .named "Pair" => true
  | _ => false) &&
  (match structOldExpShape context
      (.rStruct [.const 1, .const 2] : Exp Nat) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structOldExpShape context
      (.rField 1 (.rStruct [.const 1, .const 2]) : Exp Nat) with
  | .one => true
  | _ => false) &&
  (match structOldExpShape context (.nStruct "Pair" [] : Exp Nat) with
  | .named "Pair" => true
  | _ => false) &&
  (match structOldExpShape context
      (.nField "right" (.nStruct "Pair" []) : Exp Nat) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structOldExpShape context
      (.load (.comb [.one, .one]) (.const 0)) with
  | .comb [.one, .one] => true
  | _ => false) &&
  (match structOldExpShape context (.const 0) with
  | .one => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanStructsOldExpShapeParity

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
    .comb [.one, .one] := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, if_true]
example : oldExpShapeExact exactContext (.var .global (ofString "global") : ExpHOL 8) =
    .named (ofString "Pair") := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, if_true]
example : oldExpShapeExact exactContext (.rstruct [.const 1, .const 2] : ExpHOL 8) =
    .comb [.one, .one] := by simp +decide only [oldExpShapeExact, oldExpShapesExact, exactContext]
example : oldExpShapeExact exactContext
    (.rfield 1 (.rstruct [.const 1, .const 2]) : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, oldExpShapesExact, exactContext, List.getElem?_cons, List.getElem?_nil, Option.getD, if_true, if_false]
example : oldExpShapeExact exactContext
    (.rfield 4 (.rstruct [.const 1]) : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, oldExpShapesExact, exactContext, List.getElem?_cons, List.getElem?_nil, Option.getD, if_false]
example : oldExpShapeExact exactContext (.nstruct (ofString "Pair") [] : ExpHOL 8) =
    .named (ofString "Pair") := by simp +decide only [oldExpShapeExact, exactContext]
example : oldExpShapeExact exactContext
    (.nfield (ofString "right") (.nstruct (ofString "Pair") []) : ExpHOL 8) =
    .comb [.one, .one] := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, if_true, if_false]
example : oldExpShapeExact exactContext
    (.nfield (ofString "missing") (.nstruct (ofString "Pair") []) : ExpHOL 8) =
    .one := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, if_true, if_false]
example : oldExpShapeExact exactContext
    (.load (.comb [.one, .one]) (.const 0) : ExpHOL 8) = .comb [.one, .one] := by simp +decide only [oldExpShapeExact, exactContext]
example : oldExpShapeExact exactContext (.const 0 : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, exactContext]

-- First-match and missing-variable defensive defaults supplement captured rows.
example : oldExpShapeExact
    { exactContext with locals := [(ofString "x", .one),
        (ofString "x", .comb [.one])] }
    (.var .local (ofString "x") : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, if_true]
example : oldExpShapeExact exactContext
    (.var .global (ofString "missing") : ExpHOL 8) = .one := by simp +decide only [oldExpShapeExact, exactContext, List.findSome?, Option.getD, if_false]
end Flapjack.Test.PanStructsOldExpShapeExactParity
