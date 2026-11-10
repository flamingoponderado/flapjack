module

public import Flapjack.Pancake.Proofs.PanStructs
public import Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact
public import Flapjack.Pancake.PanStructs.CompileShapeExact
public import Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

-- Checks below run compiled code from these modules.
public meta import Flapjack.Pancake.PanStructs.CompileShapeExact
public meta import Flapjack.Pancake.Proofs.PanStructs
public meta import Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact
public meta import Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
@[expose] public section

namespace Flapjack.Test.PanStructsCompileShapeParity

open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Basis.Pure.MlString

/-! Direct replay of the source HOL-EVAL rows in
    `scripts/hol-probes/compile_shape_probe.out` using the exact
    `MlString`/`ShapeHOL` carrier. -/
private def holOuter := ofString "outer"
private def holInner := ofString "inner"
private def holField := ofString "field"
private def holValue := ofString "value"

private def exactForwardContext : ContextExact :=
  { structs :=
      [(holOuter, [(holField, .named holInner)]),
       (holInner, [(holValue, .one)])]
    , locals := []
    , globals := [] }

private def exactBackwardContext : ContextExact :=
  { structs :=
      [(holInner, [(holValue, .one)]),
       (holOuter, [(holField, .named holInner)])]
    , locals := []
    , globals := [] }

private def exactCompileShapeOracleRows : Bool :=
  (match compileShapeExact exactForwardContext.structs .one with
   | .one => true | _ => false) &&
  (match compileShapeExact exactForwardContext.structs (.comb [.one, .one]) with
   | .comb [.one, .one] => true | _ => false) &&
  (match compileShapeExact exactForwardContext.structs (.named holOuter) with
   | .comb [.comb [.one]] => true | _ => false) &&
  (match compileShapeExact exactBackwardContext.structs (.named holOuter) with
   | .comb [.one] => true | _ => false) &&
  (match compileShapeExact exactForwardContext.structs (.named (ofString "missing")) with
   | .one => true | _ => false)

#eval exactCompileShapeOracleRows
#guard exactCompileShapeOracleRows

/-! The three conjuncts of the `size_of_compile_shape_comb` oracle row. -/
private def sizeOfCompileShapeParityGuard : Bool :=
  isWfShapeExactHOL ([] : StructContextExact) (.comb [.one, .one]) &&
    (sizeOfShapeWithContextHOL [] (compileShapeExact (α := MlS) [] (.comb [.one, .one])) == 2) &&
    (sizeOfShapeWithContextHOL [] (.comb [.one, .one]) == 2)

#guard sizeOfCompileShapeParityGuard

example : Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact [] := by
  simp [Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact]

end Flapjack.Test.PanStructsCompileShapeParity
