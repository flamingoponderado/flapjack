import Flapjack.Pancake.PanToTarget.ProductionSourceEntry

namespace Flapjack.Test.PanSourceEntryParity
open Flapjack Pancake.PanLang Pancake.PanToTarget Basis.Pure.MlString

private def function (name : String) (value : BitVec 8) (exported := false) : Decl (BitVec 8) :=
  .function ⟨name, false, exported, [], .return (.const value), .one⟩

private def payload : List (DeclHOL 8) → Option (List (String × Nat × Bool × Bool))
  | [] => some []
  | .function ⟨name, false, exported, [], .return (.const value), .one⟩ :: rest =>
      (payload rest).map ((toStringOfBytes name, value.toNat, exported, false) :: ·)
  | .exnDecl name .one :: rest =>
      (payload rest).map ((toStringOfBytes name, 0, false, true) :: ·)
  | _ => none

private def missing : List (Decl (BitVec 8)) := [function "f" 7]
private theorem missingSource : ∀ d ∈ missing, DeclByteRanged d := by
  intro d member
  simp [missing] at member
  subst d
  simp [function, DeclByteRanged, FunDeclByteRanged, ProgByteRanged,
    ExpByteRanged, ListParamByteRanged, ShapeByteRanged, NameRanged]

private def missingMatches : List (Nat × Nat × WordLangProgHOL (BitVec 8)) → Bool
  | [(64, 1, .seq .skip (.seq (.call none (some 65) [0] none) .skip)),
     (65, 1, .seq (.assign 2 (.const zero)) (.seq (.return 0 [2]) .skip)),
     (66, 1, .seq (.assign 2 (.const value)) (.seq (.return 0 [2]) .skip))] => zero == 0 && value == 7
  | _ => false

end Flapjack.Test.PanSourceEntryParity
