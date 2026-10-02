import Flapjack.Compiler.Backend.LabToTarget.NopPadding
namespace Flapjack.Test.LabToTargetNopPaddingParity
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
private def enc : HolAsm 8 → List Nat | .inst .skip => [9,8] | _ => [1,2]
private def encBool : HolAsm 8 → List Bool | .inst .skip => [false,true] | _ => [true,true]
private def encEmpty : HolAsm 8 → List Nat | .inst .skip => [] | _ => [7]
private def encOdd : HolAsm 8 → List Nat | .inst .skip => [9,8] | _ => [1]
private def encZero : HolAsm 8 → List Nat | .inst .skip => [9,8] | _ => []
example : padBytes (enc (.jump 3)) 2 (enc (.inst .skip)) = [1,2] ∧ encWithNop enc (.jump 3) (padBytes (enc (.jump 3)) 2 (enc (.inst .skip))) := ⟨rfl,encWithNop_padBytes_length enc (.jump 3)⟩
example : padBytes (encEmpty (.jump 3)) 1 (encEmpty (.inst .skip)) = [7] ∧ encWithNop encEmpty (.jump 3) (padBytes (encEmpty (.jump 3)) 1 (encEmpty (.inst .skip))) := ⟨rfl,encWithNop_padBytes_length encEmpty (.jump 3)⟩
example : padBytes (enc (.jump 3)) 8 [9,8] = [1,2,9,8,9,8,9,8] ∧ encWithNop enc (.jump 3) (padBytes (enc (.jump 3)) 8 [9,8]) :=
  ⟨rfl, encWithNop_padBytes [9,8] enc (.jump 3) 8 (by decide)⟩
example : padBytes (encBool (.jump 3)) 6 [false,true] = [true,true,false,true,false,true] ∧ encWithNop encBool (.jump 3) (padBytes (encBool (.jump 3)) 6 [false,true]) :=
  ⟨rfl, encWithNop_padBytes [false,true] encBool (.jump 3) 6 (by decide)⟩
example : encWithNop encZero (.jump 3) (padBytes (encZero (.jump 3)) 0 [9,8]) :=
  encWithNop_padBytes [9,8] encZero (.jump 3) 0 (by decide)
example : padBytes (encZero (.jump 3)) 4 [9,8] = [9,8,9,8] ∧ encWithNop encZero (.jump 3) (padBytes (encZero (.jump 3)) 4 [9,8]) :=
  ⟨rfl, encWithNop_padBytes [9,8] encZero (.jump 3) 4 (by decide)⟩
example : ¬encWithNop enc (.jump 3) (padBytes (enc (.jump 3)) 5 [9,8]) := by unfold encWithNop; decide
example : ¬encWithNop encOdd (.jump 3) (padBytes (encOdd (.jump 3)) 4 [9,8]) := by unfold encWithNop; decide
example : ¬encWithNop enc (.jump 3) (padBytes (enc (.jump 3)) 4 [9,7]) := by unfold encWithNop; decide
example {width : Nat} [NeZero width] {Value : Type}
    (enc : HolAsm width → List Value) (x : HolAsm width) :
    encWithNop enc x (padBytes (enc x) (enc x).length (enc (.inst .skip))) := encWithNop_padBytes_length enc x
example {width : Nat} [NeZero width] {Value : Type}
    (nop : List Value) (enc : HolAsm width → List Value) (x : HolAsm width) (len : Nat) :
    nop = enc (.inst .skip) ∧ (enc x).length ≤ len ∧
      (enc x).length % nop.length = 0 ∧ len % nop.length = 0 ∧ 0 < nop.length →
    encWithNop enc x (padBytes (enc x) len nop) := encWithNop_padBytes nop enc x len
def runChecks : IO Bool := do
  IO.println "PASS full generic NOP-padding establishment (9 original observations, 6 actual premise instances, 2 full generic consumers)"
  pure true
end Flapjack.Test.LabToTargetNopPaddingParity
