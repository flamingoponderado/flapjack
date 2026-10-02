import Flapjack.Compiler.Backend.LabToTarget.InitialEncodingNavigation
namespace Flapjack.Test.LabToTargetInitialEncodingNavigationParity
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
example {width : Nat} [NeZero width] (sid lid : Nat) (code : List (Section (LabLineHOL width)))
    (enc : HolAsm width → List (BitVec 8)) :
    locToPc sid lid (encSecList enc code) = locToPc sid lid code := locToPc_encSecList sid lid code enc
example : locToPc 1 2 (encSecList (width := 8) (fun _ => [0,1]) []) = none := by decide +kernel
example : locToPc 1 0 (encSecList (width := 8) (fun _ => []) [⟨1,[]⟩]) = some 0 := by decide +kernel
example : locToPc 1 7 (encSecList (width := 8) (fun _ => [0,1]) [⟨1,[.asm (.asmi (.inst .skip)) [] 99,.labAsm .halt 3 [] 123,.label 1 7 456]⟩]) = some 2 := by decide +kernel
example : locToPc 99 7 (encSecList (width := 8) (fun _ => []) [⟨1,[.label 99 7 123]⟩]) = some 0 := by decide +kernel
example : locToPc 1 7 (encSecList (width := 8) (fun _ => [0,1]) [⟨1,[.label 1 7 123,.asm (.asmi (.inst .skip)) [] 99,.label 1 7 456]⟩]) = some 0 := by decide +kernel
example : locToPc 1 3 (encSecList (width := 8) (fun _ => []) [⟨1,[.label 1 7 99,.labAsm .halt 3 [] 123]⟩]) = none := by decide +kernel
example : locToPc 99 0 (encSecList (width := 8) (fun _ => []) [⟨1,[.label 99 0 123]⟩]) = none := by decide +kernel
example : locToPc 1 7 (encSecList (width := 1) (fun _ => [0]) [⟨1,[.asm (.asmi (.inst .skip)) [] 99,.label 1 7 123]⟩]) = some 1 := by decide +kernel
example : locToPc 1208925819614629174706176 7 (encSecList (width := 80) (fun _ => []) [⟨1,[.label 1208925819614629174706176 7 123]⟩]) = some 0 := by decide +kernel
-- An actual theorem application for every encoder, with invalid section ownership.
example (enc : HolAsm 8 → List (BitVec 8)) :
    locToPc 99 7 (encSecList enc [⟨1,[.label 99 7 123]⟩]) = some 0 := by
  rw [locToPc_encSecList]
  decide +kernel
end Flapjack.Test.LabToTargetInitialEncodingNavigationParity
