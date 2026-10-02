import Flapjack.Compiler.Backend.LabToTarget.ZeroLabelExistence
namespace Flapjack.Test.LabToTargetZeroLabelExistenceParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps.LabelSets Flapjack.Compiler.Backend.BackendProps

example {width : Nat} [NeZero width]
    (l : AsmWithLab HolCmp (HolRegImm width) MlString) (acc : NumSet) :
    sptDomain (zeroLabsAccOf l acc) = Prod.fst '' restrictZero (labsOf l) ∪ sptDomain acc := zeroLabsAccOf_eq_zeroLabsOf l acc

example {width : Nat} [NeZero width]
    (l : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) (acc : NumSet) :
    sptDomain (lineGetZeroLabsAcc l acc) = Prod.fst '' restrictZero (lineGetLabels l) ∪ sptDomain acc := lineGetZeroLabsAcc_eq_lineGetZeroLabels l acc

example {width : Nat} [NeZero width]
    (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (acc : NumSet) :
    sptDomain (secGetZeroLabsAcc sec acc) = Prod.fst '' restrictZero (secGetLabels sec) ∪ sptDomain acc := secGetZeroLabsAcc_eq_secGetZeroLabels sec acc

example {width : Nat} [NeZero width]
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (acc : NumSet) :
    sptDomain (code.foldr secGetZeroLabsAcc acc) = Prod.fst '' restrictZero (getLabels code) ∪ sptDomain acc := getZeroLabsAcc_eq_getZeroLabels code acc

example {width : Nat} [NeZero width] {α : Type}
    (labs : Spt (Spt α)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    zeroLabsAccExist labs code = true ↔ restrictZero (getLabels code) ⊆ labsDomain labs := zeroLabsAccExist_eq labs code

private def code {width : Nat} [NeZero width] (k : Nat) : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :=
  [⟨1,[.labAsm (.jump (.lab k 0)) 0 [] 0]⟩]
example : sptLookup 7 (zeroLabsAccOf (width := 8) (.jump (.lab 7 0)) (sptInsert 42 () .ln)) = some () ∧
    sptLookup 42 (zeroLabsAccOf (width := 8) (.jump (.lab 7 0)) (sptInsert 42 () .ln)) = some () := by decide +kernel
example : zeroLabsAccOf (width := 8) (.jump (.lab 7 1)) .ln = .ln := rfl
example : zeroLabsAccOf (width := 8) (.call (.lab 7 0)) .ln = .ln := rfl
example : sptLookup 7 (zeroLabsAccOf (width := 8) (.locValue 9 (.lab 7 0)) .ln) = some () := by decide +kernel
example : zeroLabsAccExist (width := 8) (.ln : Spt (Spt Bool)) [] = true := rfl
example : zeroLabsAccExist (sptInsert 7 (sptInsert 0 true .ln) .ln) (code (width := 8) 7) = true := by decide +kernel
example : zeroLabsAccExist (.ln : Spt (Spt Bool)) (code (width := 8) 7) = false := by decide +kernel
example : zeroLabsAccExist (sptInsert 7 (sptInsert 1 true .ln) .ln) (code (width := 8) 7) = false := by decide +kernel
example : zeroLabsAccExist (sptInsert 7 (sptInsert 0 true .ln) .ln) (code (width := 1) 7) = true := by decide +kernel
example : zeroLabsAccExist (sptInsert 1208925819614629174706176 (sptInsert 0 false .ln) .ln)
    (code (width := 80) 1208925819614629174706176) = true := by decide +kernel
end Flapjack.Test.LabToTargetZeroLabelExistenceParity
