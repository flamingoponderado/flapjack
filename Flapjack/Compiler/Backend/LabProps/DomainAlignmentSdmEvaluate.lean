import Flapjack.Compiler.Backend.LabProps.EvaluateIoEventsMono
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentSdmMemory
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentSdmNavigation
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentSdmShared
import Flapjack.Compiler.Backend.LabSem.Semantics
import Flapjack.SemanticsProps.Implements

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

/-- Flapjack-only equation form of the source shared-memory conjunction. -/
private theorem sharedProjection {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (m : HolMemop) (r : Nat) (a : HolAddr width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    shareMemOp m r a (alignSdm s) =
      (shareMemOp m r a s).map (fun pair => (pair.1, alignSdm pair.2)) := by
  cases h : shareMemOp m r a s with
  | none =>
      have hn := (shareMemOpAlignSDM m r a s s (.ret s.ffi []) hw).1.mp h
      simp only [hn, Option.map_none]
  | some pair =>
      exact (shareMemOpAlignSDM m r a s pair.2 pair.1 hw).2 h

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "evaluate_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem evaluateAlignSDM {width : Nat} [NeZero width] {C F : Type} :
    goodDimindex width → ∀ (s : Flapjack.Compiler.Backend.LabSem.State width C F),
    evaluate (alignSdm s) = let (r,next) := evaluate s; (r,alignSdm next) := by
  intro hw s
  fun_induction evaluate s
  case' case10 hc op reg address encoded len hf hs =>
    rename_i st
    have hprojection := sharedProjection hw op reg address st
  case' case11 hc op reg address encoded len hf outcome next hs =>
    rename_i st
    have hprojection := sharedProjection hw op reg address st
  case' case12 hc op reg address encoded len hf ffi bytes next hs hn ih =>
    rename_i st
    have hprojection := sharedProjection hw op reg address st
  all_goals conv_lhs => rw [evaluate]
  all_goals simp only [asmFetchAlignSDM,asmInstAlignSDM,getPcValueAlignSDM,
    getRetLocAlignSDM,regImmAlignSDM,alignSdmConst,
    decClockAlignSDM,incPcAlignSDM,updPcAlignSDM,updRegAlignSDM]
  all_goals simp_all (config := { zetaDelta := true }) [alignSdm,incPc,decClock,updPc,updReg,asmInstConsts]
  all_goals repeat' first | rfl | split | simp_all
  all_goals split_ifs <;> simp_all
  all_goals set_option backward.dsimp.instances true in dsimp only [alignSdm]
  all_goals rw [if_neg (by tauto)]

/-- Flapjack-only projection form of the full source evaluation equation. -/
private theorem evaluatePair {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    evaluate (alignSdm s) = ((evaluate s).1,alignSdm (evaluate s).2) := by
  have h := evaluateAlignSDM hw s
  cases he : evaluate s
  simpa only [he] using h

/-- Flapjack-only clock-indexed evaluator equation, with the original clock update. -/
private theorem evaluateClock {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) (clock : Nat) :
    evaluate {alignSdm s with clock := clock} =
      ((evaluate {s with clock := clock}).1,alignSdm (evaluate {s with clock := clock}).2) := by
  change evaluate (alignSdm {s with clock := clock}) = _
  exact evaluatePair hw _

/-- Flapjack-only full behavior equality deriving the original precise refinement. -/
private theorem semanticsProjection {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    semantics (alignSdm s) = semantics s := by
  have herr : (∃ clock, (evaluate {alignSdm s with clock := clock}).1 = .error) ↔
      (∃ clock, (evaluate {s with clock := clock}).1 = .error) := by
    simp only [evaluateClock hw]
  by_cases hfail : ∃ clock, (evaluate {s with clock := clock}).1 = .error
  · unfold semantics
    rw [if_pos (herr.mpr hfail), if_pos hfail]
  · unfold semantics
    rw [if_neg (fun h => hfail (herr.mp h)), if_neg hfail]
    simp only [evaluateClock hw]
    simp [alignSdm, Prod.ext_iff, and_assoc]

@[hol "cakeml/compiler/backend/semantics/labPropsScript.sml" "implements_align_sdm"
  (words_as_type_indexed_bitvec)]
theorem implementsAlignSDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → Flapjack.SemanticsPropsHOL.implementsPrimeHOL true
      (fun behavior => behavior = semantics s)
      (fun behavior => behavior = semantics (alignSdm s)) := by
  intro hw
  rw [semanticsProjection hw]
  intro _ result hresult
  exact hresult

end Flapjack.Compiler.Backend.LabProps
