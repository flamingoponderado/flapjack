import Flapjack.Compiler.Backend.LabProps.EvaluateIoEventsMono
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentDmMemory
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentDmControl
import Flapjack.Compiler.Backend.LabSem.Semantics
import Flapjack.SemanticsProps.Implements

namespace Flapjack.Compiler.Backend.LabProps
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Encoders.Asm

/-- Flapjack-only native transition equation, derived from the three exact DM implications. -/
private theorem sharedProjection {width : Nat} [NeZero width] {C : Type} {F : Type}
    (m : HolMemop) (r : Nat) (a : HolAddr width)
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    shareMemOp m r a (alignDm s) =
      (shareMemOp m r a s).map (fun pair => (pair.1,alignDm pair.2)) := by
  cases h : shareMemOp m r a s with
  | none =>
      have hn := (shareMemOpAlignDM m r a s s (⟨.sharedMem .mappedRead,[],[],.diverged⟩) s.ffi []).1 h
      simp only [hn, Option.map_none]
  | some pair =>
      rcases pair with ⟨res,next⟩
      cases res with
      | final f => exact (shareMemOpAlignDM m r a s next f s.ffi []).2.1 h
      | ret fs l => exact (shareMemOpAlignDM m r a s next (⟨.sharedMem .mappedRead,[],[],.diverged⟩) fs l).2.2 h

/-- Guarded Flapjack infrastructure for the full evaluator's source good_dimindex
premise. This is not a port of HOL's separate unconditional byte-helper theorem. -/
private theorem byteLoadDomain {width : Nat} [NeZero width] (hw : goodDimindex width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (be : Bool) (a : BitVec width) :
    memLoadByteAuxExact memory (fun x => domain x && holByteAligned x) be a =
      memLoadByteAuxExact memory domain be a := by
  have ha : holByteAligned (riscvByteAlignHOL a) = true := by
    rw [Flapjack.Compiler.Backend.LabToTarget.riscvByteAlignHOL_eq hw]
    apply (Flapjack.Compiler.Backend.LabToTarget.holAligned_word_iff hw _).2
    rw [holByteAlign_toNat hw]
    exact Nat.mul_mod_left _ _
  simp only [memLoadByteAuxExact,ha,Bool.and_true]

/-- Function-extensional native byte loader consequence for the full evaluator's guard. -/
private theorem byteLoaderDomain {width : Nat} [NeZero width] (hw : goodDimindex width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (be : Bool) :
    memLoadByteAuxExact memory (fun x => domain x && holByteAligned x) be =
      memLoadByteAuxExact memory domain be := by
  funext a
  exact byteLoadDomain hw memory domain be a

/-- Guarded Flapjack infrastructure; no claim to the unguarded HOL auxiliary. -/
private theorem byteStoreDomain {width : Nat} [NeZero width] (hw : goodDimindex width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (be : Bool) (a : BitVec width) (b : BitVec 8) :
    memStoreByteAuxExact memory (fun x => domain x && holByteAligned x) be a b =
      memStoreByteAuxExact memory domain be a b := by
  have ha : holByteAligned (riscvByteAlignHOL a) = true := by
    rw [Flapjack.Compiler.Backend.LabToTarget.riscvByteAlignHOL_eq hw]
    apply (Flapjack.Compiler.Backend.LabToTarget.holAligned_word_iff hw _).2
    rw [holByteAlign_toNat hw]
    exact Nat.mul_mod_left _ _
  simp only [memStoreByteAuxExact,ha,Bool.and_true]

/-- Guarded Flapjack infrastructure needed by the original full evaluator theorem. -/
private theorem bytearrayWriteDomain {width : Nat} [NeZero width] (hw : goodDimindex width)
    (bytes : List (BitVec 8)) (a : BitVec width) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (be : Bool) :
    writeBytearrayExact a bytes memory (fun x => domain x && holByteAligned x) be =
      writeBytearrayExact a bytes memory domain be := by
  induction bytes generalizing a memory with
  | nil => rfl
  | cons b bs ih => simp only [writeBytearrayExact,ih,byteStoreDomain hw]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateAlignDM {width : Nat} [NeZero width] {C F : Type} :
    goodDimindex width → ∀ (s : Flapjack.Compiler.Backend.LabSem.State width C F),
    evaluate (alignDm s) = let (r,next) := evaluate s; (r,alignDm next) := by
  intro hw s
  fun_induction evaluate s
  case' case10 hc op reg address encoded len hf hs =>
    rename_i st
    have hprojection := sharedProjection op reg address st
  case' case11 hc op reg address encoded len hf outcome next hs =>
    rename_i st
    have hprojection := sharedProjection op reg address st
  case' case12 hc op reg address encoded len hf ffi bytes next hs hn ih =>
    rename_i st
    have hprojection := sharedProjection op reg address st
  all_goals conv_lhs => rw [evaluate]
  all_goals simp only [asmFetchAlignDM,asmInstAlignDM _ _ hw,getPcValueAlignDM,
    getRetLocAlignDM,regImmAlignDM,alignDmConst,
    decClockAlignDM,incPcAlignDM,updPcAlignDM,updRegAlignDM]
  all_goals simp_all (config := { zetaDelta := true }) [alignDm,incPc,decClock,updPc,updReg,asmInstConsts,byteLoaderDomain hw,bytearrayWriteDomain hw]
  all_goals repeat' first | rfl | split | simp_all
  all_goals try (split_ifs <;> simp_all)
  all_goals try (set_option backward.dsimp.instances true in dsimp only [alignDm])
  all_goals try rw [if_neg (by tauto)]

/-- Flapjack-only projection form of the full source evaluation equation. -/
private theorem evaluatePair {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    evaluate (alignDm s) = ((evaluate s).1,alignDm (evaluate s).2) := by
  have h := evaluateAlignDM hw s
  cases he : evaluate s
  simpa only [he] using h

/-- Flapjack-only clock-indexed evaluator equation, with the original clock update. -/
private theorem evaluateClock {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) (clock : Nat) :
    evaluate {alignDm s with clock := clock} =
      ((evaluate {s with clock := clock}).1,alignDm (evaluate {s with clock := clock}).2) := by
  change evaluate (alignDm {s with clock := clock}) = _
  exact evaluatePair hw _

/-- Flapjack-only full behavior equality deriving the original precise refinement. -/
private theorem semanticsProjection {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width) (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    semantics (alignDm s) = semantics s := by
  have herr : (∃ clock, (evaluate {alignDm s with clock := clock}).1 = .error) ↔
      (∃ clock, (evaluate {s with clock := clock}).1 = .error) := by
    simp only [evaluateClock hw]
  by_cases hfail : ∃ clock, (evaluate {s with clock := clock}).1 = .error
  · unfold semantics
    rw [if_pos (herr.mpr hfail), if_pos hfail]
  · unfold semantics
    rw [if_neg (fun h => hfail (herr.mp h)), if_neg hfail]
    simp only [evaluateClock hw]
    simp [alignDm, Prod.ext_iff, and_assoc]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem implementsAlignDM {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F) :
    goodDimindex width → Flapjack.SemanticsPropsHOL.implementsPrimeHOL true
      (fun behavior => behavior = semantics s)
      (fun behavior => behavior = semantics (alignDm s)) := by
  intro hw
  rw [semanticsProjection hw]
  intro _ result hresult
  exact hresult

end Flapjack.Compiler.Backend.LabProps
