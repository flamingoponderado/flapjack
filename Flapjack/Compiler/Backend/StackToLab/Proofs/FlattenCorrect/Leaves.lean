import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Statement
import Flapjack.Compiler.Backend.LabProps.ClockSupport

/-! `flatten_correct` cases for the one-line StackSem leaves `Halt`, `Inst`,
`Tick`, `Return`, `Raise`, `Break` and `Continue`
(`stack_to_labProofScript.sml:1219-1240`, `1268-1320`, `1460-1530`). -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers

section
variable {width : Nat} [NeZero width] {C F : Type}

private theorem appList' {α : Type} (l : List α) : appListAppend (.list l) = l :=
  (appListAppend_thm .nil .nil l).2.1

/-- A single installed non-label line is fetched at the installation point. -/
theorem fetchSingle {pc : Nat} {x : LabLineHOL width}
    {code : LabProgHOL width} (nl : isLabelHOL x = false)
    (h : codeInstalled pc [x] code) : asmFetchAux pc code = some x := by
  rw [codeInstalled_cons] at h
  simp only [nl, Bool.false_eq_true, if_false] at h
  exact h.1

theorem relClock {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    t.clock = s.clock := rel.2.2.2.2.2.2.2.1

theorem relFfi {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    t.ffi = s.ffi := rel.2.2.2.2.2.2.1

/-- `Halt` case. -/
theorem flattenCorrectHalt (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    FlattenProp (.halt v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, -⟩
  rw [StackSemEvaluate.evaluate_halt] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.labAsm .halt 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  simp only [StackProps.callArgs] at ca
  split at ev
  · rename_i w hw
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have hreg : t1.regs t1.ptrReg = w := by
      rw [← ca]; exact InstCorrect.regOfLookup rel hw
    refine ⟨1, { t1 with clock := t1.clock + 1 }, ?_, ?_⟩
    · rw [evaluate]
      simp only [Nat.add_one_ne_zero, if_false, asmFetch, fetch, hreg]
      cases w with
      | word value =>
        by_cases hv : value = 0#width
        · simp [haltWordView, hv]
        · simp [haltWordView, hv]
      | loc a b => simp [haltWordView]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Inst` case. -/
theorem flattenCorrectInst (s1 : StackSemStateFiniteExact width C F) (i : HolInst width) :
    FlattenProp (.inst i : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_inst] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst i)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  split at ev
  · rename_i s1' hi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have rel2 := InstCorrect.instCorrect ⟨hi, rel⟩
    obtain ⟨cpc, ccode, cclock, -, -, -, -, -, cptr, clen, cptr2, clen2, clink⟩ :=
      asmInstConsts i t1
    have nf := InstCorrect.notFailed rel2
    refine ⟨1, incPc (asmInst i t1), fun ck1 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rel2⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
        LabProps.asmInstWithClock, nf, Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock, cclock, cpc]
      congr 1 <;> first | omega | exact nf.symm
    all_goals simp [incPc, cptr, clen, cptr2, clen2, clink, ccode, cpc, flattenHOL, appList',
      isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

end

end Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
