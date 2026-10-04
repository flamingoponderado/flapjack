import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveLoop
import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas

/-! Counterpart of the original trigger-update simulation at
`stack_allocProofScript.sml:4553-4590`. The helpers expose the actual native
instruction prefix and conditional branches; the final theorem retains the
original inversion statement and complete state update. -/
namespace Flapjack.Compiler.Backend.StackAlloc
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackRemove (constInst)

/-- Exact instruction prefix, before selecting the trigger value. -/
theorem setNewTriggerPrefix_eval {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (endhReg ibReg : Nat)
    (endh ib w : BitVec width) (gs : List Nat)
    (hu : s.useStore = true)
    (hd : [1,4,7,ibReg,endhReg].Nodup)
    (he : s.regs.lookup endhReg = some (.word endh))
    (hi : s.regs.lookup ibReg = some (.word ib))
    (hw : s.store.lookup .allocSize = some (.word w)) :
    evaluate (listSeqHOL [constInst 1 (getGenSize gs : BitVec width),
      .get 7 .allocSize, moveHOL 4 endhReg, subInst 4 ibReg], s) =
      (none, setVar 4 (.word (endh - ib))
        (setVar 4 (.word endh) (setVar 7 (.word w)
          (setVar 1 (.word (getGenSize gs)) s)))) := by
  have he1 : endhReg ≠ 1 := by intro h; subst endhReg; simp at hd
  have he7 : endhReg ≠ 7 := by intro h; subst endhReg; simp at hd
  have hi1 : ibReg ≠ 1 := by intro h; subst ibReg; simp at hd
  have hi4 : ibReg ≠ 4 := by intro h; subst ibReg; simp at hd
  have hi7 : ibReg ≠ 7 := by intro h; subst ibReg; simp at hd
  simp [listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    StackSemRegisterTransfers.storeOfSyntax, hu, hw, he, hi, he1, he7, hi1, hi4, hi7,
    constInst, moveHOL, subInst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, setVar, wordOpHOL, wordOp, fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- The actual conditional tree selects precisely the original `new_trig`.
This is proof infrastructure for the source theorem, not another evaluator. -/
theorem newTrig_branch_eq {width : Nat} [NeZero width]
    (h a : BitVec width) (gs : List Nat) (hd : goodDimindex width) :
    newTrig h a gs =
      if (getGenSize gs : BitVec width).toNat < a.toNat then
        if h.toNat < a.toNat then h else
          if (a &&& (if width = 32 then 3 else 7)) = 0 then a else h
      else if h.toNat < (getGenSize gs : BitVec width).toNat then h else getGenSize gs := by
  have hal := good_dimindex_byte_aligned_eq (w := a) hd
  by_cases hag : a.toNat ≤ (getGenSize gs : BitVec width).toNat
  · have hga : ¬ (getGenSize gs : BitVec width).toNat < a.toNat := by omega
    by_cases hhg : h.toNat < (getGenSize gs : BitVec width).toNat
    · simp [newTrig, hag, hga, hhg, Nat.le_of_lt hhg]
    · have hgh : (getGenSize gs : BitVec width).toNat ≤ h.toNat := by omega
      simp [newTrig, hag, hga, hhg, hgh]
  · have hga : (getGenSize gs : BitVec width).toNat < a.toNat := by omega
    by_cases hha : h.toNat < a.toNat
    · simp [newTrig, hag, hga, hha]
    · by_cases ha : holByteAligned a = true
      · have hz := hal.mp ha
        change (a &&& (if width = 32 then 3#width else 7#width)) = 0#width at hz
        simp [newTrig, hag, hga, hha, ha, hz]
      · have hz : (a &&& (if width = 32 then 3 else 7)) ≠ 0 := fun hz => ha (hal.mpr hz)
        change (a &&& (if width = 32 then 3#width else 7#width)) ≠ 0#width at hz
        have ha' : holByteAligned a = false := Bool.eq_false_iff.mpr ha
        simp [newTrig, hag, hga, hha, ha', hz]

/-- Native SetNewTrigger run; original evaluation inversion follows from this
stronger direct equation. No target result is supplied as a premise. -/
theorem setNewTrigger_run {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (endhReg ibReg : Nat)
    (endh ib w : BitVec width) (gs : List Nat)
    (hdim : goodDimindex width) (hu : s.useStore = true)
    (hd : [1,4,7,ibReg,endhReg].Nodup)
    (he : s.regs.lookup endhReg = some (.word endh))
    (hi : s.regs.lookup ibReg = some (.word ib))
    (hw : s.store.lookup .allocSize = some (.word w)) :
    ∃ r7 r1 r4,
      evaluate (setNewTrigger endhReg ibReg gs, s) =
        (none, {s with
          regs := ((s.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
          store := s.store.updateEq (.triggerGC, .word (ib + newTrig (endh-ib) w gs))}) := by
  have he1 : endhReg ≠ 1 := by intro h; subst endhReg; simp at hd
  have he4 : endhReg ≠ 4 := by intro h; subst endhReg; simp at hd
  have he7 : endhReg ≠ 7 := by intro h; subst endhReg; simp at hd
  have hi1 : ibReg ≠ 1 := by intro h; subst ibReg; simp at hd
  have hi4 : ibReg ≠ 4 := by intro h; subst ibReg; simp at hd
  have hi7 : ibReg ≠ 7 := by intro h; subst ibReg; simp at hd
  let g : BitVec width := getGenSize gs
  let h := endh - ib
  have ht := newTrig_branch_eq h w gs hdim
  by_cases hgw : g.toNat < w.toNat <;>
    by_cases hhw : h.toNat < w.toNat <;>
    by_cases hhg : h.toNat < g.toNat <;>
    by_cases hal : (w &&& (if width = 32 then 3#width else 7#width)) = 0#width
  all_goals
    refine ⟨.word (if g.toNat < w.toNat ∧ ¬h.toNat < w.toNat ∧ (w &&& (if width = 32 then 3#width else 7#width)) = 0#width then w + ib else w),
      .word (if ¬g.toNat < w.toNat ∧ ¬h.toNat < g.toNat then g + ib else g), .word h, ?_⟩
    dsimp only [g, h] at hgw hhw hhg ht ⊢
    simp only [BitVec.toNat_sub] at hhw hhg
    have halB : ((w &&& (if width = 32 then 3#width else 7#width)) == 0#width) =
        decide ((w &&& (if width = 32 then 3#width else 7#width)) = 0#width) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
    have hcancel : ib + (endh - ib) = endh := by
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    simp [setNewTrigger, listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
      evaluate_ite, evaluate_set, StackSemRegisterTransfers.storeOfSyntax,
      constInst, moveHOL, subInst, addInst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, wordSemWordCmp, wordCmpHOL, getVar, StackSemStateOps.getVarImm, AndOp.and,
      HolRegImm.toWordRegImm, setVar, setStore, wordOpHOL, wordOp, fixClock,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hw, he, hi,
      he1, he4, he7, hi1, hi4, hi7, BitVec.lt_def, hgw, hhw, hhg, hal,
      ht, halB, hcancel]
  all_goals try constructor
  all_goals
    apply regs_ext
    intro key
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    split_ifs <;> simp_all [BitVec.add_comm]

namespace SetNewTriggerSupport
/-- Codec witness for the actual native evaluator state; no duplicate carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness
end SetNewTriggerSupport

/-- Full original evaluation inversion, retaining all guards, binder order,
three existential word_loc witnesses and ordered register/store updates. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_SetNewTrigger {width : Nat} [NeZero width] {C F : Type}
    {endhReg ibReg : Nat} {gs : List Nat}
    {s newState : StackSemStateFiniteExact width C F} {res : Option (StackSemResult width)} :
    evaluate (setNewTrigger endhReg ibReg gs, s) = (res, newState) →
    ∀ (ib endh w : BitVec width),
      goodDimindex width ∧ s.useStore = true ∧ [1,4,7,ibReg,endhReg].Nodup ∧
      s.regs.lookup ibReg = some (.word ib) ∧
      s.regs.lookup endhReg = some (.word endh) ∧
      s.store.lookup .allocSize = some (.word w) →
      ∃ r7 r1 r4, res = none ∧
        newState = {s with
          regs := ((s.regs.updateEq (1,r1)).updateEq (7,r7)).updateEq (4,r4)
          store := s.store.updateEq (.triggerGC,.word (ib + newTrig (endh-ib) w gs))} := by
  rintro heval ib endh w ⟨hdim, hu, hd, hi, he, hw⟩
  obtain ⟨r7,r1,r4,hr⟩ := setNewTrigger_run s endhReg ibReg endh ib w gs hdim hu hd he hi hw
  exact ⟨r7,r1,r4,Prod.mk.inj (heval.symm.trans hr)⟩

end Flapjack.Compiler.Backend.StackAlloc
