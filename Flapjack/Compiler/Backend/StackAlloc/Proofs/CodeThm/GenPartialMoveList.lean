import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveList
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMove

/-!
# `stack_allocProof` `word_gen_gc_partial_move_list_code_thm`

`word_gen_gc_partial_move_list_code_thm` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (3809-3897): the
partial-collection counterpart of `word_gc_move_list_code_thm`. The stackLang
`word_gen_gc_partial_move_list_code` loop run by the exact StackSem `evaluate`
simulates `word_gen_gc_partial_move_list`. As in HOL, the proof is an induction
on the count; each iteration composes `word_gen_gc_partial_move_code_thm`
(reading the generation bounds from the unchanged `Temp 0w`/`Temp 1w` store
slots) with the induction hypothesis through `evaluate_add_clock`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst)

/-- The `word_gen_gc_partial_move_list_code` loop entry: the `While` test on register 7. -/
theorem wordGenGcPartialMoveListCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGenGcPartialMoveListCode conf : HolProg width) =
      .loop (.ite .notEqual 7 (.imm 0)
        (.seq (loadInst 5 8) (.seq (sub1Inst 7) (.seq (wordGenGcPartialMoveCode conf)
          (.seq (storeInst 5 8) (addBytesInWordInst 8))))) (.break 0)) := rfl

/-- HOL's induction on the count `n2w n`, with the source hypotheses. -/
theorem wordGenGcPartialMoveListCode_loop {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∀ (n : Nat) (a i pa old a1 i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveList conf (a, BitVec.ofNat width n, i, pa, old, s.memory, s.mdomain,
        gs, rs) = (a1, i1, pa1, m1, true) →
      n < 2 ^ width →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      s.regs.lookup 7 = some (.word (BitVec.ofNat width n)) → s.regs.lookup 8 = some (.word a) →
      ∃ ck r0 r1 r2 r5 r6,
        evaluate (wordGenGcPartialMoveListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, .word 0), (8, .word a1)] }) := by
  intro n
  induction n with
  | zero =>
      intro a i pa old a1 i1 pa1 m1 s hm _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8
      rw [show BitVec.ofNat width 0 = (0 : BitVec width) from rfl,
        wordGenGcPartialMoveList_zero] at hm
      simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hm
      obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
      obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
      obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
      obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
      obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
      refine ⟨0, r0, r1, r2, r5, r6, ?_⟩
      rw [wordGenGcPartialMoveListCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
      simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h7]
      simp [StackSemStateOps.getVarImm, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
        StackSemControl.exitLoop]
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
      by_cases k0 : k = 0
      · subst k0; simp [hr0]
      by_cases k1 : k = 1
      · subst k1; simp [hr1]
      by_cases k2 : k = 2
      · subst k2; simp [hr2]
      by_cases k3 : k = 3
      · subst k3; simp [h3]
      by_cases k4 : k = 4
      · subst k4; simp [h4]
      by_cases k5 : k = 5
      · subst k5; simp [hr5]
      by_cases k6 : k = 6
      · subst k6; simp [hr6]
      by_cases k7 : k = 7
      · subst k7; simp [h7]
      by_cases k8 : k = 8
      · subst k8; simp [h8]
      simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]
  | succ n ih =>
      intro a i pa old a1 i1 pa1 m1 s hm hlt hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8
      have hne : BitVec.ofNat width (n + 1) ≠ 0 := by
        intro h
        have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt hlt] at this
      have hpred : BitVec.ofNat width (n + 1) - 1 = BitVec.ofNat width n := by
        rw [BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
      rw [wordGenGcPartialMoveList_suc, if_neg hne] at hm
      simp only at hm
      generalize hmv : wordGenGcPartialMove conf (s.memory a, i, pa, old, s.memory, s.mdomain,
        gs, rs) = R1 at hm
      obtain ⟨w1, i1', pa1', m1', c1⟩ := R1
      simp only at hm
      generalize hrec : wordGenGcPartialMoveList conf (a + wordSemBytesInWord,
        BitVec.ofNat width n, i1', pa1', old, gcUpdate a w1 m1', s.mdomain, gs, rs) = R2 at hm
      obtain ⟨a2, i2, pa2, m2, c2⟩ := R2
      simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
      obtain ⟨rfl, rfl, rfl, rfl, hda, hc1, hc2⟩ := hm
      subst hc1 hc2
      -- the state entering `word_gen_gc_partial_move_code`
      let SB : StackSemStateFiniteExact width C F :=
        setVar 7 (.word (BitVec.ofNat width n)) (setVar 5 (s.memory a) s)
      obtain ⟨ck, r0, r1, r2, r6, hgc⟩ := word_gen_gc_partial_move_code_thm (s := SB)
        ⟨hmv, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, hg,
          by simpa [SB, setVar, FUPDATE_HOL] using h0, by simpa [SB, setVar, FUPDATE_HOL] using h1,
          by simpa [SB, setVar, FUPDATE_HOL] using h2, by simp [SB, getVar, setVar, FUPDATE_HOL, h3],
          by simp [SB, getVar, setVar, FUPDATE_HOL, h4], by simp [SB, getVar, setVar, FUPDATE_HOL],
          hgs, hrs,
          by simpa [SB, setVar, FUPDATE_HOL] using h1, by simpa [SB, setVar, FUPDATE_HOL] using h2,
          by simpa [SB, setVar, FUPDATE_HOL] using h6⟩
      -- the state the next iteration starts from
      let t : StackSemStateFiniteExact width C F :=
        setVar 8 (.word (a + wordSemBytesInWord))
          { SB with
            memory := gcUpdate a w1 m1'
            regs := SB.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1'),
              (4, .word i1'), (5, w1), (6, r6)] }
      obtain ⟨ck', r0', r1', r2', r5', r6', hr⟩ := ih (a + wordSemBytesInWord) i1' pa1' old
        a2 i2 pa2 m2 t hrec (by omega) hcurr huse hgs hrs
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, SB, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq,
          FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL])
      refine ⟨ck + ck' + 1, r0', r1', r2', r5', r6', ?_⟩
      -- `word_gen_gc_partial_move_code_thm` run with the `ck' + 1` clock the rest of the loop
      -- needs
      have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hgc, by simp⟩
      have hsb : setVar 7 (.word (BitVec.ofNat width (n + 1) - 1))
          (setVar 5 (s.memory a) { s with clock := s.clock + (ck + ck' + 1) }) =
          { { SB with clock := SB.clock + ck } with
            clock := { SB with clock := SB.clock + ck }.clock + (ck' + 1) } := by
        simp only [SB, setVar, hpred]
        congr 1
        omega
      have hbody : evaluate (.seq (loadInst 5 8) (.seq (sub1Inst 7)
          (.seq (wordGenGcPartialMoveCode conf) (.seq (storeInst 5 8) (addBytesInWordInst 8)))),
          { s with clock := s.clock + (ck + ck' + 1) }) =
          (none, { t with clock := t.clock + (ck' + 1) }) := by
        rw [evaluate_seq_none _ _ _ _
            (loadInst_eval { s with clock := s.clock + (ck + ck' + 1) } 5 8 a h8 hda) (by simp only [setVar]; exact Nat.le_refl _),
          evaluate_seq_none _ _ _ _
            (sub1Inst_eval (setVar 5 (s.memory a) { s with clock := s.clock + (ck + ck' + 1) }) 7
              (BitVec.ofNat width (n + 1))
              (by simp [setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq, h7])) (by simp only [setVar]; exact Nat.le_refl _),
          hsb, evaluate_seq_none _ _ _ _ hadd (by simp [SB, setVar]),
          evaluate_seq_none _ _ _ _ (storeInst_eval _ 5 8 a w1 ?_ ?_ ?_) (by exact Nat.le_refl _),
          addBytesInWordInst_eval _ 8 a ?_]
        all_goals first
          | rfl
          | exact hda
          | simp [SB, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
              FUPDATE_HOL, h8]
      rw [wordGenGcPartialMoveListCode_eq, evaluate_loop, evaluate_ite]
      simp only [getVar, HolRegImm.toWordRegImm, h7, StackSemStateOps.getVarImm, wordSemWordCmp,
        wordCmpHOL]
      have hcmp : (!(BitVec.ofNat width (n + 1) == 0)) = true := by simpa using hne
      simp only [hcmp]
      rw [hbody]
      have htc : t.clock = s.clock := rfl
      have hmin : min (s.clock + (ck + ck' + 1)) (t.clock + (ck' + 1)) = t.clock + (ck' + 1) := by
        omega
      have hck : t.clock + (ck' + 1) ≠ 0 := by omega
      simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
        ← wordGenGcPartialMoveListCode_eq]
      refine (congrArg (fun st => evaluate (wordGenGcPartialMoveListCode conf, st)) ?_).trans
        (hr.trans ?_)
      · congr 1
      · simp only [t, SB, setVar, Prod.mk.injEq, true_and]
        congr 1
        apply regs_ext
        intro k
        simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
          FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
        by_cases k0 : k = 0
        · subst k0; simp
        by_cases k1 : k = 1
        · subst k1; simp
        by_cases k2 : k = 2
        · subst k2; simp
        by_cases k3 : k = 3
        · subst k3; simp
        by_cases k4 : k = 4
        · subst k4; simp
        by_cases k5 : k = 5
        · subst k5; simp
        by_cases k6 : k = 6
        · subst k6; simp
        by_cases k7 : k = 7
        · subst k7; simp
        by_cases k8 : k = 8
        · subst k8; simp
        simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]

namespace GenPartialMoveListSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of `word_gen_gc_partial_move_list_code_thm`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GenPartialMoveListSupport

/-- Exact HOL `word_gen_gc_partial_move_list_code_thm`
(`stack_allocProofScript.sml:3809-3897`), with HOL's binder order and its three
curried premise groups. `FLOOKUP s.store`, `k IN FDOM`, `|++` and `get_var` are
the canonical carrier's lookups, `updateListEq` and `getVar`, and `Temp nw` is
`WordStore.temp n`; the existentials `ck r0 r1 r2 r5 r6` are kept. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem word_gen_gc_partial_move_list_code_thm {width : Nat} [NeZero width] {C F : Type} :
    ∀ (l a : BitVec width) (s : StackSemStateFiniteExact width C F) (pa1 pa old : BitVec width)
      (m1 m : BitVec width → WordLocW width) (i1 i : BitVec width) (dm : BitVec width → Bool)
      (conf : Config) (a1 gs rs : BitVec width),
      wordGenGcPartialMoveList conf (a, l, i, pa, old, m, dm, gs, rs) =
          (a1, i1, pa1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ goodDimindex width ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧ s.store.lookup (.temp 1) = some (.word rs) ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      getVar 7 s = some (.word l) ∧ getVar 8 s = some (.word a) →
      ∃ ck r0 r1 r2 r5 r6,
        evaluate (wordGenGcPartialMoveListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, .word 0), (8, .word a1)] }) := by
  rintro l a s pa1 pa old m1 m i1 i dm conf a1 gs rs
    ⟨hm, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, hg, hgs, hrs, h0, h1, h2, h3, h4,
      h5⟩ h6 ⟨h7, h8⟩
  have hl : l = BitVec.ofNat width l.toNat := by simp
  rw [hl] at hm h7
  exact wordGenGcPartialMoveListCode_loop hsl hws hw2 hlen hg hshift l.toNat a i pa old a1 i1 pa1
    m1 s hm l.isLt hcurr huse hgs hrs h0 h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 (by simpa [getVar] using h7) (by simpa [getVar] using h8)

end Flapjack.Compiler.Backend.StackAlloc
