import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveData
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveList

/-!
# Partial generational data simulation

Full original `word_gen_gc_partial_move_data_code_thm`
(`stack_allocProofScript.sml:4124`). The loop body uses the existing exact
partial-list simulation; the header-data branch shares the native body lemma.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)

/-- The `word_gen_gc_partial_move_data_code` loop entry: the `While` test of register 3
against register 8. -/
theorem wordGenGcPartialMoveDataCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGenGcPartialMoveDataCode conf : HolProg width) =
      .loop (.ite .notEqual 3 (.reg 8)
        (.seq (loadInst 7 8)
          (.ite .test 7 (.imm 4)
            (.seq (rightShiftInst 7 (width - conf.lenSize))
              (.seq (addBytesInWordInst 8) (wordGenGcPartialMoveListCode conf)))
            (.seq (rightShiftInst 7 (width - conf.lenSize))
              (.seq (add1Inst 7)
                (.seq (leftShiftInst 7 (wordShiftAmount width)) (addInst 8 7))))))
        (.break 0)) := rfl

theorem wordGenGcPartialMoveDataCode_run {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (old gs rs : BitVec width) :
    ∀ (k : Nat) (ha i pa i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveData conf k (ha, i, pa, old, s.memory, s.mdomain, gs, rs) =
        (i2, pa2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      s.store.lookup (.temp 0) = some (.word gs) →
      s.store.lookup (.temp 1) = some (.word rs) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      ∃ ck r0 r1 r2 r5 r6 r7,
        evaluate (wordGenGcPartialMoveDataCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ha i pa i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7
    h8
  rw [wordGenGcPartialMoveData] at hm
  by_cases hp : ha = pa
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, -⟩ := hm
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r0, r1, r2, r5, r6, r7, ?_⟩
    rw [wordGenGcPartialMoveDataCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h3]
    simp [StackSemStateOps.getVarImm, getVar, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
      StackSemControl.exitLoop, h8]
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
    · subst k7; simp [hr7]
    by_cases k8 : k = 8
    · subst k8; simp [h8]
    simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]
  have hk : k ≠ 0 := by
    intro hk; subst hk; simp [hp] at hm
  simp only [hp, hk, if_false] at hm
  have hpb : (!(pa == ha)) = true := by simpa using Ne.symm hp
  by_cases hb : (wordSemTheWord (s.memory ha)).getLsbD 2 = true
  · simp only [hb, if_true] at hm
    generalize hrec : wordGenGcPartialMoveData conf (k - 1) (ha + (decodeLength conf
      (wordSemTheWord (s.memory ha)) + 1) * wordSemBytesInWord, i, pa, old, s.memory,
      s.mdomain, gs, rs) = R at hm
    obtain ⟨i3, pa3, m3, c3⟩ := R
    simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl⟩ := hm
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hrec hb
    simp only [wordSemTheWord] at hrec hb
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (ha + (decodeLength conf x + 1) * wordSemBytesInWord))
        (setVar 7 (.word ((decodeLength conf x + 1) * wordSemBytesInWord)) s)
    obtain ⟨ck, r0, r1, r2, r5, r6, r7, hr⟩ := ih (k - 1) (by omega) _ i pa i3 pa3
      m3 s5 hrec hcurr huse hgs hrs
      (by simpa [s5, setVar, FUPDATE_HOL] using h0) (by simpa [s5, setVar, FUPDATE_HOL] using h1)
      (by simpa [s5, setVar, FUPDATE_HOL] using h2) (by simp [s5, setVar, FUPDATE_HOL, h3])
      (by simp [s5, setVar, FUPDATE_HOL, h4]) (by simpa [s5, setVar, FUPDATE_HOL] using h5)
      (by simpa [s5, setVar, FUPDATE_HOL] using h6) (by simp [s5, setVar, FUPDATE_HOL])
      (by simp [s5, setVar, FUPDATE_HOL])
    refine ⟨ck + 1, r0, r1, r2, r5, r6, r7, ?_⟩
    rw [wordGenGcPartialMoveDataCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [dataBody_skip conf _ { s with clock := s.clock + (ck + 1) } ha x hws hw2 hlen hshift
      h8 hdm hx hb]
    have hck : s.clock + (ck + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
      ← wordGenGcPartialMoveDataCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcPartialMoveDataCode conf, st)) ?_).trans (hr.trans ?_)
    · simp only [s5, setVar]
      congr 1
    · simp only [s5, setVar, Prod.mk.injEq, true_and]
      congr 1
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
        FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
      by_cases k7 : k = 7
      · subst k7; simp
      by_cases k8 : k = 8
      · subst k8; simp
      simp [k7, k8]
  · simp only [hb, Bool.false_eq_true, if_false] at hm
    generalize hl : wordGenGcPartialMoveList conf (ha + wordSemBytesInWord,
      decodeLength conf (wordSemTheWord (s.memory ha)), i, pa, old, s.memory,
      s.mdomain, gs, rs) = R at hm
    obtain ⟨ha3, i1, pa1, m1, c1⟩ := R
    simp only at hm
    generalize hrec : wordGenGcPartialMoveData conf (k - 1) (ha3, i1, pa1, old, m1,
      s.mdomain, gs, rs) = R2 at hm
    obtain ⟨i3, pa3, m3, c3⟩ := R2
    simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl, rfl⟩ := hm
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hb hl
    simp only [wordSemTheWord] at hb hl
    have hb' : x.getLsbD 2 = false := by simpa using hb
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
    obtain ⟨ck, q0, q1, q2, q5, q6, hL⟩ := word_gen_gc_partial_move_list_code_thm
      (decodeLength conf x) (ha + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain
      conf ha3 gs rs
      ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, hg, hgs, hrs,
        by simpa [s5, setVar, FUPDATE_HOL] using h0, by simpa [s5, setVar, FUPDATE_HOL] using h1,
        by simpa [s5, setVar, FUPDATE_HOL] using h2, by simp [s5, getVar, setVar, FUPDATE_HOL, h3],
        by simp [s5, getVar, setVar, FUPDATE_HOL, h4], by simpa [s5, setVar, FUPDATE_HOL] using h5⟩
      (by simpa [s5, setVar, FUPDATE_HOL] using h6)
      ⟨by simp [s5, getVar, setVar, FUPDATE_HOL], by simp [s5, getVar, setVar, FUPDATE_HOL]⟩
    let s6 : StackSemStateFiniteExact width C F :=
      { s5 with
        memory := m1
        regs := s5.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1),
          (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word ha3)] }
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, hr⟩ := ih (k - 1) (by omega) ha3 i1 pa1
      i3 pa3 m3 s6 hrec
      (by simp [s6, s5, setVar, hcurr])
      huse hgs hrs
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, ?_⟩
    have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hL, by simp⟩
    have hs5 : setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
        { s with clock := s.clock + (ck + ck' + 1) }) =
        { { s5 with clock := s5.clock + ck } with
          clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
      simp only [s5, setVar]
      congr 1
      omega
    rw [wordGenGcPartialMoveDataCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [dataBody_list conf _ { s with clock := s.clock + (ck + ck' + 1) } ha x hw2 hlen
      h8 hdm hx hb', hs5, hadd]
    have hs5c : s5.clock = s.clock := rfl
    have hmin : min (s.clock + (ck + ck' + 1)) (s5.clock + (ck' + 1)) = s5.clock + (ck' + 1) := by
      omega
    have hck : s5.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGenGcPartialMoveDataCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcPartialMoveDataCode conf, st)) ?_).trans (hr.trans ?_)
    · congr 1
    · simp only [s6, s5, setVar, Prod.mk.injEq, true_and]
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

namespace GenPartialMoveDataSupport

/-- Canonical codec for the actual StackSem finite-map state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GenPartialMoveDataSupport

/-- Full original partial-data simulation statement, source-reviewed with
the unused HOL existential types retained. Original HOL parses `t0 : δ`
and `t1 : ε`, independently of the state word-location carrier. HOL types are
inhabited; the explicit `Nonempty` instances below preserve that interpretation
for arbitrary Lean carriers instead of dropping or specializing the binders.
HOL type variables range over nonempty carriers; these instances are the
standard type interpretation, not an operational premise or another data
representation translation. `conf`, `gs`, and `rs` are free in the original source and remain
implicit parameters. All four original curried premise groups are retained. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_partial_move_data_code_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_gen_gc_partial_move_data_code_thm {width : Nat} [NeZero width]
    {C F D E : Type} [Nonempty D] [Nonempty E]
    {conf : Config} {gs rs : BitVec width} :
    ∀ (k : Nat) (ha1 i1 pa1 old1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (dm1 : BitVec width → Bool) (c1 : Bool) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveData conf k (ha1, i1, pa1, old1, m1, dm1, gs, rs) =
          (i2, pa2, m2, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old1) ∧ s.useStore = true ∧
        s.memory = m1 ∧ s.mdomain = dm1 ∧ goodDimindex width ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧
        s.store.lookup (.temp 1) = some (.word rs) ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa1) ∧ getVar 4 s = some (.word i1) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      getVar 8 s = some (.word ha1) ∧ c1 = true →
      ∃ ck r0 r1 r2 r5 r6 r7, ∃ (_t0 : D) (_t1 : E),
        evaluate (wordGenGcPartialMoveDataCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  rintro k ha1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 s
    ⟨hm, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, hg, hgs, hrs,
      h0, h1, h2, h3, h4, h5⟩ h6 h7 ⟨h8, -⟩
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, he⟩ :=
    wordGenGcPartialMoveDataCode_run hsl hws hw2 hlen hg hshift old1 gs rs k ha1 i1 pa1
      i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 (by simpa [getVar] using h3)
      (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)
  obtain ⟨t0⟩ := ‹Nonempty D›
  obtain ⟨t1⟩ := ‹Nonempty E›
  exact ⟨ck, r0, r1, r2, r5, r6, r7, t0, t1, he⟩

end Flapjack.Compiler.Backend.StackAlloc
