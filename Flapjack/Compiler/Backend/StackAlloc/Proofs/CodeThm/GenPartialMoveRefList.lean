import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveLoop
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveList

/-!
# `stack_allocProof` `word_gen_gc_partial_move_ref_list_code_thm`

`word_gen_gc_partial_move_ref_list_code_thm` of
`cakeml/compiler/backend/proofs/stack_allocProofScript.sml` (3899-3990). The
stackLang `word_gen_gc_partial_move_ref_list_code` loop run by the exact StackSem
`evaluate` simulates `word_gen_gc_partial_move_ref_list`. As in HOL, the proof is
a complete induction on the fuel `k`; each reference block's payload is moved by
`word_gen_gc_partial_move_list_code_thm`, composed with the induction hypothesis
through `evaluate_add_clock`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)

/-- The `word_gen_gc_partial_move_ref_list_code` loop entry: the `While` test
comparing registers 9 and 8. -/
theorem wordGenGcPartialMoveRefListCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGenGcPartialMoveRefListCode conf : HolProg width) =
      .loop (.ite .notEqual 9 (.reg 8)
        (.seq (loadInst 7 8) (.seq (rightShiftInst 7 (width - conf.lenSize))
          (.seq (addBytesInWordInst 8) (wordGenGcPartialMoveListCode conf))))
        (.break 0)) := rfl

/-- One loop body on a reference header word `x`: register 7 receives the decoded
length and register 8 the first payload address before the payload move `G`. -/
theorem refListBody_eval {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (G : HolProg width) (S : StackSemStateFiniteExact width C F) (pb x : BitVec width)
    (hlen : conf.lenSize ≠ 0)
    (h8 : S.regs.lookup 8 = some (.word pb)) (hdm : S.mdomain pb = true)
    (hx : S.memory pb = .word x) :
    evaluate (.seq (loadInst 7 8) (.seq (rightShiftInst 7 (width - conf.lenSize))
      (.seq (addBytesInWordInst 8) G)), S) =
      evaluate (G, setVar 8 (.word (pb + wordSemBytesInWord))
        (setVar 7 (.word (decodeLength conf x)) S)) := by
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have hlm : (width - conf.lenSize) % 2 ^ width = width - conf.lenSize :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show width - conf.lenSize ≤ width by omega) hpow)
  have hl_le : ¬ width ≤ width - conf.lenSize := by
    have : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    omega
  have hdec : x >>> (width - conf.lenSize) = decodeLength conf x := rfl
  have hsh : evaluate (rightShiftInst 7 (width - conf.lenSize), setVar 7 (S.memory pb) S) =
      (none, setVar 7 (.word (decodeLength conf x)) S) := by
    simp [evaluate_inst, rightShiftInst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hx,
      hlm, hl_le, wordShiftHOL, hdec]
    apply regs_ext
    intro k
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    by_cases k7 : k = 7
    · subst k7; simp
    simp [k7]
  rw [evaluate_seq_none _ _ _ _ (loadInst_eval S 7 8 pb h8 hdm) le_rfl,
    evaluate_seq_none _ _ _ _ hsh le_rfl,
    evaluate_seq_none _ _ _ _ (addBytesInWordInst_eval _ 8 pb
      (by simp [setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq, h8])) le_rfl]

/-- HOL's complete induction on the fuel `k`, with the source hypotheses. -/
theorem wordGenGcPartialMoveRefListCode_run {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (re old : BitVec width) :
    ∀ (k : Nat) (pb i pa : BitVec width) (c : Bool) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveRefList k conf (pb, i, pa, old, s.memory, s.mdomain, c, gs, rs, re) =
        (i2, pa2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word pb) →
      s.regs.lookup 9 = some (.word re) →
      ∃ ck r0 r1 r2 r5 r6 r7 r8 r9,
        evaluate (wordGenGcPartialMoveRefListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pb i pa c i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hc := wordGenGcPartialMoveRefList_ok k rs re pb pa old s.memory i gs s.mdomain conf c i2
    pa2 m2 hm
  rw [wordGenGcPartialMoveRefList] at hm
  by_cases hp : pb = re
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, -⟩ := hm
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r0, r1, r2, r5, r6, r7, .word pb, .word pb, ?_⟩
    rw [wordGenGcPartialMoveRefListCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h9]
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
    by_cases k9 : k = 9
    · subst k9; simp [h9]
    simp [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9]
  have hk : k ≠ 0 := by
    intro hk; subst hk; simp [hp] at hm
  simp only [hp, hk, if_false] at hm
  subst hc
  generalize hl : wordGenGcPartialMoveList conf (pb + wordSemBytesInWord,
    decodeLength conf (wordSemTheWord (s.memory pb)), i, pa, old, s.memory, s.mdomain, gs,
    rs) = R at hm
  obtain ⟨pb3, i1, pa1, m1, c1⟩ := R
  simp only at hm
  have hc0 := wordGenGcPartialMoveRefList_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm
  simp only [Bool.and_eq_true, Bool.true_and] at hc0
  obtain ⟨⟨hdm, hisw⟩, hc1⟩ := hc0
  subst hc1
  obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
  rw [hx] at hm hl
  simp only [wordSemTheWord] at hm hl
  let s5 : StackSemStateFiniteExact width C F :=
    setVar 8 (.word (pb + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
  obtain ⟨ck, q0, q1, q2, q5, q6, hL⟩ := word_gen_gc_partial_move_list_code_thm
    (decodeLength conf x) (pb + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain conf
    pb3 gs rs
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
        (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word pb3)] }
  obtain ⟨ck', r0, r1, r2, r5, r6, r7, r8, r9, hr⟩ := ih (k - 1) (by omega) pb3 i1 pa1 _ i2 pa2
    m2 s6 hm hcurr huse hgs hrs
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      FUPDATE_HOL, h9])
  refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, r8, r9, ?_⟩
  have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hL, by simp⟩
  have hs5 : setVar 8 (.word (pb + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
      { s with clock := s.clock + (ck + ck' + 1) }) =
      { { s5 with clock := s5.clock + ck } with
        clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
    simp only [s5, setVar]
    congr 1
    omega
  have hpb : (!(re == pb)) = true := by simpa using Ne.symm hp
  rw [wordGenGcPartialMoveRefListCode_eq, evaluate_loop, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, h9, StackSemStateOps.getVarImm, h8,
    wordSemWordCmp, wordCmpHOL, hpb]
  rw [refListBody_eval conf _ { s with clock := s.clock + (ck + ck' + 1) } pb x hlen h8 hdm hx,
    hs5, hadd]
  have hs5c : s5.clock = s.clock := rfl
  have hmin : min (s.clock + (ck + ck' + 1)) (s5.clock + (ck' + 1)) = s5.clock + (ck' + 1) := by
    omega
  have hck : s5.clock + (ck' + 1) ≠ 0 := by omega
  simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
    ← wordGenGcPartialMoveRefListCode_eq]
  refine (congrArg (fun st => evaluate (wordGenGcPartialMoveRefListCode conf, st)) ?_).trans
    (hr.trans ?_)
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
    by_cases k9 : k = 9
    · subst k9; simp
    simp [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9]

namespace GenPartialMoveRefListSupport

/-- Canonical finite-support codec of the owning StackSem state carrier, required
by the `fmap_as_finite_support` qualifier of
`word_gen_gc_partial_move_ref_list_code_thm`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GenPartialMoveRefListSupport

/-- Exact HOL `word_gen_gc_partial_move_ref_list_code_thm`
(`stack_allocProofScript.sml:3899-3990`, `[local]` in HOL), with HOL's binder
order; HOL's free `conf`, `gs` and `rs` are implicit, and its quantified
`r2a2 ib1 pb1 c1 ib2 pb2`, which the statement never mentions, are kept.
`FLOOKUP s.store`, `k IN FDOM`, `|++` and `get_var` are the canonical carrier's
lookups, `updateListEq` and `getVar`, and `Temp nw` is `WordStore.temp n`; the
existentials `ck r0 r1 r2 r5 r6 r7 r8 r9` are kept. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml"
  "word_gen_gc_partial_move_ref_list_code_thm"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_gen_gc_partial_move_ref_list_code_thm {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width} :
    ∀ (k : Nat) (r2a1 r1a1 _r2a2 i1 pa1 _ib1 _pb1 old1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (dm1 : BitVec width → Bool) (_c1 : Bool)
      (i2 pa2 _ib2 _pb2 : BitVec width) (m2 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveRefList k conf (r1a1, i1, pa1, old1, m1, dm1, true, gs, rs, r2a1) =
          (i2, pa2, m2, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old1) ∧ s.useStore = true ∧
        s.memory = m1 ∧ s.mdomain = dm1 ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧ s.store.lookup (.temp 1) = some (.word rs) ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa1) ∧ getVar 4 s = some (.word i1) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        (s.regs.lookup 7).isSome = true ∧
        getVar 8 s = some (.word r1a1) ∧ getVar 9 s = some (.word r2a1) →
      ∃ ck r0 r1 r2 r5 r6 r7 r8 r9,
        evaluate (wordGenGcPartialMoveRefListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) := by
  rintro k r2a1 r1a1 _ i1 pa1 _ _ old1 m1 dm1 _ i2 pa2 _ _ m2 s
    ⟨hm, hsl, hws, hw2, hlen, -, hg, hshift, hcurr, huse, rfl, rfl, hgs, hrs, h0, h1, h2, h3, h4,
      h5, h6, h7, h8, h9⟩
  exact wordGenGcPartialMoveRefListCode_run hsl hws hw2 hlen hg hshift r2a1 old1 k r1a1 i1 pa1
    true i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)
    (by simpa [getVar] using h9)

end Flapjack.Compiler.Backend.StackAlloc
