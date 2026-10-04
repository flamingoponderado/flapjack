import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveData
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveRefList

/-!
# Full generational reference-block simulation

Counterpart of `stack_allocProofScript.sml:4243`:
`word_gen_gc_move_refs_code_thm`. Each reference header supplies its payload
length, the native field mover processes that payload, and `Temp 4w` restores
register 0 before the recursive reference loop. The full theorem follows the original complete fuel induction.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst rightShiftInst)

/-- Exact native loop entry and its trailing restoration of register 0. -/
theorem wordGenGcMoveRefsCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGenGcMoveRefsCode conf : HolProg width) =
      .loop (.ite .notEqual 0 (.reg 8)
        (.seq (loadInst 7 8) (.seq (rightShiftInst 7 (width - conf.lenSize))
          (.seq (addBytesInWordInst 8)
            (.seq (wordGenGcMoveListCode conf) (.get 0 (.temp 4))))))
        (.break 0)) := rfl

/-- Source-directed reference-body decomposition, using the same exact native
header load/length/address transitions as the partial reference loop. -/
theorem refsBody_eval {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (S : StackSemStateFiniteExact width C F) (pb x : BitVec width)
    (hlen : conf.lenSize ≠ 0)
    (h8 : S.regs.lookup 8 = some (.word pb)) (hdm : S.mdomain pb = true)
    (hx : S.memory pb = .word x) :
    evaluate (.seq (loadInst 7 8) (.seq (rightShiftInst 7 (width - conf.lenSize))
      (.seq (addBytesInWordInst 8)
        (.seq (wordGenGcMoveListCode conf) (.get 0 (.temp 4))))), S) =
      evaluate (.seq (wordGenGcMoveListCode conf) (.get 0 (.temp 4)),
        setVar 8 (.word (pb + wordSemBytesInWord))
          (setVar 7 (.word (decodeLength conf x)) S)) :=
  refListBody_eval conf _ S pb x hlen h8 hdm hx

/-- The source loop restores its end bound from the unchanged `Temp 4w` slot. -/
theorem refsRestore_eval {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (re : BitVec width)
    (huse : s.useStore = true) (hbound : s.store.lookup (.temp 4) = some (.word re)) :
    evaluate ((.get 0 (.temp 4) : HolProg width), s) =
      (none, setVar 0 (.word re) s) := by
  rw [evaluate_get]
  simp only [huse, StackSemRegisterTransfers.storeOfSyntax]
  change (match s.store.lookup (.temp 4) with
    | some x => (none, setVar 0 x s)
    | none => (some StackSemResult.error, s)) = (none, setVar 0 (.word re) s)
  rw [hbound]

/-- Updating the four native field-mover temporary slots preserves the loop's
separate end-bound slot. This is infrastructure for the full simulation, not a
standalone HOL theorem port. -/
theorem refsTemps_preserve_bound {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (t0 t1 : WordLocW width) (pb ib re : BitVec width)
    (hbound : store.lookup (.temp 4) = some (.word re)) :
    (store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb),
      (.temp 3, .word ib)]).lookup (.temp 4) = some (.word re) := by
  simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]
  exact hbound

/-- Full source-directed fuel induction for the generational reference loop. -/
theorem wordGenGcMoveRefsCode_run {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (re old : BitVec width) :
    ∀ (k : Nat) (ha i pa ib pb ha2 i2 pa2 ib2 pb2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveRefs conf k (ha, re, i, pa, ib, pb, old, s.memory, s.mdomain) =
        (ha2, i2, pa2, ib2, pb2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      s.store.lookup (.temp 4) = some (.word re) →
      s.regs.lookup 0 = some (.word re) → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      ∃ ck r1 r2 r5 r6 r7 t0 t1,
        evaluate (wordGenGcMoveRefsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb2),
              (.temp 3, .word ib2)]
            regs := s.regs.updateListEq [(0, .word re), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word ha2)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ha i pa ib pb ha2 i2 pa2 ib2 pb2 m2 s hm hcurr huse ht0 ht1 ht2 ht3 ht4 h0 h1 h2 h3 h4
    h5 h6 h7 h8
  rw [wordGenGcMoveRefs] at hm
  by_cases hp : ha = re
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hm
    obtain ⟨t0, hrt0⟩ := Option.isSome_iff_exists.1 ht0
    obtain ⟨t1, hrt1⟩ := Option.isSome_iff_exists.1 ht1
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r1, r2, r5, r6, r7, t0, t1, ?_⟩
    rw [genGcMove_skip_store s t0 t1 _ _ hrt0 hrt1 ht2 ht3]
    rw [wordGenGcMoveRefsCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h0]
    simp [StackSemStateOps.getVarImm, getVar, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
      StackSemControl.exitLoop, h8]
    apply regs_ext
    intro k
    simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
    by_cases k0 : k = 0
    · subst k0; simp [h0]
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
  have hpb : (!(re == ha)) = true := by simpa using Ne.symm hp
  generalize hl : wordGenGcMoveList conf (ha + wordSemBytesInWord,
    decodeLength conf (wordSemTheWord (s.memory ha)), i, pa, ib, pb, old, s.memory,
    s.mdomain) = R at hm
  obtain ⟨ha3, i1, pa1, ib1, pb1, m1, c1⟩ := R
  simp only at hm
  generalize hrec : wordGenGcMoveRefs conf (k - 1) (ha3, re, i1, pa1, ib1, pb1, old, m1,
    s.mdomain) = R2 at hm
  obtain ⟨ha4, i3, pa3, ib3, pb3, m3, c3⟩ := R2
  simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl, rfl⟩ := hm
  obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
  rw [hx] at hl
  simp only [wordSemTheWord] at hl
  let s5 : StackSemStateFiniteExact width C F :=
    setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
  obtain ⟨ck, q0, q1, q2, q5, q6, g0, g1, hL⟩ := word_gen_gc_move_list_code_thm
    (decodeLength conf x) (ha + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain
    conf ha3 ib ib1 pb pb1
    ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, ht0, ht1, ht2, ht3,
      by simp [s5, setVar, FUPDATE_HOL, h0], by simpa [s5, setVar, FUPDATE_HOL] using h1,
      by simpa [s5, setVar, FUPDATE_HOL] using h2, by simp [s5, getVar, setVar, FUPDATE_HOL, h3],
      by simp [s5, getVar, setVar, FUPDATE_HOL, h4], by simpa [s5, setVar, FUPDATE_HOL] using h5⟩
    (by simpa [s5, setVar, FUPDATE_HOL] using h6)
    ⟨by simp [s5, getVar, setVar, FUPDATE_HOL], by simp [s5, getVar, setVar, FUPDATE_HOL]⟩
  let s6 : StackSemStateFiniteExact width C F :=
    { s5 with
      memory := m1
      store := s5.store.updateListEq [(.temp 0, g0), (.temp 1, g1), (.temp 2, .word pb1),
        (.temp 3, .word ib1)]
      regs := s5.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1),
        (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word ha3)] }
  let s7 : StackSemStateFiniteExact width C F := setVar 0 (.word re) s6
  have hLG : evaluate (.seq (wordGenGcMoveListCode conf) (.get 0 (.temp 4)),
      { s5 with clock := s5.clock + ck }) = (none, s7) := by
    rw [evaluate_seq_none _ _ _ _ hL (by change s5.clock ≤ s5.clock + ck; omega)]
    exact refsRestore_eval s6 re huse (refsTemps_preserve_bound s5.store g0 g1 pb1 ib1 re ht4)
  obtain ⟨ck', r1, r2, r5, r6, r7, u0, u1, hr⟩ := ih (k - 1) (by omega) ha3 i1 pa1 ib1 pb1
    ha4 i3 pa3 ib3 pb3 m3 s7 hrec
    (by simp [s7, s6, s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      FUPDATE_HOL, hcurr])
    huse
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (refsTemps_preserve_bound s5.store g0 g1 pb1 ib1 re ht4)
    (by simp [s7, setVar, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
  refine ⟨ck + ck' + 1, r1, r2, r5, r6, r7, u0, u1, ?_⟩
  have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hLG, by simp⟩
  have hs5 : setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
      { s with clock := s.clock + (ck + ck' + 1) }) =
      { { s5 with clock := s5.clock + ck } with
        clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
    simp only [s5, setVar]
    congr 1
    omega
  rw [wordGenGcMoveRefsCode_eq, evaluate_loop, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, h0, StackSemStateOps.getVarImm, h8,
    wordSemWordCmp, wordCmpHOL, hpb]
  rw [refsBody_eval conf { s with clock := s.clock + (ck + ck' + 1) } ha x hlen
    h8 hdm hx, hs5, hadd]
  have hs7c : s7.clock = s.clock := rfl
  have hmin : min (s.clock + (ck + ck' + 1)) (s7.clock + (ck' + 1)) = s7.clock + (ck' + 1) := by
    omega
  have hck : s7.clock + (ck' + 1) ≠ 0 := by omega
  simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
    ← wordGenGcMoveRefsCode_eq]
  refine (congrArg (fun st => evaluate (wordGenGcMoveRefsCode conf, st)) ?_).trans (hr.trans ?_)
  · congr 1
  · simp only [s7, s6, s5, setVar, Prod.mk.injEq, true_and]
    rw [temps_updateListEq_twice]
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

namespace GenGcMoveRefsSupport

/-- Canonical codec for the actual finite-support StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GenGcMoveRefsSupport

/-- Full original `word_gen_gc_move_refs_code_thm` (4243-4345), with original
binder order and all four curried premise groups. The original free `conf` is
implicit and its unused quantified Boolean `c1` and premise are retained.
The conclusion has the original four temporary-slot updates and nine register
updates, including register 0 restored to `r1a1` and register 8 set to `r2a2`.
`Temp 4w` is not changed by the field mover. There is no additional dimension,
simulation or target-evaluation premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem word_gen_gc_move_refs_code_thm {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} :
    ∀ (k : Nat) (r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (dm1 : BitVec width → Bool) (c1 : Bool)
      (i2 pa2 ib2 pb2 : BitVec width) (m2 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveRefs conf k (r2a1, r1a1, i1, pa1, ib1, pb1, old1, m1, dm1) =
          (r2a2, i2, pa2, ib2, pb2, m2, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old1) ∧ s.useStore = true ∧
        s.memory = m1 ∧ s.mdomain = dm1 ∧
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb1) ∧
        s.store.lookup (.temp 3) = some (.word ib1) ∧
        s.store.lookup (.temp 4) = some (.word r1a1) ∧
        getVar 0 s = some (.word r1a1) ∧
        (s.regs.lookup 1).isSome = true ∧ (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa1) ∧ getVar 4 s = some (.word i1) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      getVar 8 s = some (.word r2a1) ∧ c1 = true →
      ∃ ck r1 r2 r5 r6 r7 t0 t1,
        evaluate (wordGenGcMoveRefsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb2),
              (.temp 3, .word ib2)]
            regs := s.regs.updateListEq [(0, .word r1a1), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word r2a2)] }) := by
  rintro k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2 s
    ⟨hm, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, ht0, ht1, ht2, ht3, ht4,
      h0, h1, h2, h3, h4, h5⟩ h6 h7 ⟨h8, -⟩
  exact wordGenGcMoveRefsCode_run hsl hws hw2 hlen hshift r1a1 old1 k r2a1 i1 pa1 ib1 pb1
    r2a2 i2 pa2 ib2 pb2 m2 s hm hcurr huse ht0 ht1 ht2 ht3 ht4
    (by simpa [getVar] using h0) h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)

end Flapjack.Compiler.Backend.StackAlloc
