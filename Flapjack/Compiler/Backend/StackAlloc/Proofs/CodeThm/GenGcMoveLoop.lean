import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveData
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveRefs
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveRootsBitmaps

/-!
# Generational collector loop simulation

Counterpart of `stack_allocProofScript.sml:4347-4540`. The full simulation
requires complete induction on the collector fuel, with separate data and
reference branches. The helpers below expose the actual compiled loop; they
are Flapjack proof infrastructure for HOL's inline case analysis.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord

/-- The actual outer-loop body; this merely names HOL's inline branch. -/
abbrev genLoopBody {width : Nat} [NeZero width] (conf : Config) : HolProg width :=
  .ite .equal 1 (.reg 2)
    (listSeqHOL [wordGenGcMoveDataCode conf, .get 5 (.temp 2), .get 7 (.temp 4),
      moveHOL 1 7, moveHOL 2 5, subInst 7 5])
    (listSeqHOL [moveHOL 0 1, .set (.temp 6) 8, moveHOL 8 2, .set (.temp 5) 8,
      wordGenGcMoveRefsCode conf, moveHOL 7 8, .get 1 (.temp 5), .get 2 (.temp 5),
      .set (.temp 4) 2, .get 2 (.temp 2), moveHOL 3 3, moveHOL 4 4, moveHOL 7 1,
      subInst 7 2, .get 8 (.temp 6), moveHOL 5 8, subInst 5 3, orInst 7 5])

/-- Definitional expansion of the actual generational loop, retaining both
native collector calls and the original register/store transition order. -/
theorem wordGenGcMoveLoopCode_eq {width : Nat} [NeZero width] (conf : Config) :
    (wordGenGcMoveLoopCode conf : HolProg width) =
      .loop (.ite .notTest 7 (.reg 7)
        (.ite .equal 1 (.reg 2)
          (listSeqHOL [wordGenGcMoveDataCode conf, .get 5 (.temp 2),
            .get 7 (.temp 4), moveHOL 1 7, moveHOL 2 5, subInst 7 5])
          (listSeqHOL [moveHOL 0 1, .set (.temp 6) 8, moveHOL 8 2,
            .set (.temp 5) 8, wordGenGcMoveRefsCode conf, moveHOL 7 8,
            .get 1 (.temp 5), .get 2 (.temp 5), .set (.temp 4) 2,
            .get 2 (.temp 2), moveHOL 3 3, moveHOL 4 4, moveHOL 7 1,
            subInst 7 2, .get 8 (.temp 6), moveHOL 5 8, subInst 5 3,
            orInst 7 5]))
        (.break 0)) := rfl

/-- The data branch computes the next boundary test from the new `Temp 2`
and the old `Temp 4`, after the data collector has finished. -/
theorem genLoopDataTail_eval {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pb pbx : BitVec width)
    (hu : s.useStore = true)
    (h2 : s.store.lookup (.temp 2) = some (.word pb))
    (h4 : s.store.lookup (.temp 4) = some (.word pbx)) :
    evaluate (listSeqHOL [.get 5 (.temp 2), .get 7 (.temp 4),
      moveHOL 1 7, moveHOL 2 5, subInst 7 5], s) =
      (none, setVar 7 (.word (pbx - pb))
        (setVar 2 (.word pb) (setVar 1 (.word pbx)
          (setVar 7 (.word pbx) (setVar 5 (.word pb) s))))) := by
  change s.store.lookup (.temp 2#5) = some (.word pb) at h2
  change s.store.lookup (.temp 4#5) = some (.word pbx) at h4
  simp [listSeqHOL, evaluate_seq, evaluate_get, evaluate_inst,
    StackSemRegisterTransfers.storeOfSyntax, hu, h2, h4,
    moveHOL, subInst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp,
    setVar, wordOpHOL, wordOp, fixClock,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- Before the reference collector, preserve both old boundaries in the
original temporary slots and put the reference interval in registers 0/8. -/
theorem genLoopRefsPrelude_eval {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pbx pb pax : BitVec width)
    (hu : s.useStore = true)
    (h1 : s.regs.lookup 1 = some (.word pbx))
    (h2 : s.regs.lookup 2 = some (.word pb))
    (h8 : s.regs.lookup 8 = some (.word pax)) :
    evaluate (listSeqHOL [moveHOL 0 1, .set (.temp 6) 8,
      moveHOL 8 2, .set (.temp 5) 8], s) =
      (none, setStore (.temp 5) (.word pb)
        (setVar 8 (.word pb) (setStore (.temp 6) (.word pax)
          (setVar 0 (.word pbx) s)))) := by
  simp [listSeqHOL, evaluate_seq, evaluate_inst, evaluate_set, moveHOL,
    StackSemRegisterTransfers.storeOfSyntax, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, getVar, setVar, setStore,
    hu, h1, h2, h8, fixClock, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- The reference branch restores the saved boundaries, records the previous
reference end, and tests both remaining intervals through the bitwise OR. -/
theorem genLoopRefsTail_eval {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (ha pb pb' pax pa i : BitVec width)
    (hu : s.useStore = true)
    (ht5 : s.store.lookup (.temp 5) = some (.word pb))
    (ht6 : s.store.lookup (.temp 6) = some (.word pax))
    (ht2 : s.store.lookup (.temp 2) = some (.word pb'))
    (h3 : s.regs.lookup 3 = some (.word pa))
    (h4 : s.regs.lookup 4 = some (.word i))
    (h8 : s.regs.lookup 8 = some (.word ha)) :
    evaluate (listSeqHOL [moveHOL 7 8, .get 1 (.temp 5), .get 2 (.temp 5),
      .set (.temp 4) 2, .get 2 (.temp 2), moveHOL 3 3, moveHOL 4 4,
      moveHOL 7 1, subInst 7 2, .get 8 (.temp 6), moveHOL 5 8,
      subInst 5 3, orInst 7 5], s) =
      (none, setVar 7 (.word ((pb - pb') ||| (pax - pa)))
        (setVar 5 (.word (pax - pa)) (setVar 5 (.word pax)
          (setVar 8 (.word pax) (setVar 7 (.word (pb - pb'))
            (setVar 7 (.word pb) (setVar 4 (.word i) (setVar 3 (.word pa)
              (setVar 2 (.word pb') (setStore (.temp 4) (.word pb)
                (setVar 2 (.word pb) (setVar 1 (.word pb)
                  (setVar 7 (.word ha) s))))))))))))) := by
  change s.store.lookup (.temp 5#5) = some (.word pb) at ht5
  change s.store.lookup (.temp 6#5) = some (.word pax) at ht6
  change s.store.lookup (.temp 2#5) = some (.word pb') at ht2
  have hor : OrOp.or (pb - pb') (OrOp.or (pax - pa) 0#width) =
      ((pb - pb') ||| (pax - pa)) := by
    change ((pb - pb') ||| ((pax - pa) ||| 0#width)) = _
    rw [BitVec.or_zero]
  simp [listSeqHOL, evaluate_seq, evaluate_inst, evaluate_get, evaluate_set,
    moveHOL, subInst, orInst, StackSemRegisterTransfers.storeOfSyntax,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp,
    getVar, setVar, setStore, wordOpHOL, wordOp, fixClock, hu, ht5, ht6, ht2,
    h3, h4, h8, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hor]

/-- The reference tail's test is zero precisely when both intervals are
finished; no arithmetic-range premise is needed for modular subtraction. -/
theorem genLoopBoundaryZero_iff {width : Nat} (pb pb' pax pa : BitVec width) :
    ((pb - pb') ||| (pax - pa)) = 0 ↔ pb = pb' ∧ pax = pa := by
  simp [BitVec.or_eq_zero_iff, BitVec.sub_eq_iff_eq_add]

/-- When register 7 is zero, the actual compiled loop exits without any
clock consumption or state update. -/
theorem genLoopStop_eval {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (s : StackSemStateFiniteExact width C F)
    (h7 : s.regs.lookup 7 = some (.word 0)) :
    evaluate (wordGenGcMoveLoopCode conf, s) = (none, s) := by
  have hand : AndOp.and (0#width) (0#width) = 0#width := BitVec.and_self
  rw [wordGenGcMoveLoopCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
  simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm,
    wordSemWordCmp, wordCmpHOL, h7, hand, fixClock, contLoop, StackSemControl.exitLoop]

/-- Infrastructure for the zero-iteration case: writing existing values back
through the canonical finite-map list update leaves the map unchanged. -/
private theorem genLoopUpdates_noop {K V : Type} [DecidableEq K]
    (m : HolFiniteMapExact K V) (xs : List (K × V))
    (h : ∀ e, e ∈ xs → m.lookup e.1 = some e.2) : m.updateListEq xs = m := by
  induction xs with
  | nil => apply regs_ext; intro k; rfl
  | cons e xs ih =>
    have he : m.updateEq e = m := by
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
      by_cases hk : k = e.1
      · subst k; simp [h e (by simp)]
      · simp [hk]
    have hc : m.updateListEq (e :: xs) = (m.updateEq e).updateListEq xs := by
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_cons]
      rfl
    rw [hc, he]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Full unchanged-state output shape for the zero-iteration branch, including
all seven temporary updates and all nine register updates from HOL. -/
theorem genLoopStop_output {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (s : StackSemStateFiniteExact width C F) (i pa ib pb pbx pax : BitVec width)
    (ht0 : (s.store.lookup (.temp 0)).isSome = true)
    (ht1 : (s.store.lookup (.temp 1)).isSome = true)
    (ht5 : (s.store.lookup (.temp 5)).isSome = true)
    (ht6 : (s.store.lookup (.temp 6)).isSome = true)
    (ht2 : s.store.lookup (.temp 2) = some (.word pb))
    (ht3 : s.store.lookup (.temp 3) = some (.word ib))
    (ht4 : s.store.lookup (.temp 4) = some (.word pbx))
    (h0 : (s.regs.lookup 0).isSome = true)
    (h1 : s.regs.lookup 1 = some (.word pbx))
    (h2 : s.regs.lookup 2 = some (.word pb))
    (h3 : s.regs.lookup 3 = some (.word pa))
    (h4 : s.regs.lookup 4 = some (.word i))
    (h5 : (s.regs.lookup 5).isSome = true)
    (h6 : (s.regs.lookup 6).isSome = true)
    (h7 : s.regs.lookup 7 = some (.word 0))
    (h8 : s.regs.lookup 8 = some (.word pax)) :
    ∃ r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
      evaluate (wordGenGcMoveLoopCode conf, s) =
        (none, { s with
          store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb), (.temp 3, .word ib), (.temp 4, t4),
            (.temp 5, t5), (.temp 6, t6)]
          regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa),
            (4, .word i), (5, r5), (6, r6), (7, r7), (8, r8)] }) := by
  obtain ⟨t0, ht0⟩ := Option.isSome_iff_exists.1 ht0
  obtain ⟨t1, ht1⟩ := Option.isSome_iff_exists.1 ht1
  obtain ⟨t5, ht5⟩ := Option.isSome_iff_exists.1 ht5
  obtain ⟨t6, ht6⟩ := Option.isSome_iff_exists.1 ht6
  obtain ⟨r0, h0⟩ := Option.isSome_iff_exists.1 h0
  obtain ⟨r5, h5⟩ := Option.isSome_iff_exists.1 h5
  obtain ⟨r6, h6⟩ := Option.isSome_iff_exists.1 h6
  have hs : s.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
      (.temp 2, .word pb), (.temp 3, .word ib), (.temp 4, .word pbx),
      (.temp 5, t5), (.temp 6, t6)] = s.store := by
    apply genLoopUpdates_noop
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ht0
    · exact ht1
    · exact ht2
    · exact ht3
    · exact ht4
    · exact ht5
    · exact ht6
  have hr : s.regs.updateListEq [(0, r0), (1, .word pbx), (2, .word pb),
      (3, .word pa), (4, .word i), (5, r5), (6, r6), (7, .word 0),
      (8, .word pax)] = s.regs := by
    apply genLoopUpdates_noop
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
  refine ⟨r0, .word pbx, .word pb, r5, r6, .word 0, .word pax,
    t0, t1, .word pbx, t5, t6, ?_⟩
  rw [hs, hr]
  exact genLoopStop_eval conf s h7

/-- Compose a successful actual body run with the recursive loop run. The
body equation is an intermediate proof fact supplied by the two collector
theorems, not a premise of the final HOL simulation statement. -/
theorem genLoopStep_eval {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (s t u : StackSemStateFiniteExact width C F) (tt : BitVec width)
    (ckBody ckRest : Nat) (h7 : s.regs.lookup 7 = some (.word tt)) (htt : tt ≠ 0)
    (hbody : evaluate (genLoopBody conf, { s with clock := s.clock + ckBody }) = (none, t))
    (hc : t.clock = s.clock)
    (hrest : evaluate (wordGenGcMoveLoopCode conf,
      { t with clock := t.clock + ckRest }) = (none, u)) :
    evaluate (wordGenGcMoveLoopCode conf,
      { s with clock := s.clock + (ckBody + ckRest + 1) }) = (none, u) := by
  have hadd := StackProps.evaluateAddClock (ckRest + 1) _ _ _ _ ⟨hbody, by simp⟩
  have hs : { { s with clock := s.clock + ckBody } with
      clock := (s.clock + ckBody) + (ckRest + 1) } =
      { s with clock := s.clock + (ckBody + ckRest + 1) } := by
    simp only [Nat.add_assoc]
  rw [hs] at hadd
  have hand : AndOp.and tt tt = tt := BitVec.and_self
  have hcmp : (AndOp.and tt tt != (0 : BitVec width)) = true := by
    simpa only [hand, bne_iff_ne] using htt
  change evaluate (.loop (.ite .notTest 7 (.reg 7) (genLoopBody conf) (.break 0)), _) = _
  rw [evaluate_loop, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, StackSemStateOps.getVarImm,
    h7, wordSemWordCmp, wordCmpHOL, hcmp]
  rw [hadd]
  have hm : min (s.clock + (ckBody + ckRest + 1)) (t.clock + (ckRest + 1)) =
      t.clock + (ckRest + 1) := by omega
  have hn : t.clock + (ckRest + 1) ≠ 0 := by omega
  simp only [fixClock, contLoop, hm, if_true, hn, if_false, decClock]
  change evaluate (wordGenGcMoveLoopCode conf,
    { t with clock := t.clock + (ckRest + 1) - 1 }) = _
  convert hrest using 1
  congr 1

/-- Actual data branch composition. Its collector equation and clock bound
are intermediate consequences of the full data simulation theorem. -/
theorem genLoopBodyData_eval {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (s t : StackSemStateFiniteExact width C F) (pbx pb' : BitVec width)
    (h1 : s.regs.lookup 1 = some (.word pbx))
    (h2 : s.regs.lookup 2 = some (.word pbx))
    (hdata : evaluate (wordGenGcMoveDataCode conf, s) = (none, t))
    (hclock : t.clock ≤ s.clock) (huse : t.useStore = true)
    (ht2 : t.store.lookup (.temp 2) = some (.word pb'))
    (ht4 : t.store.lookup (.temp 4) = some (.word pbx)) :
    evaluate (genLoopBody conf, s) =
      (none, setVar 7 (.word (pbx - pb'))
        (setVar 2 (.word pb') (setVar 1 (.word pbx)
          (setVar 7 (.word pbx) (setVar 5 (.word pb') t))))) := by
  rw [genLoopBody, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, StackSemStateOps.getVarImm,
    h1, h2, wordSemWordCmp, wordCmpHOL, beq_self_eq_true]
  change evaluate (.seq (wordGenGcMoveDataCode conf)
    (listSeqHOL [.get 5 (.temp 2), .get 7 (.temp 4), moveHOL 1 7,
      moveHOL 2 5, subInst 7 5]), s) = _
  rw [evaluate_seq_none _ _ _ _ hdata hclock]
  exact genLoopDataTail_eval t pb' pbx huse ht2 ht4

/-- Exact Set step used by the reference branch's saved-boundary prelude. -/
theorem genLoopSet_eval {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (slot : BitVec 5) (r : Nat)
    (w : BitVec width) (hu : s.useStore = true)
    (hr : s.regs.lookup r = some (.word w)) :
    evaluate ((.set (.temp slot) r : HolProg width), s) =
      (none, setStore (.temp slot) (.word w) s) := by
  rw [evaluate_set]
  simp [hu, getVar, hr, StackSemRegisterTransfers.storeOfSyntax]

/-- The exact state on entry to the reference collector. -/
abbrev genLoopRefsEntry {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pbx pb pax : BitVec width) :=
  setStore (.temp 5) (.word pb)
    (setVar 8 (.word pb) (setStore (.temp 6) (.word pax) (setVar 0 (.word pbx) s)))

/-- Actual reference branch composition through the full reference collector.
The intermediate collector equation is discharged by the reviewed simulation
theorem in the complete induction, rather than assumed by the final port. -/
theorem genLoopBodyRefs_eval {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (s t : StackSemStateFiniteExact width C F) (pbx pb pax ha pb' pa i : BitVec width)
    (hneq : pbx ≠ pb) (huse : s.useStore = true)
    (h1 : s.regs.lookup 1 = some (.word pbx))
    (h2 : s.regs.lookup 2 = some (.word pb))
    (h8 : s.regs.lookup 8 = some (.word pax))
    (hrefs : evaluate (wordGenGcMoveRefsCode conf, genLoopRefsEntry s pbx pb pax) = (none, t))
    (hclock : t.clock ≤ s.clock) (huse' : t.useStore = true)
    (ht5 : t.store.lookup (.temp 5) = some (.word pb))
    (ht6 : t.store.lookup (.temp 6) = some (.word pax))
    (ht2 : t.store.lookup (.temp 2) = some (.word pb'))
    (h3' : t.regs.lookup 3 = some (.word pa))
    (h4' : t.regs.lookup 4 = some (.word i))
    (h8' : t.regs.lookup 8 = some (.word ha)) :
    evaluate (genLoopBody conf, s) =
      (none, setVar 7 (.word ((pb - pb') ||| (pax - pa)))
        (setVar 5 (.word (pax - pa)) (setVar 5 (.word pax)
          (setVar 8 (.word pax) (setVar 7 (.word (pb - pb'))
            (setVar 7 (.word pb) (setVar 4 (.word i) (setVar 3 (.word pa)
              (setVar 2 (.word pb') (setStore (.temp 4) (.word pb)
                (setVar 2 (.word pb) (setVar 1 (.word pb)
                  (setVar 7 (.word ha) t))))))))))))) := by
  have hcmp : (pbx == pb) = false := by simpa using hneq
  rw [genLoopBody, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, StackSemStateOps.getVarImm,
    h1, h2, wordSemWordCmp, wordCmpHOL, hcmp]
  change evaluate (.seq (moveHOL 0 1) (.seq (.set (.temp 6) 8)
    (.seq (moveHOL 8 2) (.seq (.set (.temp 5) 8)
      (.seq (wordGenGcMoveRefsCode conf) (listSeqHOL _))))), s) = _
  rw [evaluate_seq_none _ _ _ _ (moveHOL_eval s 0 1 pbx h1) le_rfl]
  rw [evaluate_seq_none _ _ _ _ (genLoopSet_eval (setVar 0 (.word pbx) s) 6 8 pax huse
    (by simp [setVar, FUPDATE_HOL, h8])) le_rfl]
  rw [evaluate_seq_none _ _ _ _ (moveHOL_eval
    (setStore (.temp 6) (.word pax) (setVar 0 (.word pbx) s)) 8 2 pb
    (by simp [setStore, setVar, FUPDATE_HOL, h2])) le_rfl]
  rw [evaluate_seq_none _ _ _ _ (genLoopSet_eval
    (setVar 8 (.word pb) (setStore (.temp 6) (.word pax) (setVar 0 (.word pbx) s)))
    5 8 pb huse
    (by simp [setVar, FUPDATE_HOL])) le_rfl]
  rw [evaluate_seq_none _ _ _ _ hrefs hclock]
  exact genLoopRefsTail_eval t ha pb pb' pax pa i huse' ht5 ht6 ht2 h3' h4' h8'

/-- Peel a successful data branch of the original shallow collector. Both
success flags and the strict fuel decrease follow from its actual equation. -/
theorem genLoopSource_data {width : Nat} [NeZero width] (conf : Config)
    (k : Nat) (pax i pa ib pb old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
    (hpa : pax ≠ pa)
    (h : wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pb, old, m, dm) =
      (i1, pa1, ib1, pb1, m1, true)) :
    ∃ i' pa' ib' pb' m', k ≠ 0 ∧
      wordGenGcMoveData conf (2 ^ width) (pax, i, pa, ib, pb, old, m, dm) =
        (i', pa', ib', pb', m', true) ∧
      wordGenGcMoveLoop conf (k - 1) (pa', i', pa', ib', pb', pb, old, m', dm) =
        (i1, pa1, ib1, pb1, m1, true) := by
  rw [wordGenGcMoveLoop] at h
  simp only [if_true, hpa, if_false] at h
  generalize hd : wordGenGcMoveData conf (2 ^ width) (pax, i, pa, ib, pb, old, m, dm) = D at h
  obtain ⟨i', pa', ib', pb', m', cd⟩ := D
  simp only at h
  have hk : k ≠ 0 := by
    intro hk
    simp [hk] at h
  simp only [hk, if_false] at h
  generalize hr : wordGenGcMoveLoop conf (k - 1)
    (pa', i', pa', ib', pb', pb, old, m', dm) = R at h
  obtain ⟨ir, par, ibr, pbr, mr, cr⟩ := R
  simp only [Prod.mk.injEq, Bool.and_eq_true] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hcd, hcr⟩ := h
  refine ⟨i', pa', ib', pb', m', hk, ?_, ?_⟩
  · simp only [hcd]
  · simpa only [hcr] using hr

/-- Peel a successful reference branch of the original shallow collector,
including its original pre-call `pb` as the recursive reference-start bound. -/
theorem genLoopSource_refs {width : Nat} [NeZero width] (conf : Config)
    (k : Nat) (pax i pa ib pb pbx old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
    (hpb : pbx ≠ pb)
    (h : wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, m, dm) =
      (i1, pa1, ib1, pb1, m1, true)) :
    ∃ ha i' pa' ib' pb' m', k ≠ 0 ∧
      wordGenGcMoveRefs conf (2 ^ width) (pb, pbx, i, pa, ib, pb, old, m, dm) =
        (ha, i', pa', ib', pb', m', true) ∧
      wordGenGcMoveLoop conf (k - 1) (pax, i', pa', ib', pb', pb, old, m', dm) =
        (i1, pa1, ib1, pb1, m1, true) := by
  rw [wordGenGcMoveLoop] at h
  simp only [hpb, if_false] at h
  generalize hd : wordGenGcMoveRefs conf (2 ^ width)
    (pb, pbx, i, pa, ib, pb, old, m, dm) = D at h
  obtain ⟨ha, i', pa', ib', pb', m', cd⟩ := D
  simp only at h
  have hk : k ≠ 0 := by
    intro hk
    simp [hk] at h
  simp only [hk, if_false] at h
  generalize hr : wordGenGcMoveLoop conf (k - 1)
    (pax, i', pa', ib', pb', pb, old, m', dm) = R at h
  obtain ⟨ir, par, ibr, pbr, mr, cr⟩ := R
  simp only [Prod.mk.injEq, Bool.and_eq_true] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hcd, hcr⟩ := h
  refine ⟨ha, i', pa', ib', pb', m', hk, ?_, ?_⟩
  · simp only [hcd]
  · simpa only [hcr] using hr

/-- The recursive outer-loop result overwrites all collector temporaries.
This is the canonical-map normalization needed after either branch. -/
theorem genLoopTemps_overwrite {width : Nat} [NeZero width]
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (a0 a1 a2 a3 b0 b1 b2 b3 b4 b5 b6 : WordLocW width) :
    (st.updateListEq [(.temp 0, a0), (.temp 1, a1), (.temp 2, a2), (.temp 3, a3)]).updateListEq
      [(.temp 0, b0), (.temp 1, b1), (.temp 2, b2), (.temp 3, b3),
        (.temp 4, b4), (.temp 5, b5), (.temp 6, b6)] =
      st.updateListEq [(.temp 0, b0), (.temp 1, b1), (.temp 2, b2), (.temp 3, b3),
        (.temp 4, b4), (.temp 5, b5), (.temp 6, b6)] := by
  apply regs_ext
  intro k
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
  by_cases k0 : k = .temp 0
  · subst k0; simp
  by_cases k1 : k = .temp 1
  · subst k1; simp
  by_cases k2 : k = .temp 2
  · subst k2; simp
  by_cases k3 : k = .temp 3
  · subst k3; simp
  simp only [BitVec.ofNat_eq_ofNat] at k0 k1 k2 k3
  simp [k0, k1, k2, k3]

/-- Infrastructure packaging of the original loop entry facts. This introduces
no new facts: the final port spells these conjuncts out in HOL order. -/
structure GenLoopReady {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F)
    (pax i pa ib pb pbx old tt : BitVec width) : Prop where
  curr : s.store.lookup .currHeap = some (.word old)
  use : s.useStore = true
  stop : tt = 0 ↔ pbx = pb ∧ pax = pa
  temp0 : (s.store.lookup (.temp 0)).isSome = true
  temp1 : (s.store.lookup (.temp 1)).isSome = true
  temp5 : (s.store.lookup (.temp 5)).isSome = true
  temp6 : (s.store.lookup (.temp 6)).isSome = true
  temp2 : s.store.lookup (.temp 2) = some (.word pb)
  temp3 : s.store.lookup (.temp 3) = some (.word ib)
  temp4 : s.store.lookup (.temp 4) = some (.word pbx)
  reg0 : (s.regs.lookup 0).isSome = true
  reg1 : s.regs.lookup 1 = some (.word pbx)
  reg2 : s.regs.lookup 2 = some (.word pb)
  reg3 : s.regs.lookup 3 = some (.word pa)
  reg4 : s.regs.lookup 4 = some (.word i)
  reg5 : (s.regs.lookup 5).isSome = true
  reg6 : (s.regs.lookup 6).isSome = true
  reg7 : s.regs.lookup 7 = some (.word tt)
  reg8 : s.regs.lookup 8 = some (.word pax)

/-- Exact existential output of the original loop theorem, factored only to
keep the induction's state normalization readable. -/
abbrev GenLoopOutput {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (s : StackSemStateFiniteExact width C F)
    (i pa ib pb : BitVec width) (m : BitVec width → WordLocW width) : Prop :=
  ∃ ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
    evaluate (wordGenGcMoveLoopCode conf, { s with clock := s.clock + ck }) =
      (none, { s with
        memory := m
        store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb),
          (.temp 3, .word ib), (.temp 4, t4), (.temp 5, t5), (.temp 6, t6)]
        regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa),
          (4, .word i), (5, r5), (6, r6), (7, r7), (8, r8)] })

/-- Actual state after the successful data collector and its register tail. -/
abbrev genLoopDataNext {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pb pb' i' pa' ib' : BitVec width)
    (m' : BitVec width → WordLocW width) (r0 r1 r2 r5 r6 r7 t0 t1 : WordLocW width) :=
  setVar 7 (.word (pb - pb')) (setVar 2 (.word pb') (setVar 1 (.word pb)
    (setVar 7 (.word pb) (setVar 5 (.word pb')
      { s with
        memory := m'
        store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb'),
          (.temp 3, .word ib')]
        regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa'),
          (4, .word i'), (5, r5), (6, r6), (7, r7), (8, .word pa')] }))))

/-- All original entry facts hold for the recursive data-branch state. -/
theorem genLoopDataNext_ready {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pax i pa ib pb old tt : BitVec width)
    (r : GenLoopReady s pax i pa ib pb pb old tt)
    (pb' i' pa' ib' : BitVec width) (m' : BitVec width → WordLocW width)
    (r0 r1 r2 r5 r6 r7 t0 t1 : WordLocW width) :
    GenLoopReady (genLoopDataNext s pb pb' i' pa' ib' m' r0 r1 r2 r5 r6 r7 t0 t1)
      pa' i' pa' ib' pb' pb old (pb - pb') := by
  constructor
  · simpa [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL] using r.curr
  · exact r.use
  · simp [BitVec.sub_eq_iff_eq_add]
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simpa [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL] using r.temp5
  · simpa [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL] using r.temp6
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simpa [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL] using r.temp4
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_HOL]
  · simp [genLoopDataNext, setVar, FUPDATE_LIST_HOL, FUPDATE_HOL]

/-- Data branch of the full fuel induction, using only the recursive
simulation IH for the original smaller-fuel collector call. -/
theorem genLoopData_case {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord)
    (k : Nat) (s : StackSemStateFiniteExact width C F)
    (pax i pa ib pb old tt i1 pa1 ib1 pb1 : BitVec width)
    (m1 : BitVec width → WordLocW width) (hpa : pax ≠ pa)
    (r : GenLoopReady s pax i pa ib pb pb old tt)
    (h : wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pb, old, s.memory, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (ih : ∀ (s' : StackSemStateFiniteExact width C F) (pax' i' pa' ib' pb' pbx' tt' : BitVec width),
      wordGenGcMoveLoop conf (k - 1) (pax', i', pa', ib', pb', pbx', old, s'.memory, s'.mdomain) =
        (i1, pa1, ib1, pb1, m1, true) →
      GenLoopReady s' pax' i' pa' ib' pb' pbx' old tt' →
      GenLoopOutput conf s' i1 pa1 ib1 pb1 m1) :
    GenLoopOutput conf s i1 pa1 ib1 pb1 m1 := by
  obtain ⟨i', pa', ib', pb', m', hk, hd, hr⟩ :=
    genLoopSource_data conf k pax i pa ib pb old s.memory s.mdomain i1 pa1 ib1 pb1 m1 hpa h
  obtain ⟨ckD, q0, q1, q2, q5, q6, q7, u0, u1, hD⟩ :=
    wordGenGcMoveDataCode_run hsl hws hw2 hlen hshift old (2 ^ width)
      pax i pa ib pb i' pa' ib' pb' m' s hd r.curr r.use r.temp0 r.temp1 r.temp2 r.temp3
      r.reg0 (by simp [r.reg1]) (by simp [r.reg2]) r.reg3 r.reg4 r.reg5 r.reg6
      (by simp [r.reg7]) r.reg8
  let d := genLoopDataNext s pb pb' i' pa' ib' m' q0 q1 q2 q5 q6 q7 u0 u1
  let t : StackSemStateFiniteExact width C F :=
    { s with
      memory := m'
      store := s.store.updateListEq [(.temp 0, u0), (.temp 1, u1), (.temp 2, .word pb'),
        (.temp 3, .word ib')]
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa'),
        (4, .word i'), (5, q5), (6, q6), (7, q7), (8, .word pa')] }
  have hb : evaluate (genLoopBody conf, { s with clock := s.clock + ckD }) = (none, d) := by
    exact genLoopBodyData_eval conf _ t pb pb' r.reg1 r.reg2 hD
      (by dsimp [t]; omega) r.use
      (by simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simpa [t, FUPDATE_LIST_HOL, FUPDATE_HOL] using r.temp4)
  have rd := genLoopDataNext_ready s pax i pa ib pb old tt r
    pb' i' pa' ib' m' q0 q1 q2 q5 q6 q7 u0 u1
  obtain ⟨ckR, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hR⟩ :=
    ih d pa' i' pa' ib' pb' pb (pb - pb') hr rd
  have htt : tt ≠ 0 := by
    intro ht
    exact hpa ((r.stop.mp ht).2)
  refine ⟨ckD + ckR + 1, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, ?_⟩
  have H := genLoopStep_eval conf s d _ tt ckD ckR r.reg7 htt hb rfl hR
  refine H.trans ?_
  simp only [d, setVar, Prod.mk.injEq, true_and]
  rw [genLoopTemps_overwrite]
  congr 1
  apply regs_ext
  intro n
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
    FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
  by_cases n0 : n = 0
  · subst n0; simp
  by_cases n1 : n = 1
  · subst n1; simp
  by_cases n2 : n = 2
  · subst n2; simp
  by_cases n3 : n = 3
  · subst n3; simp
  by_cases n4 : n = 4
  · subst n4; simp
  by_cases n5 : n = 5
  · subst n5; simp
  by_cases n6 : n = 6
  · subst n6; simp
  by_cases n7 : n = 7
  · subst n7; simp
  by_cases n8 : n = 8
  · subst n8; simp
  simp [n0, n1, n2, n3, n4, n5, n6, n7, n8]

/-- Canonical state after the reference collector and its complete tail. -/
abbrev genLoopRefsNext {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pbx pb pax pb' i' pa' ib' : BitVec width)
    (m' : BitVec width → WordLocW width) (q6 t0 t1 : WordLocW width) :=
  { s with
    memory := m'
    store := ((genLoopRefsEntry s pbx pb pax).store.updateListEq
      [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb'), (.temp 3, .word ib')]).updateEq
        (.temp 4, .word pb)
    regs := s.regs.updateListEq [(0, .word pbx), (1, .word pb), (2, .word pb'),
      (3, .word pa'), (4, .word i'), (5, .word (pax - pa')), (6, q6),
      (7, .word ((pb - pb') ||| (pax - pa'))), (8, .word pax)] }

/-- Every original recursive entry fact follows from the actual reference
result, including both boundary equalities tested by the OR. -/
theorem genLoopRefsNext_ready {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pax i pa ib pb pbx old tt : BitVec width)
    (r : GenLoopReady s pax i pa ib pb pbx old tt)
    (pb' i' pa' ib' : BitVec width) (m' : BitVec width → WordLocW width)
    (q6 t0 t1 : WordLocW width) :
    GenLoopReady (genLoopRefsNext s pbx pb pax pb' i' pa' ib' m' q6 t0 t1)
      pax i' pa' ib' pb' pb old ((pb - pb') ||| (pax - pa')) := by
  constructor
  · simpa [genLoopRefsNext, genLoopRefsEntry, setVar, setStore,
      FUPDATE_LIST_HOL, FUPDATE_HOL] using r.curr
  · exact r.use
  · exact genLoopBoundaryZero_iff pb pb' pax pa'
  · simp [genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [genLoopRefsEntry, setVar, setStore, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]
  · simp [FUPDATE_LIST_HOL, FUPDATE_HOL]

/-- Exact result state supplied by the full reference collector theorem. -/
abbrev genLoopRefsResult {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pbx pb pax ha pb' i' pa' ib' : BitVec width)
    (m' : BitVec width → WordLocW width) (q1 q2 q5 q6 q7 t0 t1 : WordLocW width) :=
  let e := genLoopRefsEntry s pbx pb pax
  { e with
    memory := m'
    store := e.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb'),
      (.temp 3, .word ib')]
    regs := e.regs.updateListEq [(0, .word pbx), (1, q1), (2, q2), (3, .word pa'),
      (4, .word i'), (5, q5), (6, q6), (7, q7), (8, .word ha)] }

/-- Normalize the complete actual reference tail to the recursive state. -/
theorem genLoopRefsTail_normalize {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (pbx pb pax ha pb' i' pa' ib' : BitVec width)
    (m' : BitVec width → WordLocW width) (q1 q2 q5 q6 q7 t0 t1 : WordLocW width)
    (hu : s.useStore = true) :
    evaluate (listSeqHOL [moveHOL 7 8, .get 1 (.temp 5), .get 2 (.temp 5),
      .set (.temp 4) 2, .get 2 (.temp 2), moveHOL 3 3, moveHOL 4 4,
      moveHOL 7 1, subInst 7 2, .get 8 (.temp 6), moveHOL 5 8,
      subInst 5 3, orInst 7 5],
      genLoopRefsResult s pbx pb pax ha pb' i' pa' ib' m' q1 q2 q5 q6 q7 t0 t1) =
      (none, genLoopRefsNext s pbx pb pax pb' i' pa' ib' m' q6 t0 t1) := by
  let R := genLoopRefsResult s pbx pb pax ha pb' i' pa' ib' m' q1 q2 q5 q6 q7 t0 t1
  have H := genLoopRefsTail_eval R ha pb pb' pax pa' i' hu
    (by simp [R, genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [R, genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [R, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [R, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [R, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [R, FUPDATE_LIST_HOL, FUPDATE_HOL])
  refine H.trans ?_
  simp only [R, genLoopRefsNext, genLoopRefsEntry, setVar, setStore,
    Prod.mk.injEq, true_and]
  congr 1
  apply regs_ext
  intro n
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
    FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
  by_cases n0 : n = 0
  · subst n0; simp
  by_cases n1 : n = 1
  · subst n1; simp
  by_cases n2 : n = 2
  · subst n2; simp
  by_cases n3 : n = 3
  · subst n3; simp
  by_cases n4 : n = 4
  · subst n4; simp
  by_cases n5 : n = 5
  · subst n5; simp
  by_cases n6 : n = 6
  · subst n6; simp
  by_cases n7 : n = 7
  · subst n7; simp
  by_cases n8 : n = 8
  · subst n8; simp
  simp [n0, n1, n2, n3, n4, n5, n6, n7, n8]

/-- The final recursive seven-slot result also overwrites the saved reference
boundaries; none of the prelude's temporary writes escape the full result. -/
theorem genLoopRefsStore_overwrite {width : Nat} [NeZero width]
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : WordLocW width) :
    ((((st.updateEq (.temp 6, a6)).updateEq (.temp 5, a5)).updateListEq
      [(.temp 0, a0), (.temp 1, a1), (.temp 2, a2), (.temp 3, a3)]).updateEq
      (.temp 4, a4)).updateListEq
      [(.temp 0, b0), (.temp 1, b1), (.temp 2, b2), (.temp 3, b3),
        (.temp 4, b4), (.temp 5, b5), (.temp 6, b6)] =
      st.updateListEq [(.temp 0, b0), (.temp 1, b1), (.temp 2, b2), (.temp 3, b3),
        (.temp 4, b4), (.temp 5, b5), (.temp 6, b6)] := by
  apply regs_ext
  intro k
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
    FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
  by_cases k0 : k = .temp 0
  · subst k0; simp
  by_cases k1 : k = .temp 1
  · subst k1; simp
  by_cases k2 : k = .temp 2
  · subst k2; simp
  by_cases k3 : k = .temp 3
  · subst k3; simp
  by_cases k4 : k = .temp 4
  · subst k4; simp
  by_cases k5 : k = .temp 5
  · subst k5; simp
  by_cases k6 : k = .temp 6
  · subst k6; simp
  simp only [BitVec.ofNat_eq_ofNat] at k0 k1 k2 k3 k4 k5 k6
  simp [k0, k1, k2, k3, k4, k5, k6]

/-- Reference branch of the full fuel induction, with only the smaller-fuel
simulation as its IH and all recursive state facts derived. -/
theorem genLoopRefs_case {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord)
    (k : Nat) (s : StackSemStateFiniteExact width C F)
    (pax i pa ib pb pbx old tt i1 pa1 ib1 pb1 : BitVec width)
    (m1 : BitVec width → WordLocW width) (hpb : pbx ≠ pb)
    (r : GenLoopReady s pax i pa ib pb pbx old tt)
    (h : wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, s.memory, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (ih : ∀ (s' : StackSemStateFiniteExact width C F) (pax' i' pa' ib' pb' pbx' tt' : BitVec width),
      wordGenGcMoveLoop conf (k - 1) (pax', i', pa', ib', pb', pbx', old, s'.memory, s'.mdomain) =
        (i1, pa1, ib1, pb1, m1, true) →
      GenLoopReady s' pax' i' pa' ib' pb' pbx' old tt' →
      GenLoopOutput conf s' i1 pa1 ib1 pb1 m1) :
    GenLoopOutput conf s i1 pa1 ib1 pb1 m1 := by
  obtain ⟨ha, i', pa', ib', pb', m', hk, hd, hr⟩ :=
    genLoopSource_refs conf k pax i pa ib pb pbx old s.memory s.mdomain i1 pa1 ib1 pb1 m1 hpb h
  let e := genLoopRefsEntry s pbx pb pax
  obtain ⟨ckD, q1, q2, q5, q6, q7, u0, u1, hD⟩ :=
    wordGenGcMoveRefsCode_run hsl hws hw2 hlen hshift pbx old (2 ^ width)
      pb i pa ib pb ha i' pa' ib' pb' m' e hd
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.curr)
      r.use
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp0)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp1)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp2)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp3)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp4)
      (by simp [e, setVar, setStore, FUPDATE_HOL])
      (by simp [e, setVar, setStore, FUPDATE_HOL, r.reg1])
      (by simp [e, setVar, setStore, FUPDATE_HOL, r.reg2])
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.reg3)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.reg4)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.reg5)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.reg6)
      (by simp [e, setVar, setStore, FUPDATE_HOL, r.reg7])
      (by simp [e, setVar, setStore, FUPDATE_HOL])
  let t := genLoopRefsResult s pbx pb pax ha pb' i' pa' ib' m' q1 q2 q5 q6 q7 u0 u1
  let d := genLoopRefsNext s pbx pb pax pb' i' pa' ib' m' q6 u0 u1
  have ht5 : t.store.lookup (.temp 5) = some (.word pb) := by
    simp [t, genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht6 : t.store.lookup (.temp 6) = some (.word pax) := by
    simp [t, genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht2 : t.store.lookup (.temp 2) = some (.word pb') := by
    simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht3 : t.regs.lookup 3 = some (.word pa') := by simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht4 : t.regs.lookup 4 = some (.word i') := by simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht8 : t.regs.lookup 8 = some (.word ha) := by simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have hb : evaluate (genLoopBody conf, { s with clock := s.clock + ckD }) = (none, d) := by
    have H := genLoopBodyRefs_eval conf { s with clock := s.clock + ckD } t
      pbx pb pax ha pb' pa' i' hpb r.use r.reg1 r.reg2 r.reg8 hD
      (by dsimp [t, genLoopRefsEntry, setVar, setStore]; omega)
      r.use ht5 ht6 ht2 ht3 ht4 ht8
    have ht := genLoopRefsTail_eval t ha pb pb' pax pa' i' r.use ht5 ht6 ht2 ht3 ht4 ht8
    exact H.trans (ht.symm.trans (genLoopRefsTail_normalize s pbx pb pax ha pb' i' pa' ib'
      m' q1 q2 q5 q6 q7 u0 u1 r.use))
  have rd := genLoopRefsNext_ready s pax i pa ib pb pbx old tt r
    pb' i' pa' ib' m' q6 u0 u1
  obtain ⟨ckR, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hR⟩ :=
    ih d pax i' pa' ib' pb' pb ((pb - pb') ||| (pax - pa')) hr rd
  have htt : tt ≠ 0 := by
    intro ht
    exact hpb ((r.stop.mp ht).1)
  refine ⟨ckD + ckR + 1, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, ?_⟩
  have H := genLoopStep_eval conf s d _ tt ckD ckR r.reg7 htt hb rfl hR
  refine H.trans ?_
  simp only [d, genLoopRefsEntry, setVar, setStore, Prod.mk.injEq, true_and]
  rw [genLoopRefsStore_overwrite]
  congr 1
  apply regs_ext
  intro n
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
    FUPDATE_HOL]
  by_cases n0 : n = 0
  · subst n0; simp
  by_cases n1 : n = 1
  · subst n1; simp
  by_cases n2 : n = 2
  · subst n2; simp
  by_cases n3 : n = 3
  · subst n3; simp
  by_cases n4 : n = 4
  · subst n4; simp
  by_cases n5 : n = 5
  · subst n5; simp
  by_cases n6 : n = 6
  · subst n6; simp
  by_cases n7 : n = 7
  · subst n7; simp
  by_cases n8 : n = 8
  · subst n8; simp
  simp [n0, n1, n2, n3, n4, n5, n6, n7, n8]

/-- Full native generational-loop simulation by complete induction on the
original fuel. The final tagged theorem expands the entry/output packages. -/
theorem wordGenGcMoveLoopCode_run {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord)
    (old : BitVec width) :
    ∀ (k : Nat) (s : StackSemStateFiniteExact width C F)
      (pax i pa ib pb pbx tt i1 pa1 ib1 pb1 : BitVec width)
      (m1 : BitVec width → WordLocW width),
      wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, s.memory, s.mdomain) =
        (i1, pa1, ib1, pb1, m1, true) →
      GenLoopReady s pax i pa ib pb pbx old tt → GenLoopOutput conf s i1 pa1 ib1 pb1 m1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s pax i pa ib pb pbx tt i1 pa1 ib1 pb1 m1 h r
    by_cases hpb : pbx = pb
    · subst pbx
      by_cases hpa : pax = pa
      · subst pax
        rw [wordGenGcMoveLoop] at h
        simp only [if_true, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := h
        have ht : tt = 0 := r.stop.mpr ⟨rfl, rfl⟩
        subst tt
        obtain ⟨r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, he⟩ :=
          genLoopStop_output conf s i pa ib pb pb pa r.temp0 r.temp1 r.temp5 r.temp6
            r.temp2 r.temp3 r.temp4 r.reg0 r.reg1 r.reg2 r.reg3 r.reg4 r.reg5 r.reg6
            r.reg7 r.reg8
        exact ⟨0, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, by simpa using he⟩
      · obtain ⟨_, _, _, _, _, hk, _, _⟩ :=
          genLoopSource_data conf k pax i pa ib pb old s.memory s.mdomain
            i1 pa1 ib1 pb1 m1 hpa h
        apply genLoopData_case hsl hws hw2 hlen hshift k s pax i pa ib pb old tt
          i1 pa1 ib1 pb1 m1 hpa r h
        intro s' pax' i' pa' ib' pb' pbx' tt' h' r'
        exact ih (k - 1) (by omega) s' pax' i' pa' ib' pb' pbx' tt'
          i1 pa1 ib1 pb1 m1 h' r'
    · obtain ⟨_, _, _, _, _, _, hk, _, _⟩ :=
        genLoopSource_refs conf k pax i pa ib pb pbx old s.memory s.mdomain
          i1 pa1 ib1 pb1 m1 hpb h
      apply genLoopRefs_case hsl hws hw2 hlen hshift k s pax i pa ib pb pbx old tt
        i1 pa1 ib1 pb1 m1 hpb r h
      intro s' pax' i' pa' ib' pb' pbx' tt' h' r'
      exact ih (k - 1) (by omega) s' pax' i' pa' ib' pb' pbx' tt'
        i1 pa1 ib1 pb1 m1 h' r'

namespace GenGcMoveLoopSupport

/-- Canonical codec for the actual StackSem finite-support carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end GenGcMoveLoopSupport

/-- Full original `word_gen_gc_move_loop_code_thm` (4347-4540), with its
explicit binder order, conjunctive hypothesis, twelve existential witnesses,
seven temporary-slot updates and nine register updates. Original free `conf`
and Boolean `c1` are implicit universal binders; the unused `c1` premise is
retained. Complete induction derives both collector success flags and every
recursive entry fact. No additional dimension, target-run or simulation
premise is introduced. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem word_gen_gc_move_loop_code_thm {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {c1 : Bool} :
    ∀ (k : Nat) (pax i pa ib pb pbx old : BitVec width)
      (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
      (i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (tt : BitVec width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, m, dm) =
          (i1, pa1, ib1, pb1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ (tt = 0 ↔ pbx = pb ∧ pax = pa) ∧
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        (s.store.lookup (.temp 5)).isSome = true ∧ (s.store.lookup (.temp 6)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb) ∧ s.store.lookup (.temp 3) = some (.word ib) ∧
        s.store.lookup (.temp 4) = some (.word pbx) ∧ (s.regs.lookup 0).isSome = true ∧
        getVar 1 s = some (.word pbx) ∧ getVar 2 s = some (.word pb) ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        getVar 7 s = some (.word tt) ∧ getVar 8 s = some (.word pax) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧ c1 = true →
      ∃ ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
        evaluate (wordGenGcMoveLoopCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1), (.temp 4, t4), (.temp 5, t5), (.temp 6, t6)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8)] }) := by
  rintro k pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 tt s
    ⟨hm, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, hstop,
      ht0, ht1, ht5, ht6, ht2, ht3, ht4, h0, h1, h2, h3, h4, h7, h8, h5, h6, -⟩
  exact wordGenGcMoveLoopCode_run hsl hws hw2 hlen hshift old k s
    pax i pa ib pb pbx tt i1 pa1 ib1 pb1 m1 hm
    ⟨hcurr, huse, hstop, ht0, ht1, ht5, ht6, ht2, ht3, ht4, h0,
      by simpa [getVar] using h1, by simpa [getVar] using h2,
      by simpa [getVar] using h3, by simpa [getVar] using h4, h5, h6,
      by simpa [getVar] using h7, by simpa [getVar] using h8⟩

end Flapjack.Compiler.Backend.StackAlloc
