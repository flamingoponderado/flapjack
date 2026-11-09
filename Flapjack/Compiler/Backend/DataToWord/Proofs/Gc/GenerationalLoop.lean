module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalData

@[expose] public section

/-! Major collector loop simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Every heap element occupies at least one word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "LENGTH_LESS_EQ_SUM_el_length"]
theorem length_le_heapLength {α β : Type} (elements : List (HeapElement α β)) :
    elements.length ≤ heapLength elements := by
  induction elements with
  | nil => simp [heapLength]
  | cons head tail ih =>
    simp only [heapLength, List.map_cons, List.sum_cons] at ih ⊢
    cases head <;> simp [elLength] at * <;> omega

/-- The original heap-length invariant bounds the fuel needed by the data and
reference scans in one major collector loop iteration. -/
theorem genLoop_scanFuel {α β : Type} (state : GcState α β) (limit : Nat)
    (invariant : genLenInv state) (heapBound : heapLength state.heap ≤ limit) :
    heapLength state.h2 + state.n + heapLength state.r4 ≤ limit ∧ state.r4.length ≤ limit := by
  have listBound := length_le_heapLength state.r4
  simp only [genLenInv, heapLength_append] at invariant
  omega

/-- The nonempty data region advances the scan pointer without wrapping.
This is local arithmetic for the major collector loop. -/
theorem genLoop_dataPointers_ne {width : Nat} [NeZero width] {α β : Type}
    (state : GcState α β) (p : BitVec width) (good : goodDimindex width)
    (invariant : genLenInv state)
    (bytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (nonempty : state.h2 ≠ []) :
    p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1) ≠
      p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)) := by
  have positive : 0 < heapLength state.h2 := by
    cases h : state.h2 with
    | nil => exact False.elim (nonempty h)
    | cons head tail =>
      simp only [heapLength, List.map_cons, List.sum_cons]
      cases head <;> simp [elLength]
  have wordBytes : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have totalBound : (heapLength state.h1 + heapLength state.h2) * (width / 8) < 2 ^ width := by
    have le : heapLength state.h1 + heapLength state.h2 ≤ heapLength state.heap := by
      simp only [genLenInv, heapLength_append] at invariant
      omega
    have mult := Nat.mul_le_mul_right (width / 8) le
    omega
  simpa only [heapLength_append, BitVec.mul_comm] using
    scanOffsets_ne p (heapLength state.h1) (heapLength state.h2) positive wordBytes totalBound

/-- The nonempty reference region advances its end pointer without wrapping.
This is local arithmetic for the major collector loop. -/
theorem genLoop_refPointers_ne {width : Nat} [NeZero width] {α β : Type}
    (state : GcState α β) (p : BitVec width) (good : goodDimindex width)
    (invariant : genLenInv state)
    (bytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (nonempty : state.r4 ≠ []) :
    p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n) ≠
      p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n) := by
  have positive : 0 < heapLength state.r4 := by
    cases h : state.r4 with
    | nil => exact False.elim (nonempty h)
    | cons head tail =>
      simp only [heapLength, List.map_cons, List.sum_cons]
      cases head <;> simp [elLength]
  have wordBytes : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have totalBound : (heapLength (state.h1 ++ state.h2) + state.n + heapLength state.r4) *
      (width / 8) < 2 ^ width := by
    have le : heapLength (state.h1 ++ state.h2) + state.n + heapLength state.r4 ≤ heapLength state.heap := by
      simp only [genLenInv, heapLength_append] at invariant ⊢
      omega
    have mult := Nat.mul_le_mul_right (width / 8) le
    omega
  have ne := scanOffsets_ne p (heapLength (state.h1 ++ state.h2) + state.n)
    (heapLength state.r4) positive wordBytes totalBound
  simpa only [heapLength_append, BitVec.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ne

/-- A successful nonempty data iteration has fuel and continues from the
abstract data scan. This is local unfolding of the loop definition. -/
theorem genLoop_dataStep {α β : Type} (conf : GenGc.Config β) (state final : GcState α β)
    (k : Nat) (refsEmpty : state.r4 = []) (dataNonempty : state.h2 ≠ [])
    (run : GenGc.gcMoveLoop conf state k = final) (success : final.ok = true) :
    0 < k ∧ GenGc.gcMoveLoop conf (GenGc.gcMoveData conf state) (k - 1) = final ∧
      (GenGc.gcMoveData conf state).ok = true := by
  classical
  cases k with
  | zero =>
    rw [GenGc.gcMoveLoop] at run
    cases pending : state.h2 with
    | nil => exact False.elim (dataNonempty pending)
    | cons head tail =>
      simp [refsEmpty, pending] at run
      rw [← run] at success
      simp at success
  | succ k =>
    have next : GenGc.gcMoveLoop conf (GenGc.gcMoveData conf state) k = final := by
      rw [GenGc.gcMoveLoop] at run
      cases pending : state.h2 with
      | nil => exact False.elim (dataNonempty pending)
      | cons head tail => simpa [refsEmpty, pending] using run
    refine ⟨Nat.zero_lt_succ k, by simpa using next, ?_⟩
    apply GenGc.gcMoveLoop_ok conf _ k
    simpa [next] using success

/-- A successful nonempty reference iteration has fuel and continues from the
abstract reference scan. This is local unfolding of the loop definition. -/
theorem genLoop_refsStep {α β : Type} (conf : GenGc.Config β) (state final : GcState α β)
    (k : Nat) (refsNonempty : state.r4 ≠ [])
    (run : GenGc.gcMoveLoop conf state k = final) (success : final.ok = true) :
    0 < k ∧ GenGc.gcMoveLoop conf
      (GenGc.gcMoveRefs conf { state with r2 := state.r4, r4 := [] }) (k - 1) = final ∧
      (GenGc.gcMoveRefs conf { state with r2 := state.r4, r4 := [] }).ok = true := by
  classical
  cases k with
  | zero =>
    rw [GenGc.gcMoveLoop] at run
    cases refs : state.r4 with
    | nil => exact False.elim (refsNonempty refs)
    | cons head tail =>
      simp [refs] at run
      rw [← run] at success
      simp at success
  | succ k =>
    have next : GenGc.gcMoveLoop conf
        (GenGc.gcMoveRefs conf { state with r2 := state.r4, r4 := [] }) k = final := by
      rw [GenGc.gcMoveLoop] at run
      cases refs : state.r4 with
      | nil => exact False.elim (refsNonempty refs)
      | cons head tail => simpa [refs] using run
    refine ⟨Nat.zero_lt_succ k, by simpa using next, ?_⟩
    apply GenGc.gcMoveLoop_ok conf _ k
    simpa [next] using success

/-- A successful collector loop preserves the allocation-index/work-list
relationship across both kinds of scan. -/
theorem genLoop_dataIndex {α β : Type} (conf : GenGc.Config β) (k : Nat)
    (state final : GcState α β) (run : GenGc.gcMoveLoop conf state k = final) (success : final.ok = true) :
    final.a + heapLength state.h1 + heapLength state.h2 =
      state.a + heapLength final.h1 + heapLength final.h2 := by
  classical
  induction k generalizing state final with
  | zero =>
    cases refs : state.r4 with
    | nil =>
      cases pending : state.h2 with
      | nil => rw [GenGc.gcMoveLoop] at run; simp [refs, pending] at run; subst final; simp [pending]
      | cons head tail =>
        have positive := (genLoop_dataStep conf state final 0 refs (by simp [pending]) run success).1
        omega
    | cons head tail =>
      have positive := (genLoop_refsStep conf state final 0 (by simp [refs]) run success).1
      omega
  | succ k ih =>
    cases refs : state.r4 with
    | nil =>
      cases pending : state.h2 with
      | nil => rw [GenGc.gcMoveLoop] at run; simp [refs, pending] at run; subst final; simp [pending]
      | cons head tail =>
        obtain ⟨_, next, nextOk⟩ := genLoop_dataStep conf state final (k + 1) refs (by simp [pending]) run success
        have step := genMoveData_dataIndex conf state nextOk
        have rest := ih (GenGc.gcMoveData conf state) final (by simpa using next) success
        rw [pending] at step
        omega
    | cons head tail =>
      obtain ⟨_, next, _⟩ := genLoop_refsStep conf state final (k + 1) (by simp [refs]) run success
      let start := { state with r2 := state.r4, r4 := [] }
      have step := genMoveRefs_dataIndex conf start
      have rest := ih (GenGc.gcMoveRefs conf start) final (by simpa [start] using next) success
      dsimp only [start] at step rest
      omega

/-- Expose the data scan and recursive concrete loop, retaining both flags.
This is local unfolding of the word-level loop. -/
theorem genLoop_wordDataStep {width : Nat} [NeZero width] (conf : Config)
    (k : Nat) (pax i pa ib pb old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (different : pax ≠ pa) (positive : 0 < k)
    (run : wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pb, old, m, dm) =
      (i1, pa1, ib1, pb1, m1, c1)) :
    ∃ i' pa' ib' pb' m' cd cr,
      wordGenGcMoveData conf (2 ^ width) (pax, i, pa, ib, pb, old, m, dm) =
        (i', pa', ib', pb', m', cd) ∧
      wordGenGcMoveLoop conf (k - 1) (pa', i', pa', ib', pb', pb, old, m', dm) =
        (i1, pa1, ib1, pb1, m1, cr) ∧ c1 = (cd && cr) := by
  rw [wordGenGcMoveLoop] at run
  simp only [if_true, different, if_false, Nat.ne_of_gt positive] at run
  generalize scan : wordGenGcMoveData conf (2 ^ width) (pax, i, pa, ib, pb, old, m, dm) = result at run
  obtain ⟨i', pa', ib', pb', m', cd⟩ := result
  simp only at run
  generalize loop : wordGenGcMoveLoop conf (k - 1) (pa', i', pa', ib', pb', pb, old, m', dm) = result at run
  obtain ⟨ir, par, ibr, pbr, mr, cr⟩ := result
  simp only [Prod.mk.injEq] at run
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := run
  exact ⟨i', pa', ib', pb', m', cd, cr, rfl, loop, rfl⟩

/-- Expose the reference scan and recursive concrete loop, including the
source loop's original reference bound and both success flags. -/
theorem genLoop_wordRefsStep {width : Nat} [NeZero width] (conf : Config)
    (k : Nat) (pax i pa ib pb pbx old : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width) (c1 : Bool)
    (different : pbx ≠ pb) (positive : 0 < k)
    (run : wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, m, dm) =
      (i1, pa1, ib1, pb1, m1, c1)) :
    ∃ end' i' pa' ib' pb' m' cd cr,
      wordGenGcMoveRefs conf (2 ^ width) (pb, pbx, i, pa, ib, pb, old, m, dm) =
        (end', i', pa', ib', pb', m', cd) ∧
      wordGenGcMoveLoop conf (k - 1) (pax, i', pa', ib', pb', pb, old, m', dm) =
        (i1, pa1, ib1, pb1, m1, cr) ∧ c1 = (cd && cr) := by
  rw [wordGenGcMoveLoop] at run
  simp only [different, if_false, Nat.ne_of_gt positive] at run
  generalize scan : wordGenGcMoveRefs conf (2 ^ width) (pb, pbx, i, pa, ib, pb, old, m, dm) = result at run
  obtain ⟨end', i', pa', ib', pb', m', cd⟩ := result
  simp only at run
  generalize loop : wordGenGcMoveLoop conf (k - 1) (pax, i', pa', ib', pb', pb, old, m', dm) = result at run
  obtain ⟨ir, par, ibr, pbr, mr, cr⟩ := result
  simp only [Prod.mk.injEq] at run
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := run
  exact ⟨end', i', pa', ib', pb', m', cd, cr, rfl, loop, rfl⟩

/-- The completed-scan case of the major collector loop simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_loop_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveLoop_empty {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr p : BitVec width) (xs : List (WordLocW width))
    (pb1 pa1 ib1 i1 : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (abstractRun : GenGc.gcMoveLoop genConf state k = state1) (_stateOk : state1.ok = true)
    (_heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (_heapBytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (_dataBound : conf.lenSize + 2 < width) (r3Empty : state.r3 = []) (r2Empty : state.r2 = [])
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (_lenBound : conf.lenSize + 5 ≤ width)
    (wordRun : wordGenGcMoveLoop conf k
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1),
       BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       BitVec.ofNat width (state.a + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n),
       curr, memory, domain) = (i1, pa1, ib1, pb1, memory1, c1))
    (invariant : genLenInv state)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (length : xs.length = state.n) (_good : goodDimindex width)
    (r4Empty : state.r4 = []) (h2Empty : state.h2 = []) :
    ∃ xs1,
      SetSep.star (SetSep.star (wordHeap curr state1.heap conf) (wordHeapParts conf p state1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.h2 = [] ∧ state1.r4 = [] ∧ state1.r3 = [] ∧ state1.r2 = [] ∧
      heapLength state1.heap = heapLength state.heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width state1.a ∧ state1.n = xs1.length ∧ genLenInv state1 ∧
      pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1) ∧
      pb1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1 + state1.n) ∧
      ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.r1.all (isRefElement genConf.isRef) = true := by
  have abstractEq : GenGc.gcMoveLoop genConf state k = state := by
    rw [GenGc.gcMoveLoop]
    simp [r4Empty, h2Empty]
  rw [abstractEq] at abstractRun
  subst state1
  simp only [h2Empty, r4Empty, List.append_nil] at wordRun
  rw [wordGenGcMoveLoop] at wordRun
  simp only [↓reduceIte, Prod.mk.injEq] at wordRun
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
  exact ⟨xs, separated, h2Empty, r4Empty, r3Empty, r2Empty, rfl, rfl, rfl,
    length.symm, invariant, rfl, rfl, rfl, by simpa [r4Empty, r3Empty, r2Empty] using refs⟩

/-- Original major collector loop simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_loop_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMoveLoop_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width))) (k : Nat)
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (curr p : BitVec width) (xs : List (WordLocW width))
    (pb1 pa1 ib1 i1 : BitVec width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop) (c1 : Bool)
    (abstractRun : GenGc.gcMoveLoop genConf state k = state1) (stateOk : state1.ok = true)
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (heapBytesBound : heapLength state.heap * (width / 8) < 2 ^ width)
    (dataBound : conf.lenSize + 2 < width) (r3Empty : state.r3 = []) (r2Empty : state.r2 = [])
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (lenBound : conf.lenSize + 5 ≤ width)
    (wordRun : wordGenGcMoveLoop conf k
      (p + wordSemBytesInWord * BitVec.ofNat width (heapLength state.h1),
       BitVec.ofNat width state.a,
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2)),
       BitVec.ofNat width (state.a + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2) + state.n),
       p + wordSemBytesInWord * BitVec.ofNat width (heapLength (state.h1 ++ state.h2 ++ state.r4) + state.n),
       curr, memory, domain) = (i1, pa1, ib1, pb1, memory1, c1))
    (invariant : genLenInv state)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (wordHeapParts conf p state xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true)
    (length : xs.length = state.n) (good : goodDimindex width) :
    ∃ xs1,
      SetSep.star (SetSep.star (wordHeap curr state1.heap conf) (wordHeapParts conf p state1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      state1.h2 = [] ∧ state1.r4 = [] ∧ state1.r3 = [] ∧ state1.r2 = [] ∧
      heapLength state1.heap = heapLength state.heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width state1.a ∧ state1.n = xs1.length ∧ genLenInv state1 ∧
      pa1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1) ∧
      pb1 = p + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h1 + state1.n) ∧
      ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.r1.all (isRefElement genConf.isRef) = true := by
  classical
  induction k using Nat.strong_induction_on generalizing state state1 memory memory1 xs pb1 pa1 ib1 i1 c1 with
  | h k ih =>
    by_cases r4Empty : state.r4 = []
    · by_cases h2Empty : state.h2 = []
      · exact wordGenGcMoveLoop_empty conf genConf k state state1 memory memory1 domain curr p xs
          pb1 pa1 ib1 i1 frame c1 abstractRun stateOk heapBound heapBytesBound dataBound r3Empty r2Empty
          refClass lenBound wordRun invariant separated refs length good r4Empty h2Empty
      · obtain ⟨positive, abstractTail, middleOk⟩ :=
          genLoop_dataStep genConf state state1 k r4Empty h2Empty abstractRun stateOk
        have different := genLoop_dataPointers_ne state p good invariant heapBytesBound h2Empty
        simp only [r4Empty, List.append_nil] at wordRun
        obtain ⟨i', pa', ib', pb', m', cd, cr, wordScan, wordTail, flags⟩ :=
          genLoop_wordDataStep conf k _ _ _ _ _ curr memory domain i1 pa1 ib1 pb1 memory1 c1
            different positive wordRun
        have heapLimit : heapLength state.heap ≤ 2 ^ width :=
          heapBound.trans (Nat.div_le_self _ _)
        have countBound := (genLoop_scanFuel state (2 ^ width) invariant heapLimit).1
        obtain ⟨xs', sep', h2', heapEq, cdTrue, iEq, ibEq, xsLen, inv', totalEq,
            paEq, pbEq, refs'⟩ :=
          wordGenGcMoveData_thm conf genConf (2 ^ width) state (GenGc.gcMoveData genConf state)
            memory m' domain curr p xs pb' pa' ib' i' frame cd rfl middleOk heapBound
            heapBytesBound dataBound refClass lenBound wordScan countBound invariant separated refs length good
        have constants := genMoveData_const genConf state (GenGc.gcMoveData genConf state) rfl
        have tailRun : wordGenGcMoveLoop conf (k - 1)
            (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (GenGc.gcMoveData genConf state).h1),
             BitVec.ofNat width (GenGc.gcMoveData genConf state).a,
             p + wordSemBytesInWord * BitVec.ofNat width
               (heapLength ((GenGc.gcMoveData genConf state).h1 ++ (GenGc.gcMoveData genConf state).h2)),
             BitVec.ofNat width ((GenGc.gcMoveData genConf state).a + (GenGc.gcMoveData genConf state).n),
             p + wordSemBytesInWord * BitVec.ofNat width
               (heapLength ((GenGc.gcMoveData genConf state).h1 ++ (GenGc.gcMoveData genConf state).h2) +
                 (GenGc.gcMoveData genConf state).n),
             p + wordSemBytesInWord * BitVec.ofNat width
               (heapLength ((GenGc.gcMoveData genConf state).h1 ++ (GenGc.gcMoveData genConf state).h2 ++
                 (GenGc.gcMoveData genConf state).r4) + (GenGc.gcMoveData genConf state).n),
             curr, m', domain) = (i1, pa1, ib1, pb1, memory1, cr) := by
          rw [iEq, ibEq, paEq, pbEq] at wordTail
          simp only [h2', r4Empty, List.append_nil] at totalEq
          simpa only [h2', List.append_nil, totalEq] using wordTail
        have result := ih (k - 1) (by omega) (GenGc.gcMoveData genConf state) state1 m' memory1
          xs' pb1 pa1 ib1 i1 cr abstractTail stateOk (by simpa [heapEq] using heapBound)
          (by simpa [heapEq] using heapBytesBound) (constants.2.2.trans r3Empty)
          (constants.2.1.trans r2Empty) tailRun inv' sep' refs' xsLen.symm
        rw [flags, cdTrue]
        simpa only [Bool.true_and, heapEq] using result
    · obtain ⟨positive, abstractTail, middleOk⟩ :=
        genLoop_refsStep genConf state state1 k r4Empty abstractRun stateOk
      have different := (genLoop_refPointers_ne state p good invariant heapBytesBound r4Empty).symm
      obtain ⟨end', i', pa', ib', pb', m', cd, cr, wordScan, wordTail, flags⟩ :=
        genLoop_wordRefsStep conf k _ _ _ _ _ _ curr memory domain i1 pa1 ib1 pb1 memory1 c1
          different positive wordRun
      let start := { state with r2 := state.r4, r4 := [] }
      have startInv : genLenInv start := by
        simpa [start, genLenInv, r2Empty, r3Empty] using invariant
      have startSep : SetSep.star (SetSep.star (wordHeap curr start.heap conf) (wordHeapParts conf p start xs)) frame
          (SetSep.fun2Set (memory, fun address => domain address = true)) := by
        simpa [start, wordHeapParts, r2Empty, r3Empty] using separated
      have startRefs : (start.r4 ++ start.r3 ++ start.r2 ++ start.r1).all (isRefElement genConf.isRef) = true := by
        simpa [start, r2Empty, r3Empty] using refs
      have heapLimit : heapLength state.heap ≤ 2 ^ width := heapBound.trans (Nat.div_le_self _ _)
      have countBound : start.r2.length ≤ 2 ^ width := by
        simpa [start] using (genLoop_scanFuel state (2 ^ width) invariant heapLimit).2
      have scanRun : wordGenGcMoveRefs conf (2 ^ width)
          (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (start.h1 ++ start.h2 ++ start.r4 ++ start.r3) + xs.length),
           p + wordSemBytesInWord * BitVec.ofNat width (heapLength (start.h1 ++ start.h2 ++ start.r4 ++ start.r3 ++ start.r2) + xs.length),
           BitVec.ofNat width start.a,
           p + wordSemBytesInWord * BitVec.ofNat width (heapLength (start.h1 ++ start.h2)),
           BitVec.ofNat width (start.a + start.n),
           p + wordSemBytesInWord * BitVec.ofNat width (heapLength (start.h1 ++ start.h2) + start.n),
           curr, memory, domain) = (end', i', pa', ib', pb', m', cd) := by
        simpa [start, r3Empty, length, List.append_assoc] using wordScan
      obtain ⟨xs', sep', r3', r2', heapEq, cdTrue, iEq, ibEq, xsLen, accounting,
          paEq, pbEq, endEq, inv', refs'⟩ :=
        wordGenGcMoveRefs_thm conf genConf (2 ^ width) start (GenGc.gcMoveRefs genConf start)
          memory m' domain curr p xs pb' pa' ib' i' end' frame cd rfl (by simpa [start] using middleOk)
          (by simpa [start] using heapBound) (by simpa [start] using heapBytesBound)
          refClass lenBound scanRun countBound startInv startSep startRefs (by simpa [start] using length) good
      have h1Eq := genMoveRefs_const genConf start (GenGc.gcMoveRefs genConf start) rfl
      have endCount : heapLength ((GenGc.gcMoveRefs genConf start).h1 ++
          (GenGc.gcMoveRefs genConf start).h2 ++ (GenGc.gcMoveRefs genConf start).r4) +
            (GenGc.gcMoveRefs genConf start).n = heapLength (state.h1 ++ state.h2) + state.n := by
        change heapLength state.h2 + state.n + 0 =
          heapLength (GenGc.gcMoveRefs genConf start).h2 + (GenGc.gcMoveRefs genConf start).n +
            heapLength (GenGc.gcMoveRefs genConf start).r4 at accounting
        have h1State : (GenGc.gcMoveRefs genConf start).h1 = state.h1 := by simpa [start] using h1Eq
        simp only [heapLength_append, h1State] at ⊢
        omega
      have tailRun : wordGenGcMoveLoop conf (k - 1)
          (p + wordSemBytesInWord * BitVec.ofNat width (heapLength (GenGc.gcMoveRefs genConf start).h1),
           BitVec.ofNat width (GenGc.gcMoveRefs genConf start).a,
           p + wordSemBytesInWord * BitVec.ofNat width
             (heapLength ((GenGc.gcMoveRefs genConf start).h1 ++ (GenGc.gcMoveRefs genConf start).h2)),
           BitVec.ofNat width ((GenGc.gcMoveRefs genConf start).a + (GenGc.gcMoveRefs genConf start).n),
           p + wordSemBytesInWord * BitVec.ofNat width
             (heapLength ((GenGc.gcMoveRefs genConf start).h1 ++ (GenGc.gcMoveRefs genConf start).h2) +
               (GenGc.gcMoveRefs genConf start).n),
           p + wordSemBytesInWord * BitVec.ofNat width
             (heapLength ((GenGc.gcMoveRefs genConf start).h1 ++ (GenGc.gcMoveRefs genConf start).h2 ++
               (GenGc.gcMoveRefs genConf start).r4) + (GenGc.gcMoveRefs genConf start).n),
           curr, m', domain) = (i1, pa1, ib1, pb1, memory1, cr) := by
        rw [iEq, ibEq, paEq, pbEq] at wordTail
        rw [endCount]
        simpa only [h1Eq, start] using wordTail
      have result := ih (k - 1) (by omega) (GenGc.gcMoveRefs genConf start) state1 m' memory1
        xs' pb1 pa1 ib1 i1 cr (by simpa [start] using abstractTail) stateOk
        (by simpa [heapEq, start] using heapBound) (by simpa [heapEq, start] using heapBytesBound)
        r3' r2' tailRun inv' sep' refs' xsLen.symm
      rw [flags, cdTrue]
      simpa only [Bool.true_and, heapEq, start] using result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
