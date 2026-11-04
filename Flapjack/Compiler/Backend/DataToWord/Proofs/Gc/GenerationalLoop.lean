import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalData

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
