module

public import Flapjack.Compiler.Backend.GenGc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MoveData

@[expose] public section

/-! Invariants and immediate-root case of major generational collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The reference classifier applies only to data elements. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "is_Ref_def"]
def isRefElement {α β : Type} (isRef : β → Bool) : HeapElement α β → Bool
  | .dataElement _ _ payload => isRef payload
  | _ => false

/-- The major collector partitions its original heap length among scanned,
not-yet-scanned, free, and reference portions. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "len_inv_def"]
def genLenInv {α β : Type} (state : GcState α β) : Prop :=
  heapLength state.heap = heapLength (state.h1 ++ state.h2) + state.n +
    heapLength (state.r4 ++ state.r3 ++ state.r2 ++ state.r1)

/-- Header tag bits used for mutable references and thunks. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "muttag_header_def"
  (words_as_type_indexed_bitvec)]
def muttagHeader {width : Nat} [NeZero width] : HeapTag → BitVec width
  | .thunkTag mode => (thunkTagToBits mode <<< (3 : Nat)) ||| 6
  | _ => 2

/-- A mutable-tag payload encodes its pointers and validity in the source form. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "isMutTag_word_payload_IMP"
  (words_as_type_indexed_bitvec)]
theorem isMutTag_wordPayloadImp {headerWidth : Nat} {payloadWidth : Nat} [NeZero headerWidth] [NeZero payloadWidth]
    (addresses : List (HeapAddress (WordLocW payloadWidth))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW payloadWidth)) (conf : Config) (header : BitVec headerWidth)
    (words : List (WordLocW payloadWidth)) (valid : Bool)
    (encoded : wordPayload addresses len tag payload conf = (header, words, valid))
    (mutable : isMutTag tag) :
    header = makeHeader conf (muttagHeader tag) addresses.length ∧
      words = addresses.map (wordAddr conf) ∧
      (valid = true ↔ payload = [] ∧ addresses.length = len ∧ (tag ≠ .refTag → len = 1)) := by
  rcases mutable with rfl | ⟨mode, rfl⟩
  · simp [wordPayload] at encoded
    obtain ⟨rfl, rfl, rfl⟩ := encoded
    simp [muttagHeader]
  · simp [wordPayload] at encoded
    obtain ⟨rfl, rfl, rfl⟩ := encoded
    simp [muttagHeader]
    intro _ h
    subst len
    rfl

/-- A reference header has bit 3 set and bit 2 clear. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "is_ref_header_alt"
  (words_as_type_indexed_bitvec)]
theorem isRefHeader_alt {width : Nat} [NeZero width] (w : BitVec width)
    (good : goodDimindex width) :
    isRefHeader w = true ↔ w.getLsbD 2 = false ∧ w.getLsbD 3 = true := by
  have widthBound : 3 < width := by rcases good with h | h <;> omega
  have w2 : 2 < width := by omega
  have w3 : 3 < width := by omega
  simp only [isRefHeader, decide_eq_true_eq]
  constructor
  · intro eq
    have h2 := congrArg (fun v : BitVec width => v.getLsbD 2) eq
    have h3 := congrArg (fun v : BitVec width => v.getLsbD 3) eq
    simp only [BitVec.getLsbD_and] at h2 h3
    change (w.getLsbD 2 && (BitVec.ofNat width 12).getLsbD 2) = (BitVec.ofNat width 8).getLsbD 2 at h2
    change (w.getLsbD 3 && (BitVec.ofNat width 12).getLsbD 3) = (BitVec.ofNat width 8).getLsbD 3 at h3
    simp only [BitVec.getLsbD_ofNat, w2, w3, decide_true, Bool.true_and] at h2 h3
    change (w.getLsbD 2 && true) = false at h2
    change (w.getLsbD 3 && true) = true at h3
    simp only [Bool.and_true] at h2 h3
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and]
    change (w.getLsbD i && (BitVec.ofNat width 12).getLsbD i) = (BitVec.ofNat width 8).getLsbD i
    simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    by_cases i2 : i = 2
    · subst i
      change (w.getLsbD 2 && true) = false
      simpa only [Bool.and_true] using h2
    by_cases i3 : i = 3
    · subst i
      change (w.getLsbD 3 && true) = true
      simpa only [Bool.and_true] using h3
    have b12 : (12 : Nat).testBit i = false := by
      by_cases small : i < 4
      · have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl <;> decide
      · have p : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
        exact Nat.testBit_lt_two_pow (by omega)
    have b8 : (8 : Nat).testBit i = false := by
      by_cases small : i < 4
      · have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl <;> decide
      · have p : 2 ^ 4 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (by omega)
        exact Nat.testBit_lt_two_pow (by omega)
    simp only [b12, b8, Bool.and_false]

/-- The header reference bit agrees with the source mutable-tag classifier,
with independent header and payload word widths. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "is_ref_header_thm"
  (words_as_type_indexed_bitvec)]
theorem isRefHeader_thm {headerWidth : Nat} {payloadWidth : Nat} [NeZero headerWidth] [NeZero payloadWidth]
    (addresses : List (HeapAddress (WordLocW payloadWidth))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW payloadWidth)) (conf : Config) (header : BitVec headerWidth)
    (words : List (WordLocW payloadWidth)) (valid : Bool)
    (encoded : wordPayload addresses len tag payload conf = (header, words, valid))
    (good : goodDimindex headerWidth) (bound : conf.lenSize + 5 ≤ headerWidth) :
    isRefHeader header = true ↔ isMutTag tag := by
  rw [isRefHeader_alt header good]
  have shiftBound : 3 < headerWidth - conf.lenSize := by omega
  rcases good with hw | hw <;> subst headerWidth
  all_goals cases tag <;> simp [wordPayload] at encoded
  all_goals rcases encoded with ⟨rfl, rfl, rfl⟩
  all_goals simp_all [makeHeader, makeByteHeader, isMutTag, thunkTagToBits]
  all_goals try (split <;> simp_all)
  all_goals intro h; omega

private theorem clearLowBit {width : Nat} (value : BitVec width) :
    (1 : BitVec width) &&& (value &&& ~~~(1 : BitVec width)) = 0 := by
  rw [BitVec.and_comm, BitVec.and_assoc]
  simp

private theorem starEmptyRight {α : Type} (p : (α → Prop) → Prop) : SetSep.star p SetSep.emp = p := by
  rw [SetSep.starComm, StackRemove.StackHeap.starEmptyLeft]

/-- Immediate-root case of the major generational move simulation, preserving
all original hypotheses and conclusions. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMove_data {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (value : WordLocW width) (root1 : HeapAddress (WordLocW width))
    (curr pa i1 pa1 ib1 pb1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (w : WordLocW width) (c1 : Bool)
    (abstractRun : GenGc.gcMove genConf state (.data value) = (root1, state1))
    (stateOk : state1.ok = true) (h2Empty : state.h2 = []) (r4Empty : state.r4 = [])
    (_heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (_refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (_lenBound : conf.lenSize + 5 ≤ width)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcMove conf (wordAddr conf (.data value), BitVec.ofNat width state.a, pa,
      BitVec.ofNat width (state.a + state.n), pa + wordSemBytesInWord * BitVec.ofNat width state.n,
      curr, memory, domain) = (w, i1, pa1, ib1, pb1, memory1, c1))
    (length : xs.length = state.n) (_good : goodDimindex width)
    (refs : (state.r4 ++ state.r3 ++ state.r2 ++ state.r1).all (isRefElement genConf.isRef) = true) :
    ∃ xs1,
      SetSep.star (SetSep.star (SetSep.star (SetSep.star (wordHeap curr state1.heap conf)
        (wordHeap pa state1.h2 conf)) (wordHeap pb1 state1.r4 conf)) (Misc.wordList pa1 xs1)) frame
        (SetSep.fun2Set (memory1, fun address => domain address = true)) ∧
      w = wordAddr conf root1 ∧ heapLength state1.heap = heapLength state.heap ∧ c1 = true ∧
      i1 = BitVec.ofNat width state1.a ∧ ib1 = BitVec.ofNat width (state1.a + state1.n) ∧
      state1.n = xs1.length ∧ state.n = heapLength state1.h2 + state1.n + heapLength state1.r4 ∧
      pa1 = pa + wordSemBytesInWord * BitVec.ofNat width (heapLength state1.h2) ∧
      pb1 = pa1 + wordSemBytesInWord * BitVec.ofNat width state1.n ∧
      (state1.r4 ++ state1.r3 ++ state1.r2 ++ state1.r1).all (isRefElement genConf.isRef) = true := by
  simp only [GenGc.gcMove, Prod.mk.injEq] at abstractRun
  obtain ⟨rfl, rfl⟩ := abstractRun
  cases value with
  | loc l1 l2 =>
    simp only [wordAddr, wordGenGcMove, decide_true, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, ?_, rfl, rfl, rfl, rfl, rfl, length.symm, ?_, ?_, rfl, refs⟩
    · simpa [h2Empty, r4Empty, wordHeap, starEmptyRight] using separated
    · simp [h2Empty, r4Empty, heapLength]
    · simp [h2Empty, heapLength]
  | word bits =>
    simp only [wordAddr, wordGenGcMove, clearLowBit, ↓reduceIte, Prod.mk.injEq] at wordRun
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := wordRun
    refine ⟨xs, ?_, rfl, rfl, rfl, rfl, rfl, length.symm, ?_, ?_, rfl, refs⟩
    · simpa [h2Empty, r4Empty, wordHeap, starEmptyRight] using separated
    · simp [h2Empty, r4Empty, heapLength]
    · simp [h2Empty, heapLength]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
