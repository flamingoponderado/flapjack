import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PartialData

/-! Remembered-reference scan for partial generational collection. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

private instance {α : Type} : Std.Associative (SetSep.star (α := α)) :=
  ⟨fun p q r => (SetSep.starAssoc p q r).symm⟩
private instance {α : Type} : Std.Commutative (SetSep.star (α := α)) := ⟨SetSep.starComm⟩

/-- Expose the first remembered reference's header and roots for the partial
root-list simulation. This is local factoring of the reference-scan proof. -/
theorem partialRefScan_headCell {width : Nat} [NeZero width] (conf : Config)
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail old current : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa k : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (mutable : isMutTag tag)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true))) :
    ∃ header : BitVec width,
      wordPayload roots len tag payload conf = (header, roots.map (wordAddr conf), true) ∧
      roots.length = len ∧ roots.length < 2 ^ (width - 4) ∧
      decodeLength conf header = BitVec.ofNat width roots.length ∧
      memory k = .word header ∧ domain k = true ∧
      SetSep.star (SetSep.star (SetSep.star
        (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
        (Misc.wordList pa xs)) (Misc.wordList (k + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (k, .word header))
          (SetSep.star frame (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf)))
        (SetSep.fun2Set (memory, fun address => domain address = true)) := by
  let source := wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf
  let rest := SetSep.star source frame
  have arrangement : SetSep.star (SetSep.star
      (wordHeap k ([] ++ .dataElement roots len (tag, payload) :: tail) conf) (Misc.wordList pa xs)) rest
      (SetSep.fun2Set (memory, fun address => domain address = true)) := by
    have reorder : SetSep.star (SetSep.star (SetSep.star source (Misc.wordList pa xs))
        (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame =
      SetSep.star (SetSep.star (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)
        (Misc.wordList pa xs)) rest := by dsimp [rest]; ac_rfl
    change SetSep.star (SetSep.star (SetSep.star source (Misc.wordList pa xs))
      (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame _ at separated
    rw [reorder] at separated
    simpa only [List.nil_append] using separated
  obtain ⟨header, encoded, rootLen, bound, decoded, read, present, cell⟩ :=
    refScan_dataCell conf [] tail roots len tag payload k pa xs memory domain rest mutable arrangement
  refine ⟨header, encoded, rootLen, bound, decoded, ?_, ?_, ?_⟩
  · simpa [heapLength] using read
  · simpa [heapLength] using present
  · simp only [heapLength, List.map_nil, List.sum_nil, wordHeap] at cell
    simp only [BitVec.mul_zero, BitVec.add_zero] at cell
    have reorder : SetSep.star (SetSep.star (Misc.wordList pa xs)
        (Misc.wordList (k + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (k, .word header)) (SetSep.star (SetSep.star rest SetSep.emp)
          (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))) =
      SetSep.star (SetSep.star (SetSep.star source (Misc.wordList pa xs))
        (Misc.wordList (k + wordSemBytesInWord) (roots.map (wordAddr conf))))
        (SetSep.star (SetSep.one (k, .word header))
          (SetSep.star frame (wordHeap (k + wordSemBytesInWord * BitVec.ofNat width (len + 1)) tail conf))) := by
      rw [SetSep.starComm rest SetSep.emp, StackRemove.StackHeap.starEmptyLeft]
      dsimp [rest]
      ac_rfl
    exact (congrFun reorder _).mp cell

/-- The represented nonempty reference list takes one concrete scan step. -/
theorem partialRefScan_wordStep {width : Nat} [NeZero width] (conf : Config) (fuel : Nat)
    (genConf : GenGcPartial.Config (HeapTag × List (WordLocW width)))
    (roots : List (HeapAddress (WordLocW width))) (len : Nat) (tag : HeapTag)
    (payload : List (WordLocW width))
    (tail old current : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (curr pa k i : BitVec width) (xs : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (mutable : isMutTag tag)
    (separated : SetSep.star (SetSep.star (SetSep.star
      (wordHeap (curr + wordSemBytesInWord * BitVec.ofNat width (heapLength old)) current conf)
      (Misc.wordList pa xs)) (wordHeap k (.dataElement roots len (tag, payload) :: tail) conf)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (countBound : heapLength (.dataElement roots len (tag, payload) :: tail) ≤ fuel)
    (byteBound : heapLength (.dataElement roots len (tag, payload) :: tail) * (width / 8) < 2 ^ width)
    (good : goodDimindex width) :
    let last := k + wordSemBytesInWord * BitVec.ofNat width (heapLength (.dataElement roots len (tag, payload) :: tail))
    let gs := wordSemBytesInWord * BitVec.ofNat width genConf.genStart
    let rs := wordSemBytesInWord * BitVec.ofNat width genConf.refsStart
    wordGenGcPartialMoveRefList fuel conf (k, i, pa, curr, memory, domain, true, gs, rs, last) =
      (let (next, i1, pa1, memory1, c1) := wordGenGcPartialMoveList conf
        (k + wordSemBytesInWord, BitVec.ofNat width roots.length, i, pa, curr, memory, domain, gs, rs)
       wordGenGcPartialMoveRefList (fuel - 1) conf (next, i1, pa1, curr, memory1, domain, c1, gs, rs, last)) := by
  obtain ⟨header, _, _, _, decoded, read, present, _⟩ :=
    partialRefScan_headCell conf roots len tag payload tail old current curr pa k xs memory domain frame mutable separated
  have positive : 0 < heapLength (.dataElement roots len (tag, payload) :: tail) := by simp [heapLength, elLength]
  have bytesPositive : 0 < width / 8 := by rcases good with rfl | rfl <;> decide
  have bound : (width / 8) * heapLength (.dataElement roots len (tag, payload) :: tail) < 2 ^ width := by
    simpa only [Nat.mul_comm] using byteBound
  have nonzero : wordSemBytesInWord * BitVec.ofNat width (heapLength (.dataElement roots len (tag, payload) :: tail)) ≠ 0 := by
    intro eq
    have natEq := congrArg BitVec.toNat eq
    simp [wordSemBytesInWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at natEq
    rcases natEq with small | empty <;> omega
  have different : k ≠ k + wordSemBytesInWord * BitVec.ofNat width (heapLength (.dataElement roots len (tag, payload) :: tail)) := by
    intro eq
    apply nonzero
    apply add_left_cancel (a := k)
    simpa using eq.symm
  have fuelNonzero : fuel ≠ 0 := by omega
  dsimp only
  rw [wordGenGcPartialMoveRefList, if_neg different, if_neg fuelNonzero]
  simp only [read, present, wordSemIsWordLoc, wordSemTheWord, Bool.true_and, decoded]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
