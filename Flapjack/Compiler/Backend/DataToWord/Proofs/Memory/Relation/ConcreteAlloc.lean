module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.HeaderDecode
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StoreListThm
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
public import Flapjack.Compiler.Backend.GcShared.Filter
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- A valid constructor cell has the concrete header-and-fields word list.
This is Flapjack infrastructure for the original constructor memory proof. -/
theorem wordElBlockEq {width : Nat} [NeZero width] (c : DataToWord.Config)
    (addr : BitVec width) (tag : Nat) (rs : List (HeapAddress (WordLocW width)))
    (ws : List (WordLocW width)) (hd : BitVec width)
    (mapped : rs.map (wordAddr c) = ws)
    (encoded : encodeHeader c (4 * tag) ws.length = some hd)
    (configBound : c.lenSize + 5 < width) (good : goodDimindex width) :
    wordEl addr (blockRep tag rs) c = Misc.wordList addr (.word hd :: ws) := by
  have size : rs.length = ws.length := by have h := congrArg List.length mapped; simpa using h
  have header : makeHeader c ((BitVec.ofNat width tag) <<< (2 : Nat)) rs.length = hd := by
    have h := encoded
    simp only [encodeHeader] at h
    split at h
    · have eq := Option.some.inj h
      rw [← eq, size]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mul_comm]
    · simp at h
  have decoded := encodeHeaderImp c (4 * tag) ws.length hd encoded configBound good
  funext heap
  apply propext
  simp only [wordEl, blockRep, wordPayload, List.isEmpty_nil, Bool.true_and]
  rw [header, mapped, size]
  simp [show encodeHeader c (tag * 4) ws.length = some hd by simpa [Nat.mul_comm] using encoded, decoded.1, decoded.2, StackRemove.WordListExists.starCond]
private theorem starSwapFirst {α : Type} (p q r : (α → Prop) → Prop) :
    SetSep.star p (SetSep.star q r) = SetSep.star q (SetSep.star p r) := by
  rw [SetSep.starAssoc, SetSep.starComm p q, ← SetSep.starAssoc]

/-- Store a constructor into free space while preserving the separated heap frame.
This is Flapjack infrastructure for the original constructor memory proof. -/
theorem wordHeapAlloc {width : Nat} [NeZero width] (c : DataToWord.Config)
    (curr : BitVec width) (pre post : ValueHeap width) (free : Nat)
    (tag : Nat) (rs : List (HeapAddress (WordLocW width))) (ws : List (WordLocW width))
    (hd : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (fits : ws.length + 1 ≤ free) (mapped : rs.map (wordAddr c) = ws)
    (encoded : encodeHeader c (4 * tag) ws.length = some hd)
    (configBound : c.lenSize + 5 < width) (good : goodDimindex width)
    (old : SetSep.star (wordHeap curr (pre ++ heapExpand free ++ post) c) frame
      (SetSep.fun2Set (m, fun x => dm x = true))) :
    ∃ m1, storeList (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))
        (.word hd :: ws) m dm = some m1 ∧
      SetSep.star (wordHeap curr
        (pre ++ [blockRep tag rs] ++ heapExpand (free - (ws.length + 1)) ++ post) c) frame
        (SetSep.fun2Set (m1, fun x => dm x = true)) := by
  let a := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
  let k := ws.length + 1
  let rem := free - k
  have splitLen : k + rem = free := by dsimp [k, rem]; omega
  have splitWords : Misc.wordListExists (β := WordLocW width) a free =
      SetSep.star (Misc.wordListExists a k)
        (Misc.wordListExists (a + StackRemove.bytesInWord width * BitVec.ofNat width k) rem) := by
    rw [← splitLen]
    exact StackRemove.Proofs.WordListMemory.wordListExistsAdd k rem a
  have old1 := old
  rw [List.append_assoc, wordHeapAppend, wordHeapAppend, wordHeap_heapExpand, splitWords] at old1
  simp only [heapLength_heapExpand] at old1
  repeat rw [← SetSep.starAssoc] at old1
  rw [starSwapFirst] at old1
  let other := SetSep.star (wordHeap curr pre c)
    (SetSep.star (Misc.wordListExists (a + StackRemove.bytesInWord width * BitVec.ofNat width k) rem)
      (SetSep.star (wordHeap (a + StackRemove.bytesInWord width * BitVec.ofNat width free) post c) frame))
  have storePremise : SetSep.star (Misc.wordListExists a (.word hd :: ws).length) other
      (SetSep.fun2Set (m, fun x => dm x = true)) := by
    simpa [a, k, other] using old1
  obtain ⟨m1, run, new1⟩ := storeListThm (.word hd :: ws) a other m dm storePremise
  refine ⟨m1, run, ?_⟩
  have cell := wordElBlockEq c a tag rs ws hd mapped encoded configBound good
  simp only [other] at new1
  rw [starSwapFirst] at new1
  repeat rw [SetSep.starAssoc] at new1
  have size : rs.length = ws.length := by have h := congrArg List.length mapped; simpa using h
  have cellLength : elLength (blockRep (β := WordLocW width) tag rs) = k := by
    simp [blockRep, elLength, size, k]
  have endAddr : (a + StackRemove.bytesInWord width * BitVec.ofNat width k) +
      StackRemove.bytesInWord width * BitVec.ofNat width rem =
      a + StackRemove.bytesInWord width * BitVec.ofNat width free := by
    calc
      _ = a + (StackRemove.bytesInWord width * BitVec.ofNat width k +
          StackRemove.bytesInWord width * BitVec.ofNat width rem) := by rw [BitVec.add_assoc]
      _ = a + StackRemove.bytesInWord width * (BitVec.ofNat width k + BitVec.ofNat width rem) := by rw [BitVec.mul_add]
      _ = _ := by rw [← BitVec.ofNat_add, splitLen]
  simp only [List.append_assoc, wordHeapAppend, List.singleton_append, wordHeap]
  have suffixLen : heapLength (blockRep (β := WordLocW width) tag rs :: heapExpand rem) = free := by
    change elLength (blockRep (β := WordLocW width) tag rs) + heapLength (heapExpand rem : ValueHeap width) = free
    rw [cellLength, heapLength_heapExpand, splitLen]
  rw [cellLength, suffixLen, wordHeap_heapExpand, cell]
  repeat rw [SetSep.starAssoc]
  simpa [a, k, rem] using new1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
