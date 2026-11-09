module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.StoreEach
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapExpand
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteStore
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

@[expose] public section

/-! Recovering the constructor's free word region from the actual heap relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Writing a separated free region establishes the exact word-list assertion
for the values written, while preserving the entire disjoint frame. -/
theorem storeEachMemory_wordList {width : Nat} [NeZero width]
    (base offset : BitVec width) (values : List (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (free : SetSep.star (Misc.wordListExists (base + offset) values.length) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    SetSep.star (Misc.wordList (base + offset) values) frame
      (SetSep.fun2Set (storeEachMemory base offset values memory, fun addr => domain addr = true)) := by
  classical
  induction values generalizing offset memory frame with
  | nil =>
    simpa [storeEachMemory, Misc.wordList,
      (StackRemove.WordListExists.wordListExistsThm (β := WordLocW width) (base + offset) 0).1] using free
  | cons value values ih =>
    simp only [List.length_cons, (StackRemove.WordListExists.wordListExistsThm (base + offset) values.length).2] at free
    obtain ⟨region, outer, split, ⟨old, head, tail, inner, singleton, rest⟩, outerInv⟩ := free
    have exposed : SetSep.star (SetSep.one (base + offset, old))
        (SetSep.star (Misc.wordListExists (base + offset + StackRemove.bytesInWord width) values.length) frame)
        (SetSep.fun2Set (memory, fun addr => domain addr = true)) := by
      rw [SetSep.starAssoc]
      exact ⟨region, outer, split, ⟨head, tail, inner, singleton, rest⟩, outerInv⟩
    have written := SetSep.writeFun2Set value (base + offset) old _ memory (fun addr => domain addr = true) exposed
    rw [SetSep.starComm, star_swap_first] at written
    have tailFree : SetSep.star
        (Misc.wordListExists (base + (offset + BitVec.ofNat width (width / 8))) values.length)
        (SetSep.star (SetSep.one (base + offset, value)) frame)
        (SetSep.fun2Set ((fun key => if key = base + offset then value else memory key),
          fun addr => domain addr = true)) := by
      simp only [StackRemove.bytesInWord, BitVec.add_assoc] at written
      convert written using 1
      congr 2
      funext key
      by_cases same : key = base + offset <;> simp [same]
    have tailResult := ih (offset + BitVec.ofNat width (width / 8)) _ _ tailFree
    rw [star_swap_first, SetSep.starAssoc] at tailResult
    simpa [storeEachMemory, Misc.wordList, StackRemove.bytesInWord, BitVec.add_assoc] using tailResult

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
