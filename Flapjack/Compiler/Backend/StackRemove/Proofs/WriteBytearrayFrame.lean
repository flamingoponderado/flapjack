import Flapjack.Compiler.Backend.StackRemove.Proofs.WriteBytearray
import Flapjack.Compiler.Backend.StackRemove.Proofs.Memory

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack

/-- Full original frame theorem over the actual reviewed Memory/SetSep carriers.
The arbitrary frame predicate and its whole heap remain unchanged after both
writes; union and disjointness are derived from the original separation premise.
No carrier definitions or parallel separation predicates are introduced here.
All original premises and the complete updated frame conclusion are retained.
Alignment is a common symbolic key, without a numerical LOG2 or width premise. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml"
  "write_bytearray_lemma" (words_as_type_indexed_bitvec)]
theorem writeBytearrayFrame {width : Nat} [NeZero width]
    (bytes : List (BitVec 8)) (address : BitVec width)
    (source : BitVec width → WordLocW width) (sourceDomain : BitVec width → Bool)
    (bigEndian : Bool) (readBytes : List (BitVec 8))
    (p : ((BitVec width × WordLocW width) → Prop) → Prop)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (original : SetSep.star (memoryHOL source (fun key => sourceDomain key = true)) p
      (SetSep.fun2Set (memory, fun key => domain key = true)) ∧
      readBytearrayWordHOL address bytes.length
        (memLoadByteAuxExact source sourceDomain bigEndian) = some readBytes) :
    SetSep.star
      (memoryHOL (writeBytearrayExact address bytes source sourceDomain bigEndian)
        (fun key => sourceDomain key = true)) p
      (SetSep.fun2Set (writeBytearrayExact address bytes memory domain bigEndian,
        fun key => domain key = true)) := by
  rcases original with ⟨⟨left, frame, partition, leftMemory, preserved⟩, read⟩
  have union (point value) : domain point = true ∧ memory point = value ↔
      (sourceDomain point = true ∧ source point = value) ∨ frame (point, value) := by
    have eq := congrFun partition.1 (point, value)
    rw [leftMemory] at eq
    simpa only [SetSep.fun2SetThm, and_comm] using (iff_of_eq eq).symm
  have disjoint (point value) (owned : sourceDomain point = true ∧ source point = value)
      (framed : frame (point, value)) : False := by
    apply partition.2 (point, value)
    refine ⟨?_, framed⟩
    rw [leftMemory]
    exact (SetSep.fun2SetThm source _ point value).mpr ⟨owned.2, owned.1⟩
  have correspondence (point) (inside : sourceDomain point = true) :
      source point = memory point ∧ domain point = true := by
    have whole := (union point (source point)).mpr (Or.inl ⟨inside, rfl⟩)
    exact ⟨whole.2.symm, whole.1⟩
  have subset (point) (inside : sourceDomain point = true) : domain point = true :=
    (correspondence point inside).2
  have outside (point value) (framed : frame (point, value)) :
      sourceDomain point = false := by
    cases inside : sourceDomain point with
    | false => rfl
    | true =>
      have whole := (union point value).mpr (Or.inr framed)
      exact False.elim (disjoint point value
        ⟨inside, (correspondence point inside).1.trans whole.2⟩ framed)
  have same (point) (inside : sourceDomain point = true) :
      writeBytearrayExact address bytes source sourceDomain bigEndian point =
        writeBytearrayExact address bytes memory domain bigEndian point :=
    writeBytearrayEq bytes address source memory readBytes point sourceDomain domain bigEndian
      ⟨subset, correspondence, read, (correspondence point inside).1⟩
  have ignored (point) (out : sourceDomain point = false) :
      writeBytearrayExact address bytes memory domain bigEndian point = memory point :=
    writeBytearrayIgnore bytes address readBytes point source memory sourceDomain domain bigEndian
      ⟨subset, read, out⟩
  refine ⟨SetSep.fun2Set (writeBytearrayExact address bytes source sourceDomain bigEndian,
    fun key => sourceDomain key = true), frame, ⟨?_, ?_⟩, rfl, preserved⟩
  · funext entry
    rcases entry with ⟨point, value⟩
    apply propext
    constructor
    · intro part
      rcases part with owned | framed
      · have facts := (SetSep.fun2SetThm _ _ point value).mp owned
        exact (SetSep.fun2SetThm _ _ point value).mpr
          ⟨(same point facts.2).symm.trans facts.1, subset point facts.2⟩
      · have whole := (union point value).mpr (Or.inr framed)
        exact (SetSep.fun2SetThm _ _ point value).mpr
          ⟨(ignored point (outside point value framed)).trans whole.2, whole.1⟩
    · intro writtenGraph
      have facts := (SetSep.fun2SetThm _ _ point value).mp writtenGraph
      cases sourceInside : sourceDomain point with
      | true =>
        exact Or.inl ((SetSep.fun2SetThm _ _ point value).mpr
          ⟨(same point sourceInside).trans facts.1, sourceInside⟩)
      | false =>
        have old := (ignored point sourceInside).symm.trans facts.1
        rcases (union point value).mp ⟨facts.2, old⟩ with owned | framed
        · simp [sourceInside] at owned
        · exact Or.inr framed
  · rintro ⟨point, value⟩ ⟨owned, framed⟩
    have facts := (SetSep.fun2SetThm _ _ point value).mp owned
    have incompatible := outside point value framed
    rw [facts.2] at incompatible
    cases incompatible

end Flapjack.Compiler.Backend.StackRemove
