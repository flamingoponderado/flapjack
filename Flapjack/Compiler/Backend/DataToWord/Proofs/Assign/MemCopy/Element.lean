module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Variables
@[expose] public section

/-! Memory-relation preservation for the generated block-copy loop. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum

namespace MemCopyWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end MemCopyWitness

/-- Extend the paired roots with the next block field read by the copy loop. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IMP_memcopy_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem impMemcopyLemma {width : Nat} [NeZero width] {C F C2 F2 : Type}
    (c : Config) (s1 : WordSemStateFiniteExact width C F) (x : DataSem.State C2 F2)
    (ts sp a1 stamp tag start : Nat) (values ys : List DataSem.Value) (words : List (WordLocW width))
    (vars : List (DataSem.Value × WordLocW width)) (wptr wx : BitVec width)
    (m : BitVec width → WordLocW width)
    (rel : memoryRel c s1.be ts x.refs sp s1.store m s1.mdomain
      ((.block stamp tag values, .word wptr) :: (ys.zip words ++ vars)))
    (bound : start < values.length) (length : ys.length = words.length) (good : goodDimindex width)
    (read : sptLookup (adjustVar a1) s1.locals = some (.word wptr))
    (eval : s1.wordExp (realAddr c (adjustVar a1)) = some (.word wx)) :
    memoryRel c s1.be ts x.refs sp s1.store m s1.mdomain
      ((.block stamp tag values, .word wptr) ::
        ((ys ++ [values[start]]).zip (words ++ [m (wx + StackRemove.bytesInWord width +
          StackRemove.bytesInWord width * BitVec.ofNat width start)]) ++ vars)) ∧
      s1.mdomain (wx + StackRemove.bytesInWord width +
        StackRemove.bytesInWord width * BitVec.ofNat width start) = true := by
  obtain ⟨ptr, addr, _, ptrEq, real, dom, extended⟩ :=
    memoryRel_elAny c s1.be ts x.refs sp s1.store m s1.mdomain stamp tag values (.word wptr)
      (ys.zip words ++ vars) start bound ⟨rel, good⟩
  have ptrEq' : ptr = wptr := (WordLocW.word.inj ptrEq).symm
  subst ptr
  have shift : shiftLength c < width := by
    obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, _⟩ := rel
    exact heapMem.2.2.2.2.2.1
  have eval2 := getRealAddr_lemma c (adjustVar a1) s1 wptr addr
    ⟨shift, good, by simpa [WordSemStateFiniteExact.getVar] using read, real⟩
  have same : wx = addr := WordLocW.word.inj (Option.some.inj (eval.symm.trans eval2))
  subst wx
  constructor
  · rw [List.zip_append length]
    simp only [List.zip_cons_cons, List.zip_nil_left]
    apply memoryRel_rearrange c s1.be ts x.refs sp s1.store m s1.mdomain _ _ ?_ extended
    intro pair member
    simp only [List.mem_cons, List.mem_append] at member ⊢
    tauto
  · exact dom
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
