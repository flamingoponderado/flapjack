module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalNonRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalRef

@[expose] public section

/-! Full single-root major-collector simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The complete single-root major-collector simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_gen_gc_move_thm"
  (words_as_type_indexed_bitvec)]
theorem wordGenGcMove_thm {width : Nat} [NeZero width] (conf : Config)
    (genConf : GenGc.Config (HeapTag × List (WordLocW width)))
    (state state1 : GcState (WordLocW width) (HeapTag × List (WordLocW width)))
    (root root1 : HeapAddress (WordLocW width))
    (curr pa i1 pa1 ib1 pb1 : BitVec width) (xs : List (WordLocW width))
    (memory memory1 : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (w : WordLocW width) (c1 : Bool)
    (abstractRun : GenGc.gcMove genConf state root = (root1, state1))
    (stateOk : state1.ok = true) (h2Empty : state.h2 = []) (r4Empty : state.r4 = [])
    (heapBound : heapLength state.heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (refClass : ∀ t r, genConf.isRef (t, r) = true ↔ isMutTag t)
    (lenBound : conf.lenSize + 5 ≤ width)
    (separated : SetSep.star (SetSep.star (wordHeap curr state.heap conf) (Misc.wordList pa xs)) frame
      (SetSep.fun2Set (memory, fun address => domain address = true)))
    (wordRun : wordGenGcMove conf (wordAddr conf root, BitVec.ofNat width state.a, pa,
      BitVec.ofNat width (state.a + state.n), pa + wordSemBytesInWord * BitVec.ofNat width state.n,
      curr, memory, domain) = (w, i1, pa1, ib1, pb1, memory1, c1))
    (length : xs.length = state.n) (good : goodDimindex width)
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
  cases root with
  | data value =>
    exact wordGenGcMove_data conf genConf state state1 value root1 curr pa i1 pa1 ib1 pb1 xs memory memory1
      domain frame w c1 abstractRun stateOk h2Empty r4Empty heapBound refClass lenBound separated wordRun length good refs
  | pointer ptr value =>
    cases found : heapLookup ptr state.heap with
    | none =>
      simp only [GenGc.gcMove, found, Prod.mk.injEq] at abstractRun
      obtain ⟨_, rfl⟩ := abstractRun
      simp at stateOk
    | some element =>
      cases element with
      | unused len =>
        simp only [GenGc.gcMove, found, Prod.mk.injEq] at abstractRun
        obtain ⟨_, rfl⟩ := abstractRun
        simp at stateOk
      | forwardPointer forwarded oldValue len =>
        exact wordGenGcMove_forward conf genConf state state1 ptr forwarded len value oldValue root1 curr pa i1 pa1
          ib1 pb1 xs memory memory1 domain frame w c1 found abstractRun stateOk h2Empty r4Empty heapBound
          refClass lenBound separated wordRun length good refs
      | dataElement addresses len payload =>
        rcases payload with ⟨tag, payload⟩
        by_cases isRef : isMutTag tag
        · exact wordGenGcMove_ref conf genConf state state1 ptr len value addresses tag payload root1 curr pa i1 pa1
            ib1 pb1 xs memory memory1 domain frame w c1 found isRef abstractRun stateOk h2Empty r4Empty heapBound
            refClass lenBound separated wordRun length good refs
        · exact wordGenGcMove_nonRef conf genConf state state1 ptr len value addresses tag payload root1 curr pa i1 pa1
            ib1 pb1 xs memory memory1 domain frame w c1 found isRef abstractRun stateOk h2Empty r4Empty heapBound
            refClass lenBound separated wordRun length good refs

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
