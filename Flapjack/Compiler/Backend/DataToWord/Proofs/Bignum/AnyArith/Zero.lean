module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith.Iop
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.BitLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute

@[expose] public section

/-! `AnyArith_thm`: the state relation after the bignum call, before the
result is stored (Flapjack-only helpers following the HOL proof's
"check point 2"). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- Reassembling the word heap around the reserved space. -/
theorem heap_rebuild {width : Nat} [NeZero width] {c : Config}
    {heap ha hb : ValueHeap width} {n k limit : Nat} {curr other : BitVec width}
    {x0 ow : WordLocW width} {ys : List (WordLocW width)}
    {m : BitVec width → WordLocW width} {dm : BitVec width → Prop}
    (hheap : heap = ha ++ .unused (n + k) :: hb) (limNZ : limit ≠ 0) (hys : ys.length = n)
    (hmem : SetSep.star
      (Misc.wordList (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength ha) +
        StackRemove.bytesInWord width) ys)
      (SetSep.star (SetSep.one (curr + StackRemove.bytesInWord width *
          BitVec.ofNat width (heapLength ha), x0))
        (SetSep.star (SetSep.one (other, ow)) (splitFrame c curr other ha hb n k limit)))
      (SetSep.fun2Set (m, dm))) :
    SetSep.star (wordHeap curr heap c) (wordHeap other (heapExpand limit) c)
      (SetSep.fun2Set (m, dm)) := by
  set b := StackRemove.bytesInWord width
  set u := curr + b * BitVec.ofNat width (heapLength ha)
  have hbAddr : u + b * BitVec.ofNat width (elLength (HeapElement.unused (α := WordLocW width)
      (β := HeapTag × List (WordLocW width)) (n + k))) =
      u + b + b * BitVec.ofNat width n + b * BitVec.ofNat width k := by
    simp only [elLength, BitVec.ofNat_add]
    rw [show (1#width : BitVec width) = 1 from rfl]; ring
  rw [hheap, wordHeapAppend, wordHeap, wordEl, wordListExists_split3,
    Gc.wordHeap_nonEmptyLimit limNZ, hbAddr, show (wordSemBytesInWord : BitVec width) = b from rfl,
    SetSep.starComm _ (SetSep.sepExists _), starExists_left]
  refine ⟨ow, ?_⟩
  unfold splitFrame at hmem
  dsimp only at hmem
  set A := wordHeap curr ha c
  set Wk := Misc.wordListExists (β := WordLocW width) (u + b + b * BitVec.ofNat width n) k
  set B := wordHeap (valueWidth := width) (u + b + b * BitVec.ofNat width n + b * BitVec.ofNat width k) hb c
  set O := wordHeap (valueWidth := width) (other + b) (heapExpand (limit - 1)) c
  rw [show SetSep.star (Misc.wordList (u + b) ys) (SetSep.star (SetSep.one (u, x0))
      (SetSep.star (SetSep.one (other, ow)) (SetSep.star A (SetSep.star Wk (SetSep.star B O))))) =
      SetSep.star (Misc.wordList (u + b) ys) (SetSep.star (SetSep.one (u, x0))
      (SetSep.star (SetSep.one (other, ow)) (SetSep.star A (SetSep.star Wk (SetSep.star B O))))) from rfl]
    at hmem
  have h1 := starWordListExists_intro_left _ _ _ _ hmem
  rw [hys, show SetSep.star (Misc.wordListExists (u + b) n) (SetSep.star (SetSep.one (u, x0))
      (SetSep.star (SetSep.one (other, ow)) (SetSep.star A (SetSep.star Wk (SetSep.star B O))))) =
      SetSep.star (Misc.wordList u [x0]) (SetSep.star (Misc.wordListExists (u + b) n)
      (SetSep.star (SetSep.one (other, ow)) (SetSep.star A (SetSep.star Wk (SetSep.star B O))))) by
      rw [wordList_single]; ac_rfl] at h1
  have h2 := starWordListExists_intro_left _ _ _ _ h1
  simp only [List.length_singleton] at h2
  rw [show SetSep.star (SetSep.star (SetSep.one (other, ow)) O)
      (SetSep.star A (SetSep.star (SetSep.star (Misc.wordListExists u 1)
        (SetSep.star (Misc.wordListExists (u + b) n) Wk)) B)) =
      SetSep.star (Misc.wordListExists u 1) (SetSep.star (Misc.wordListExists (u + b) n)
      (SetSep.star (SetSep.one (other, ow)) (SetSep.star A (SetSep.star Wk (SetSep.star B O))))) by
      ac_rfl]
  exact h2


/-- The state relation after the bignum call, returning a placeholder zero
(HOL: the `∃new_c. state_rel ... (SOME [(Number 0,Word 0w)])` step of
`AnyArith_thm`). -/
theorem zero_stateRel {width : Nat} [NeZero width] {C F : Type} {c : Config} {l1 l2 r1 r2 : Nat}
    {s : DataSem.State C F} {L0 : Spt DataSem.Value} {s9 R : WordSemStateFiniteExact width C F}
    {locs : List (Nat × Nat)} {n : Nat}
    {heap ha hb : ValueHeap width} {limit a sp sp1 k : Nat} {gens : GcCombined.GenState}
    {curr other : BitVec width} {x0 ow : WordLocW width} {ys : List (WordLocW width)}
    (rel9 : stateRel c l1 l2 { s with locals := L0, space := n + 1 } s9 none locs)
    (hims : heapInMemoryStore heap a sp sp1 gens c s9.store s9.memory s9.mdomain limit)
    (wml : wordMlInv (heap, s9.be, a, sp, sp1, gens) limit (holThe s.tstamps) c s.refs
      ([] ++ joinEnv L0 (sptToAList (sptInter s9.locals (adjustSet L0))) ++
        [(theGlobal s.global, holFapply s9.store .globals)] ++ flatStack s.stack s9.stack))
    (lim : (limit + 3) * (width / 8) + 1 < 2 ^ width) (spLe : n + 1 ≤ sp)
    (hheap : heap = ha ++ .unused (n + k) :: hb) (limNZ : limit ≠ 0) (hys : ys.length = n)
    (hstore : ∀ key, (∀ r, key ≠ .temp r) → R.store.lookup key = s9.store.lookup key)
    (hmem : SetSep.star
      (Misc.wordList (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength ha) +
        StackRemove.bytesInWord width) ys)
      (SetSep.star (SetSep.one (curr + StackRemove.bytesInWord width *
          BitVec.ofNat width (heapLength ha), x0))
        (SetSep.star (SetSep.one (other, ow)) (splitFrame c curr other ha hb n k limit)))
      (SetSep.fun2Set (R.memory, fun x => R.mdomain x = true)))
    (hcurr : s9.store.lookup .currHeap = some (.word curr))
    (hother : s9.store.lookup .otherHeap = some (.word other))
    (hffi : R.ffi = s9.ffi) (hhandler : R.handler = s9.handler) (hgc : R.gcFun = s9.gcFun)
    (hcode : R.code = s9.code) (hcomp : R.compile = s9.compile)
    (horacle : R.compileOracle = s9.compileOracle) (hcb : R.codeBuffer = s9.codeBuffer)
    (hdb : R.dataBuffer = s9.dataBuffer) (hbe : R.be = s9.be) (hss : R.stackSize = s9.stackSize)
    (hsl : R.stackLimit = s9.stackLimit) (hstack : R.stack = s9.stack)
    (hls : R.localsSize = some 0) (hloc : R.locals = .ln)
    (hmax : BackendProps.optionLe (Option.map₂ (· + ·) (wordSemStackSize R.stack) (some 0)) R.stackMax) :
    stateRel c r1 r2
      { s with locals := .ln, localsSize := some 0, stackMax := none, clock := R.clock,
               space := n + 1 } R (some [(.number 0, .word 0)]) locs := by
  obtain ⟨h1, _, h3, h4, h5, h6, h7, h8, h9, h10, _, _, h13, h14, _, _, h17, _, h19, _⟩ := rel9
  have nt : ∀ key : WordStoreHOL, key ∈ [WordStore.globals, .codeBuffer, .codeBufferEnd, .bitmapBuffer,
      .bitmapBufferEnd, .heapLength, .currHeap, .otherHeap, .nextFree, .triggerGC, .endOfHeap,
      .globReal, .genStart] → R.store.lookup key = s9.store.lookup key := by
    intro key hk
    apply hstore
    intro r e
    subst e
    simp at hk
  refine ⟨hffi.trans h1, rfl, hhandler.trans h3, hgc.trans h4, hcode ▸ h5, ?_, h7, h8, h9, ?_,
    by simp, ?_, hstack ▸ h13, hstack ▸ h14, hls ▸ hmax, trivial, hss.trans h17, hls, ?_, ?_⟩
  · unfold codeOracleRel at h6 ⊢
    rw [nt .codeBuffer (by simp), nt .codeBufferEnd (by simp), nt .bitmapBuffer (by simp),
      nt .bitmapBufferEnd (by simp), hcomp, horacle, hcb, hdb]
    exact h6
  · intro key hk
    simp only [List.mem_singleton] at hk
    subst hk
    rw [nt _ (by simp)]
    exact h10 _ (by simp)
  · intro n h
    simp [sptLookup] at h
  · rw [nt .heapLength (by simp), hsl]
    exact h19
  have hj : joinEnv (.ln : Spt DataSem.Value) (sptToAList (sptInter R.locals (adjustSet (.ln : Spt DataSem.Value)))) = [] := by
    rw [hloc]; simp [sptInter, sptToAList, joinEnv, sptFoldi]
  have hg : holFapply R.store .globals = holFapply s9.store .globals := by
    unfold holFapply; rw [nt .globals (by simp)]
  simp only [Option.getD, hj, hg, hstack, List.nil_append, List.cons_append]
  have z : (WordLocW.word 0 : WordLocW width) = .word (smallnum (0 : Int)) := by simp [smallnum]
  rw [z]
  apply impMemoryRel_number c R.be _ s.refs (n + 1) R.store R.memory R.mdomain _ 0
  refine ⟨h7, small_int_0 width h7, heap, limit, a, sp, sp1, gens, ?_, ?_, lim, spLe⟩
  · obtain ⟨b1, b2, b3, b4, b5, b6, glob, curr', other', al1, al2, hc, ho, hn, ht, he, hl, hgr, hgs,
      _⟩ := hims
    rw [hcurr] at hc
    rw [hother] at ho
    cases hc
    cases ho
    refine ⟨b1, b2, b3, b4, b5, b6, by rw [nt _ (by simp)]; exact glob, curr, other, al1, al2,
      by rw [nt _ (by simp)]; exact hcurr, by rw [nt _ (by simp)]; exact hother,
      by rw [nt _ (by simp)]; exact hn, by rw [nt _ (by simp)]; exact ht,
      by rw [nt _ (by simp)]; exact he, by rw [nt _ (by simp)]; exact hl,
      by rw [nt _ (by simp), nt _ (by simp)]; exact hgr, by rw [nt _ (by simp)]; exact hgs, ?_⟩
    exact heap_rebuild hheap limNZ hys hmem
  · rw [hbe]
    apply wordMlInv_rearrange _ _ _ _ _ _ _ _ _ _ _ _ _ wml
    intro pair hp
    simp only [List.mem_append, List.nil_append, List.mem_cons] at hp ⊢
    rcases hp with h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.AnyArith
