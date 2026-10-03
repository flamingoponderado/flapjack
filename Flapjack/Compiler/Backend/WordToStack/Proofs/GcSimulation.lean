import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelGetVar
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackRelAux
import Flapjack.Compiler.Backend.WordToStack.Proofs.FilterBitmap
import Flapjack.Compiler.Backend.WordToStack.Proofs.MapFst
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.WordToStack.Proofs.MapBitmap
import Flapjack.Compiler.Backend.StackProps.StackLengths
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexReconstruction
import Flapjack.Compiler.Backend.WordToStack.Proofs.FrameOffsets
import Flapjack.Compiler.Backend.WordToStack.Proofs.DecodedFrameShape
import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLengths
import Mathlib.Data.List.Forall2
import Flapjack.Compiler.Backend.WordToStack.Proofs.SourceFrameSize
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocSimulation
import Flapjack.Misc.FiniteMapApply

/-!
# Word-to-Stack garbage-collection simulation

The stack encoding/decoding simulation of `word_to_stackProofScript.sml`
(1613-2073): a related StackSem stack encodes to the WordSem roots, decodes the
collector's roots back in step with WordSem, and so `gc` preserves `state_rel`.
-/

namespace Flapjack.WordToStackProofs.GcSimulation
open Flapjack.StackSem Flapjack.Compiler.Encoders.Asm

/-- Inhabitation of the source frame carrier for total HOL `EL`, as in `stackRelAux`. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

/-- Exact HOL `read_bitmap_not_empty` (`word_to_stackProofScript.sml:1613-1620`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_not_empty"
  (words_as_type_indexed_bitvec)]
theorem readBitmapNotEmpty {width : Nat} [NeZero width] (stack : List (BitVec width))
    (a : List Bool) : readBitmap stack = some a → stack ≠ [] := by
  rintro h rfl
  simp [readBitmap] at h

/-- Exact HOL `n2w_lsr_1` (`word_to_stackProofScript.sml:1622-1627`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "n2w_lsr_1"
  (words_as_type_indexed_bitvec)]
theorem n2wLsr1 {width : Nat} [NeZero width] (n : Nat) :
    n < 2 ^ width →
      (BitVec.ofNat width n : BitVec width) >>> (1 : Nat) = BitVec.ofNat width (n / 2) := by
  intro h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_one, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- Exact HOL `handler_bitmap_props` (`word_to_stackProofScript.sml:1629-1638`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "handler_bitmap_props"
  (words_as_type_indexed_bitvec)]
theorem handlerBitmapProps {width : Nat} [NeZero width] (stack : List (BitVec width)) :
    goodDimindex width → readBitmap ((4 : BitVec width) :: stack) = some [false, false] := by
  intro hw
  rcases hw with hw | hw <;> subst hw
  · have h4 : bitLength (4 : BitVec 32) = 3 := by
      rw [bitLength, if_neg (by decide), bitLength, if_neg (by decide), bitLength,
        if_neg (by decide), bitLength, if_pos (by decide)]
    simp only [readBitmap, h4]
    rw [if_neg (by decide)]
    decide
  · have h4 : bitLength (4 : BitVec 64) = 3 := by
      rw [bitLength, if_neg (by decide), bitLength, if_neg (by decide), bitLength,
        if_neg (by decide), bitLength, if_pos (by decide)]
    simp only [readBitmap, h4]
    rw [if_neg (by decide)]
    decide

theorem fullReadBitmap_ne_zero {width : Nat} [NeZero width] {bs : List (BitVec width)}
    {w : WordLocW width} {bits : List Bool} (h : fullReadBitmap bs w = some bits) :
    w ≠ .word 0 := by
  rintro rfl
  simp [fullReadBitmap] at h

/-- Exact HOL `enc_stack_lemma` (`word_to_stackProofScript.sml:1640-1690`). HOL's
free `k` and `len` are explicit; its quantified `bs'` occurs nowhere in the
statement and is omitted. Bitmaps, source frames and the target stack share the
word dimension, as the HOL conclusion forces. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "enc_stack_lemma"
  (words_as_type_indexed_bitvec)]
theorem encStackLemma {width : Nat} [NeZero width] (k len : Nat) :
    ∀ (bs : List (BitVec width)) (wstack : List (WordSemStackFrame width))
      (sstack : List (WordLocW width)) (lens : List Nat)
      (astack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width))),
      goodDimindex width ∧ bs.length + 1 < 2 ^ width ∧
      absStack bs wstack sstack lens = some astack ∧ 1 ≤ bs.length ∧ holHd bs = 4 ∧
      stackRelAux k len wstack astack →
      encStack bs sstack = some (wordSemEncStack wstack) := by
  intro bs wstack
  induction wstack with
  | nil =>
    rintro sstack lens astack ⟨-, -, habs, -, -, -⟩
    rcases lens with _ | ⟨len0, lens⟩
    · rw [absStack.eq_def] at habs
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at habs
      obtain ⟨rfl, -⟩ := habs
      rw [encStack, if_pos rfl, if_pos rfl]
      rfl
    · rw [absStack.eq_def] at habs
      simp at habs
  | cons frame xs ih =>
    rintro sstack lens astack ⟨hgood, hlen, habs, hone, hhd, hrel⟩
    rcases sstack with _ | ⟨w, stack⟩
    · rw [absStack.eq_def] at habs
      rcases frame with ⟨_, _, _, _ | _⟩ <;> simp at habs
    rcases lens with _ | ⟨len0, lens⟩
    · rw [absStack.eq_def] at habs
      rcases frame with ⟨_, _, _, _ | _⟩ <;> simp at habs
    rcases frame with ⟨n, l0, l, _ | ⟨h1, l1, l2⟩⟩
    · rw [absStack.eq_def] at habs
      simp only at habs
      rcases hb : fullReadBitmap bs w with _ | bits
      · simp [hb] at habs
      simp only [hb] at habs
      split at habs
      · simp at habs
      split at habs
      · simp at habs
      rename_i hlen0 hstack
      rcases hys : absStack bs xs (stack.drop len0) lens with _ | ys
      · simp [hys] at habs
      simp only [hys, Option.some.injEq] at habs
      subst habs
      simp only [stackRelAux] at hrel
      obtain ⟨-, hfilter, -, hrest⟩ := hrel
      have hbl : bits.length = len0 := by simpa using hlen0
      subst hbl
      have hf := Compiler.Backend.WordToStack.filterBitmapIndexReconstruct bits stack k _ hfilter
      rw [encStack, if_neg (fullReadBitmap_ne_zero hb)]
      simp only [hb]
      split
      · rename_i h; rw [hf] at h; cases h
      · rename_i selected remainder h
        rw [hf] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rw [ih _ lens ys ⟨hgood, hlen, hys, hone, hhd, hrest⟩]
        simp [wordSemEncStack, List.map_map, Function.comp_def]
    · rw [absStack.eq_def] at habs
      simp only at habs
      split at habs
      · simp at habs
      rename_i hw1
      have hw : w = .word 1 := by simpa using hw1
      subst hw
      rcases stack with _ | ⟨loc, _ | ⟨hv, _ | ⟨w, stack⟩⟩⟩ <;> simp only [reduceCtorEq] at habs
      rcases hb : fullReadBitmap bs w with _ | bits
      · simp [hb] at habs
      simp only [hb] at habs
      split at habs
      · simp at habs
      split at habs
      · simp at habs
      rename_i hlen0 hstack
      rcases hys : absStack bs xs (stack.drop len0) lens with _ | ys
      · simp [hys] at habs
      simp only [hys, Option.some.injEq] at habs
      subst habs
      simp only [stackRelAux] at hrel
      obtain ⟨-, -, -, hfilter, -, hrest⟩ := hrel
      have hbl : bits.length = len0 := by simpa using hlen0
      subst hbl
      have hf := Compiler.Backend.WordToStack.filterBitmapIndexReconstruct bits stack k _ hfilter
      obtain ⟨b0, bs', rfl⟩ : ∃ b0 bs', bs = b0 :: bs' := by
        cases bs with
        | nil => simp at hone
        | cons b0 bs' => exact ⟨b0, bs', rfl⟩
      have hb0 : b0 = 4 := hhd
      subst hb0
      have h10 : (1 : BitVec width) ≠ 0 := by
        rcases hgood with hw | hw <;> subst hw <;> decide
      have hread : fullReadBitmap ((4 : BitVec width) :: bs') (WordLocW.word (1 : BitVec width)) =
          some [false, false] := by
        simp only [fullReadBitmap, if_neg h10]
        rw [show ((1 : BitVec width) - 1).toNat = 0 by simp]
        exact handlerBitmapProps bs' hgood
      rw [encStack, if_neg (by simpa using h10)]
      simp only [hread]
      split
      · rename_i h; simp [filterBitmap] at h
      · rename_i selected remainder h
        simp only [filterBitmap, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hinner : encStack ((4 : BitVec width) :: bs') (w :: stack) =
            some (l.map Prod.snd ++ wordSemEncStack xs) := by
          rw [encStack, if_neg (fullReadBitmap_ne_zero hb)]
          simp only [hb]
          split
          · rename_i h; rw [hf] at h; cases h
          · rename_i selected remainder h
            rw [hf] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            rw [ih _ lens ys ⟨hgood, hlen, hys, hone, rfl, hrest⟩]
            simp [List.map_map, Function.comp_def]
        rw [hinner]
        simp [wordSemEncStack]

/-- Canonical source-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Exact HOL `IMP_enc_stack` (`word_to_stackProofScript.sml:1692-1700`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IMP_enc_stack"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store,
    StackSemStateFiniteExact.regs, StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem impEncStack {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat)
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (t1 : StackSemStateFiniteExact width C F) (lens : List Nat) :
    stateRel ac k 0 0 s1 t1 lens 0 →
      encStack t1.bitmaps (t1.stack.drop t1.stackSpace) = some (wordSemEncStack s1.stack) := by
  intro h
  unfold stateRel at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h28,
    -, h30, h31, h32, -, -, -, -, -, h38, -⟩ := h
  obtain ⟨-, astack, habs, -, hrel⟩ := h38
  simp only [Nat.add_zero, List.drop_zero] at habs
  exact encStackLemma k _ _ _ _ _ _ ⟨h28, by omega, habs, h31, h32, hrel⟩

theorem lookup_eq_sptAListLookup {α : Type} (n : Nat) :
    ∀ l : List (Nat × α), l.lookup n = sptAListLookup n l
  | [] => rfl
  | (m, v) :: l => by
      by_cases h : n = m
      · subst h; simp [List.lookup, sptAListLookup]
      · have hb : (n == m) = false := by simpa using h
        simp [List.lookup, sptAListLookup, h, hb, lookup_eq_sptAListLookup n l]

theorem lookup_zip_mapFst_eq_none {α β : Type} (n : Nat) :
    ∀ (l : List (Nat × α)) (ys : List β), ys.length = l.length →
      ((l.map Prod.fst).zip ys).lookup n = none → l.lookup n = none
  | [], _, _, _ => rfl
  | (m, v) :: l, y :: ys, hlen, h => by
      by_cases hm : n = m
      · subst hm; simp at h
      · have hb : (n == m) = false := by simpa using hm
        simp only [List.map_cons, List.zip_cons_cons, List.lookup, hb] at h ⊢
        exact lookup_zip_mapFst_eq_none n l ys (by simpa using hlen) h
  | _ :: _, [], hlen, _ => by simp at hlen

theorem indexList_mapFst_eq {α β : Type} (k : Nat) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (indexList xs k).map Prod.fst = (indexList ys k).map Prod.fst
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [indexList, h, indexList_mapFst_eq k xs ys h]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- One frame of the `dec_stack_lemma1` simulation: a frame related by
`stack_rel_aux`'s bitmap conjuncts decodes the collector's roots in step with
WordSem `dec_stack`, and the decoded frame again satisfies those conjuncts.
Flapjack helper shared by HOL's two frame cases; no separate HOL original. -/
theorem decFrameStep {width : Nat} [NeZero width] (k : Nat) (bits : List Bool)
    (stack ls : List (WordLocW width)) (l0 l : List (Nat × WordLocW width))
    (hlen : bits.length ≤ stack.length) (hll : l.length ≤ ls.length)
    (hA : ∀ n' v, l0.lookup n' = some v → l.lookup n' = none →
      adjustNames n' < k + bits.length ∧
      bits[k + bits.length - (adjustNames n' + 1)]? = some false ∧
      (indexList (stack.take bits.length) k).lookup (n' / 2) = some v)
    (hB : filterBitmap bits (indexList (stack.take bits.length) k) =
      some (l.map (fun p => (adjustNames p.1, p.2)), [])) :
    ∃ x, mapBitmap bits ls stack = some (x, ls.drop l.length, stack.drop bits.length) ∧
      x.length = bits.length ∧
      (∀ n' v, l0.lookup n' = some v →
        ((l.map Prod.fst).zip (ls.take l.length)).lookup n' = none →
        adjustNames n' < k + bits.length ∧
        bits[k + bits.length - (adjustNames n' + 1)]? = some false ∧
        (indexList x k).lookup (n' / 2) = some v) ∧
      filterBitmap bits (indexList x k) =
        some (((l.map Prod.fst).zip (ls.take l.length)).map
          (fun p => (adjustNames p.1, p.2)), []) := by
  have hf := Compiler.Backend.WordToStack.filterBitmapIndexReconstruct bits stack k _ hB
  have htake : (ls.take l.length).length = l.length := by simp [hll]
  obtain ⟨x, hm, hfx⟩ := Compiler.Backend.WordToStack.mapBitmapSuccess bits stack _ _
    (ls.take l.length) hf (by simp [htake])
  have hm' := Compiler.Backend.WordToStack.mapBitmapMoreSimp bits l ls stack x _ hm
  have hxl := (StackPropsStackLengths.mapBitmapLengths bits _ _ _ _ _ hm).2
  refine ⟨x, hm', hxl, ?_, ?_⟩
  · intro n' v hl0 hnone
    obtain ⟨ha, hb, hc⟩ := hA n' v hl0 (lookup_zip_mapFst_eq_none n' l _ htake hnone)
    refine ⟨ha, hb, ?_⟩
    have hlt : n' / 2 < bits.length + k := by
      simp only [adjustNames] at ha; omega
    obtain ⟨u, hxu, hsu⟩ := Compiler.Backend.WordToStack.mapBitmapLookupFalse bits _ stack _
      _ _ _ hb hm
    have hi : k + bits.length - (adjustNames n' + 1) < bits.length := by
      have := (List.getElem?_eq_some_iff.mp hb).1; exact this
    rw [lookup_eq_sptAListLookup] at hc ⊢
    rw [aLookupIndexList _ _ _ (by simp [Nat.min_eq_left hlen]; omega)] at hc
    rw [aLookupIndexList _ _ _ (by rw [hxl]; omega)]
    simp only [List.length_take, Nat.min_eq_left hlen, adjustNames] at hc hxu hsu hi ⊢
    rw [hxl, show bits.length + k - (n' / 2 + 1) = k + bits.length - (n' / 2 + 1) by omega,
      hxu]
    rw [show bits.length + k - (n' / 2 + 1) = k + bits.length - (n' / 2 + 1) by omega,
      List.getElem?_take_of_lt hi, hsu] at hc
    exact hc
  · apply Compiler.Backend.WordToStack.filterBitmapPairReconstruct
    · rw [mapSndIndexList, List.map_map]
      have : (fun p : Nat × WordLocW width => p.2) ∘ (fun p => (adjustNames p.1, p.2)) =
          Prod.snd := rfl
      rw [this, List.map_snd_zip (by simp [htake])]
      exact hfx
    · rw [indexList_mapFst_eq k x (stack.take bits.length) (by simp [hxl, hlen])]
      have h1 := Compiler.Backend.WordToStack.filterBitmapMapFst bits _ _ hB
      have key : ∀ xs : List (Nat × WordLocW width),
          (xs.map (fun p => (adjustNames p.1, p.2))).map Prod.fst =
            (xs.map Prod.fst).map adjustNames := by
        intro xs; simp [List.map_map, Function.comp_def]
      have hz : ((l.map Prod.fst).zip (ls.take l.length)).map Prod.fst = l.map Prod.fst :=
        List.map_fst_zip (by simp [htake])
      rw [h1, key, key, hz]

/-- Exact HOL `dec_stack_lemma1` (`word_to_stackProofScript.sml:1827-1960`). HOL's
free `k` and `len` are explicit; HOL `LIST_REL` is `List.Forall₂`. Bitmaps,
source frames and both target stacks share the word dimension. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "dec_stack_lemma1"
  (words_as_type_indexed_bitvec)]
theorem decStackLemma1 {width : Nat} [NeZero width] (k len : Nat) :
    ∀ (bs : List (BitVec width)) (wstack : List (WordSemStackFrame width))
      (sstack : List (WordLocW width)) (lens : List Nat)
      (astack : List (Option (WordLocW width × WordLocW width) × List Bool × List (WordLocW width)))
      (wdec : List (WordSemStackFrame width)) (ls : List (WordLocW width)),
      goodDimindex width ∧ 1 ≤ bs.length ∧ holHd bs = 4 ∧
      absStack bs wstack sstack lens = some astack ∧ stackRelAux k len wstack astack ∧
      wordSemDecStack ls wstack = some wdec →
      ∃ sdec bstack, decStack bs ls sstack = some sdec ∧
        absStack bs wdec sdec lens = some bstack ∧ stackRelAux k len wdec bstack ∧
        List.Forall₂ absFrameEq astack bstack := by
  intro bs wstack
  induction wstack with
  | nil =>
    rintro sstack lens astack wdec ls ⟨-, -, -, habs, -, hdec⟩
    rcases lens with _ | ⟨len0, lens⟩
    · rw [absStack.eq_def] at habs
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at habs
      obtain ⟨rfl, rfl⟩ := habs
      rcases ls with _ | ⟨l1, ls⟩
      · simp only [wordSemDecStack, Option.some.injEq] at hdec
        subst hdec
        refine ⟨[.word 0], [], ?_, ?_, trivial, List.Forall₂.nil⟩
        · rw [decStack, if_pos rfl, if_pos ⟨rfl, rfl⟩]
        · rw [absStack.eq_def]; simp
      · simp [wordSemDecStack] at hdec
    · rw [absStack.eq_def] at habs; simp at habs
  | cons frame xs ih =>
    rintro sstack lens astack wdec ls ⟨hgood, hone, hhd, habs, hrel, hdec⟩
    rcases frame with ⟨n, l0, l, handler⟩
    simp only [wordSemDecStack] at hdec
    split at hdec
    · simp at hdec
    rename_i hll
    rcases hs' : wordSemDecStack (ls.drop l.length) xs with _ | s'
    · simp [hs'] at hdec
    simp only [hs', Option.some.injEq] at hdec
    subst hdec
    rcases sstack with _ | ⟨w, stack⟩
    · rw [absStack.eq_def] at habs; rcases handler with _ | _ <;> simp at habs
    rcases lens with _ | ⟨len0, lens⟩
    · rw [absStack.eq_def] at habs; rcases handler with _ | _ <;> simp at habs
    rcases handler with _ | ⟨h1, l1, l2⟩
    · rw [absStack.eq_def] at habs
      simp only at habs
      rcases hb : fullReadBitmap bs w with _ | bits
      · simp [hb] at habs
      simp only [hb] at habs
      split at habs
      · simp at habs
      split at habs
      · simp at habs
      rename_i hlen0 hstack
      rcases hys : absStack bs xs (stack.drop len0) lens with _ | ys
      · simp [hys] at habs
      simp only [hys, Option.some.injEq] at habs
      subst habs
      have hbl : bits.length = len0 := by simpa using hlen0
      subst hbl
      simp only [stackRelAux] at hrel
      obtain ⟨hA, hB, hC, hrest⟩ := hrel
      obtain ⟨x, hm, hxl, hA', hB'⟩ :=
        decFrameStep k bits stack ls l0 l (by omega) (by omega) hA hB
      obtain ⟨sdec', bstack', hsdec, hbabs, hbrel, hfa⟩ :=
        ih _ lens ys s' (ls.drop l.length) ⟨hgood, hone, hhd, hys, hrest, hs'⟩
      refine ⟨[w] ++ x ++ sdec', (none, bits, x) :: bstack', ?_, ?_, ?_, ?_⟩
      · rw [decStack, if_neg (fullReadBitmap_ne_zero hb)]
        simp only [hb]
        split
        · rename_i h; rw [hm] at h; cases h
        · rename_i front rem remainder h
          rw [hm] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [hsdec]
      · rw [absStack.eq_def]
        simp only [List.cons_append, hb]
        rw [if_neg (by simp), if_neg (by simp [hxl]), List.nil_append, List.take_left' hxl,
          List.drop_left' hxl, hbabs]
      · simp only [stackRelAux]
        refine ⟨hA', hB', ?_, hbrel⟩
        rw [hxl]; simpa [Nat.min_eq_left (by omega : bits.length ≤ stack.length)] using hC
      · exact List.Forall₂.cons ⟨rfl, rfl, by simp [hxl]; omega⟩ hfa
    · rw [absStack.eq_def] at habs
      simp only at habs
      split at habs
      · simp at habs
      rename_i hw1
      have hw : w = .word 1 := by simpa using hw1
      subst hw
      rcases stack with _ | ⟨loc, _ | ⟨hv, _ | ⟨w, stack⟩⟩⟩ <;> simp only [reduceCtorEq] at habs
      rcases hb : fullReadBitmap bs w with _ | bits
      · simp [hb] at habs
      simp only [hb] at habs
      split at habs
      · simp at habs
      split at habs
      · simp at habs
      rename_i hlen0 hstack
      rcases hys : absStack bs xs (stack.drop len0) lens with _ | ys
      · simp [hys] at habs
      simp only [hys, Option.some.injEq] at habs
      subst habs
      have hbl : bits.length = len0 := by simpa using hlen0
      subst hbl
      simp only [stackRelAux] at hrel
      obtain ⟨hH, hloc, hA, hB, hC, hrest⟩ := hrel
      obtain ⟨x, hm, hxl, hA', hB'⟩ :=
        decFrameStep k bits stack ls l0 l (by omega) (by omega) hA hB
      obtain ⟨sdec', bstack', hsdec, hbabs, hbrel, hfa⟩ :=
        ih _ lens ys s' (ls.drop l.length) ⟨hgood, hone, hhd, hys, hrest, hs'⟩
      obtain ⟨b0, bs', rfl⟩ : ∃ b0 bs', bs = b0 :: bs' := by
        cases bs with
        | nil => simp at hone
        | cons b0 bs' => exact ⟨b0, bs', rfl⟩
      have hb0 : b0 = 4 := hhd
      subst hb0
      have h10 : (1 : BitVec width) ≠ 0 := by
        rcases hgood with hw | hw <;> subst hw <;> decide
      have hread : fullReadBitmap ((4 : BitVec width) :: bs') (WordLocW.word (1 : BitVec width)) =
          some [false, false] := by
        simp only [fullReadBitmap, if_neg h10]
        rw [show ((1 : BitVec width) - 1).toNat = 0 by simp]
        exact handlerBitmapProps bs' hgood
      have hinner : decStack ((4 : BitVec width) :: bs') ls (w :: stack) =
          some ([w] ++ x ++ sdec') := by
        rw [decStack, if_neg (fullReadBitmap_ne_zero hb)]
        simp only [hb]
        split
        · rename_i h; rw [hm] at h; cases h
        · rename_i front rem remainder h
          rw [hm] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [hsdec]
      refine ⟨[.word 1] ++ [loc, hv] ++ ([w] ++ x ++ sdec'),
        (some (loc, hv), bits, x) :: bstack', ?_, ?_, ?_, ?_⟩
      · rw [decStack, if_neg (by simpa using h10)]
        simp only [hread]
        split
        · rename_i h; simp [mapBitmap] at h
        · rename_i front rem remainder h
          simp only [mapBitmap, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [hinner]
      · rw [absStack.eq_def]
        simp only [List.cons_append, List.nil_append, hb]
        rw [if_neg (by simp), if_neg (by simp), if_neg (by simp [hxl]), List.take_left' hxl,
          List.drop_left' hxl, hbabs]
      · simp only [stackRelAux]
        have hlenEq : ys.length = bstack'.length := hfa.length_eq
        have hxsLen : ys.length = xs.length := (absStackImpLength _ _ _ _ _ hys).1
        have hsLen : xs.length = s'.length :=
          WordSemStackEq.sKeyEqLength xs s' (WordSemStackEq.decStackStackKeyEq _ xs s' hs')
        refine ⟨?_, hloc, hA', hB', ?_, hbrel⟩
        · intro hlt hhandler
          rw [← hlenEq] at hlt hhandler ⊢
          have hi : ys.length - (h1 + 1) < xs.length := by omega
          have hframe : isHandlerFrame (Flapjack.holEl (ys.length - (h1 + 1)) xs) = true := by
            rw [holEl_eq_getElem _ _ hi]
            rw [holEl_eq_getElem _ _ (by omega)] at hhandler
            exact (wordStackDecStackShape _ xs s' _ hs' hi).mpr hhandler
          rw [hH hlt hframe, listRelAbsFrameEqHandlerVal _ _
            (List.forall₂_drop (ys.length - (h1 + 1)) hfa)]
        · rw [hxl]; simpa [Nat.min_eq_left (by omega : bits.length ≤ stack.length)] using hC
      · exact List.Forall₂.cons ⟨rfl, rfl, by simp [hxl]; omega⟩ hfa

/-- Exact HOL `dec_stack_lemma` (`word_to_stackProofScript.sml:1962-1995`). HOL's
free `k`, `lens`, `x0` and `x` are explicit; HOL's total `t1.store ' Handler` is
`holFapply`. The source configuration carrier is `Nat × C` as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "dec_stack_lemma"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem decStackLemma {width : Nat} [NeZero width] {C F : Type} (k : Nat) (lens : List Nat)
    (t1 : StackSemStateFiniteExact width C F) (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (x0 : List (WordLocW width)) (x : List (WordSemStackFrame width)) :
    goodDimindex width ∧ 1 ≤ t1.bitmaps.length ∧ holHd t1.bitmaps = 4 ∧
      t1.stackSpace ≤ t1.stack.length ∧
      encStack t1.bitmaps (t1.stack.drop t1.stackSpace) = some (wordSemEncStack s1.stack) ∧
      wordSemDecStack x0 s1.stack = some x ∧
      stackRel k s1.handler s1.stack (some (holFapply t1.store .handler))
        (t1.stack.drop t1.stackSpace) t1.stack.length t1.bitmaps lens ∧
      (wordSemEncStack s1.stack).length = x0.length →
    ∃ yy, decStack t1.bitmaps x0 (t1.stack.drop t1.stackSpace) = some yy ∧
      t1.stackSpace + yy.length = t1.stack.length ∧
      stackRel k s1.handler x (some (holFapply t1.store .handler)) yy t1.stack.length
        t1.bitmaps lens := by
  rintro ⟨hgood, hone, hhd, hspace, -, hdec, hrel, -⟩
  obtain ⟨hsorted, astack, habs, hH, haux⟩ := hrel
  obtain ⟨sdec, bstack, hsdec, hbabs, hbaux, hfa⟩ :=
    decStackLemma1 k t1.stack.length t1.bitmaps s1.stack _ lens astack x x0
      ⟨hgood, hone, hhd, habs, haux, hdec⟩
  refine ⟨sdec, hsdec, ?_, wordStackDecStackSorted x0 s1.stack x hdec hsorted, bstack, hbabs,
    ?_, hbaux⟩
  · have := StackPropsStackLengths.decStackLength _ _ _ _ hsdec
    simp only [List.length_drop] at this
    omega
  · have hlenEq : astack.length = bstack.length := hfa.length_eq
    have haLen : astack.length = s1.stack.length := (absStackImpLength _ _ _ _ _ habs).1
    have hxLen : s1.stack.length = x.length :=
      WordSemStackEq.sKeyEqLength s1.stack x (WordSemStackEq.decStackStackKeyEq _ s1.stack x hdec)
    intro hlt hhandler
    rw [← hxLen] at hlt hhandler
    have hi : s1.stack.length - (s1.handler + 1) < s1.stack.length := by omega
    have hframe : isHandlerFrame
        (Flapjack.holEl (s1.stack.length - (s1.handler + 1)) s1.stack) = true := by
      rw [holEl_eq_getElem _ _ hi]
      rw [holEl_eq_getElem _ _ (by omega)] at hhandler
      exact (wordStackDecStackShape _ s1.stack x _ hdec hi).mpr hhandler
    rw [hH hlt hframe, ← hlenEq, listRelAbsFrameEqHandlerVal _ _
      (List.forall₂_drop (astack.length - (s1.handler + 1)) hfa)]

/-- Exact HOL `gc_state_rel` (`word_to_stackProofScript.sml:2045-2073`). WordSem
and StackSem `gc` are the native transitions; the source configuration carrier
is `Nat × C` as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "gc_state_rel"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store,
    StackSemStateFiniteExact.regs, StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem gcStateRel {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat)
    (s1 s2 : WordSemStateFiniteExact width (Nat × C) F)
    (t1 : StackSemStateFiniteExact width C F) (lens : List Nat) :
    WordSemStateFiniteExact.gc s1 = some s2 ∧ stateRel ac k 0 0 s1 t1 lens 0 →
    ∃ t2, StackSemAllocation.gc t1 = some t2 ∧
      stateRel ac k 0 0 { s2 with locals := .ln } t2 lens 0 ∧
      t2.stack.length = t1.stack.length ∧ t2.stackSpace = t1.stackSpace := by
  rintro ⟨hgc, hrel⟩
  have henc := impEncStack ac k s1 t1 lens hrel
  unfold stateRel at hrel
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36,
    h37, h38, -⟩ := hrel
  simp only [Nat.add_zero, List.drop_zero] at h33 h38
  simp only [WordSemStateFiniteExact.gc] at hgc
  rcases hf : s1.gcFun (wordSemEncStack s1.stack, s1.memory, s1.mdomain, s1.store) with
    _ | ⟨wl, m, st⟩
  · simp [hf] at hgc
  simp only [hf] at hgc
  rcases hd : wordSemDecStack wl s1.stack with _ | stack
  · simp [hd] at hgc
  simp only [hd, Option.some.injEq] at hgc
  subst hgc
  obtain ⟨hv, hvl, -⟩ := wordGcHandlerValue t1.store h17 (.loc 0 0)
  have hok := h13 (wordSemEncStack s1.stack) s1.memory s1.mdomain t1.store wl m st
    ⟨h17, by rw [h2.symm, ← h12, hf]⟩
  obtain ⟨hwlLen, hstNone, htf⟩ := hok
  have hfap : holFapply t1.store .handler = hv := holFapply_of_lookup hvl
  have h38' := h38
  rw [hvl, ← hfap] at h38'
  obtain ⟨yy, hyy, hyyLen, hyyRel⟩ :=
    decStackLemma k lens t1 s1 wl stack
      ⟨h28, h31, h32, by omega, henc, hd, h38', hwlLen⟩
  refine ⟨{ t1 with
      stack := t1.stack.take t1.stackSpace ++ yy
      store := st.updateEq (.handler, (t1.store.lookup .handler).getD (.loc 0 0))
      regs := HolFiniteMapExact.empty
      memory := m }, ?_, ?_, ?_, rfl⟩
  · simp only [StackSemAllocation.gc, if_neg (by omega : ¬ t1.stack.length < t1.stackSpace),
      henc]
    rw [h8, h9, htf]
    simp only [hyy]
  · have hlen' : (t1.stack.take t1.stackSpace ++ yy).length = t1.stack.length := by
      simp; omega
    have hdropt : (t1.stack.take t1.stackSpace ++ yy).drop t1.stackSpace = yy :=
      List.drop_left' (by simp; omega)
    unfold stateRel
    refine ⟨h1, h2, h3, h4, h5, h6, h7, rfl, h9, h10, h11, ?_, h13, h14, h15, h16, ?_, h18,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, ?_, ?_, h35,
      sptWf_ln, ?_, ?_⟩
    · apply AllocSimulation.fmap_ext
      intro key
      by_cases hk : key = .handler
      · subst hk
        simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hstNone]
      · simp [HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL, hk]
    · simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]
    · show t1.stackSpace + 0 ≤ (t1.stack.take t1.stackSpace ++ yy).length
      omega
    · show (t1.stack.take t1.stackSpace ++ yy).length < 2 ^ width
      omega
    · obtain ⟨-, hlim, hmax⟩ := h37
      refine ⟨by simp, by rw [hlim, hlen'], ?_⟩
      intro maximum hm
      obtain ⟨hle, hsome, size, hsize, hsz⟩ := hmax maximum hm
      refine ⟨by rw [hlen']; exact hle, hsome, size, ?_, by rw [hlen']; exact hsz⟩
      rw [← decStackStackSize wl s1.stack stack hd]
      exact hsize
    · refine ⟨?_, ?_⟩
      · show stackRel k s1.handler stack
          ((st.updateEq (.handler, (t1.store.lookup .handler).getD (.loc 0 0))).lookup .handler)
          (((t1.stack.take t1.stackSpace ++ yy).drop (t1.stackSpace + 0)).drop 0)
          (t1.stack.take t1.stackSpace ++ yy).length t1.bitmaps lens
        rw [Nat.add_zero, List.drop_zero, hdropt, hlen']
        have : (st.updateEq (.handler, (t1.store.lookup .handler).getD (.loc 0 0))).lookup
            .handler = some (holFapply t1.store .handler) := by
          simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hvl, hfap]
        rw [this]
        exact hyyRel
      · intro n v hn
        simp [sptLookup] at hn
  · show (t1.stack.take t1.stackSpace ++ yy).length = t1.stack.length
    simp; omega

end Flapjack.WordToStackProofs.GcSimulation
