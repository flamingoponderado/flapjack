module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.UnusedWrite
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsAltWritten
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.UpdateThunk

@[expose] public section

/-!
# Copying a source list into a fresh block

Counterparts of `memory_rel_IMP_word_list_exists`, `copy_list_def`,
`copy_list_thm` and `memory_rel_FromList` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`(P * SEP_T) (fun2set (m,dm))` is `SetSep.star P SetSep.sepT
(SetSep.fun2Set (m, fun a => dm a = true))`, `(b =+ x) m` is the pointwise
update `fun key => if key = b then x else m key`, and `b ∈ dm` is `dm b = true`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

namespace copyListMap
/-- Canonical lookup and support roundtrip for `st`. -/
theorem holFmapAsFiniteSupportParamWitness_copyList_st {width : Nat} [NeZero width]
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad st)).lookup key = st.lookup key ∧
      (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad st)).finiteSupport = st.finiteSupport ∧
      FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad st) = st := ⟨rfl, rfl, rfl⟩
end copyListMap

/-- Exact HOL `copy_list_def`: copy the elements of a heap list into
consecutive words starting at `b`, after first writing `x` at `b`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "copy_list_def"
  (fmap_as_finite_support_parameters := [st]) (words_as_type_indexed_bitvec)]
def copyList {width : Nat} [NeZero width] (c' : DataToWord.Config)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (k : Nat)
    (args : WordLocW width × WordLocW width × BitVec width × (BitVec width → WordLocW width) ×
      (BitVec width → Bool)) : Option (BitVec width × (BitVec width → WordLocW width)) :=
  let (a, x, b, m, dm) := args
  let c := dm b = true
  let m := fun key => if key = b then x else m key
  let b := b + StackRemove.bytesInWord width
  if k = 0 then (if c then some (b, m) else none) else
  match a with
  | .loc _ _ => none
  | .word a =>
    match getRealAddr c' st a with
    | none => none
    | some a =>
      let c := (c ∧ dm (a + 2#width * StackRemove.bytesInWord width) = true ∧
        dm (a + StackRemove.bytesInWord width) = true)
      let x := m (a + StackRemove.bytesInWord width)
      let a := m (a + 2#width * StackRemove.bytesInWord width)
      if c then copyList c' st (k - 1) (a, x, b, m, dm) else none
termination_by k
decreasing_by omega

/-- The empty word list separates from any frame. Flapjack infrastructure. -/
theorem star_wordListExists_zero {width : Nat} [NeZero width] (f : BitVec width)
    (h : (BitVec width × WordLocW width) → Prop) :
    SetSep.star (Misc.wordListExists f 0) SetSep.sepT h := by
  refine ⟨fun _ => False, h, ⟨by funext x; simp, by simp⟩, ⟨[], ?_⟩, trivial⟩
  exact (StackRemove.WordListExists.starCond _ _ _).mpr ⟨rfl, rfl⟩

/-- Exact HOL `memory_rel_IMP_word_list_exists`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_IMP_word_list_exists"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_imp_wordListExists {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (n : Nat) (f : BitVec width) :
    memoryRel c be ts refs sp st m dm vars ∧ n ≤ sp ∧ st.lookup .nextFree = some (.word f) →
    SetSep.star (Misc.wordListExists f n) SetSep.sepT (SetSep.fun2Set (m, fun a => dm a = true)) := by
  rintro ⟨⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, _, spaceBound⟩, bound, hf⟩
  by_cases n0 : n = 0
  · subst n0
    exact star_wordListExists_zero f _
  obtain ⟨_, _, _, _, _, _, _, curr, _, _, _, _, _, freeLookup, _, _, _, _, _, heapSep⟩ := heapMem
  have unused : unusedSpaceInv a (sp0 + sp1) heap := by
    obtain ⟨roots, inv, addresses⟩ := wordInv
    exact inv.2.2.2.1
  have fEq : f = curr + StackRemove.bytesInWord width * BitVec.ofNat width a := by
    have := hf.symm.trans freeLookup
    simpa using this
  subst fEq
  have found := unused.1 (by omega)
  obtain ⟨pre, post, heapEq, indexEq⟩ := heapLookup_split heap a _ found
  subst heap
  subst a
  rw [wordHeapAppend] at heapSep
  simp only [wordHeap, wordEl] at heapSep
  repeat rw [← SetSep.starAssoc] at heapSep
  rw [star_swap_first] at heapSep
  rw [show sp0 + sp1 - 1 + 1 = n + (sp0 + sp1 - n) by omega, StackRemove.Proofs.WordListMemory.wordListExistsAdd,
    ← SetSep.starAssoc] at heapSep
  exact star_mono_both heapSep (fun _ h => h) (fun _ _ => trivial)


/-- One word step of an allocation address. Flapjack infrastructure. -/
theorem bwStep {width : Nat} (B C : BitVec width) (k : Nat) :
    B + C * BitVec.ofNat width k + C = B + C * BitVec.ofNat width (k + 1) := by
  rw [BitVec.add_assoc]
  congr 1
  have : BitVec.ofNat width (k + 1) = BitVec.ofNat width k + 1 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, Nat.add_mod]
  rw [this, BitVec.mul_add]
  simp

/-- A decoded nonempty source list is a cons block. Flapjack infrastructure. -/
theorem valueToList_cons (v h : Flapjack.Compiler.Backend.DataSem.Value)
    (t : List Flapjack.Compiler.Backend.DataSem.Value)
    (hv : Flapjack.Compiler.Backend.DataSem.valueToList v = some (h :: t)) :
    ∃ stamp h2, v = .block stamp BackendCommon.consTag [h, h2] ∧ Flapjack.Compiler.Backend.DataSem.valueToList h2 = some t := by
  match v, hv with
  | .block stamp tag [h', h2], hv =>
    rw [Flapjack.Compiler.Backend.DataSem.valueToList] at hv
    split at hv
    · rename_i htag
      cases e : Flapjack.Compiler.Backend.DataSem.valueToList h2 with
      | none => simp [e] at hv
      | some t' =>
        simp [e] at hv
        obtain ⟨rfl, rfl⟩ := hv
        exact ⟨stamp, h2, by rw [htag], e⟩
    · simp at hv
  | .block stamp tag [], hv | .block stamp tag [_], hv | .block stamp tag (_ :: _ :: _ :: _), hv
  | .number _, hv | .word64 _, hv | .codePtr _, hv | .refPtr _ _, hv =>
    simp [Flapjack.Compiler.Backend.DataSem.valueToList] at hv

/-- Write the head cell of an existential list and expose the tail as a
concrete list. Flapjack infrastructure for `copy_list_thm`. -/
theorem wordListExists_writeHead' {width : Nat} [NeZero width] (B : BitVec width) (L : Nat)
    (x : WordLocW width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (sep : SetSep.star (Misc.wordListExists B (L + 1)) frame (SetSep.fun2Set (m, fun a => dm a = true))) :
    dm B = true ∧ ∃ ys : List (WordLocW width), ys.length = L ∧
    SetSep.star (Misc.wordList (B + StackRemove.bytesInWord width) ys)
      (SetSep.star (SetSep.one (B, x)) frame)
      (SetSep.fun2Set ((fun key => if key = B then x else m key), fun a => dm a = true)) := by
  obtain ⟨left, right, part, ⟨xs, hx⟩, frameRight⟩ := sep
  obtain ⟨xsLeft, length⟩ := (StackRemove.WordListExists.starCond _ _ _).mp hx
  have sepList : SetSep.star (Misc.wordList B xs) frame (SetSep.fun2Set (m, fun a => dm a = true)) :=
    ⟨left, right, part, xsLeft, frameRight⟩
  have member := wordList_indexMember xs 0 (by omega) B left xsLeft
  have memGraph : SetSep.fun2Set (m, fun a => dm a = true) (B + BitVec.ofNat width 0 * StackRemove.bytesInWord width, xs[0]) := by
    rw [← part.1]
    exact Or.inl member
  have inDomain := ((SetSep.fun2SetThm m (fun a => dm a = true) _ _).mp memGraph).2
  have changed := wordList_write B xs 0 x m (fun a => dm a = true) frame (by omega) sepList
  simp only [BitVec.zero_mul, BitVec.add_zero] at inDomain changed
  refine ⟨inDomain, ?_⟩
  cases xs with
  | nil => simp at length
  | cons y ys =>
    simp only [List.set_cons_zero, Misc.wordList] at changed
    rw [← SetSep.starAssoc, star_swap_first] at changed
    exact ⟨ys, by simpa using length, changed⟩

/-- Fold a written head cell back into the list. Flapjack infrastructure. -/
theorem wordList_foldHead {width : Nat} [NeZero width] (B : BitVec width) (x : WordLocW width)
    (ys : List (WordLocW width)) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (h : (BitVec width × WordLocW width) → Prop)
    (sep : SetSep.star (Misc.wordList (B + StackRemove.bytesInWord width) ys)
      (SetSep.star (SetSep.one (B, x)) frame) h) :
    SetSep.star (Misc.wordList B (x :: ys)) frame h := by
  simp only [Misc.wordList]
  rw [← SetSep.starAssoc]
  rw [star_swap_first] at sep
  exact sep

/-- `copy_list_thm` before HOL's specialisation to offset 0 (the `Q.prove`
statement of the source). Flapjack infrastructure. -/
theorem copyList_gen {width : Nat} [NeZero width] (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (dm : BitVec width → Bool) (b : BitVec width)
    (good : goodDimindex width) (hb : st.lookup .nextFree = some (.word b)) :
    ∀ (vs : List Flapjack.Compiler.Backend.DataSem.Value) (v : Flapjack.Compiler.Backend.DataSem.Value)
      (k : Nat) (m : BitVec width → WordLocW width)
      (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (a x : WordLocW width)
      (frame : ((BitVec width × WordLocW width) → Prop) → Prop),
      memoryRel c be ts refs sp st m dm ((v, a) :: vars) →
      Flapjack.Compiler.Backend.DataSem.valueToList v = some vs →
      SetSep.star (Misc.wordListExists (b + StackRemove.bytesInWord width * BitVec.ofNat width k) (vs.length + 1))
        frame (SetSep.fun2Set (m, fun a => dm a = true)) →
      k + vs.length < sp →
      ∃ (xs : List (WordLocW width)) (m1 : BitVec width → WordLocW width),
        copyList c st vs.length (a, x, b + StackRemove.bytesInWord width * BitVec.ofNat width k, m, dm) =
          some (b + StackRemove.bytesInWord width * BitVec.ofNat width (k + vs.length + 1), m1) ∧
        vs.length = xs.length ∧
        memoryRel c be ts refs sp st m1 dm (vs.zip xs ++ vars) ∧
        SetSep.star (Misc.wordList (b + StackRemove.bytesInWord width * BitVec.ofNat width k) (x :: xs)) frame
          (SetSep.fun2Set (m1, fun a => dm a = true)) := by
  intro vs
  induction vs with
  | nil =>
    intro v k m vars a x frame rel _ sep hk
    obtain ⟨dB, ys, hys, sep'⟩ := wordListExists_writeHead' _ 0 x m dm frame sep
    obtain ⟨free, hfree, wr⟩ := memoryRel_write c be ts refs sp st m dm vars x
      (memoryRel_tail c be ts refs sp st m dm _ _ rel)
    have freeEq : free = b := by
      have := hfree.symm.trans hb
      simpa using this
    subst freeEq
    obtain ⟨_, rel'⟩ := wr k (by simpa using hk)
    refine ⟨[], _, ?_, rfl, by simpa using rel', ?_⟩
    · rw [copyList.eq_def]
      simp only [List.length_nil, dB, if_true, Nat.add_zero, bwStep]
    · cases ys with
      | nil => exact wordList_foldHead _ x [] frame _ sep'
      | cons _ _ => simp at hys
  | cons h t ih =>
    intro v k m vars a x frame rel hv sep hk
    obtain ⟨stamp, h2, rfl, hv2⟩ := valueToList_cons v h t hv
    simp only [List.length_cons] at sep hk ⊢
    have stepB : b + StackRemove.bytesInWord width * BitVec.ofNat width k + StackRemove.bytesInWord width =
        b + StackRemove.bytesInWord width * BitVec.ofNat width (k + 1) := bwStep _ _ k
    obtain ⟨dB, ys, hys, sep0⟩ := wordListExists_writeHead' _ (t.length + 1) x m dm frame sep
    obtain ⟨free, hfree, wr⟩ := memoryRel_write c be ts refs sp st m dm _ x rel
    have freeEq : b = free := by
      have := hb.symm.trans hfree
      simpa using this
    subst freeEq
    obtain ⟨_, rel0⟩ := wr k (by omega)
    obtain ⟨w7, a7, _, hloc, real, d1, rel1⟩ := memoryRel_elAny c be ts refs sp st _ dm stamp
      BackendCommon.consTag [h, h2] a vars 0 (by simp) ⟨rel0, good⟩
    have rel1s := memoryRel_swap c be ts refs sp st _ dm _ _ _ rel1
    obtain ⟨w7', a7', _, hloc', real', d2, rel2⟩ := memoryRel_elAny c be ts refs sp st _ dm stamp
      BackendCommon.consTag [h, h2] a _ 1 (by simp) ⟨rel1s, good⟩
    subst hloc
    cases hloc'
    cases real'.symm.trans real
    have e1 : a7 + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width 0 =
        a7 + StackRemove.bytesInWord width := by simp
    have e2 : a7 + StackRemove.bytesInWord width + StackRemove.bytesInWord width * BitVec.ofNat width 1 =
        a7 + 2#width * StackRemove.bytesInWord width := by
      rw [BitVec.add_assoc]
      congr 1
      simp [BitVec.two_mul]
    simp only [e1, e2, List.getElem_cons_zero, List.getElem_cons_succ] at d1 d2 rel1 rel2
    have rel3 := memoryRel_rearrange c be ts refs sp st _ dm _
      ((h2, (fun key => if key = b + StackRemove.bytesInWord width * BitVec.ofNat width k then x else m key)
          (a7 + 2#width * StackRemove.bytesInWord width)) ::
        (h, (fun key => if key = b + StackRemove.bytesInWord width * BitVec.ofNat width k then x else m key)
          (a7 + StackRemove.bytesInWord width)) :: vars)
      (by intro p hp; simp at hp ⊢; tauto) rel2
    have sepIH : SetSep.star (Misc.wordListExists (b + StackRemove.bytesInWord width * BitVec.ofNat width (k + 1))
        (t.length + 1)) (SetSep.star (SetSep.one (b + StackRemove.bytesInWord width * BitVec.ofNat width k, x)) frame)
        (SetSep.fun2Set ((fun key => if key = b + StackRemove.bytesInWord width * BitVec.ofNat width k then x else m key),
          fun a => dm a = true)) := by
      rw [← stepB]
      exact star_mono_both sep0
        (fun part hp => ⟨ys, (StackRemove.WordListExists.starCond _ _ _).mpr ⟨hp, hys⟩⟩) (fun _ h => h)
    obtain ⟨xs, m1, hc, hl, hr, hs⟩ := ih h2 (k + 1) _ _ _
      ((fun key => if key = b + StackRemove.bytesInWord width * BitVec.ofNat width k then x else m key)
        (a7 + StackRemove.bytesInWord width)) _ rel3 hv2 sepIH (by omega)
    refine ⟨((fun key => if key = b + StackRemove.bytesInWord width * BitVec.ofNat width k then x else m key)
        (a7 + StackRemove.bytesInWord width)) :: xs, m1, ?_, by simp [hl], ?_, ?_⟩
    · rw [copyList.eq_def]
      simp only [Nat.add_one_ne_zero, if_false, real, dB, d1, d2, and_self, if_true, Nat.add_sub_cancel, stepB]
      rw [show k + (t.length + 1) + 1 = k + 1 + t.length + 1 by omega]
      exact hc
    · refine memoryRel_rearrange c be ts refs sp st _ dm _ _ ?_ hr
      intro p hp
      simp at hp ⊢
      tauto
    · rw [← stepB] at hs
      exact wordList_foldHead _ x _ frame _ hs

/-- Exact HOL `copy_list_thm` (the stored theorem: the source's `Q.prove`
specialised to offset 0, i.e. `Q.SPECL [v, 0]` then simplified). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "copy_list_thm"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem copyList_thm {width : Nat} [NeZero width] (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (dm : BitVec width → Bool) :
    ∀ (v : Flapjack.Compiler.Backend.DataSem.Value) (vs : List Flapjack.Compiler.Backend.DataSem.Value)
      (b : BitVec width) (m : BitVec width → WordLocW width)
      (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (a x : WordLocW width)
      (frame : ((BitVec width × WordLocW width) → Prop) → Prop),
      memoryRel c be ts refs sp st m dm ((v, a) :: vars) ∧
      Flapjack.Compiler.Backend.DataSem.valueToList v = some vs ∧
      SetSep.star (Misc.wordListExists b (vs.length + 1)) frame (SetSep.fun2Set (m, fun a => dm a = true)) ∧
      goodDimindex width ∧ st.lookup .nextFree = some (.word b) ∧ vs.length < sp →
      ∃ (xs : List (WordLocW width)) (m1 : BitVec width → WordLocW width),
        copyList c st vs.length (a, x, b, m, dm) =
          some (b + StackRemove.bytesInWord width * BitVec.ofNat width (vs.length + 1), m1) ∧
        vs.length = xs.length ∧
        memoryRel c be ts refs sp st m1 dm (vs.zip xs ++ vars) ∧
        SetSep.star (Misc.wordList b (x :: xs)) frame (SetSep.fun2Set (m1, fun a => dm a = true)) := by
  rintro v vs b m vars a x frame ⟨rel, hv, sep, good, hb, hlen⟩
  have e0 : b + StackRemove.bytesInWord width * BitVec.ofNat width 0 = b := by simp
  have := copyList_gen c be ts refs sp st dm b good hb vs v 0 m vars a x frame rel hv
    (by rw [e0]; exact sep) (by omega)
  rw [e0, Nat.zero_add] at this
  exact this

/-- Exact HOL `memory_rel_FromList`. HOL's conclusion also binds `∃xs` of an
independent type β that occurs nowhere else; it is vacuous and omitted, as in
the reviewed `new_thunk_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_FromList"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_fromList {width : Nat} [NeZero width] (v : Flapjack.Compiler.Backend.DataSem.Value)
    (vs : List Flapjack.Compiler.Backend.DataSem.Value) (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (a : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (tag : Nat) (hd : BitVec width) :
    Flapjack.Compiler.Backend.DataSem.valueToList v = some vs ∧ vs ≠ [] ∧
      memoryRel c be ts refs sp st m dm ((v, a) :: vars) ∧
      encodeHeader c (4 * tag) vs.length = some hd ∧ vs.length < sp ∧ goodDimindex width →
    ∃ (free curr : BitVec width) (m1 : BitVec width → WordLocW width) (f1 : BitVec width),
      st.lookup .nextFree = some (.word free) ∧ st.lookup .currHeap = some (.word curr) ∧
      copyList c st vs.length (a, .word hd, free, m, dm) = some (f1, m1) ∧
      memoryRel c be (ts + 1) refs (sp - (vs.length + 1)) (st.update (.nextFree, .word f1)) m1 dm
        ((.block ts tag vs, Build.makeConsPtr c (free - curr) tag vs.length) :: vars) := by
  rintro ⟨hv, ne, rel, encoded, hlen, good⟩
  obtain ⟨free, hfree, _⟩ := memoryRel_write c be ts refs sp st m dm _ (.word hd) rel
  have ex := memoryRel_imp_wordListExists c be ts refs sp st m dm _ (vs.length + 1) free
    ⟨rel, by omega, hfree⟩
  obtain ⟨xs, m1, hc, hl, rel1, sep1⟩ :=
    copyList_thm c be ts refs sp st dm v vs free m vars a (.word hd) SetSep.sepT ⟨rel, hv, ex, good, hfree, hlen⟩
  obtain ⟨free', curr, _, h1, h2, imp⟩ := memoryRel_consAlt (β := Unit) c be ts refs sp st m1 dm vs xs vars tag hd
    rel1 hl ne (by rw [← hl]; exact encoded) (by omega) good
  have freeEq : free' = free := by
    have := h1.symm.trans hfree
    simpa using this
  subst freeEq
  have result := imp sep1
  rw [← hl] at result
  exact ⟨free', curr, m1, _, h1, h2, hc, result⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
