module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Memory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.BuildWords
public import Flapjack.Compiler.Backend.DataSpace.Requirements
public import Flapjack.Compiler.Backend.Semantics.DataSem.Build
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.NumberSize
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Unit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.BuildFacts
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.PartAdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreConsts
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
/-- The word list produced for a Word64 constant is exactly its abstract heap
payload. This Flapjack helper connects the source builder's Word64 case to
`memory_rel_Word64_alt`. -/
private theorem word64Rep_buildPayload {width : Nat} [NeZero width] (word : BitVec 64) (good : goodDimindex width) :
    let words : List (BitVec width) := if width < 64 then
      [BitVec.ofNat width (word.toNat / 2 ^ 32), BitVec.ofNat width (word.toNat % 2 ^ 32)]
      else [BitVec.ofNat width word.toNat]
    (word64Rep word : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) =
      .dataElement [] words.length (.word64Tag, words.map .word) := by
  rcases good with h | h <;> subst width
  · simp only [word64Rep, show 32 < 64 by decide, ↓reduceIte, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil]
    congr 2
    simp only [List.cons.injEq, WordLocW.word.injEq, and_true]
    constructor <;> apply BitVec.eq_of_toNat_eq <;>
      simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · simp only [word64Rep, show ¬ 64 < 64 by decide, ↓reduceIte, List.length_cons,
      List.length_nil, List.map_cons, List.map_nil]
    congr 2
    simp only [List.cons.injEq, WordLocW.word.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    simp
private theorem partLength {width : Nat} [NeZero width] (conf : Config) (memory : Nat → WordLocW width)
    (part : ClosLang.ConstPart) (off : BitVec width) (w : WordLocW width) (ws : List (WordLocW width))
    (run : buildPartWords conf memory part off = some (w, ws)) (good : goodDimindex width) :
    ws.length ≤ DataSpace.partSpaceReq part := by
  classical
  cases part with
  | con tag refs =>
    cases refs with
    | nil => simp [buildPartWords] at run; simp [DataSpace.partSpaceReq, ← run.2]
    | cons x xs =>
      simp only [buildPartWords, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
      cases h : encodeHeader (width := width) conf (4 * tag) (xs.length + 1) with
      | none => simp [h] at run
      | some header =>
        simp [h] at run
        obtain ⟨_, rfl⟩ := run
        simp [DataSpace.partSpaceReq]
  | w64 w64 =>
    by_cases narrow : width < 64
    · simp only [buildPartWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases h : encodeHeader (width := width) conf 3 2 <;> simp_all [DataSpace.partSpaceReq]
      obtain ⟨_, rfl⟩ := run
      simp
    · simp only [buildPartWords, narrow, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases h : encodeHeader (width := width) conf 3 1 <;> simp_all [DataSpace.partSpaceReq]
      obtain ⟨_, rfl⟩ := run
      simp
  | int i =>
    by_cases small : smallInt width i
    · simp [buildPartWords, small] at run
      obtain ⟨_, rfl⟩ := run
      simp
    · have absBig : ¬ i.natAbs < 536870912 := by
        intro h
        apply small
        unfold smallInt
        rcases good with hw | hw <;> rw [hw] <;> cases i <;> simp_all [Int.natAbs] <;> omega
      have bound := length_n2mw_le_numSize good i.natAbs i.natAbs (Nat.le_refl _)
      simp only [buildPartWords, small, ↓reduceIte, Misc.Multiword.i2mw] at run
      cases h : encodeHeader (width := width) conf ((((if decide (i < 0) then 1 else 0 : BitVec width) <<< 2) ||| 3).toNat)
          (Misc.Multiword.n2mw (width := width) i.natAbs).length <;>
        simp_all [DataSpace.partSpaceReq]
      obtain ⟨_, rfl⟩ := run
      simp only [List.length_cons, List.length_map]
      split <;> omega
  | str text =>
    simp only [buildPartWords] at run
    split at run
    · simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      simp only [List.length_map, List.length_cons, writeBytes_wordCount, List.length_replicate]
      simp only [DataSpace.partSpaceReq]
      rw [Flapjack.Basis.Pure.MlString.MlString.length_explode]
      rcases good with hw | hw
      · simp [Build.byteLen, hw]
      · simp only [Build.byteLen, hw]
        norm_num
        have bound : text.strlen / 8 ≤ text.strlen / 4 := Nat.div_le_div_left (by decide) (by decide)
        omega
    · simp_all

private theorem partStep {width : Nat} [NeZero width] (c : Config) (be : Bool) (ts ts1 : Nat)
    (refs refs1 : Spt (BvlSem.Ref Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (source : Nat → Value) (target : Nat → WordLocW width)
    (vars : List (Value × WordLocW width)) (free curr : BitVec width)
    (part : ClosLang.ConstPart) (value : Value) (w : WordLocW width) (ws : List (WordLocW width))
    (partRun : doPart source part refs (some ts) = (value, refs1, some ts1))
    (run : buildPartWords c target part (free - curr) = some (w, ws))
    (budget : DataSpace.partSpaceReq part ≤ sp)
    (freeLookup : st.lookup .nextFree = some (.word free)) (currLookup : st.lookup .currHeap = some (.word curr))
    (context : ∀ (ks : List Nat), memoryRel c be ts refs sp st m dm (ks.map (fun k => (source k, target k)) ++ vars))
    (good : goodDimindex width) (ks : List Nat) :
    ∃ m1, storeList free ws m dm = some m1 ∧
      memoryRel c be ts1 refs1 (sp - ws.length)
        (st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width ws.length))) m1 dm
        ((value, w) :: ks.map (fun k => (source k, target k)) ++ vars) := by
  cases part with
  | w64 word =>
    simp [doPart] at partRun
    obtain ⟨rfl, rfl, rfl⟩ := partRun
    rcases good with width32 | width64 <;> subst width
    · simp only [buildPartWords, show 32 < 64 by decide, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases enc : encodeHeader (width := 32) c 3 2 with
      | none => simp [enc] at run
      | some hd =>
        simp [enc] at run
        obtain ⟨rfl, rfl⟩ := run
        have rep := word64Rep_buildPayload (width := 32) word (by simp [goodDimindex])
        simp only [show 32 < 64 by decide, ↓reduceIte, List.length_cons, List.length_nil, List.map_cons, List.map_nil] at rep
        have room : 2 < sp := by simp [DataSpace.partSpaceReq] at budget; omega
        obtain ⟨ne, curr1, m1, nf, ch, stored, after⟩ :=
          memoryRel_word64Alt c be ts refs sp st m dm [] (ks.map (fun k => (source k, target k)) ++ vars)
            word [ .word (BitVec.ofNat 32 (word.toNat / 2 ^ 32)), .word (BitVec.ofNat 32 (word.toNat % 2 ^ 32)) ] hd
            (by simpa using context ks) (by simp [goodDimindex]) rep (by simpa using room) (by simpa using enc)
        have eqFree : ne = free := by simpa [freeLookup] using nf.symm
        have eqCurr : curr1 = curr := by simpa [currLookup] using ch.symm
        subst ne
        subst curr1
        exact ⟨m1, by simpa using stored, by simpa using after⟩
    · simp only [buildPartWords, show ¬ 64 < 64 by decide, ↓reduceIte, List.length_cons, List.length_nil] at run
      cases enc : encodeHeader (width := 64) c 3 1 with
      | none => simp [enc] at run
      | some hd =>
        simp [enc] at run
        obtain ⟨rfl, rfl⟩ := run
        have rep := word64Rep_buildPayload (width := 64) word (by simp [goodDimindex])
        simp only [show ¬ 64 < 64 by decide, ↓reduceIte, List.length_cons, List.length_nil, List.map_cons, List.map_nil] at rep
        have room : 1 < sp := by simp [DataSpace.partSpaceReq] at budget; omega
        obtain ⟨ne, curr1, m1, nf, ch, stored, after⟩ :=
          memoryRel_word64Alt c be ts refs sp st m dm [] (ks.map (fun k => (source k, target k)) ++ vars)
            word [.word (BitVec.ofNat 64 word.toNat)] hd
            (by simpa using context ks) (by simp [goodDimindex]) rep (by simpa using room) (by simpa using enc)
        have eqFree : ne = free := by simpa [freeLookup] using nf.symm
        have eqCurr : curr1 = curr := by simpa [currLookup] using ch.symm
        subst ne
        subst curr1
        exact ⟨m1, by simpa using stored, by simpa using after⟩
  | int i =>
    simp [doPart] at partRun
    obtain ⟨rfl, rfl, rfl⟩ := partRun
    by_cases small : smallInt width i
    · simp [buildPartWords, small] at run
      obtain ⟨rfl, rfl⟩ := run
      have storeSame : st.update (.nextFree, .word free) = st := by
        cases st with
        | mk lookup support =>
          simp only [HolFiniteMapExact.update]
          congr 1
          exact FUPDATE_eq_self_of_lookup_some lookup .nextFree (.word free) freeLookup
      have result := impMemoryRel_number c be ts refs sp st m dm
        (ks.map (fun k => (source k, target k)) ++ vars) i ⟨good, small, context ks⟩
      refine ⟨m, ?_, ?_⟩
      · simp [storeList]
      · simpa [storeSame] using result
    · have big : ¬ i.natAbs < 536870912 := by
        intro bound
        apply small
        unfold smallInt
        rcases good with h | h <;> rw [h] <;> cases i <;> simp_all [Int.natAbs] <;> omega
      let digits : List (BitVec width) := Misc.Multiword.n2mw i.natAbs
      let sign := decide (i < 0)
      let tag : Nat := (((if sign then 1 else 0 : BitVec width) <<< 2) ||| 3).toNat
      simp only [buildPartWords, small, ↓reduceIte, Misc.Multiword.i2mw] at run
      change (do let header ← encodeHeader c tag digits.length
                 some (Build.makePtr c (free - curr) (0 : BitVec width) digits.length,
                   (header :: digits).map WordLocW.word)) = some (w, ws) at run
      cases enc : encodeHeader (width := width) c tag digits.length with
      | none => simp [enc] at run
      | some hd =>
        simp [enc] at run
        obtain ⟨rfl, rfl⟩ := run
        have digitBound := length_n2mw_le_numSize good i.natAbs i.natAbs (Nat.le_refl _)
        have room : digits.length < sp := by
          simp [DataSpace.partSpaceReq, big] at budget
          dsimp [digits] at *
          omega
        have rep : (bignumRep i : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) =
            .dataElement [] digits.length (.numTag sign, digits.map .word) := by
          simp [bignumRep, Misc.Multiword.i2mw, digits, sign]
        obtain ⟨ne, curr1, m1, nf, ch, stored, after⟩ :=
          memoryRel_bignumAlt c be ts refs sp st m dm (ks.map (fun k => (source k, target k)) ++ vars)
            i sign digits hd (context ks) good small rep room (by simpa [tag] using enc)
        have eqFree : ne = free := by simpa [freeLookup] using nf.symm
        have eqCurr : curr1 = curr := by simpa [currLookup] using ch.symm
        subst ne
        subst curr1
        exact ⟨m1, by simpa using stored, by simpa using after⟩
  | con tag indices =>
    cases indices with
    | nil =>
      simp [doPart] at partRun
      obtain ⟨rfl, rfl, rfl⟩ := partRun
      simp [buildPartWords] at run
      obtain ⟨bound, rfl, rfl⟩ := run
      have storeSame : st.update (.nextFree, .word free) = st := by
        cases st with
        | mk lookup support =>
          simp only [HolFiniteMapExact.update]
          congr 1
          exact FUPDATE_eq_self_of_lookup_some lookup .nextFree (.word free) freeLookup
      have result := memoryRel_consEmpty c be ts refs sp st m dm
        (ks.map (fun k => (source k, target k)) ++ vars) tag ⟨context ks, bound, good⟩
      have imm : (blockNil tag : BitVec width) = BitVec.ofNat width (16 * tag + 2) := by
        rcases good with hw | hw <;> subst width <;> apply BitVec.eq_of_toNat_eq <;>
          simp [blockNil, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
            Nat.shiftLeft_eq, Nat.mul_mod, Nat.add_mod, Nat.mul_comm]
      refine ⟨m, by simp [storeList], ?_⟩
      simpa [storeSame, imm] using result
    | cons head tail =>
      simp [doPart] at partRun
      obtain ⟨rfl, rfl, rfl⟩ := partRun
      simp only [buildPartWords, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
      cases enc : encodeHeader (width := width) c (4 * tag) (tail.length + 1) with
      | none => simp [enc] at run
      | some hd =>
        simp [enc] at run
        obtain ⟨rfl, rfl⟩ := run
        have zipEq : ∀ (xs : List Nat), (xs.map source).zip (xs.map target) = xs.map (fun k => (source k, target k)) := by
          intro xs
          induction xs with
          | nil => rfl
          | cons x xs ih => simp [ih]
        have rel : memoryRel c be ts refs sp st m dm
            (((head :: tail).map source).zip ((head :: tail).map target) ++
              (ks.map (fun k => (source k, target k)) ++ vars)) := by
          rw [zipEq]
          simpa [List.map_append, List.append_assoc] using context ((head :: tail) ++ ks)
        have room : (head :: tail).length < sp := by
          simp [DataSpace.partSpaceReq] at budget
          simp only [List.length_cons]
          omega
        obtain ⟨ne, curr1, m1, nf, ch, stored, after⟩ :=
          memoryRel_cons1 c be ts refs sp st m dm ((head :: tail).map source) ((head :: tail).map target)
            (ks.map (fun k => (source k, target k)) ++ vars) tag hd rel (by simp) (by simp)
            (by simpa using enc) (by simpa using room) good
        have eqFree : ne = free := by simpa [freeLookup] using nf.symm
        have eqCurr : curr1 = curr := by simpa [currLookup] using ch.symm
        subst ne
        subst curr1
        exact ⟨m1, by simpa using stored, by simpa using after⟩
  | str text =>
    simp [doPart] at partRun
    obtain ⟨rfl, rfl, rfl⟩ := partRun
    let n := text.explode.length
    let count := Build.byteLen width n
    by_cases bounds : count < 2 ^ (width - 4) ∧ count < 2 ^ c.lenSize
    · simp [buildPartWords, show Build.byteLen width text.explode.length < 2 ^ (width - 4) ∧ Build.byteLen width text.explode.length < 2 ^ c.lenSize by simpa [count, n] using bounds] at run
      obtain ⟨rfl, rfl⟩ := run
      have endian : c.be = be := by
        obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, rest⟩ := context ks
        obtain ⟨roots, absInv, addresses⟩ := wordInv
        obtain ⟨f, tf, h1, h2, h3, h4, h5, h6, h7⟩ := absInv.2.2.2.2
        exact h6
      have room : count < sp := by
        dsimp [count, n]
        rw [Flapjack.Basis.Pure.MlString.MlString.length_explode]
        rcases good with hw | hw <;> subst width <;> simp [Build.byteLen, DataSpace.partSpaceReq] at budget ⊢ <;> omega
      obtain ⟨ne, curr1, m1, nf, ch, stored, after⟩ :=
        memoryRel_freshByte c be ts refs sp st m dm (ks.map (fun k => (source k, target k)) ++ vars)
          (DataSem.leastUnusedRef refs) n true text.explode (context ks)
          (leastNotInDomain refs) room bounds.1 bounds.2 rfl good
      have eqFree : ne = free := by simpa [freeLookup] using nf.symm
      have eqCurr : curr1 = curr := by simpa [currLookup] using ch.symm
      subst ne
      subst curr1
      exact ⟨m1, by simpa [n, count, endian] using stored,
        by simpa [n, count, endian, writeBytes_wordCount] using after⟩
    · simp [buildPartWords, show ¬ (Build.byteLen width text.explode.length < 2 ^ (width - 4) ∧ Build.byteLen width text.explode.length < 2 ^ c.lenSize) by simpa [count, n] using bounds] at run


/-- Constant construction preserves the full memory relation and writes the exact output words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_do_build"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_doBuild {width : Nat} [NeZero width] {β : Type} (c : Config) (be : Bool)
    (parts : List ClosLang.ConstPart) (i : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (free curr : BitVec width) (sp : Nat)
    (source : Nat → Value) (target : Nat → WordLocW width)
    (refs : Spt (BvlSem.Ref Value)) (ts : Nat) (refs1 : Spt (BvlSem.Ref Value)) (_shadowed : β)
    (m : BitVec width → WordLocW width) (value : Value) (ws : List (WordLocW width))
    (ts1 : Nat) (w : WordLocW width) (dm : BitVec width → Bool) (vars : List (Value × WordLocW width))
    (sourceRun : doBuild source i parts refs (some ts) = (value, refs1, some ts1))
    (targetRun : buildWords c target i parts (free - curr) = some (w, ws))
    (budget : (parts.map DataSpace.partSpaceReq).sum ≤ sp)
    (freeLookup : st.lookup .nextFree = some (.word free)) (currLookup : st.lookup .currHeap = some (.word curr))
    (context : ∀ ks : List Nat, memoryRel c be ts refs sp st m dm (ks.map (fun k => (source k, target k)) ++ vars))
    (good : goodDimindex width) :
    ∃ m1, memoryRel c be ts1 refs1 (sp - ws.length)
      (st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width ws.length))) m1 dm
      ((value, w) :: vars) ∧ storeList free ws m dm = some m1 := by
  induction parts generalizing i st free curr sp source target refs ts refs1 m value ws ts1 w with
  | nil =>
    simp [doBuild] at sourceRun
    obtain ⟨rfl, rfl, rfl⟩ := sourceRun
    simp [buildWords] at targetRun
    obtain ⟨rfl, rfl⟩ := targetRun
    have storeSame : st.update (.nextFree, .word free) = st := by
      cases st with
      | mk lookup support =>
        simp only [HolFiniteMapExact.update]
        congr 1
        exact FUPDATE_eq_self_of_lookup_some lookup .nextFree (.word free) freeLookup
    refine ⟨m, ?_, by simp [storeList]⟩
    simpa [storeSame] using context [i - 1]
  | cons part parts ih =>
    simp only [doBuild] at sourceRun
    cases hp : doPart source part refs (some ts) with
    | mk partVal rest =>
      cases rest with
      | mk partRefs partTs =>
        obtain ⟨midTs, ht⟩ := doPartSome source part refs partRefs ts partVal partTs hp
        subst partTs
        simp only [hp] at sourceRun
        simp only [buildWords] at targetRun
        cases hq : buildPartWords c target part (free - curr) with
        | none => simp [hq] at targetRun
        | some partResult =>
          cases partResult with
          | mk partWord partWords =>
            simp only [hq] at targetRun
            cases hr : buildWords c (fun key => if key = i then partWord else target key) (i+1) parts
              (free - curr + wordSemBytesInWord * BitVec.ofNat width partWords.length) with
            | none => simp [hr] at targetRun
            | some result =>
              cases result with
              | mk finalWord restWords =>
                simp [hr] at targetRun
                obtain ⟨rfl, rfl⟩ := targetRun
                have partBudget : DataSpace.partSpaceReq part ≤ sp := by simp at budget; omega
                obtain ⟨midMem, stored, _midRel⟩ := partStep c be ts midTs refs partRefs sp st m dm source target vars free curr part partVal partWord partWords hp hq partBudget freeLookup currLookup context good []
                let nextFree := free + wordSemBytesInWord * BitVec.ofNat width partWords.length
                let nextStore := st.update (.nextFree, .word nextFree)
                have updatedContext : ∀ ks : List Nat,
                    memoryRel c be midTs partRefs (sp - partWords.length) nextStore midMem dm
                      (ks.map (fun k => ((if k = i then partVal else source k), (if k = i then partWord else target k))) ++ vars) := by
                  intro ks
                  obtain ⟨mem2, stored2, rel2⟩ := partStep c be ts midTs refs partRefs sp st m dm source target vars free curr part partVal partWord partWords hp hq partBudget freeLookup currLookup context good ks
                  have same : mem2 = midMem := Option.some.inj (stored2.symm.trans stored)
                  subst mem2
                  simpa [nextStore, nextFree, Function.update] using
                    memoryRel_mapUpdate c be midTs partRefs (sp - partWords.length) nextStore midMem dm partVal partWord source target i ks vars rel2
                have partBound := partLength c target part (free - curr) partWord partWords hq good
                have restBudget : (parts.map DataSpace.partSpaceReq).sum ≤ sp - partWords.length := by
                  simp only [List.map_cons, List.sum_cons] at budget
                  omega
                have freeNext : nextStore.lookup .nextFree = some (.word nextFree) := by
                  simp [nextStore, HolFiniteMapExact.lookup_update, FUPDATE]
                have currNext : nextStore.lookup .currHeap = some (.word curr) := by
                  simp [nextStore, HolFiniteMapExact.lookup_update, FUPDATE, currLookup]
                have targetNext : buildWords c (fun key => if key = i then partWord else target key) (i+1) parts
                    (nextFree - curr) = some (finalWord, restWords) := by
                  convert hr using 1; dsimp [nextFree]; simp only [BitVec.sub_eq_add_neg]; ac_rfl
                obtain ⟨finalMem, finalRel, finalStore⟩ := ih (i+1) nextStore nextFree curr (sp-partWords.length)
                  (fun key => if key = i then partVal else source key) (fun key => if key = i then partWord else target key)
                  partRefs midTs refs1 midMem value restWords ts1 finalWord sourceRun targetNext restBudget freeNext currNext updatedContext
                refine ⟨finalMem, ?_, ?_⟩
                · have storeEq : nextStore.update (.nextFree, .word (nextFree + wordSemBytesInWord * BitVec.ofNat width restWords.length)) =
                      st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width (partWords ++ restWords).length)) := by
                    dsimp [nextStore, nextFree]
                    simp only [List.length_append, BitVec.ofNat_add, BitVec.mul_add]
                    cases st with
                    | mk lookup support =>
                      simp only [HolFiniteMapExact.update]
                      congr 1
                      funext key
                      simp only [FUPDATE]
                      split <;> simp_all [BitVec.add_assoc]
                  have spaceEq : sp - partWords.length - restWords.length = sp - (partWords ++ restWords).length := by simp [Nat.sub_sub]
                  rw [← storeEq, ← spaceEq]
                  exact finalRel
                · rw [Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.storeList_append, stored]
                  exact finalStore


/-- Building a constant preserves the memory relation and stores the relocated words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_do_build_const"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_doBuildConst {width : Nat} [NeZero width] (c : Config) (be : Bool)
    (parts : List ClosLang.ConstPart) (refs refs1 : Spt (BvlSem.Ref Value)) (ts ts1 : Nat)
    (value : Value) (w : Build.Value width) (ws : List (Build.Value width))
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vars : List (Value × WordLocW width)) (free curr : BitVec width)
    (sourceRun : doBuildConst parts refs (some ts) = (value, refs1, some ts1))
    (targetRun : Build.partsWords c parts = some (w, ws))
    (rel : memoryRel c be ts refs sp st m dm vars)
    (budget : (parts.map DataSpace.partSpaceReq).sum ≤ sp)
    (freeLookup : st.lookup .nextFree = some (.word free))
    (currLookup : st.lookup .currHeap = some (.word curr)) (good : goodDimindex width) :
    ∃ m1, memoryRel c be ts1 refs1 (sp - ws.length)
      (st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width ws.length))) m1 dm
      ((value, wordCondAdd c (free - curr) w) :: vars) ∧
      storeList free (ws.map (wordCondAdd c (free - curr))) m dm = some m1 := by
  obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, heapBound, spaceBound⟩ := rel
  have rel : memoryRel c be ts refs sp st m dm vars :=
    ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, heapBound, spaceBound⟩
  obtain ⟨h1, h2, shiftBound, h4, h5, h6, h7, oldCurr, other, currAligned, otherAligned,
    currGet, otherGet, freeGet, rest⟩ := heapMem
  have currEq : oldCurr = curr := by simpa [currLookup] using currGet.symm
  subst oldCurr
  have freeEq : free = curr + StackRemove.bytesInWord width * BitVec.ofNat width a := by
    simpa [freeLookup] using freeGet
  have offsetAligned : holByteAligned (free - curr) = true := by
    rw [freeEq]
    simpa [StackRemove.bytesInWord, wordSemBytesInWord] using (byteAlignMultBytesInWord (BitVec.ofNat width a) good).2
  have context : ∀ ks : List Nat, memoryRel c be ts refs sp st m dm
      (ks.map (fun _ => (Value.number 0, WordLocW.word (0 : BitVec width))) ++ vars) := by
    intro ks
    induction ks with
    | nil => simpa using rel
    | cons k ks ih =>
      have small : smallInt width 0 := by rcases good with h | h <;> simp [smallInt, h]
      have h := impMemoryRel_number c be ts refs sp st m dm _ 0 ⟨good, small, ih⟩
      simpa [smallnum] using h
  have targetRun1 : Build.partsToWords c .ln 0 parts 0 = some (w, ws) := targetRun
  obtain ⟨v1, ws1, relocated, wordsEq, valueEq⟩ :=
    partsWords_add c parts .ln 0 0 (free - curr) w ws .ln targetRun1
      (by simp [holByteAligned, holAligned, holAlign_eq_shift]) offsetAligned good shiftBound (by intro i; simp [Build.lookupMem, wordCondAdd])
  have built := partsWords_imp_build c .ln 0 parts (free - curr) v1 ws1 (by simpa using relocated)
    good offsetAligned shiftBound
  have built0 : buildWords c (fun _ => .word (0 : BitVec width)) 0 parts (free - curr) =
      some (wordCondAdd c (free - curr) w, ws.map (wordCondAdd c (free - curr))) := by
    simpa [Build.lookupMem, valueEq, wordsEq] using built
  have h := memoryRel_doBuild c be parts 0 st free curr sp (fun _ => .number 0) (fun _ => .word 0)
    refs ts refs1 () m value (ws.map (wordCondAdd c (free-curr))) ts1 _ dm vars
    (by simpa [doBuildConst] using sourceRun) built0 budget freeLookup currLookup context good
  simpa using h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
