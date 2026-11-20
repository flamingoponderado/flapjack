module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GetWords
public import Flapjack.Misc.SptreeLookup
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.StoreConsts
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! Correctness of the data-to-word constant-layout store. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

namespace StoreAnyConstsPort

/-- Canonical witness for the finite-map state fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StoreAnyConstsPort



/-- The location-writing evaluator step used in the induction. -/
private theorem loc_step {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 label : Nat) (s : WordSemStateFiniteExact width C F)
    (free : BitVec width) (p : WordLangProgHOL (BitVec width))
    (hne : r2 ≠ r1) (hcode : sptMem label s.code)
    (hfree : sptLookup r2 s.locals = some (.word free))
    (hdom : s.mdomain free = true) :
    evaluate (wordListSeq [.locValue r1 label, .store (.var r2) r1,
      .assign r2 (.op .add [.var r2, .const wordSemBytesInWord]), p]) s =
    evaluate p { s with locals := sptInsert r2 (.word (free + wordSemBytesInWord)) (sptInsert r1 (.loc label 0) s.locals), memory := fun x => if x = free then .loc label 0 else s.memory x } := by
  simp [wordListSeq, evaluate, wordExp, getVar, setVar, memStore,
    WordSemStateFiniteExact.fixClock, hcode, hfree, hdom, hne,
    sptLookup_sptInsert_ne, sptLookup_sptInsert_same, theWords, wordOpHOL, wordOp]



/-- The constant-word evaluator step used in the induction. -/
private theorem words_step {width : Nat} [NeZero width] {C F : Type}
    (r2 r3 : Nat) (s : WordSemStateFiniteExact width C F)
    (free off : BitVec width) (words : List (Bool × BitVec width))
    (p : WordLangProgHOL (BitVec width)) (memory : BitVec width → WordLocW width)
    (hfree : sptLookup r2 s.locals = some (.word free))
    (hoff : sptLookup r3 s.locals = some (.word off))
    (haddr : wordSemConstAddresses free words s.mdomain = true)
    (hwrite : wordSemConstWrites free off words s.memory = memory) :
    evaluate (.seq (.storeConsts r2 r3 r2 r3 words) p) s =
    evaluate p {s with memory := memory, locals := sptInsert r2 (.word (free + wordSemBytesInWord * BitVec.ofNat width words.length)) (sptInsert r3 (.word off) (sptDelete r2 (sptDelete r3 s.locals)))} := by
  simp [evaluate, getVar, hfree, hoff, haddr, hwrite, unsetVar, setVar,
    WordSemStateFiniteExact.fixClock]


/-- Evaluating a constant layout stores the specified words and leaves all
    unrelated locals unchanged. The evaluator inherits the real-model
    assumption recorded in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_StoreAnyConsts"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_storeAnyConsts {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 r3 : Nat) (vs : List (Bool × WordLocW width)) (w : Bool × WordLocW width)
    (s : WordSemStateFiniteExact width C F) (free a : BitVec width) (c : Config)
    (m m1 : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (run : storeList free (vs.map (wordCondAdd c a)) m dm = some m1)
    (hm : m = s.memory) (hdm : dm = s.mdomain) (distinct : [r1,r2,r3].Nodup)
    (good : ∀ v ∈ w :: vs, goodLoc (sptDomain s.code) v.2)
    (hr2 : sptLookup r2 s.locals = some (.word free))
    (hr3 : sptLookup r3 s.locals = some (.word (a <<< (shiftLength c - wordShiftAmount width)))) :
    ∃ ll, evaluate (storeAnyConsts r1 r2 r3 vs w) s =
      (none, {s with memory := m1, locals := ll, store := s.store.updateEq (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width vs.length))}) ∧
      sptLookup r1 ll = some (wordCondAdd c a w) ∧
      ∀ n, n ∉ [r1,r2,r3] → sptLookup n ll = sptLookup n s.locals := by
  cases vs with
  | nil =>
    have hm1 : m1 = s.memory := by
      simpa [storeList, hm] using run.symm
    subst m1
    simp only [List.length_nil]
    have good : goodLoc (sptDomain s.code) w.2 := good w (by simp)
    rcases w with ⟨b, v⟩
    cases v with
    | loc label offset =>
      simp only [goodLoc] at good
      rcases good with ⟨rfl, hlabel⟩
      have hmem : sptMem label s.code := hlabel
      refine ⟨sptInsert r1 (.loc label 0) s.locals, ?_, ?_, ?_⟩
      · simp [storeAnyConsts, evaluate, wordExp, getVar, hr2, setStore, WordSemStateFiniteExact.fixClock, setVar, hmem]
      · cases b <;> simp [wordCondAdd, sptLookup_sptInsert_same]
      · intro n hn
        apply sptLookup_sptInsert_ne
        intro eq
        apply hn
        simp [eq]
    | word value =>
      refine ⟨sptInsert r1 (wordCondAdd c a (b, .word value)) s.locals, ?_, ?_, ?_⟩
      all_goals cases b <;> simp_all [storeAnyConsts, evaluate, wordExp, getVar, setStore, WordSemStateFiniteExact.fixClock, setVar,
        wordCondAdd, theWords, wordOpHOL, wordOp, sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
  | cons x xs =>
    rcases x with ⟨b, v⟩
    cases v with
    | word word =>
      subst m
      subst dm
      have hdist : (r1 ≠ r2 ∧ r1 ≠ r3) ∧ r2 ≠ r3 := by simpa using distinct
      have h32 : r3 ≠ r2 := Ne.symm hdist.2
      cases hget : Build.getWords ((b, .word word) :: xs) [] with
      | mk words rest =>
        have hsplit := getWords_thm ((b, .word word) :: xs) words rest hget
        have hlen : rest.length < ((b, .word word) :: xs).length := by
          have h := Build.getWordsRestLength xs [(b, word)]
          have hgetTail : Build.getWords xs [(b, word)] = (words, rest) := hget
          rw [hgetTail] at h
          simp only at h
          simp only [List.length_cons]
          omega
        rw [hsplit, List.map_append, storeList_append] at run
        cases hprefix : storeList free ((words.map (fun (flag, word) => (flag, .word word))).map (wordCondAdd c a)) s.memory s.mdomain with
        | none => rw [hprefix] at run; contradiction
        | some middle =>
          rw [hprefix] at run
          have hprefixWords : storeList free (words.map (fun (flag, word) => wordCondAdd c a (flag, .word word))) s.memory s.mdomain = some middle := by
            simpa only [List.map_map, Function.comp_def] using hprefix
          have ⟨haddr, hwrite⟩ := storeList_wordCondAdd_imp c s.mdomain words s.memory a middle free hprefixWords
          have hgood : ∀ v ∈ w :: rest, goodLoc (sptDomain s.code) v.2 := by
            intro v hv
            apply good v
            rw [hsplit]
            simp only [List.mem_cons, List.mem_append] at hv ⊢
            exact hv.elim Or.inl (fun h => Or.inr (Or.inr h))
          let s1 := {s with memory := middle, locals := sptInsert r2 (.word (free + wordSemBytesInWord * BitVec.ofNat width words.length)) (sptInsert r3 (.word (a <<< (shiftLength c - wordShiftAmount width))) (sptDelete r2 (sptDelete r3 s.locals)))}
          have hr21 : sptLookup r2 s1.locals = some (.word (free + wordSemBytesInWord * BitVec.ofNat width words.length)) := by
            simp [s1, sptLookup_sptInsert_same]
          have hr31 : sptLookup r3 s1.locals = some (.word (a <<< (shiftLength c - wordShiftAmount width))) := by
            simp [s1, sptLookup_sptInsert_ne, sptLookup_sptInsert_same, h32]
          have run1 : storeList (free + wordSemBytesInWord * BitVec.ofNat width words.length) (rest.map (wordCondAdd c a)) s1.memory s1.mdomain = some m1 := by
            simpa [s1] using run
          have good1 : ∀ v ∈ w :: rest, goodLoc (sptDomain s1.code) v.2 := by simpa [s1] using hgood
          obtain ⟨ll, heval, hval, hother⟩ := evaluate_storeAnyConsts r1 r2 r3 rest w s1 _ a c s1.memory m1 s1.mdomain run1 rfl rfl distinct good1 hr21 hr31
          refine ⟨ll, ?_, hval, ?_⟩
          · rw [storeAnyConsts, hget]
            rw [words_step r2 r3 s free _ words _ middle hr2 hr3 haddr hwrite, heval]
            have hlength : ((b, WordLocW.word word) :: xs).length = words.length + rest.length := by
              simpa using congrArg List.length hsplit
            rw [hlength]
            simp only [s1, BitVec.ofNat_add, BitVec.mul_add]
            congr 1
            ac_rfl
          · intro n hn
            rw [hother n hn]
            simp only [s1]
            rw [sptLookup_sptInsert_ne, sptLookup_sptInsert_ne]
            simp only [sptLookup_sptDelete]
            have h2 : n ≠ r2 := by intro e; apply hn; simp [e]
            have h3 : n ≠ r3 := by intro e; apply hn; simp [e]
            simp [h2, h3]
            all_goals intro e; apply hn; simp [e]
    | loc label offset =>
      have hg := good (b, .loc label offset) (by simp)
      simp only [goodLoc] at hg
      obtain ⟨rfl, hcode⟩ := hg
      subst m
      subst dm
      have hdist : (r1 ≠ r2 ∧ r1 ≠ r3) ∧ r2 ≠ r3 := by simpa using distinct
      have h21 : r2 ≠ r1 := Ne.symm hdist.1.1
      have h31 : r3 ≠ r1 := Ne.symm hdist.1.2
      have h32 : r3 ≠ r2 := Ne.symm hdist.2
      have hdom : s.mdomain free = true := by
        by_contra h
        simp [storeList, wordCondAdd, h] at run
      let s1 := {s with locals := sptInsert r2 (.word (free + wordSemBytesInWord)) (sptInsert r1 (.loc label 0) s.locals), memory := fun x => if x = free then .loc label 0 else s.memory x}
      have run1 : storeList (free + wordSemBytesInWord) (xs.map (wordCondAdd c a)) s1.memory s1.mdomain = some m1 := by
        simpa [storeList, wordCondAdd, hdom, s1] using run
      have good1 : ∀ v ∈ w :: xs, goodLoc (sptDomain s1.code) v.2 := by
        intro v hv
        apply good v
        simp only [List.mem_cons] at hv ⊢
        exact hv.elim Or.inl (fun h => Or.inr (Or.inr h))
      have hr21 : sptLookup r2 s1.locals = some (.word (free + wordSemBytesInWord)) := by
        simp [s1, sptLookup_sptInsert_same]
      have hr31 : sptLookup r3 s1.locals = some (.word (a <<< (shiftLength c - wordShiftAmount width))) := by
        simpa [s1, sptLookup_sptInsert_ne, h31, h32] using hr3
      obtain ⟨ll, heval, hval, hother⟩ := evaluate_storeAnyConsts r1 r2 r3 xs w s1 (free + wordSemBytesInWord) a c s1.memory m1 s1.mdomain run1 rfl rfl distinct good1 hr21 hr31
      refine ⟨ll, ?_, hval, ?_⟩
      · rw [storeAnyConsts, loc_step r1 r2 label s free _ h21 hcode hr2 hdom, heval]
        simp only [s1, List.length_cons, BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one]
        congr 1
        ac_rfl
      · intro n hn
        rw [hother n hn]
        simp only [s1]
        rw [sptLookup_sptInsert_ne, sptLookup_sptInsert_ne]
        all_goals intro heq; apply hn; simp [heq]
termination_by vs.length

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
