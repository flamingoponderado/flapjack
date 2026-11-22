module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WriteWord64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumMemory
@[expose] public section

/-! Boxed bignum allocation evaluator cases used by `assign_WordToInt`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace WriteBignumWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WriteBignumWitness

/-- A nonzero machine word is its own single-digit multiword representation.
Flapjack arithmetic infrastructure for the bignum allocation cases. -/
theorem n2mw_word {width : Nat} [NeZero width] (w : BitVec width) (nz : w.toNat ≠ 0) :
    Misc.Multiword.n2mw (width := width) w.toNat = [w] := by
  rw [Misc.Multiword.n2mw]
  simp only [nz, if_false, Nat.mod_eq_of_lt w.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [Nat.div_eq_of_lt w.isLt, Misc.Multiword.n2mw]
  simp

/-- Allocate a one-digit nonnegative bignum. Proof infrastructure for
`evaluate_WriteWord64_bignum` and `evaluate_WriteWord32_bignum`. -/
private theorem bignumAlloc1 {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (ts space : Nat) (refs : Spt (BvlSem.Ref DataSem.Value))
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (mem : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (DataSem.Value × WordLocW width)) (w header : BitVec width)
    (rel : memoryRel conf be ts refs space store mem domain vars) (good : goodDimindex width)
    (large : ¬ smallInt width (w.toNat : Int))
    (enough : 1 < space) (encoded : encodeHeader conf 3 1 = some header) :
    ∃ ne curr mem1, store.lookup .nextFree = some (.word ne) ∧
      store.lookup .currHeap = some (.word curr) ∧
      storeList ne [.word header, .word w] mem domain = some mem1 ∧
      memoryRel conf be ts refs (space - 2)
        (store.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat width 2))) mem1 domain
        ((.number (w.toNat : Int), Build.makePtr conf (ne - curr) (0 : BitVec width) 1) :: vars) := by
  have nz : w.toNat ≠ 0 := by
    intro h
    apply large
    rw [h]
    rcases good with g | g <;> subst width <;> simp [smallInt]
  have rep : (bignumRep (w.toNat : Int) : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) =
      .dataElement [] [w].length (.numTag false, [w].map .word) := by
    simp [bignumRep, Misc.Multiword.i2mw, n2mw_word w nz]
  have header3 : (((if false then 1 else 0 : BitVec width) <<< 2) ||| 3).toNat = 3 := by
    rcases good with g | g <;> subst width <;> decide
  have h := memoryRel_bignumAlt conf be ts refs space store mem domain vars (w.toNat : Int) false [w]
    header rel good large rep (by simpa using enough) (by rw [header3]; simpa using encoded)
  simpa using h

/-- Writing a one-digit nonnegative bignum on a 64-bit target preserves the
full memory relation. HOL's final existential `v` is unused in its body and is
omitted here after source review; every other binder, premise and conclusion is
retained. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_WriteWord64_bignum"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateWriteWord64Bignum {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts space : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (target : WordSemStateFiniteExact width C F)
    (sl : Spt Flapjack.Compiler.Backend.DataSem.Value) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (src dest : Nat) (w header : BitVec width)
    (rel : memoryRel conf be ts refs space target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars))
    (readSrc : target.getVar src = some (.word w))
    (shiftBound : shiftLength conf < width) (srcNe : src ≠ 1) (enough : 1 < space)
    (widthIs : width = 64) (encoded : encodeHeader conf 3 1 = some header)
    (large : ¬ smallInt width (w.toNat : Int))
    (present : ∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) target.locals).isSome) :
    ∃ (nf : WordLocW width) (mem1 : BitVec width → WordLocW width)
      (locals1 : Spt (WordLocW width)),
      WordSemStateFiniteExact.evaluate (writeWord64 conf header dest src) target =
        (none, {target with store := target.store.update (.nextFree, nf), memory := mem1, locals := locals1}) ∧
      memoryRel conf be ts refs (space - 2) (target.store.update (.nextFree, nf)) mem1 target.mdomain
        (joinEnvLocals (sptInsert dest (.number (w.toNat : Int)) sl) locals1 ++ vars) ∧
      (∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) locals1).isSome) ∧
      (sptLookup (adjustVar dest) locals1).isSome ∧ sptLookup 0 locals1 = sptLookup 0 target.locals := by
  subst width
  obtain ⟨ne, curr, mem1, nextFree, currHeap, stored, resultRel⟩ :=
    bignumAlloc1 conf be ts space refs target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars) w header rel (Or.inr rfl) large enough encoded
  have dom0 : target.mdomain ne = true := by
    by_contra h
    simp [storeList, h] at stored
  have dom1 : target.mdomain (ne + wordSemBytesInWord) = true := by
    by_contra h
    simp [storeList, dom0, h] at stored
  have memEq : mem1 = fun x => if x = ne + wordSemBytesInWord then .word w else
      if x = ne then .word header else target.memory x := by
    simpa [storeList, dom0, dom1] using stored.symm
  let ptr := Build.makePtr conf (ne - curr) (0 : BitVec 64) 1
  let tmp := sptInsert 3 (.word header) (sptInsert 1 (.word ne) target.locals)
  let locals1 := sptInsert (adjustVar dest) ptr tmp
  have relTmp : memoryRel conf be ts refs (space - 2)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat 64 2))) mem1 target.mdomain
      ([(.number (w.toNat : Int), ptr)] ++ joinEnvLocals sl tmp ++ vars) := by
    simpa [ptr, tmp, joinEnvLocals_insertOdd, List.append_assoc] using resultRel
  have relFinal := memoryRel_insert conf be ts refs (space - 2)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat 64 2))) mem1 target.mdomain
      (.number (w.toNat : Int)) ptr sl tmp vars dest (by simpa [joinEnvLocals] using relTmp)
  refine ⟨.word (ne + wordSemBytesInWord * BitVec.ofNat 64 2), mem1, locals1, ?_, ?_, ?_, ?_, ?_⟩
  · have srcLookup : sptLookup src target.locals = some (.word w) := readSrc
    have diff : ne + (wordSemBytesInWord : BitVec 64) ≠ ne := by
      simp [wordSemBytesInWord]
    have memoryOrder : (fun x => if x = ne then .word header else
          if x = ne + wordSemBytesInWord then .word w else target.memory x) = mem1 := by
      rw [memEq]
      funext x
      by_cases h0 : x = ne <;> by_cases h1 : x = ne + wordSemBytesInWord <;> simp_all
    have shiftSmall : shiftLength conf - 3 < 64 := by omega
    have shiftMod : (shiftLength conf - 3) % (2 ^ 64) = shiftLength conf - 3 := by
      apply Nat.mod_eq_of_lt
      omega
    change (shiftLength conf - 3) % 18446744073709551616 = shiftLength conf - 3 at shiftMod
    have shiftNot : ¬ 64 ≤ shiftLength conf - 3 := Nat.not_le_of_gt shiftSmall
    simp [writeWord64, shiftN, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.memStore,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords,
      nextFree, currHeap, srcLookup, dom0, dom1, srcNe, locals1, tmp, ptr,
      Build.makePtr, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
      FUPDATE_HOL, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      wordShiftHOL, wordShiftAmount, BitVec.toNat_ofNat, shiftMod, shiftNot, memoryOrder, OrOp.or, BitVec.or_zero, BitVec.mul_comm]
    funext key
    by_cases h : key = .nextFree
    · simp [FUPDATE_HOL, FUPDATE, h]
    · simp [FUPDATE_HOL, FUPDATE, h, Ne.symm h]
  · simpa [locals1, joinEnvLocals] using relFinal
  · intro n hn
    by_cases hnd : n = dest
    · subst n
      simp [locals1, sptLookup_sptInsert_same]
    · have nadj : adjustVar n ≠ adjustVar dest := by simp [adjustVar] at *; omega
      have odd1 : adjustVar n ≠ 1 := by simp [adjustVar]
      have odd3 : adjustVar n ≠ 3 := by simp [adjustVar]
      simpa [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ nadj,
        sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd1] using present n hn
  · simp [locals1, sptLookup_sptInsert_same]
  · have destNe : (0 : Nat) ≠ adjustVar dest := by simp [adjustVar]
    simp [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ destNe, sptLookup_sptInsert_ne]

/-- Writing a one-digit nonnegative bignum on a 32-bit target preserves the
full memory relation. HOL's final existential `v` is unused in its body and is
omitted here after source review; every other binder, premise and conclusion is
retained. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_WriteWord32_bignum"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateWriteWord32Bignum {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts space : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (target : WordSemStateFiniteExact width C F)
    (sl : Spt Flapjack.Compiler.Backend.DataSem.Value) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (src dest : Nat) (w header : BitVec width)
    (rel : memoryRel conf be ts refs space target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars))
    (readSrc : target.getVar src = some (.word w))
    (shiftBound : shiftLength conf < width) (srcNe : src ≠ 1) (enough : 1 < space)
    (widthIs : width = 32) (encoded : encodeHeader conf 3 1 = some header)
    (large : ¬ smallInt width (w.toNat : Int))
    (present : ∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) target.locals).isSome) :
    ∃ (nf : WordLocW width) (mem1 : BitVec width → WordLocW width)
      (locals1 : Spt (WordLocW width)),
      WordSemStateFiniteExact.evaluate (writeWord32On32 conf header dest src) target =
        (none, {target with store := target.store.update (.nextFree, nf), memory := mem1, locals := locals1}) ∧
      memoryRel conf be ts refs (space - 2) (target.store.update (.nextFree, nf)) mem1 target.mdomain
        (joinEnvLocals (sptInsert dest (.number (w.toNat : Int)) sl) locals1 ++ vars) ∧
      (∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) locals1).isSome) ∧
      (sptLookup (adjustVar dest) locals1).isSome ∧ sptLookup 0 locals1 = sptLookup 0 target.locals := by
  subst width
  obtain ⟨ne, curr, mem1, nextFree, currHeap, stored, resultRel⟩ :=
    bignumAlloc1 conf be ts space refs target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars) w header rel (Or.inl rfl) large enough encoded
  have dom0 : target.mdomain ne = true := by
    by_contra h
    simp [storeList, h] at stored
  have dom1 : target.mdomain (ne + wordSemBytesInWord) = true := by
    by_contra h
    simp [storeList, dom0, h] at stored
  have memEq : mem1 = fun x => if x = ne + wordSemBytesInWord then .word w else
      if x = ne then .word header else target.memory x := by
    simpa [storeList, dom0, dom1] using stored.symm
  let ptr := Build.makePtr conf (ne - curr) (0 : BitVec 32) 1
  let tmp := sptInsert 3 (.word header) (sptInsert 1 (.word ne) target.locals)
  let locals1 := sptInsert (adjustVar dest) ptr tmp
  have relTmp : memoryRel conf be ts refs (space - 2)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat 32 2))) mem1 target.mdomain
      ([(.number (w.toNat : Int), ptr)] ++ joinEnvLocals sl tmp ++ vars) := by
    simpa [ptr, tmp, joinEnvLocals_insertOdd, List.append_assoc] using resultRel
  have relFinal := memoryRel_insert conf be ts refs (space - 2)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat 32 2))) mem1 target.mdomain
      (.number (w.toNat : Int)) ptr sl tmp vars dest (by simpa [joinEnvLocals] using relTmp)
  refine ⟨.word (ne + wordSemBytesInWord * BitVec.ofNat 32 2), mem1, locals1, ?_, ?_, ?_, ?_, ?_⟩
  · have srcLookup : sptLookup src target.locals = some (.word w) := readSrc
    have diff : ne + (wordSemBytesInWord : BitVec 32) ≠ ne := by
      simp [wordSemBytesInWord]
    have memoryOrder : (fun x => if x = ne then .word header else
          if x = ne + wordSemBytesInWord then .word w else target.memory x) = mem1 := by
      rw [memEq]
      funext x
      by_cases h0 : x = ne <;> by_cases h1 : x = ne + wordSemBytesInWord <;> simp_all
    have shiftSmall : shiftLength conf - 2 < 32 := by omega
    have shiftMod : (shiftLength conf - 2) % (2 ^ 32) = shiftLength conf - 2 := by
      apply Nat.mod_eq_of_lt
      omega
    change (shiftLength conf - 2) % 4294967296 = shiftLength conf - 2 at shiftMod
    have shiftNot : ¬ 32 ≤ shiftLength conf - 2 := Nat.not_le_of_gt shiftSmall
    simp [writeWord32On32, shiftN, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.memStore,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords,
      nextFree, currHeap, srcLookup, dom0, dom1, srcNe, locals1, tmp, ptr,
      Build.makePtr, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
      FUPDATE_HOL, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      wordShiftHOL, wordShiftAmount, BitVec.toNat_ofNat, shiftMod, shiftNot, memoryOrder, OrOp.or, BitVec.or_zero, BitVec.mul_comm]
    funext key
    by_cases h : key = .nextFree
    · simp [FUPDATE_HOL, FUPDATE, h]
    · simp [FUPDATE_HOL, FUPDATE, h, Ne.symm h]
  · simpa [locals1, joinEnvLocals] using relFinal
  · intro n hn
    by_cases hnd : n = dest
    · subst n
      simp [locals1, sptLookup_sptInsert_same]
    · have nadj : adjustVar n ≠ adjustVar dest := by simp [adjustVar] at *; omega
      have odd1 : adjustVar n ≠ 1 := by simp [adjustVar]
      have odd3 : adjustVar n ≠ 3 := by simp [adjustVar]
      simpa [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ nadj,
        sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd1] using present n hn
  · simp [locals1, sptLookup_sptInsert_same]
  · have destNe : (0 : Nat) ≠ adjustVar dest := by simp [adjustVar]
    simp [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ destNe, sptLookup_sptInsert_ne]

/-- Allocate a two-digit nonnegative bignum on a 32-bit target.
Proof infrastructure for `evaluate_WriteWord64_on_32_num`. -/
private theorem bignumAlloc2 (conf : DataToWord.Config) (be : Bool)
    (ts space : Nat) (refs : Spt (BvlSem.Ref DataSem.Value))
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 32))
    (mem : BitVec 32 → WordLocW 32) (domain : BitVec 32 → Bool)
    (vars : List (DataSem.Value × WordLocW 32)) (w1 w2 header : BitVec 32)
    (rel : memoryRel conf be ts refs space store mem domain vars) (nz : w2 ≠ 0)
    (enough : 2 < space) (encoded : encodeHeader conf 3 2 = some header) :
    ∃ ne curr mem1, store.lookup .nextFree = some (.word ne) ∧
      store.lookup .currHeap = some (.word curr) ∧
      storeList ne [.word header, .word w1, .word w2] mem domain = some mem1 ∧
      memoryRel conf be ts refs (space - 3)
        (store.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat 32 3))) mem1 domain
        ((.number ((w2.toNat * 2 ^ 32 + w1.toNat : Nat) : Int),
          Build.makePtr conf (ne - curr) (0 : BitVec 32) 2) :: vars) := by
  have nz' : w2.toNat ≠ 0 := by
    intro h; apply nz; exact BitVec.eq_of_toNat_eq (by simpa using h)
  have w1lt := w1.isLt
  have w2lt := w2.isLt
  have large : ¬ smallInt 32 ((w2.toNat * 2 ^ 32 + w1.toNat : Nat) : Int) := by
    rintro ⟨_, h⟩
    have : 1 ≤ w2.toNat := Nat.pos_of_ne_zero nz'
    simp only [Int.ofNat_eq_natCast, Nat.reducePow, Nat.reduceDiv] at h
    omega
  have digits : Misc.Multiword.n2mw (width := 32) (w2.toNat * 2 ^ 32 + w1.toNat) = [w1, w2] := by
    rw [Misc.Multiword.n2mw]
    have ne0 : w2.toNat * 2 ^ 32 + w1.toNat ≠ 0 := by
      have : 1 ≤ w2.toNat := Nat.pos_of_ne_zero nz'
      omega
    have hmod : (w2.toNat * 2 ^ 32 + w1.toNat) % 2 ^ 32 = w1.toNat := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt w1lt
    have hdiv : (w2.toNat * 2 ^ 32 + w1.toNat) / 2 ^ 32 = w2.toNat := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt w1lt, Nat.zero_add]
    simp only [ne0, if_false, hmod, hdiv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [n2mw_word w2 nz']
  have rep : (bignumRep ((w2.toNat * 2 ^ 32 + w1.toNat : Nat) : Int) :
      HeapElement (WordLocW 32) (HeapTag × List (WordLocW 32))) =
      .dataElement [] [w1, w2].length (.numTag false, [w1, w2].map .word) := by
    have absEq : ((w2.toNat * 2 ^ 32 + w1.toNat : Nat) : Int).natAbs = w2.toNat * 2 ^ 32 + w1.toNat :=
      Int.natAbs_natCast _
    simp only [bignumRep, Misc.Multiword.i2mw, absEq, digits]
    have nonneg : decide (((w2.toNat * 2 ^ 32 + w1.toNat : Nat) : Int) < 0) = false := by
      simp only [decide_eq_false_iff_not, not_lt]
      exact Int.natCast_nonneg _
    rw [nonneg]
  have header3 : (((if false then 1 else 0 : BitVec 32) <<< 2) ||| 3).toNat = 3 := by decide
  have h := memoryRel_bignumAlt conf be ts refs space store mem domain vars _ false [w1, w2]
    header rel (Or.inl rfl) large rep (by simpa using enough) (by rw [header3]; simpa using encoded)
  simpa using h

/-- Writing a two-digit nonnegative bignum on a 32-bit target preserves the
full memory relation. HOL's final existential `v` is unused in its body and is
omitted here after source review; every other binder, premise and conclusion is
retained. HOL's `dimword (:'a)` is `2 ^ 32` under the premise `width = 32`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_WriteWord64_on_32_num"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateWriteWord64On32Num {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts space : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (target : WordSemStateFiniteExact width C F)
    (sl : Spt Flapjack.Compiler.Backend.DataSem.Value) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (src1 src2 dest : Nat) (w1 w2 header : BitVec width)
    (rel : memoryRel conf be ts refs space target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars))
    (readLow : target.getVar src1 = some (.word w1))
    (readHigh : target.getVar src2 = some (.word w2))
    (shiftBound : shiftLength conf < width) (nz : w2 ≠ 0) (src1Ne : src1 ≠ 1) (src2Ne : src2 ≠ 1)
    (enough : 2 < space) (widthIs : width = 32) (encoded : encodeHeader conf 3 2 = some header)
    (present : ∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) target.locals).isSome) :
    ∃ (nf : WordLocW width) (mem1 : BitVec width → WordLocW width)
      (locals1 : Spt (WordLocW width)),
      WordSemStateFiniteExact.evaluate (writeWord64On32 conf header dest src2 src1) target =
        (none, {target with store := target.store.update (.nextFree, nf), memory := mem1, locals := locals1}) ∧
      memoryRel conf be ts refs (space - 3) (target.store.update (.nextFree, nf)) mem1 target.mdomain
        (joinEnvLocals (sptInsert dest (.number ((w2.toNat * 2 ^ width + w1.toNat : Nat) : Int)) sl)
          locals1 ++ vars) ∧
      (∀ n, (sptLookup n sl).isSome → (sptLookup (adjustVar n) locals1).isSome) ∧
      (sptLookup (adjustVar dest) locals1).isSome ∧ sptLookup 0 locals1 = sptLookup 0 target.locals := by
  subst width
  obtain ⟨ne, curr, mem1, nextFree, currHeap, stored, resultRel⟩ :=
    bignumAlloc2 conf be ts space refs target.store target.memory target.mdomain
      (joinEnvLocals sl target.locals ++ vars) w1 w2 header rel nz enough encoded
  have dom0 : target.mdomain ne = true := by
    by_contra h
    simp [storeList, h] at stored
  have dom1 : target.mdomain (ne + wordSemBytesInWord) = true := by
    by_contra h
    simp [storeList, dom0, h] at stored
  have dom2 : target.mdomain (ne + wordSemBytesInWord + wordSemBytesInWord) = true := by
    by_contra h
    simp [storeList, dom0, dom1, h] at stored
  have memEq : mem1 = fun x =>
      if x = ne + wordSemBytesInWord + wordSemBytesInWord then .word w2
      else if x = ne + wordSemBytesInWord then .word w1
      else if x = ne then .word header else target.memory x := by
    simpa [storeList, dom0, dom1, dom2] using stored.symm
  let ptr := Build.makePtr conf (ne - curr) (0 : BitVec 32) 2
  let tmp := sptInsert 3 (.word header) (sptInsert 1 (.word ne) target.locals)
  let locals1 := sptInsert (adjustVar dest) ptr tmp
  have relTmp : memoryRel conf be ts refs (space - 3)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat 32 3))) mem1 target.mdomain
      ([((.number ((w2.toNat * 2 ^ 32 + w1.toNat : Nat) : Int)), ptr)] ++ joinEnvLocals sl tmp ++ vars) := by
    simpa [ptr, tmp, joinEnvLocals_insertOdd, List.append_assoc] using resultRel
  have relFinal := memoryRel_insert conf be ts refs (space - 3)
      (target.store.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat 32 3))) mem1 target.mdomain
      (.number ((w2.toNat * 2 ^ 32 + w1.toNat : Nat) : Int)) ptr sl tmp vars dest (by simpa [joinEnvLocals] using relTmp)
  refine ⟨.word (ne + wordSemBytesInWord * BitVec.ofNat 32 3), mem1, locals1, ?_, ?_, ?_, ?_, ?_⟩
  · have lowLookup : sptLookup src1 target.locals = some (.word w1) := readLow
    have highLookup : sptLookup src2 target.locals = some (.word w2) := readHigh
    have d01 : ne + (wordSemBytesInWord : BitVec 32) ≠ ne := by simp [wordSemBytesInWord]
    have d02 : ne + (wordSemBytesInWord : BitVec 32) + wordSemBytesInWord ≠ ne := by
      simp [wordSemBytesInWord, BitVec.add_assoc]
    have memoryOrder : (fun x => if x = ne then .word header else
          if x = ne + wordSemBytesInWord + wordSemBytesInWord then .word w2 else
          if x = ne + wordSemBytesInWord then .word w1 else target.memory x) = mem1 := by
      rw [memEq]
      funext x
      by_cases h0 : x = ne <;> by_cases h1 : x = ne + wordSemBytesInWord <;>
        by_cases h2 : x = ne + wordSemBytesInWord + wordSemBytesInWord <;> simp_all
    have shiftSmall : shiftLength conf - 2 < 32 := by omega
    have shiftMod : (shiftLength conf - 2) % (2 ^ 32) = shiftLength conf - 2 := by
      apply Nat.mod_eq_of_lt
      omega
    change (shiftLength conf - 2) % 4294967296 = shiftLength conf - 2 at shiftMod
    have shiftNot : ¬ 32 ≤ shiftLength conf - 2 := Nat.not_le_of_gt shiftSmall
    simp [wordSemBytesInWord, BitVec.add_assoc] at dom1 dom2 memoryOrder
    simp [writeWord64On32, shiftN, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.memStore,
      WordSemStateFiniteExact.fixClock, wordOpHOL, wordOp, theWords,
      nextFree, currHeap, lowLookup, highLookup, dom0, dom1, dom2, src1Ne, src2Ne, locals1, tmp, ptr,
      Build.makePtr, HolFiniteMapExact.update, HolFiniteMapExact.updateEq,
      FUPDATE_HOL, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      wordShiftHOL, wordShiftAmount, BitVec.toNat_ofNat, shiftMod, shiftNot,
      OrOp.or, BitVec.or_zero, BitVec.mul_comm, wordSemBytesInWord]
    constructor
    · funext key
      by_cases h : key = .nextFree
      · simp [FUPDATE_HOL, FUPDATE, h]
      · simp [FUPDATE_HOL, FUPDATE, h, Ne.symm h]
    · rw [← memoryOrder]
      funext x
      by_cases h0 : x = ne <;> by_cases h1 : x = ne + 8#32 <;> (simp only [h0, h1, if_false, if_true]; try rfl)
  · simpa [locals1, joinEnvLocals] using relFinal
  · intro n hn
    by_cases hnd : n = dest
    · subst n
      simp [locals1, sptLookup_sptInsert_same]
    · have nadj : adjustVar n ≠ adjustVar dest := by simp [adjustVar] at *; omega
      have odd1 : adjustVar n ≠ 1 := by simp [adjustVar]
      have odd3 : adjustVar n ≠ 3 := by simp [adjustVar]
      simpa [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ nadj,
        sptLookup_sptInsert_ne _ _ _ _ odd3, sptLookup_sptInsert_ne _ _ _ _ odd1] using present n hn
  · simp [locals1, sptLookup_sptInsert_same]
  · have destNe : (0 : Nat) ≠ adjustVar dest := by simp [adjustVar]
    simp [locals1, tmp, sptLookup_sptInsert_ne _ _ _ _ destNe, sptLookup_sptInsert_ne]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
