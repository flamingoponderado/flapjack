module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Compare1
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
public import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock
@[expose] public section

/-! Mutual correctness of the word equality runtime stubs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.BackendProps
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem seqAfter {width : Nat} [NeZero width] {C F : Type}
    (a b : WordLangProgHOL (BitVec width)) (s next : WordSemStateFiniteExact width C F)
    (run : WordSemStateFiniteExact.evaluate a s = (none, next))
    (sameClock : next.clock ≤ s.clock) (sameDepth : next.termdep = s.termdep) :
    WordSemStateFiniteExact.evaluate (.seq a b) s = WordSemStateFiniteExact.evaluate b next := by
  rw [WordSemStateFiniteExact.evaluate, run]
  cases next
  simp only at sameClock sameDepth
  simp [WordSemStateFiniteExact.fixClock, Nat.not_lt_of_ge sameClock, ← sameDepth]

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem seqResult {width : Nat} [NeZero width] {C F : Type}
    (a b : WordLangProgHOL (BitVec width)) (s next : WordSemStateFiniteExact width C F)
    (result : WordSemResult width) (run : WordSemStateFiniteExact.evaluate a s = (some result, next))
    (sameClock : next.clock ≤ s.clock) (sameDepth : next.termdep = s.termdep) :
    WordSemStateFiniteExact.evaluate (.seq a b) s = (some result, next) := by
  rw [WordSemStateFiniteExact.evaluate, run]
  cases next
  simp only at sameClock sameDepth
  simp [WordSemStateFiniteExact.fixClock, Nat.not_lt_of_ge sameClock, ← sameDepth]

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem equalHeadStackBound (a b localSize eqSize eq1Size cmpSize k : Option Nat)
    (localEq : localSize = eqSize ∨ localSize = eq1Size)
    (bound : optionLe (Option.map₂ max eqSize (Option.map₂ max eq1Size cmpSize)) k) :
    optionLe
      (Option.map₂ max
        (wordSemOptionMax (wordSemOptionMax a (wordSemOptionAdd localSize b))
          (wordSemOptionAdd (wordSemOptionAdd localSize b) eqSize))
        (Option.map₂ (· + ·) (wordSemOptionAdd localSize b) k))
      (Option.map₂ max a
        (Option.map₂ (· + ·) b
          (Option.map₂ (· + ·) (Option.map₂ max eqSize (Option.map₂ max eq1Size cmpSize)) k))) := by
  cases a <;> cases b <;> cases localSize <;> cases eqSize <;> cases eq1Size <;> cases cmpSize <;> cases k <;>
    (simp_all [optionLe, wordSemOptionMax, wordSemOptionAdd]; all_goals omega)

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem equalTailStackBound (a b head e total : Option Nat)
    (headBound : optionLe head (Option.map₂ max a (Option.map₂ (· + ·) b total)))
    (eBound : optionLe e total) :
    optionLe (Option.map₂ max (Option.map₂ max head (Option.map₂ (· + ·) b e))
      (Option.map₂ (· + ·) b total))
      (Option.map₂ max a (Option.map₂ (· + ·) b total)) := by
  cases a <;> cases b <;> cases head <;> cases e <;> cases total <;>
    (simp_all [optionLe]; all_goals omega)

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem tagMask_eq_slice {width : Nat} [NeZero width] (conf : Config)
    (good : goodDimindex width) (lt : conf.lenSize < width) :
    tagMask (width := width) conf = holWordSlice (width - conf.lenSize - 1) 2 (~~~(0 : BitVec width)) := by
  rcases good with h | h <;> subst width <;> interval_cases hlen : conf.lenSize <;>
    simp_all only [tagMask, holWordSlice] <;> decide +kernel

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem headerBits {width : Nat} [NeZero width] (w : BitVec width) (good : goodDimindex width) :
    ((w &&& (4 : BitVec width)) = 0 ↔ w.getLsbD 2 = false) ∧
    ((w &&& (24 : BitVec width)) = 16 ↔ (w.getLsbD 3 = false ∧ w.getLsbD 4 = true)) := by
  rcases good with h | h <;> subst width <;> constructor <;> bv_decide

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem shiftBytes {width : Nat} [NeZero width] (w : BitVec width) (good : goodDimindex width) :
    (w <<< wordShiftAmount width) = StackRemove.bytesInWord width * w := by
  rcases good with h | h <;> subst width <;> simp [wordShiftAmount, StackRemove.bytesInWord] <;> bv_decide

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem compareStackBound (a b e total : Option Nat) (h : optionLe e total) :
    optionLe (Option.map₂ max (Option.map₂ max a (Option.map₂ (· + ·) b e)) (Option.map₂ (· + ·) b e))
      (Option.map₂ max a (Option.map₂ (· + ·) b total)) := by
  cases a <;> cases b <;> cases e <;> cases total <;> (simp_all [optionLe]; all_goals omega)

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem equalCode_same {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (t : WordSemStateFiniteExact width C F) (loc1 loc2 : Nat) (w : BitVec width)
    (h0 : t.getVar 0 = some (.loc loc1 loc2)) (h2 : t.getVar 2 = some (.word w))
    (h4 : t.getVar 4 = some (.word w)) :
    WordSemStateFiniteExact.evaluate (equalCode conf) t =
      (some (.result (.loc loc1 loc2) [.word 1]), {t with locals := .ln, localsSize := some 0}) := by
  simp only [WordSemStateFiniteExact.getVar] at h0 h2 h4
  simp [equalCode, wordListSeq, WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.wordExp,
    WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
    WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.getVars, wordSemWordCmp, Encoders.Asm.wordCmpHOL,
    sptLookup_sptInsert_same, sptLookup_sptInsert_ne, h0, h2, h4]

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem lowBit_zero {width : Nat} [NeZero width] (w1 w2 : BitVec width)
    (low : (w1.getLsbD 0 && w2.getLsbD 0) = false) :
    (w1 &&& (w2 &&& BitVec.allOnes width) &&& BitVec.ofNat width 1) = BitVec.ofNat width 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases iz : i = 0
  · subst i
    simp [BitVec.getLsbD_and, low]
  · have hp : 1 < 2 ^ i := Nat.one_lt_two_pow (by omega)
    have hz : 1 >>> i = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt hp
    simp [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit, hz]

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem lowBit_nonzero {width : Nat} [NeZero width] (w1 w2 : BitVec width)
    (low : (w1.getLsbD 0 && w2.getLsbD 0) = true) :
    (w1 &&& (w2 &&& BitVec.allOnes width) &&& BitVec.ofNat width 1) ≠ BitVec.ofNat width 0 := by
  intro eq
  have h := congrArg (fun w : BitVec width => w.getLsbD 0) eq
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have both : w1.getLsbD 0 = true ∧ w2.getLsbD 0 = true := by simpa using low
  simp [   pos, both.1] at h
  simp only [BitVec.getLsbD_eq_getElem pos] at both
  simp [both.2] at h

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem equalCode_lowBit {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (t : WordSemStateFiniteExact width C F) (loc1 loc2 : Nat) (w1 w2 : BitVec width)
    (different : w1 ≠ w2) (low : (w1.getLsbD 0 && w2.getLsbD 0) = false)
    (h0 : t.getVar 0 = some (.loc loc1 loc2)) (h2 : t.getVar 2 = some (.word w1))
    (h4 : t.getVar 4 = some (.word w2)) :
    WordSemStateFiniteExact.evaluate (equalCode conf) t =
      (some (.result (.loc loc1 loc2) [.word 0]), {t with locals := .ln, localsSize := some 0}) := by
  have test := lowBit_zero w1 w2 low
  have test2 : (w1 &&& w2 &&& BitVec.ofNat width 1) = BitVec.ofNat width 0 := by simpa using test
  have ne : (w1 == w2) = false := beq_eq_false_iff_ne.mpr different
  simp only [WordSemStateFiniteExact.getVar] at h0 h2 h4
  have first : WordSemStateFiniteExact.evaluate
      (.ite .equal 2 (.reg 4) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) t = (none, t) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
      WordSemStateFiniteExact.getVar, wordSemWordCmp, Encoders.Asm.wordCmpHOL, h2, h4, ne]
  rw [equalCode, wordListSeq, WordSemStateFiniteExact.evaluate, first]
  simp only [WordSemStateFiniteExact.fixClock, lt_self_iff_false, ↓reduceIte]
  have second : WordSemStateFiniteExact.evaluate
      (.assign 1 (.op .and [.var 2, .var 4])) t =
      (none, t.setVar 1 (.word (w1 &&& (w2 &&& BitVec.allOnes width)))) := by
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.getVar, wordOpHOL, wordOp, theWords, AndOp.and, h2, h4]
  rw [wordListSeq, WordSemStateFiniteExact.evaluate, second]
  simp only [WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.setVar,
    lt_self_iff_false, ↓reduceIte]
  let next := t.setVar 1 (.word (w1 &&& (w2 &&& BitVec.allOnes width)))
  have third : WordSemStateFiniteExact.evaluate
      (.ite .test 1 (.imm 1) (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])) .skip) next =
      (some (.result (.loc loc1 loc2) [.word 0]), {t with locals := .ln, localsSize := some 0}) := by
    simp [next, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVars,
      wordSemWordCmp, Encoders.Asm.wordCmpHOL, AndOp.and, sptLookup_sptInsert_same, sptLookup_sptInsert_ne, h0, test2]
  dsimp [next, WordSemStateFiniteExact.setVar] at third
  rw [show BitVec.ofNat width 1 = (1 : BitVec width) by rfl] at third
  rw [wordListSeq, WordSemStateFiniteExact.evaluate, third]
  simp [WordSemStateFiniteExact.fixClock]


/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem equal1_cut {width : Nat} [NeZero width] (env : Spt (WordLocW width))
    (v0 v2 v4 v6 : WordLocW width)
    (h0 : sptLookup 0 env = some v0) (h2 : sptLookup 2 env = some v2)
    (h4 : sptLookup 4 env = some v4) (h6 : sptLookup 6 env = some v6) :
    wordSemCutEnvs (sptListInsert [0, 2, 4, 6] .ln, .ln) env =
      some (sptInter env (sptListInsert [0, 2, 4, 6] .ln), .ln) := by
  have subset : LoopSemStateFiniteExact.sptSubsetLive (sptListInsert [0, 2, 4, 6] .ln) env := by
    intro k present
    simp only [sptListInsert, sptMem_sptInsert] at present
    have choices : k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 := by
      simpa [or_assoc, or_comm, or_left_comm] using present
    rcases choices with rfl | rfl | rfl | rfl
    · exact (sptMem_iff_lookup 0 env).2 ⟨v0, h0⟩
    · exact (sptMem_iff_lookup 2 env).2 ⟨v2, h2⟩
    · exact (sptMem_iff_lookup 4 env).2 ⟨v4, h4⟩
    · exact (sptMem_iff_lookup 6 env).2 ⟨v6, h6⟩
  have empty : LoopSemStateFiniteExact.sptSubsetLive (.ln : NumSet) env := by
    intro k present
    exact (sptMem_ln k present).elim
  have interEmpty : sptInter env (.ln : NumSet) = .ln := by cases env <;> simp [sptInter]
  simp [wordSemCutEnvs, wordSemCutNames, subset, empty, interEmpty]

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem emptyEnvToList {width : Nat} [NeZero width] (p : Nat → Nat → Nat) :
    (wordSemEnvToList (.ln : Spt (WordLocW width)) p).1 = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e h
  have hm := (wordSemEnvToList_mem_iff (.ln : Spt (WordLocW width)) p e).mp h
  simp at hm

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem equal1_saved_roundtrip {width : Nat} [NeZero width]
    (env : Spt (WordLocW width)) :
    sptFromAList (sptToAList (sptInter env (sptListInsert [0, 2, 4, 6] .ln))) =
      sptInter env (sptListInsert [0, 2, 4, 6] .ln) := by
  apply (sptEqThm _ _ ⟨sptWfFromAList _, sptWfInter _ _⟩).2
  intro key
  exact sptLookup_sptFromAList_sptToAList key _

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem wordHeader_cases {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (domain : BitVec width → Bool)
    (memory : BitVec width → WordLocW width) (pointer address header : BitVec width)
    (h : wordHeader conf store pointer domain memory = some (address, header)) :
    getRealAddr conf store pointer = some address ∧ domain address = true ∧ memory address = .word header := by
  cases haddr : getRealAddr conf store pointer with
  | none => simp [wordHeader, haddr] at h
  | some addr =>
    by_cases hd : domain addr = true
    · cases hm : memory addr with
      | loc x y => simp [wordHeader, haddr, hd, hm] at h
      | word head =>
        simp [wordHeader, haddr, hd, hm] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hd, hm⟩
    · simp [wordHeader, haddr, hd] at h

/-- Flapjack proof infrastructure for the equality-code simulation; no separate HOL declaration. -/
private theorem equal1Code_zero {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (loc1 loc2 : Nat)
    (h0 : t.getVar 0 = some (.loc loc1 loc2)) (h2 : t.getVar 2 = some (.word 0)) :
    WordSemStateFiniteExact.evaluate equal1Code t =
      (some (.result (.loc loc1 loc2) [.word 1]), {t with locals := .ln, localsSize := some 0}) := by
  simp only [WordSemStateFiniteExact.getVar] at h0 h2
  simp [equal1Code, wordListSeq, WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.wordExp,
    WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
    WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.getVars, wordSemWordCmp, Encoders.Asm.wordCmpHOL,
    sptLookup_sptInsert_same, sptLookup_sptInsert_ne, h0, h2]
namespace EqualCodeWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EqualCodeWitness

/-- Both equality runtime stubs implement the complete mutually recursive word equality semantics. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "Equal_code_lemma"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store, store1, store2])
  (words_as_type_indexed_bitvec)]
theorem equalCodeLemma {width : Nat} [NeZero width] {C F : Type} :
    (∀ (conf : Config) (store1 : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (limit clock : Nat) (v1 v2 : BitVec width) (t : WordSemStateFiniteExact width C F)
      (loc1 loc2 : Nat) (res : BitVec width) (remaining remainingClock : Nat),
      wordEq conf store1 domain memory limit clock v1 v2 = some (res, remaining, remainingClock) ∧
      domain = t.mdomain ∧ memory = t.memory ∧ store1 = t.store ∧ limit ≤ t.clock ∧ shiftLength conf < width ∧
      sptLookup equalLocation t.code = some (3, equalCode conf) ∧
      sptLookup equal1Location t.code = some (4, equal1Code) ∧
      sptLookup compare1Location t.code = some (4, compare1Code) ∧
      t.getVar 0 = some (.loc loc1 loc2) ∧ t.getVar 2 = some (.word v1) ∧ t.getVar 4 = some (.word v2) ∧
      conf.lenSize ≠ 0 ∧ conf.lenSize < width ∧ saneLocalsSize t ∧ goodDimindex width →
      ∃ ck newP smx, WordSemStateFiniteExact.evaluate (equalCode conf) t =
        (some (.result (.loc loc1 loc2) [.word res]), {t with clock := ck, locals := .ln, localsSize := some 0, permute := newP, stackMax := smx}) ∧
      optionLe smx (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack) (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) ∧
      remaining ≤ ck) ∧
    (∀ (conf : Config) (store2 : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (limit clock : Nat) (count a1 a2 : BitVec width) (t : WordSemStateFiniteExact width C F)
      (loc1 loc2 : Nat) (res : BitVec width) (remaining remainingClock : Nat),
      wordEqList conf store2 domain memory limit clock count a1 a2 = some (res, remaining, remainingClock) ∧
      domain = t.mdomain ∧ memory = t.memory ∧ store2 = t.store ∧ limit ≤ t.clock ∧ shiftLength conf < width ∧
      sptLookup equalLocation t.code = some (3, equalCode conf) ∧
      sptLookup equal1Location t.code = some (4, equal1Code) ∧
      sptLookup compare1Location t.code = some (4, compare1Code) ∧
      t.getVar 0 = some (.loc loc1 loc2) ∧ t.getVar 2 = some (.word count) ∧
      t.getVar 4 = some (.word a1) ∧ t.getVar 6 = some (.word a2) ∧
      saneLocalsSize t ∧ conf.lenSize ≠ 0 ∧ conf.lenSize < width ∧ goodDimindex width →
      ∃ ck newP smx, WordSemStateFiniteExact.evaluate equal1Code t =
        (some (.result (.loc loc1 loc2) [.word res]), {t with clock := ck, locals := .ln, localsSize := some 0, permute := newP, stackMax := smx}) ∧
      optionLe smx (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack) (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) ∧
      remaining ≤ ck) := by
  have aux : ∀ limit : Nat,
    (∀ (conf : Config) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (clock : Nat) (v1 v2 : BitVec width) (t : WordSemStateFiniteExact width C F)
      (loc1 loc2 : Nat) (res : BitVec width) (remaining remainingClock : Nat),
      wordEq conf store domain memory limit clock v1 v2 = some (res, remaining, remainingClock) ∧
      domain = t.mdomain ∧ memory = t.memory ∧ store = t.store ∧ limit ≤ t.clock ∧ shiftLength conf < width ∧
      sptLookup equalLocation t.code = some (3, equalCode conf) ∧
      sptLookup equal1Location t.code = some (4, equal1Code) ∧
      sptLookup compare1Location t.code = some (4, compare1Code) ∧
      t.getVar 0 = some (.loc loc1 loc2) ∧ t.getVar 2 = some (.word v1) ∧ t.getVar 4 = some (.word v2) ∧
      conf.lenSize ≠ 0 ∧ conf.lenSize < width ∧ saneLocalsSize t ∧ goodDimindex width →
      ∃ ck newP smx, WordSemStateFiniteExact.evaluate (equalCode conf) t =
        (some (.result (.loc loc1 loc2) [.word res]), {t with clock := ck, locals := .ln, localsSize := some 0, permute := newP, stackMax := smx}) ∧
      optionLe smx (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack) (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) ∧
      remaining ≤ ck) ∧
    (∀ (conf : Config) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (clock : Nat) (count a1 a2 : BitVec width) (t : WordSemStateFiniteExact width C F)
      (loc1 loc2 : Nat) (res : BitVec width) (remaining remainingClock : Nat),
      wordEqList conf store domain memory limit clock count a1 a2 = some (res, remaining, remainingClock) ∧
      domain = t.mdomain ∧ memory = t.memory ∧ store = t.store ∧ limit ≤ t.clock ∧ shiftLength conf < width ∧
      sptLookup equalLocation t.code = some (3, equalCode conf) ∧
      sptLookup equal1Location t.code = some (4, equal1Code) ∧
      sptLookup compare1Location t.code = some (4, compare1Code) ∧
      t.getVar 0 = some (.loc loc1 loc2) ∧ t.getVar 2 = some (.word count) ∧
      t.getVar 4 = some (.word a1) ∧ t.getVar 6 = some (.word a2) ∧
      saneLocalsSize t ∧ conf.lenSize ≠ 0 ∧ conf.lenSize < width ∧ goodDimindex width →
      ∃ ck newP smx, WordSemStateFiniteExact.evaluate equal1Code t =
        (some (.result (.loc loc1 loc2) [.word res]), {t with clock := ck, locals := .ln, localsSize := some 0, permute := newP, stackMax := smx}) ∧
      optionLe smx (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack) (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) ∧
      remaining ≤ ck) := by
    intro limit
    induction limit using Nat.strong_induction_on with
    | h limit ih =>
      constructor
      · intro conf store domain memory clock v1 v2 t loc1 loc2 res remaining remainingClock h
        obtain ⟨run, dom, mem, storeEq, time, shift, code, code1, codeCmp, r0, r2, r4,
          lenNe, lenLt, localSize, good⟩ := h
        by_cases equal : v1 = v2
        · subst v2
          simp [wordEq] at run
          obtain ⟨rfl, rfl, _⟩ := run
          refine ⟨t.clock, t.permute, t.stackMax, ?_, ?_, time⟩
          · exact equalCode_same conf t loc1 loc2 v1 r0 r2 r4
          · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
        · by_cases low : (v1.getLsbD 0 && v2.getLsbD 0) = false
          · simp [wordEq, equal, low] at run
            obtain ⟨rfl, rfl, _⟩ := run
            refine ⟨t.clock, t.permute, t.stackMax, ?_, ?_, time⟩
            · exact equalCode_lowBit conf t loc1 loc2 v1 v2 equal low r0 r2 r4
            · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
          · have lowTrue : (v1.getLsbD 0 && v2.getLsbD 0) = true := by
              cases h : (v1.getLsbD 0 && v2.getLsbD 0) with
              | false => exact (low h).elim
              | true => rfl
            rw [wordEq] at run
            simp only [equal, ↓reduceIte, lowTrue, Bool.not_true] at run
            cases h1 : wordHeader conf store v1 domain memory with
            | none => simp [h1] at run
            | some p1 =>
              cases h2 : wordHeader conf store v2 domain memory with
              | none => simp [h1, h2] at run
              | some p2 =>
                obtain ⟨addr1, head1⟩ := p1
                obtain ⟨addr2, head2⟩ := p2
                simp only [h1, h2] at run
                obtain ⟨addrRead1, domain1, contents1⟩ := wordHeader_cases conf store domain memory v1 addr1 head1 h1
                obtain ⟨addrRead2, domain2, contents2⟩ := wordHeader_cases conf store domain memory v2 addr2 head2 h2
                rw [storeEq] at addrRead1 addrRead2
                have real1 := Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.getRealAddr_lemma
                  conf 2 t v1 addr1 ⟨shift, good, r2, addrRead1⟩
                have real2 := Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.getRealAddr_lemma
                  conf 4 t v2 addr2 ⟨shift, good, r4, addrRead2⟩
                rw [dom] at domain1 domain2
                rw [mem] at contents1 contents2
                have differentBeq : (v1 == v2) = false := beq_eq_false_iff_ne.mpr equal
                have testNonzero := lowBit_nonzero v1 v2 lowTrue
                have testSimple : (v1 &&& v2 &&& BitVec.ofNat width 1) ≠ BitVec.ofNat width 0 := by
                  simpa using testNonzero
                let temp := v1 &&& (v2 &&& BitVec.allOnes width)
                let state1 := t.setVar 1 (.word temp)
                have firstStep : WordSemStateFiniteExact.evaluate
                    (.ite .equal 2 (.reg 4) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) t = (none, t) := by
                  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                    wordSemWordCmp, Encoders.Asm.wordCmpHOL, r2, r4, differentBeq]
                have andStep : WordSemStateFiniteExact.evaluate
                    (.assign 1 (.op .and [.var 2, .var 4])) t = (none, state1) := by
                  simp [state1, temp, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                    wordOpHOL, wordOp, theWords, AndOp.and, r2, r4]
                have testStep : WordSemStateFiniteExact.evaluate
                    (.ite .test 1 (.imm 1) (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])) .skip) state1 =
                    (none, state1) := by
                  have cmp : ((v1 &&& v2 &&& BitVec.ofNat width 1) == BitVec.ofNat width 0) = false :=
                    beq_eq_false_iff_ne.mpr testSimple
                  simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, state1, temp,
                    wordSemWordCmp, Encoders.Asm.wordCmpHOL, AndOp.and, sptLookup_sptInsert_same, cmp]
                let state20 := state1.setVar 20 (.word addr1)
                have real1State : state1.wordExp (realAddr conf 2) = some (.word addr1) := by
                  have preserve := (wordExp_realAddr_insert conf t 2 1 1 (.word temp) (.word temp)).1 (by decide)
                  simpa [state1, WordSemStateFiniteExact.setVar] using preserve.trans real1
                have addr1Step : WordSemStateFiniteExact.evaluate (.assign 20 (realAddr conf 2)) state1 =
                    (none, state20) := by
                  simp [WordSemStateFiniteExact.evaluate, real1State, state20]
                have real2State : state20.wordExp (realAddr conf 4) = some (.word addr2) := by
                  have preserve := (wordExp_realAddr_insert conf t 4 20 1 (.word addr1) (.word temp)).2 (by simp)
                  simpa [state20, state1, WordSemStateFiniteExact.setVar] using preserve.trans real2
                let state40 := state20.setVar 40 (.word addr2)
                have addr2Step : WordSemStateFiniteExact.evaluate (.assign 40 (realAddr conf 4)) state20 =
                    (none, state40) := by
                  simp [WordSemStateFiniteExact.evaluate, real2State, state40]
                let state21 := state40.setVar 21 (.word head1)
                have read20 : state40.getVar 20 = some (.word addr1) := by
                  simp [state40, state20, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                have loadHead1 : WordSemStateFiniteExact.evaluate (.assign 21 (.load (.var 20))) state40 =
                    (none, state21) := by
                  simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, read20,
                    WordSemStateFiniteExact.memLoad]
                  simp [state40, state20, state1, WordSemStateFiniteExact.setVar, domain1, contents1, state21]
                let heapState := state21.setVar 41 (.word head2)
                have read40 : state21.getVar 40 = some (.word addr2) := by
                  simp [state21, state40, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                have loadHead2 : WordSemStateFiniteExact.evaluate (.assign 41 (.load (.var 40))) state21 =
                    (none, heapState) := by
                  simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, read40,
                    WordSemStateFiniteExact.memLoad]
                  simp [state21, state40, state20, state1, WordSemStateFiniteExact.setVar, domain2, contents2, heapState]
                let bytes : BitVec width := wordSemBytesInWord
                let mask := tagMask conf ||| (2 : BitVec width)
                let block := wordListSeq [
                    .assign 1 (.op .and [.var 21, .const mask]),
                    .ite .equal 1 (.imm 482) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip,
                    .ite .equal 1 (.imm 498) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip,
                    .ite .equal 21 (.reg 41) .skip (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])),
                    .assign 6 (shiftVar .lsr 21 (width - conf.lenSize)),
                    .assign 20 (.op .add [.var 20, .const bytes]), .assign 40 (.op .add [.var 40, .const bytes]),
                    .call none (some equal1Location) [0, 6, 20, 40] none]
                let rest := wordListSeq [
                  .ite .test 21 (.imm 12) block .skip,
                  .ite .equal 21 (.reg 41) .skip (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])),
                  .ite .test 21 (.imm 4) (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])) .skip,
                  .assign 1 (.op .and [.var 21, .const 24]),
                  .ite .equal 1 (.imm 16) (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])) .skip,
                  .assign 6 (shiftVar .lsr 21 (width - conf.lenSize)),
                  .assign 2 (.op .add [.var 20, shiftVar .lsl 6 (wordShiftAmount width)]),
                  .assign 4 (.op .add [.var 40, shiftVar .lsl 6 (wordShiftAmount width)]),
                  .call none (some compare1Location) [0, 6, 2, 4] none]
                have heapPrefix : WordSemStateFiniteExact.evaluate (equalCode conf) t =
                    WordSemStateFiniteExact.evaluate rest heapState := by
                  rw [equalCode, wordListSeq]
                  rw [seqAfter _ _ _ _ firstStep (Nat.le_refl _) rfl]
                  rw [wordListSeq]
                  rw [seqAfter _ _ _ _ andStep (by simp [state1, WordSemStateFiniteExact.setVar])
                    (by simp [state1, WordSemStateFiniteExact.setVar])]
                  rw [wordListSeq]
                  rw [seqAfter _ _ _ _ testStep (Nat.le_refl _) rfl]
                  rw [wordListSeq]
                  rw [seqAfter _ _ _ _ addr1Step (by simp [state20, WordSemStateFiniteExact.setVar])
                    (by simp [state20, WordSemStateFiniteExact.setVar])]
                  rw [wordListSeq]
                  rw [seqAfter _ _ _ _ addr2Step (by simp [state40, WordSemStateFiniteExact.setVar])
                    (by simp [state40, WordSemStateFiniteExact.setVar])]
                  rw [wordListSeq]
                  rw [seqAfter _ _ _ _ loadHead1 (by simp [state21, WordSemStateFiniteExact.setVar])
                    (by simp [state21, WordSemStateFiniteExact.setVar])]
                  rw [wordListSeq]
                  rw [seqAfter _ _ _ _ loadHead2 (by simp [heapState, WordSemStateFiniteExact.setVar])
                    (by simp [heapState, WordSemStateFiniteExact.setVar])]
                have heapRead21 : heapState.getVar 21 = some (.word head1) := by
                  simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.getVar,
                    WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                have heapRead41 : heapState.getVar 41 = some (.word head2) := by
                  simp [heapState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_same]
                have heapRead0 : heapState.getVar 0 = some (.loc loc1 loc2) := by
                  simpa [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.getVar,
                    WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using r0
                have heapRead20 : heapState.getVar 20 = some (.word addr1) := by
                  simp [heapState, state21, state40, state20, WordSemStateFiniteExact.getVar,
                    WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                have heapRead40 : heapState.getVar 40 = some (.word addr2) := by
                  simp [heapState, state21, state40, WordSemStateFiniteExact.getVar,
                    WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                have closureEq : wordIsClos conf head1 ↔
                    (head1 &&& mask = BitVec.ofNat width 482 ∨ head1 &&& mask = BitVec.ofNat width 498) := by
                  simp [wordIsClos, mask, tagMask_eq_slice conf good lenLt]
                by_cases blockZero : head1 &&& (12 : BitVec width) = 0
                · have blockRaw : head1 &&& BitVec.ofNat width 12 = BitVec.ofNat width 0 := by simpa using blockZero
                  have dispatch : WordSemStateFiniteExact.evaluate
                      (.ite .test 21 (.imm 12) block .skip) heapState =
                      WordSemStateFiniteExact.evaluate block heapState := by
                    have cmp : (head1 &&& BitVec.ofNat width 12 == BitVec.ofNat width 0) = true :=
                      beq_iff_eq.mpr blockRaw
                    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                      wordSemWordCmp, Encoders.Asm.wordCmpHOL, AndOp.and, heapRead21, cmp]
                  by_cases closure : wordIsClos conf head1
                  · simp [blockRaw, closure] at run
                    obtain ⟨rfl, rfl, _⟩ := run
                    have tagCases := closureEq.mp closure
                    let maskState := heapState.setVar 1 (.word (head1 &&& mask))
                    have maskStep : WordSemStateFiniteExact.evaluate
                        (.assign 1 (.op .and [.var 21, .const mask])) heapState = (none, maskState) := by
                      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                        wordOpHOL, wordOp, theWords, AndOp.and, heapRead21, maskState]
                    have maskRead1 : maskState.getVar 1 = some (.word (head1 &&& mask)) := by
                      simp [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                    have maskRead0 : maskState.getVar 0 = some (.loc loc1 loc2) := by
                      simpa [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                        sptLookup_sptInsert_ne] using heapRead0
                    have heapRead0Lookup : sptLookup 0 heapState.locals = some (.loc loc1 loc2) := by
                      simpa [WordSemStateFiniteExact.getVar] using heapRead0
                    have blockRun : WordSemStateFiniteExact.evaluate block heapState =
                        (some (.result (.loc loc1 loc2) [.word 1]),
                          {heapState with locals := .ln, localsSize := some 0}) := by
                      by_cases tag482 : head1 &&& mask = BitVec.ofNat width 482
                      · have beq : (head1 &&& mask == BitVec.ofNat width 482) = true := beq_iff_eq.mpr tag482
                        have step : WordSemStateFiniteExact.evaluate
                            (.ite .equal 1 (.imm 482) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) maskState =
                            (some (.result (.loc loc1 loc2) [.word 1]), {maskState with locals := .ln, localsSize := some 0}) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                            WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
                            WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
                            WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
                            wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_ne,
                            sptLookup_sptInsert_same, maskState, heapRead0Lookup,  beq]
                        dsimp only [block]
                        rw [wordListSeq]
                        rw [seqAfter _ _ _ _ maskStep (by simp [maskState, WordSemStateFiniteExact.setVar])
                          (by simp [maskState, WordSemStateFiniteExact.setVar])]
                        rw [wordListSeq]
                        rw [seqResult _ _ _ _ _ step (by simp) (by simp)]
                        simp [maskState, WordSemStateFiniteExact.setVar]
                      · have tag498 : head1 &&& mask = BitVec.ofNat width 498 := by
                          rcases tagCases with h | h
                          · exact (tag482 h).elim
                          · exact h
                        have beq482 : (head1 &&& mask == BitVec.ofNat width 482) = false := beq_eq_false_iff_ne.mpr tag482
                        have beq498 : (head1 &&& mask == BitVec.ofNat width 498) = true := beq_iff_eq.mpr tag498
                        have skipStep : WordSemStateFiniteExact.evaluate
                            (.ite .equal 1 (.imm 482) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) maskState = (none, maskState) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                            wordSemWordCmp, Encoders.Asm.wordCmpHOL, maskRead1, beq482]
                        have retStep : WordSemStateFiniteExact.evaluate
                            (.ite .equal 1 (.imm 498) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) maskState =
                            (some (.result (.loc loc1 loc2) [.word 1]), {maskState with locals := .ln, localsSize := some 0}) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                            WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
                            WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
                            WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
                            wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_ne,
                            sptLookup_sptInsert_same, maskState, heapRead0Lookup,  beq498]
                        dsimp only [block]
                        rw [wordListSeq]
                        rw [seqAfter _ _ _ _ maskStep (by simp [maskState, WordSemStateFiniteExact.setVar])
                          (by simp [maskState, WordSemStateFiniteExact.setVar])]
                        rw [wordListSeq]
                        rw [seqAfter _ _ _ _ skipStep (Nat.le_refl _) rfl]
                        rw [wordListSeq]
                        rw [seqResult _ _ _ _ _ retStep (by simp) (by simp)]
                        simp [maskState, WordSemStateFiniteExact.setVar]
                    have dispatchRun : WordSemStateFiniteExact.evaluate
                        (.ite .test 21 (.imm 12) block .skip) heapState =
                        (some (.result (.loc loc1 loc2) [.word 1]),
                          {heapState with locals := .ln, localsSize := some 0}) := dispatch.trans blockRun
                    refine ⟨t.clock, t.permute, t.stackMax, ?_, ?_, time⟩
                    · rw [heapPrefix]
                      dsimp only [rest]
                      rw [wordListSeq]
                      rw [seqResult _ _ _ _ _ dispatchRun (by simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar])
                        (by simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar])]
                      simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar]
                    · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
                  · by_cases heads : head1 = head2
                    · subst head2
                      by_cases limitZero : limit = 0
                      · simp [blockRaw, closure, limitZero] at run
                      · rw [if_pos blockZero] at run
                        simp only [closure, ↓reduceIte, limitZero] at run
                        have limitPositive : 0 < limit := by omega
                        have clockPositive : 0 < t.clock := by omega
                        let decoded := WordGcFunctions.decodeLength conf head1
                        let listEntry := WordSemStateFiniteExact.callEnv
                          [.loc loc1 loc2, .word decoded, .word (addr1 + bytes), .word (addr2 + bytes)]
                          (sptLookup equal1Location t.stackSize) (WordSemStateFiniteExact.decClock t)
                        have listTime : limit - 1 ≤ listEntry.clock := by
                          change limit - 1 ≤ t.clock - 1
                          omega
                        have list0 : listEntry.getVar 0 = some (.loc loc1 loc2) := by
                          simp [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                            sptFromList2, sptLookup_sptInsert_ne,  sptLookup]
                        have list2 : listEntry.getVar 2 = some (.word decoded) := by
                          simp [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                            sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                        have list4 : listEntry.getVar 4 = some (.word (addr1 + bytes)) := by
                          simp [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                            sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                        have list6 : listEntry.getVar 6 = some (.word (addr2 + bytes)) := by
                          simp [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                            sptFromList2,  sptLookup_sptInsert_same]
                        have listSize : saneLocalsSize listEntry := by right; rfl
                        obtain ⟨listCk, listPerm, listPeak, listEval, listStack, listBound⟩ :=
                          (ih (limit - 1) (by omega)).2 conf store domain memory clock decoded
                            (addr1 + bytes) (addr2 + bytes) listEntry loc1 loc2 res remaining remainingClock
                            ⟨by simpa [decoded, bytes, StackRemove.bytesInWord, wordSemBytesInWord] using run,
                              by simpa [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using dom,
                              by simpa [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using mem,
                              by simpa [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using storeEq,
                              listTime, shift,
                              by simpa [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using code,
                              by simpa [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using code1,
                              by simpa [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using codeCmp,
                              list0, list2, list4, list6, listSize, lenNe, lenLt, good⟩
                        have equal1Below : optionLe (sptLookup equal1Location t.stackSize)
                            (DataSem.eqCodeStackMax (clock + 1) t.stackSize) := by
                          have leftBound : optionLe (sptLookup equal1Location t.stackSize)
                              (Option.map₂ max (sptLookup equalLocation t.stackSize)
                                (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize))) := by
                            apply (optionLe_max_right _ _ _).2
                            right
                            exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
                          have rightBound : optionLe
                              (Option.map₂ max (sptLookup equalLocation t.stackSize)
                                (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize)))
                              (DataSem.eqCodeStackMax (clock + 1) t.stackSize) := by
                            unfold DataSem.eqCodeStackMax
                            cases hmax : Option.map₂ max (sptLookup equalLocation t.stackSize)
                                (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize)) with
                            | none => simp [optionLe]
                            | some value =>
                              simp only [Option.map_some, optionLe]
                              nlinarith
                          exact optionLe_trans _ _ _ ⟨leftBound, rightBound⟩
                        have optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
                          cases x <;> cases y <;> rfl
                        have optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
                          cases x <;> cases y <;> rfl
                        simp only [listEntry, WordSemStateFiniteExact.callEnv,
                          WordSemStateFiniteExact.decClock, optMax, optAdd] at listStack
                        have listFinalStack : optionLe listPeak
                            (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack)
                              (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) := by
                          apply optionLe_trans _ _ _ ⟨listStack, ?_⟩
                          apply equalTailStackBound t.stackMax (wordSemStackSize t.stack) t.stackMax
                            (sptLookup equal1Location t.stackSize) (DataSem.eqCodeStackMax (clock + 1) t.stackSize)
                          · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
                          · exact equal1Below
                        have not482 : head1 &&& mask ≠ BitVec.ofNat width 482 := by
                          intro h; exact closure (closureEq.mpr (Or.inl h))
                        have not498 : head1 &&& mask ≠ BitVec.ofNat width 498 := by
                          intro h; exact closure (closureEq.mpr (Or.inr h))
                        have cmp482 : (head1 &&& mask == BitVec.ofNat width 482) = false := beq_eq_false_iff_ne.mpr not482
                        have cmp498 : (head1 &&& mask == BitVec.ofNat width 498) = false := beq_eq_false_iff_ne.mpr not498
                        let maskState := heapState.setVar 1 (.word (head1 &&& mask))
                        have maskStep : WordSemStateFiniteExact.evaluate
                            (.assign 1 (.op .and [.var 21, .const mask])) heapState = (none, maskState) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                            wordOpHOL, wordOp, theWords, AndOp.and, heapRead21, maskState]
                        have maskRead1 : maskState.getVar 1 = some (.word (head1 &&& mask)) := by
                          simp [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                        have maskRead21 : maskState.getVar 21 = some (.word head1) := by
                          simpa [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_ne] using heapRead21
                        have maskRead41 : maskState.getVar 41 = some (.word head1) := by
                          simpa [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_ne] using heapRead41
                        have skip482 : WordSemStateFiniteExact.evaluate
                            (.ite .equal 1 (.imm 482) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) maskState = (none, maskState) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                            wordSemWordCmp, Encoders.Asm.wordCmpHOL, maskRead1, cmp482]
                        have skip498 : WordSemStateFiniteExact.evaluate
                            (.ite .equal 1 (.imm 498) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) maskState = (none, maskState) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                            wordSemWordCmp, Encoders.Asm.wordCmpHOL, maskRead1, cmp498]
                        have skipHeads : WordSemStateFiniteExact.evaluate
                            (.ite .equal 21 (.reg 41) .skip (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2]))) maskState = (none, maskState) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                            wordSemWordCmp, Encoders.Asm.wordCmpHOL, maskRead21, maskRead41]
                        let decodedState := maskState.setVar 6 (.word decoded)
                        have decodedExp : maskState.wordExp (shiftVar .lsr 21 (width - conf.lenSize)) = some (.word decoded) := by
                          have h : sptLookup 21 maskState.locals = some (.word head1) := by
                            simpa [WordSemStateFiniteExact.getVar] using maskRead21
                          rw [Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.wordExpShiftVar]
                          simp [h, decoded, WordGcFunctions.decodeLength, Flapjack.SemanticPrimitivesProps.shiftLookup]
                        have decodeStep : WordSemStateFiniteExact.evaluate
                            (.assign 6 (shiftVar .lsr 21 (width - conf.lenSize))) maskState = (none, decodedState) := by
                          simp [WordSemStateFiniteExact.evaluate, decodedExp, decodedState]
                        have decodedRead20 : decodedState.getVar 20 = some (.word addr1) := by
                          simpa [decodedState, maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_ne] using heapRead20
                        let addr20State := decodedState.setVar 20 (.word (addr1 + bytes))
                        have addr20Step : WordSemStateFiniteExact.evaluate
                            (.assign 20 (.op .add [.var 20, .const bytes])) decodedState = (none, addr20State) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                            wordOpHOL, wordOp, theWords, decodedRead20, addr20State]
                        have addrRead40 : addr20State.getVar 40 = some (.word addr2) := by
                          simpa [addr20State, decodedState, maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_ne] using heapRead40
                        let tailState := addr20State.setVar 40 (.word (addr2 + bytes))
                        have addr40Step : WordSemStateFiniteExact.evaluate
                            (.assign 40 (.op .add [.var 40, .const bytes])) addr20State = (none, tailState) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                            wordOpHOL, wordOp, theWords, addrRead40, tailState]
                        have tailRead0 : tailState.getVar 0 = some (.loc loc1 loc2) := by
                          simpa [tailState, addr20State, decodedState, maskState,
                            WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                            sptLookup_sptInsert_ne] using heapRead0
                        have tailRead6 : tailState.getVar 6 = some (.word decoded) := by
                          simp [tailState, addr20State, decodedState, WordSemStateFiniteExact.getVar,
                            WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                        have tailRead20 : tailState.getVar 20 = some (.word (addr1 + bytes)) := by
                          simp [tailState, addr20State, WordSemStateFiniteExact.getVar,
                            WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                        have tailRead40 : tailState.getVar 40 = some (.word (addr2 + bytes)) := by
                          simp [tailState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                        have tailCode : sptLookup equal1Location tailState.code = some (4, equal1Code) := by
                          simpa [tailState, addr20State, decodedState, maskState, heapState, state21, state40,
                            state20, state1, WordSemStateFiniteExact.setVar] using code1
                        have tailSize : sptLookup equal1Location tailState.stackSize = sptLookup equal1Location t.stackSize := by rfl
                        have tailClock : tailState.clock ≠ 0 := by
                          simpa [tailState, addr20State, decodedState, maskState, heapState, state21, state40,
                            state20, state1, WordSemStateFiniteExact.setVar] using (Nat.ne_of_gt clockPositive)
                        have tailEntryEq : WordSemStateFiniteExact.callEnv
                            [.loc loc1 loc2, .word decoded, .word (addr1 + bytes), .word (addr2 + bytes)]
                            (sptLookup equal1Location t.stackSize) (WordSemStateFiniteExact.decClock tailState) = listEntry := by
                          simp [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                            tailState, addr20State, decodedState, maskState, heapState, state21, state40,
                            state20, state1, WordSemStateFiniteExact.setVar]
                        have tailCall : WordSemStateFiniteExact.evaluate
                            (.call none (some equal1Location) [0, 6, 20, 40] none) tailState =
                            (some (.result (.loc loc1 loc2) [.word res]),
                              {t with clock := listCk, locals := .ln, localsSize := some 0, permute := listPerm, stackMax := listPeak}) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
                            tailRead0, tailRead6, tailRead20, tailRead40, wordSemBadDestArgs,
                            wordSemAddRetLoc, wordSemFindCode, tailCode, tailSize, tailClock, tailEntryEq, listEval,
                            wordSemBadFunReturn]
                          simp [listEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]
                        have blockRun : WordSemStateFiniteExact.evaluate block heapState =
                            (some (.result (.loc loc1 loc2) [.word res]),
                              {t with clock := listCk, locals := .ln, localsSize := some 0, permute := listPerm, stackMax := listPeak}) := by
                          dsimp only [block]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ maskStep (by simp [maskState, WordSemStateFiniteExact.setVar])
                            (by simp [maskState, WordSemStateFiniteExact.setVar])]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ skip482 (Nat.le_refl _) rfl]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ skip498 (Nat.le_refl _) rfl]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ skipHeads (Nat.le_refl _) rfl]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ decodeStep (by simp [decodedState, WordSemStateFiniteExact.setVar])
                            (by simp [decodedState, WordSemStateFiniteExact.setVar])]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ addr20Step (by simp [addr20State, WordSemStateFiniteExact.setVar])
                            (by simp [addr20State, WordSemStateFiniteExact.setVar])]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ addr40Step (by simp [tailState, WordSemStateFiniteExact.setVar])
                            (by simp [tailState, WordSemStateFiniteExact.setVar])]
                          simpa [wordListSeq] using tailCall
                        have dispatchRun : WordSemStateFiniteExact.evaluate
                            (.ite .test 21 (.imm 12) block .skip) heapState =
                            (some (.result (.loc loc1 loc2) [.word res]),
                              {t with clock := listCk, locals := .ln, localsSize := some 0, permute := listPerm, stackMax := listPeak}) :=
                          dispatch.trans blockRun
                        have listClockLe : listCk ≤ t.clock := by
                          have hc := (WordSemStateFiniteExact.evaluate_clock equal1Code listEntry _ _ listEval).1
                          change listCk ≤ t.clock - 1 at hc
                          omega
                        refine ⟨listCk, listPerm, listPeak, ?_, listFinalStack, listBound⟩
                        rw [heapPrefix]
                        dsimp only [rest]
                        rw [wordListSeq]
                        exact seqResult _ _ _ _ _ dispatchRun (by
                          simpa [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar] using listClockLe)
                          (by simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar])
                    · simp [blockRaw, closure, heads] at run
                      obtain ⟨rfl, rfl, _⟩ := run
                      have not482 : head1 &&& mask ≠ BitVec.ofNat width 482 := by
                        intro h
                        exact closure (closureEq.mpr (Or.inl h))
                      have not498 : head1 &&& mask ≠ BitVec.ofNat width 498 := by
                        intro h
                        exact closure (closureEq.mpr (Or.inr h))
                      have cmp482 : (head1 &&& mask == BitVec.ofNat width 482) = false := beq_eq_false_iff_ne.mpr not482
                      have cmp498 : (head1 &&& mask == BitVec.ofNat width 498) = false := beq_eq_false_iff_ne.mpr not498
                      have cmpHeads : (head1 == head2) = false := beq_eq_false_iff_ne.mpr heads
                      let maskState := heapState.setVar 1 (.word (head1 &&& mask))
                      have maskStep : WordSemStateFiniteExact.evaluate
                          (.assign 1 (.op .and [.var 21, .const mask])) heapState = (none, maskState) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          wordOpHOL, wordOp, theWords, AndOp.and, heapRead21, maskState]
                      have maskRead1 : maskState.getVar 1 = some (.word (head1 &&& mask)) := by
                        simp [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                      have maskRead21 : maskState.getVar 21 = some (.word head1) := by
                        simpa [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne] using heapRead21
                      have maskRead41 : maskState.getVar 41 = some (.word head2) := by
                        simpa [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne] using heapRead41
                      have maskRead0 : sptLookup 0 maskState.locals = some (.loc loc1 loc2) := by
                        simpa [maskState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne] using heapRead0
                      have skip482 : WordSemStateFiniteExact.evaluate
                          (.ite .equal 1 (.imm 482) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) maskState = (none, maskState) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                          wordSemWordCmp, Encoders.Asm.wordCmpHOL, maskRead1, cmp482]
                      have skip498 : WordSemStateFiniteExact.evaluate
                          (.ite .equal 1 (.imm 498) (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) maskState = (none, maskState) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                          wordSemWordCmp, Encoders.Asm.wordCmpHOL, maskRead1, cmp498]
                      have maskRead21Lookup : sptLookup 21 maskState.locals = some (.word head1) := by
                        simpa [WordSemStateFiniteExact.getVar] using maskRead21
                      have maskRead41Lookup : sptLookup 41 maskState.locals = some (.word head2) := by
                        simpa [WordSemStateFiniteExact.getVar] using maskRead41
                      have headsReturn : WordSemStateFiniteExact.evaluate
                          (.ite .equal 21 (.reg 41) .skip (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2]))) maskState =
                          (some (.result (.loc loc1 loc2) [.word 0]), {maskState with locals := .ln, localsSize := some 0}) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                          WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
                          WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
                          WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
                          wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_ne,
                          sptLookup_sptInsert_same, maskRead0, maskRead21Lookup, maskRead41Lookup, cmpHeads]
                      have blockRun : WordSemStateFiniteExact.evaluate block heapState =
                          (some (.result (.loc loc1 loc2) [.word 0]), {heapState with locals := .ln, localsSize := some 0}) := by
                        dsimp only [block]
                        rw [wordListSeq]
                        rw [seqAfter _ _ _ _ maskStep (by simp [maskState, WordSemStateFiniteExact.setVar])
                          (by simp [maskState, WordSemStateFiniteExact.setVar])]
                        rw [wordListSeq]
                        rw [seqAfter _ _ _ _ skip482 (Nat.le_refl _) rfl]
                        rw [wordListSeq]
                        rw [seqAfter _ _ _ _ skip498 (Nat.le_refl _) rfl]
                        rw [wordListSeq]
                        rw [seqResult _ _ _ _ _ headsReturn (by simp) (by simp)]
                        simp [maskState, WordSemStateFiniteExact.setVar]
                      have dispatchRun : WordSemStateFiniteExact.evaluate
                          (.ite .test 21 (.imm 12) block .skip) heapState =
                          (some (.result (.loc loc1 loc2) [.word 0]),
                            {heapState with locals := .ln, localsSize := some 0}) := dispatch.trans blockRun
                      refine ⟨t.clock, t.permute, t.stackMax, ?_, ?_, time⟩
                      · rw [heapPrefix]
                        dsimp only [rest]
                        rw [wordListSeq]
                        rw [seqResult _ _ _ _ _ dispatchRun (by simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar])
                          (by simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar])]
                        simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar]
                      · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
                · have blockRaw : head1 &&& BitVec.ofNat width 12 ≠ BitVec.ofNat width 0 := by simpa using blockZero
                  have cmpBlock : (head1 &&& BitVec.ofNat width 12 == BitVec.ofNat width 0) = false :=
                    beq_eq_false_iff_ne.mpr blockRaw
                  have dispatch : WordSemStateFiniteExact.evaluate
                      (.ite .test 21 (.imm 12) block .skip) heapState = (none, heapState) := by
                    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                      wordSemWordCmp, Encoders.Asm.wordCmpHOL, AndOp.and, heapRead21, cmpBlock]
                  rw [if_neg blockZero] at run
                  by_cases heads : head1 = head2
                  · subst head2
                    have skipHeads : WordSemStateFiniteExact.evaluate
                        (.ite .equal 21 (.reg 41) .skip (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2]))) heapState =
                        (none, heapState) := by
                      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                        wordSemWordCmp, Encoders.Asm.wordCmpHOL, heapRead21, heapRead41]
                    by_cases bit2 : head1.getLsbD 2 = false
                    · simp [bit2] at run
                      obtain ⟨rfl, rfl, _⟩ := run
                      have bit4 : head1 &&& BitVec.ofNat width 4 = BitVec.ofNat width 0 := by
                        simpa using (headerBits head1 good).1.mpr bit2
                      have cmp4 : (head1 &&& BitVec.ofNat width 4 == BitVec.ofNat width 0) = true := beq_iff_eq.mpr bit4
                      have heapRead0Lookup : sptLookup 0 heapState.locals = some (.loc loc1 loc2) := by
                        simpa [WordSemStateFiniteExact.getVar] using heapRead0
                      have heapRead21Lookup : sptLookup 21 heapState.locals = some (.word head1) := by
                        simpa [WordSemStateFiniteExact.getVar] using heapRead21
                      have returnBit : WordSemStateFiniteExact.evaluate
                          (.ite .test 21 (.imm 4) (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])) .skip) heapState =
                          (some (.result (.loc loc1 loc2) [.word 0]), {heapState with locals := .ln, localsSize := some 0}) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                          WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
                          WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
                          WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
                          wordSemWordCmp, Encoders.Asm.wordCmpHOL, AndOp.and, sptLookup_sptInsert_ne,
                          sptLookup_sptInsert_same, heapRead0Lookup, heapRead21Lookup, cmp4]
                      refine ⟨t.clock, t.permute, t.stackMax, ?_, ?_, time⟩
                      · rw [heapPrefix]
                        dsimp only [rest]
                        rw [wordListSeq]
                        rw [seqAfter _ _ _ _ dispatch (Nat.le_refl _) rfl]
                        rw [wordListSeq]
                        rw [seqAfter _ _ _ _ skipHeads (Nat.le_refl _) rfl]
                        rw [wordListSeq]
                        rw [seqResult _ _ _ _ _ returnBit (by simp) (by simp)]
                        simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar]
                      · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
                    · have bit2True : head1.getLsbD 2 = true := by
                        cases h : head1.getLsbD 2 with
                        | false => exact (bit2 h).elim
                        | true => rfl
                      have no4 : head1 &&& BitVec.ofNat width 4 ≠ BitVec.ofNat width 0 := by
                        intro h
                        have hbit : head1.getLsbD 2 = false := (headerBits head1 good).1.mp (by simpa using h)
                        rw [bit2True] at hbit
                        contradiction
                      have cmp4 : (head1 &&& BitVec.ofNat width 4 == BitVec.ofNat width 0) = false := beq_eq_false_iff_ne.mpr no4
                      have skipBit : WordSemStateFiniteExact.evaluate
                          (.ite .test 21 (.imm 4) (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])) .skip) heapState = (none, heapState) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                          wordSemWordCmp, Encoders.Asm.wordCmpHOL, AndOp.and, heapRead21, cmp4]
                      let tagValue := head1 &&& (24 : BitVec width)
                      let tagState := heapState.setVar 1 (.word tagValue)
                      have tagStep : WordSemStateFiniteExact.evaluate
                          (.assign 1 (.op .and [.var 21, .const 24])) heapState = (none, tagState) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          wordOpHOL, wordOp, theWords, AndOp.and, heapRead21, tagState, tagValue]
                      have tagRead1 : tagState.getVar 1 = some (.word tagValue) := by
                        simp [tagState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                      have tagRead0 : sptLookup 0 tagState.locals = some (.loc loc1 loc2) := by
                        simpa [tagState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_ne] using heapRead0
                      by_cases special : head1.getLsbD 3 = false ∧ head1.getLsbD 4 = true
                      · simp [bit2True, special.1, special.2] at run
                        obtain ⟨rfl, rfl, _⟩ := run
                        have tagEq : tagValue = BitVec.ofNat width 16 := by
                          simpa [tagValue] using (headerBits head1 good).2.mpr special
                        have cmpTag : (tagValue == BitVec.ofNat width 16) = true := beq_iff_eq.mpr tagEq
                        have heapRead0Lookup : sptLookup 0 heapState.locals = some (.loc loc1 loc2) := by
                          simpa [WordSemStateFiniteExact.getVar] using heapRead0
                        have tagReturn : WordSemStateFiniteExact.evaluate
                            (.ite .equal 1 (.imm 16) (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])) .skip) tagState =
                            (some (.result (.loc loc1 loc2) [.word 0]), {tagState with locals := .ln, localsSize := some 0}) := by
                          simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                            WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
                            WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
                            WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
                            wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_ne,
                            sptLookup_sptInsert_same, tagState,   heapRead0Lookup, cmpTag]
                        refine ⟨t.clock, t.permute, t.stackMax, ?_, ?_, time⟩
                        · rw [heapPrefix]
                          dsimp only [rest]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ dispatch (Nat.le_refl _) rfl]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ skipHeads (Nat.le_refl _) rfl]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ skipBit (Nat.le_refl _) rfl]
                          rw [wordListSeq]
                          rw [seqAfter _ _ _ _ tagStep (by simp [tagState, WordSemStateFiniteExact.setVar])
                            (by simp [tagState, WordSemStateFiniteExact.setVar])]
                          rw [wordListSeq]
                          rw [seqResult _ _ _ _ _ tagReturn (by simp) (by simp)]
                          simp [tagState, heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar]
                        · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
                      · have specialBool : (!head1.getLsbD 3 && head1.getLsbD 4) = false := by
                          cases h3 : head1.getLsbD 3 <;> cases h4 : head1.getLsbD 4 <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and, Bool.false_eq_true, Bool.true_eq_false, and_self, not_true_eq_false]
                        simp only [bit2True, Bool.not_true, Bool.false_eq_true, ↓reduceIte, specialBool] at run
                        by_cases exhausted : limit ≤ (WordGcFunctions.decodeLength conf head1).toNat
                        · simp [exhausted] at run
                        · simp only [exhausted, ↓reduceIte] at run
                          cases cmpRun : wordCmpLoop (WordGcFunctions.decodeLength conf head1)
                              (addr1 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf head1)
                              (addr2 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf head1) domain memory with
                          | none => simp [cmpRun] at run
                          | some cmpResult =>
                            simp [cmpRun] at run
                            obtain ⟨rfl, rfl, _⟩ := run
                            let decoded := WordGcFunctions.decodeLength conf head1
                            let cmpAddr1 := addr1 + StackRemove.bytesInWord width * decoded
                            let cmpAddr2 := addr2 + StackRemove.bytesInWord width * decoded
                            let cmpEntry := WordSemStateFiniteExact.callEnv
                              [.loc loc1 loc2, .word decoded, .word cmpAddr1, .word cmpAddr2]
                              (sptLookup compare1Location t.stackSize) (WordSemStateFiniteExact.decClock t)
                            have cmpTime : decoded.toNat ≤ cmpEntry.clock := by
                              change (WordGcFunctions.decodeLength conf head1).toNat ≤ t.clock - 1
                              omega
                            have cmp0 : cmpEntry.getVar 0 = some (.loc loc1 loc2) := by
                              simp [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                                sptFromList2, sptLookup_sptInsert_ne,  sptLookup]
                            have cmp2 : cmpEntry.getVar 2 = some (.word decoded) := by
                              simp [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                                sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                            have cmp4 : cmpEntry.getVar 4 = some (.word cmpAddr1) := by
                              simp [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                                sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                            have cmp6 : cmpEntry.getVar 6 = some (.word cmpAddr2) := by
                              simp [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                                sptFromList2,  sptLookup_sptInsert_same]
                            obtain ⟨cmpCk, cmpPeak, cmpEval, cmpStack, cmpClock⟩ := compare1Code_correct
                              decoded cmpAddr1 cmpAddr2 domain memory cmpResult cmpEntry loc1 loc2
                              (by simpa [decoded, cmpAddr1, cmpAddr2] using cmpRun)
                              (by simpa [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using dom)
                              (by simpa [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using mem)
                              (by simpa [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] using codeCmp)
                              (by simp [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]) cmp0 cmp2 cmp4 cmp6 cmpTime
                            have remainingBound : limit - 1 - decoded.toNat ≤ cmpCk := by
                              change t.clock - 1 ≤ decoded.toNat + cmpCk at cmpClock
                              omega
                            have cmpBelow : optionLe (sptLookup compare1Location t.stackSize)
                                (DataSem.eqCodeStackMax (clock + 1) t.stackSize) := by
                              have leftBound : optionLe (sptLookup compare1Location t.stackSize)
                                  (Option.map₂ max (sptLookup equalLocation t.stackSize)
                                    (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize))) := by
                                apply (optionLe_max_right _ _ _).2
                                right
                                exact (optionLe_max_right _ _ _).2 (Or.inr (optionLe_refl _))
                              have rightBound : optionLe
                                  (Option.map₂ max (sptLookup equalLocation t.stackSize)
                                    (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize)))
                                  (DataSem.eqCodeStackMax (clock + 1) t.stackSize) := by
                                unfold DataSem.eqCodeStackMax
                                cases hmax : Option.map₂ max (sptLookup equalLocation t.stackSize)
                                    (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize)) with
                                | none => simp [optionLe]
                                | some value =>
                                  simp only [Option.map_some, optionLe]
                                  nlinarith
                              exact optionLe_trans _ _ _ ⟨leftBound, rightBound⟩
                            have optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
                              cases x <;> cases y <;> rfl
                            have optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
                              cases x <;> cases y <;> rfl
                            simp only [cmpEntry, WordSemStateFiniteExact.callEnv,
                              WordSemStateFiniteExact.decClock, optMax, optAdd] at cmpStack
                            have cmpFinalStack : optionLe cmpPeak
                                (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack)
                                  (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) := by
                              apply optionLe_trans _ _ _ ⟨cmpStack, ?_⟩
                              exact compareStackBound t.stackMax (wordSemStackSize t.stack)
                                (sptLookup compare1Location t.stackSize) (DataSem.eqCodeStackMax (clock + 1) t.stackSize) cmpBelow
                            have tagNe : tagValue ≠ BitVec.ofNat width 16 := by
                              intro h
                              exact special ((headerBits head1 good).2.mp (by simpa [tagValue] using h))
                            have cmpTag : (tagValue == BitVec.ofNat width 16) = false := beq_eq_false_iff_ne.mpr tagNe
                            have skipTag : WordSemStateFiniteExact.evaluate
                                (.ite .equal 1 (.imm 16) (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2])) .skip) tagState = (none, tagState) := by
                              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                                wordSemWordCmp, Encoders.Asm.wordCmpHOL, tagRead1, cmpTag]
                            have tagRead21 : tagState.getVar 21 = some (.word head1) := by
                              simpa [tagState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne] using heapRead21
                            have tagRead20 : tagState.getVar 20 = some (.word addr1) := by
                              simpa [tagState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne] using heapRead20
                            have tagRead40 : tagState.getVar 40 = some (.word addr2) := by
                              simpa [tagState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne] using heapRead40
                            let decodedState := tagState.setVar 6 (.word decoded)
                            have decodedExp : tagState.wordExp (shiftVar .lsr 21 (width - conf.lenSize)) = some (.word decoded) := by
                              have h : sptLookup 21 tagState.locals = some (.word head1) := by
                                simpa [WordSemStateFiniteExact.getVar] using tagRead21
                              rw [Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.wordExpShiftVar]
                              simp [h, decoded, WordGcFunctions.decodeLength, Flapjack.SemanticPrimitivesProps.shiftLookup]
                            have decodeStep : WordSemStateFiniteExact.evaluate
                                (.assign 6 (shiftVar .lsr 21 (width - conf.lenSize))) tagState = (none, decodedState) := by
                              simp [WordSemStateFiniteExact.evaluate, decodedExp, decodedState]
                            have decodedRead6 : sptLookup 6 decodedState.locals = some (.word decoded) := by
                              simp [decodedState, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
                            have decodedRead20 : decodedState.getVar 20 = some (.word addr1) := by
                              simpa [decodedState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne] using tagRead20
                            have shiftedExp : decodedState.wordExp (shiftVar .lsl 6 (wordShiftAmount width)) =
                                some (.word (StackRemove.bytesInWord width * decoded)) := by
                              rw [Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.wordExpShiftVar]
                              simp [decodedRead6, Flapjack.SemanticPrimitivesProps.shiftLookup, shiftBytes decoded good]
                            let addr2State := decodedState.setVar 2 (.word cmpAddr1)
                            have addr2Step : WordSemStateFiniteExact.evaluate
                                (.assign 2 (.op .add [.var 20, shiftVar .lsl 6 (wordShiftAmount width)])) decodedState =
                                (none, addr2State) := by
                              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                                wordOpHOL, wordOp, theWords, decodedRead20, shiftedExp, addr2State, cmpAddr1]
                            have state2Read6 : sptLookup 6 addr2State.locals = some (.word decoded) := by
                              simpa [addr2State, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using decodedRead6
                            have state2Read40 : addr2State.getVar 40 = some (.word addr2) := by
                              simpa [addr2State, decodedState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne] using tagRead40
                            have shiftedExp2 : addr2State.wordExp (shiftVar .lsl 6 (wordShiftAmount width)) =
                                some (.word (StackRemove.bytesInWord width * decoded)) := by
                              rw [Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.wordExpShiftVar]
                              simp [state2Read6, Flapjack.SemanticPrimitivesProps.shiftLookup, shiftBytes decoded good]
                            let tailState := addr2State.setVar 4 (.word cmpAddr2)
                            have addr4Step : WordSemStateFiniteExact.evaluate
                                (.assign 4 (.op .add [.var 40, shiftVar .lsl 6 (wordShiftAmount width)])) addr2State =
                                (none, tailState) := by
                              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                                wordOpHOL, wordOp, theWords, state2Read40, shiftedExp2, tailState, cmpAddr2]
                            have tailRead0 : tailState.getVar 0 = some (.loc loc1 loc2) := by
                              simpa [tailState, addr2State, decodedState, tagState, WordSemStateFiniteExact.getVar,
                                WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne] using heapRead0
                            have tailRead6 : tailState.getVar 6 = some (.word decoded) := by
                              simpa [tailState, addr2State, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne] using decodedRead6
                            have tailRead2 : tailState.getVar 2 = some (.word cmpAddr1) := by
                              simp [tailState, addr2State, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                            have tailRead4 : tailState.getVar 4 = some (.word cmpAddr2) := by
                              simp [tailState, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                                sptLookup_sptInsert_same]
                            have tailCode : sptLookup compare1Location tailState.code = some (4, compare1Code) := by
                              simpa [tailState, addr2State, decodedState, tagState, heapState, state21, state40,
                                state20, state1, WordSemStateFiniteExact.setVar] using codeCmp
                            have tailSize : sptLookup compare1Location tailState.stackSize = sptLookup compare1Location t.stackSize := by rfl
                            have tailClock : tailState.clock ≠ 0 := by
                              have positive : 0 < t.clock := by omega
                              simpa [tailState, addr2State, decodedState, tagState, heapState, state21, state40,
                                state20, state1, WordSemStateFiniteExact.setVar] using (Nat.ne_of_gt positive)
                            have cmpEntryEq : WordSemStateFiniteExact.callEnv
                                [.loc loc1 loc2, .word decoded, .word cmpAddr1, .word cmpAddr2]
                                (sptLookup compare1Location t.stackSize) (WordSemStateFiniteExact.decClock tailState) = cmpEntry := by
                              simp [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                                tailState, addr2State, decodedState, tagState, heapState, state21, state40,
                                state20, state1, WordSemStateFiniteExact.setVar]
                            have tailCall : WordSemStateFiniteExact.evaluate
                                (.call none (some compare1Location) [0, 6, 2, 4] none) tailState =
                                (some (.result (.loc loc1 loc2) [.word cmpResult]),
                                  {t with clock := cmpCk, locals := .ln, localsSize := some 0, stackMax := cmpPeak}) := by
                              simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
                                tailRead0, tailRead6, tailRead2, tailRead4, wordSemBadDestArgs,
                                wordSemAddRetLoc, wordSemFindCode, tailCode, tailSize, tailClock, cmpEntryEq, cmpEval,
                                wordSemBadFunReturn]
                              simp [cmpEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock]
                            refine ⟨cmpCk, t.permute, cmpPeak, ?_, cmpFinalStack, remainingBound⟩
                            rw [heapPrefix]
                            dsimp only [rest]
                            rw [wordListSeq]
                            rw [seqAfter _ _ _ _ dispatch (Nat.le_refl _) rfl]
                            rw [wordListSeq]
                            rw [seqAfter _ _ _ _ skipHeads (Nat.le_refl _) rfl]
                            rw [wordListSeq]
                            rw [seqAfter _ _ _ _ skipBit (Nat.le_refl _) rfl]
                            rw [wordListSeq]
                            rw [seqAfter _ _ _ _ tagStep (by simp [tagState, WordSemStateFiniteExact.setVar])
                              (by simp [tagState, WordSemStateFiniteExact.setVar])]
                            rw [wordListSeq]
                            rw [seqAfter _ _ _ _ skipTag (Nat.le_refl _) rfl]
                            rw [wordListSeq]
                            rw [seqAfter _ _ _ _ decodeStep (by simp [decodedState, WordSemStateFiniteExact.setVar])
                              (by simp [decodedState, WordSemStateFiniteExact.setVar])]
                            rw [wordListSeq]
                            rw [seqAfter _ _ _ _ addr2Step (by simp [addr2State, WordSemStateFiniteExact.setVar])
                              (by simp [addr2State, WordSemStateFiniteExact.setVar])]
                            rw [wordListSeq]
                            rw [seqAfter _ _ _ _ addr4Step (by simp [tailState, WordSemStateFiniteExact.setVar])
                              (by simp [tailState, WordSemStateFiniteExact.setVar])]
                            simpa [wordListSeq] using tailCall
                  · simp [heads] at run
                    obtain ⟨rfl, rfl, _⟩ := run
                    have cmpHeads : (head1 == head2) = false := beq_eq_false_iff_ne.mpr heads
                    have heapRead0Lookup : sptLookup 0 heapState.locals = some (.loc loc1 loc2) := by
                      simpa [WordSemStateFiniteExact.getVar] using heapRead0
                    have heapRead21Lookup : sptLookup 21 heapState.locals = some (.word head1) := by
                      simpa [WordSemStateFiniteExact.getVar] using heapRead21
                    have heapRead41Lookup : sptLookup 41 heapState.locals = some (.word head2) := by
                      simpa [WordSemStateFiniteExact.getVar] using heapRead41
                    have returnHeads : WordSemStateFiniteExact.evaluate
                        (.ite .equal 21 (.reg 41) .skip (.seq (.assign 2 (.const (BitVec.ofNat width 0))) (.return 0 [2]))) heapState =
                        (some (.result (.loc loc1 loc2) [.word 0]), {heapState with locals := .ln, localsSize := some 0}) := by
                      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
                        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
                        WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.flushState,
                        wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_ne,
                        sptLookup_sptInsert_same, heapRead0Lookup, heapRead21Lookup, heapRead41Lookup, cmpHeads]
                    refine ⟨t.clock, t.permute, t.stackMax, ?_, ?_, time⟩
                    · rw [heapPrefix]
                      dsimp only [rest]
                      rw [wordListSeq]
                      rw [seqAfter _ _ _ _ dispatch (Nat.le_refl _) rfl]
                      rw [wordListSeq]
                      rw [seqResult _ _ _ _ _ returnHeads (by simp) (by simp)]
                      simp [heapState, state21, state40, state20, state1, WordSemStateFiniteExact.setVar]
                    · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
      · intro conf store domain memory clock count a1 a2 t loc1 loc2 res remaining remainingClock h
        obtain ⟨run, dom, mem, storeEq, time, shift, code, code1, codeCmp, r0, r2, r4, r6,
          localSize, lenNe, lenLt, good⟩ := h
        by_cases zero : count = 0
        · subst count
          simp [wordEqList] at run
          obtain ⟨rfl, rfl, _⟩ := run
          refine ⟨t.clock, t.permute, t.stackMax, ?_, ?_, time⟩
          · exact equal1Code_zero t loc1 loc2 r0 r2
          · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
        · rw [wordEqList_unclamped] at run
          simp only [zero, ↓reduceIte] at run
          by_cases invalid : domain a1 = false ∨ domain a2 = false ∨ limit = 0 ∨ clock = 0
          · simp [invalid] at run
          · simp only [invalid, ↓reduceIte] at run
            cases m1 : memory a1 with
            | loc x y => simp [m1] at run
            | word v1 =>
              cases m2 : memory a2 with
              | loc x y => simp [m1, m2] at run
              | word v2 =>
                simp only [m1, m2] at run
                cases headRun : wordEq conf store domain memory (limit - 1) (clock - 1) v1 v2 with
                | none => simp [headRun] at run
                | some triple =>
                  obtain ⟨headResult, headRemaining, headClock⟩ := triple
                  simp only [headRun] at run
                  have limitPos : 0 < limit := by omega
                  have clockPos : 0 < clock := by omega
                  have tClockPos : 0 < t.clock := by omega
                  let base := {t with locals := sptInsert 3 (.word v2) (sptInsert 1 (.word v1) t.locals)}
                  let saved := sptInter base.locals (sptListInsert [0, 2, 4, 6] .ln)
                  have base0 : sptLookup 0 base.locals = some (.loc loc1 loc2) := by
                    simpa [base, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne] using r0
                  have base2 : sptLookup 2 base.locals = some (.word count) := by
                    simpa [base, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne] using r2
                  have base4 : sptLookup 4 base.locals = some (.word a1) := by
                    simpa [base, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne] using r4
                  have base6 : sptLookup 6 base.locals = some (.word a2) := by
                    simpa [base, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne] using r6
                  have cut : wordSemCutEnvs (sptListInsert [0, 2, 4, 6] .ln, .ln) base.locals = some (saved, .ln) := by
                    exact equal1_cut base.locals _ _ _ _ base0 base2 base4 base6
                  let entry := WordSemStateFiniteExact.callEnv
                    [.loc equal1Location 2, .word v1, .word v2] (sptLookup equalLocation t.stackSize)
                    (WordSemStateFiniteExact.pushEnv (saved, .ln) none (WordSemStateFiniteExact.decClock base))
                  have entryTime : limit - 1 ≤ entry.clock := by
                    simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv_clock,
                      WordSemStateFiniteExact.decClock, base]
                    omega
                  have entryRead0 : entry.getVar 0 = some (.loc equal1Location 2) := by
                    simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                      sptFromList2, sptLookup_sptInsert_ne,  sptLookup]
                  have entryRead2 : entry.getVar 2 = some (.word v1) := by
                    simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                      sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                  have entryRead4 : entry.getVar 4 = some (.word v2) := by
                    simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                      sptFromList2,  sptLookup_sptInsert_same]
                  have entrySize : saneLocalsSize entry := by
                    left
                    rfl
                  obtain ⟨headCk, headPerm, headPeak, headEval, headStack, headTime⟩ :=
                    (ih (limit - 1) (by omega)).1 conf store domain memory (clock - 1) v1 v2 entry
                      equal1Location 2 headResult headRemaining headClock ⟨headRun,
                        by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                          WordSemStateFiniteExact.decClock, base] using dom,
                        by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                          WordSemStateFiniteExact.decClock, base] using mem,
                        by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                          WordSemStateFiniteExact.decClock, base] using storeEq,
                        entryTime, shift,
                        by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                          WordSemStateFiniteExact.decClock, base] using code,
                        by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                          WordSemStateFiniteExact.decClock, base] using code1,
                        by simpa [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                          WordSemStateFiniteExact.decClock, base] using codeCmp,
                        entryRead0, entryRead2, entryRead4, lenNe, lenLt, entrySize, good⟩
                  obtain ⟨perm, envEq⟩ : ∃ perm, wordSemEnvToList (.ln : Spt (WordLocW width)) base.permute = ([], perm) := by
                    cases e : wordSemEnvToList (.ln : Spt (WordLocW width)) base.permute with
                    | mk entries perm =>
                      have nil : entries = [] := by simpa [e] using emptyEnvToList (width := width) base.permute
                      exact ⟨perm, by simp [nil] at e ⊢⟩
                  have savedRound : sptFromAList (sptToAList saved) = saved := by
                    exact equal1_saved_roundtrip base.locals
                  let returned := {entry with
                    clock := headCk
                    permute := headPerm
                    stackMax := headPeak
                    locals := .ln
                    localsSize := some 0}
                  let restored := {returned with locals := saved, stack := base.stack, localsSize := base.localsSize}
                  have headCkLe : headCk ≤ entry.clock := by
                    have hc := WordSemStateFiniteExact.evaluate_clock (equalCode conf) entry _ _ headEval
                    exact hc.1
                  have fixed : entry.fixClock (WordSemStateFiniteExact.evaluate (equalCode conf) entry) =
                      (some (.result (.loc equal1Location 2) [.word headResult]), returned) := by
                    rw [headEval]
                    simp [WordSemStateFiniteExact.fixClock, returned, Nat.not_lt_of_ge headCkLe]
                  have pop : WordSemStateFiniteExact.popEnv returned = some restored := by
                    simp only [returned, restored, entry, WordSemStateFiniteExact.callEnv,
                      WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.popEnv, envEq,
                      WordSemStateFiniteExact.decClock]
                    rw [savedRound]
                    simp [sptFromAList, sptUnion]
                  have saved0 : sptLookup 0 saved = some (.loc loc1 loc2) := by
                    simp [saved, sptLookup_sptInterCases, sptListInsert, sptLookup_sptInsert_ne,
                       sptLookup, base0]
                  have saved2 : sptLookup 2 saved = some (.word count) := by
                    simp [saved, sptLookup_sptInterCases, sptListInsert, sptLookup_sptInsert_ne,
                      sptLookup_sptInsert_same,  base2]
                  have saved4 : sptLookup 4 saved = some (.word a1) := by
                    simp [saved, sptLookup_sptInterCases, sptListInsert, sptLookup_sptInsert_ne,
                      sptLookup_sptInsert_same,  base4]
                  have saved6 : sptLookup 6 saved = some (.word a2) := by
                    simp [saved, sptLookup_sptInterCases, sptListInsert, 
                      sptLookup_sptInsert_same,  base6]
                  have domainEq : sptDomainEqUnion restored.locals saved (.ln : Spt (WordLocW width)) := by
                    intro key
                    simp [restored]
                  have baseRead1 : base.getVar 1 = some (.word v1) := by
                    simp [base, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                  have baseRead3 : base.getVar 3 = some (.word v2) := by
                    simp [base, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
                  have namesNonempty : ¬ sptDomainEmpty (sptListInsert [0, 2, 4, 6] .ln) := by
                    intro empty
                    apply empty 0
                    simp [sptListInsert, sptMem_sptInsert]
                  have clockNotLt : ¬ entry.clock < headCk := Nat.not_lt_of_ge headCkLe
                  dsimp only [entry] at clockNotLt
                  have popExpanded := pop
                  dsimp only [returned, entry] at popExpanded
                  have headEvalExpanded := headEval
                  dsimp only [entry] at headEvalExpanded
                  have callEval : WordSemStateFiniteExact.evaluate
                      (.call (some ([5], (sptListInsert [0, 2, 4, 6] .ln, .ln), .skip, equal1Location, 2))
                        (some equalLocation) [1, 3] none) base =
                      (none, restored.setVar 5 (.word headResult)) := by
                    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
                      baseRead1, baseRead3, wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode,
                      show sptLookup equalLocation base.code = some (3, equalCode conf) by simpa [base] using code,
                      show sptLookup equalLocation base.stackSize = sptLookup equalLocation t.stackSize by rfl,
                      show base.clock ≠ 0 by simpa [base] using (Nat.ne_of_gt tClockPos), cut,
                      namesNonempty, headEvalExpanded,    WordSemStateFiniteExact.setVars,
                      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock]
                    rw [headEvalExpanded]
                    simp [  clockNotLt,   
                      ]
                    rw [if_neg clockNotLt]
                    rw [popExpanded]
                    simp [domainEq,  
                      LoopSemStateFiniteExact.sptAlistInsert]
                  have zeroRaw : (count == BitVec.ofNat width 0) = false := by
                    apply beq_eq_false_iff_ne.mpr
                    simpa using zero
                  have firstStep : WordSemStateFiniteExact.evaluate
                      (.ite .equal 2 (.imm (BitVec.ofNat width 0))
                        (.seq (.assign 2 (.const (BitVec.ofNat width 1))) (.return 0 [2])) .skip) t = (none, t) := by
                    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                      wordSemWordCmp, Encoders.Asm.wordCmpHOL, r2, zeroRaw]
                  have domainA1 : t.mdomain a1 = true := by
                    have : domain a1 ≠ false := by tauto
                    cases h : domain a1 <;> simp_all only
                  have domainA2 : t.mdomain a2 = true := by
                    have : domain a2 ≠ false := by tauto
                    cases h : domain a2 <;> simp_all only
                  have memoryA1 : t.memory a1 = .word v1 := by simpa [mem] using m1
                  have memoryA2 : t.memory a2 = .word v2 := by simpa [mem] using m2
                  have loadFirst : WordSemStateFiniteExact.evaluate (.assign 1 (.load (.var 4))) t =
                      (none, t.setVar 1 (.word v1)) := by
                    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                      WordSemStateFiniteExact.memLoad, r4, domainA1, memoryA1]
                  have loadSecond : WordSemStateFiniteExact.evaluate (.assign 3 (.load (.var 6)))
                      (t.setVar 1 (.word v1)) = (none, base) := by
                    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                      WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
                      WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, base,
                      show sptLookup 6 t.locals = some (.word a2) by simpa [WordSemStateFiniteExact.getVar] using r6,
                      domainA2, memoryA2]
                  let after := restored.setVar 5 (.word headResult)
                  have afterClock : after.clock ≤ base.clock := by
                    change headCk ≤ t.clock
                    have x : entry.clock = t.clock - 1 := by
                      simp [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv_clock,
                        WordSemStateFiniteExact.decClock, base]
                    omega
                  have afterDepth : after.termdep = base.termdep := by
                    simp [after, WordSemStateFiniteExact.setVar, restored, returned, entry,
                      WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                      WordSemStateFiniteExact.decClock, base]
                  have prefixEval : WordSemStateFiniteExact.evaluate equal1Code t =
                      WordSemStateFiniteExact.evaluate (wordListSeq [
                        .ite .equal 5 (.imm 1) .skip (.return 0 [5]),
                        .assign 2 (.op .sub [.var 2, .const 1]),
                        .assign 4 (.op .add [.var 4, .const (BitVec.ofNat width (width / 8))]),
                        .assign 6 (.op .add [.var 6, .const (BitVec.ofNat width (width / 8))]),
                        .call none (some equal1Location) [0, 2, 4, 6] none]) after := by
                    rw [show BitVec.ofNat width 0 = (0 : BitVec width) by rfl] at firstStep
                    rw [show BitVec.ofNat width 1 = (1 : BitVec width) by rfl] at firstStep
                    rw [equal1Code, wordListSeq]
                    rw [seqAfter _ _ _ _ firstStep (Nat.le_refl _) rfl]
                    rw [wordListSeq]
                    rw [seqAfter _ _ _ _ loadFirst (by simp [WordSemStateFiniteExact.setVar]) (by simp [WordSemStateFiniteExact.setVar])]
                    rw [wordListSeq]
                    rw [seqAfter _ _ _ _ loadSecond (by simp [base, WordSemStateFiniteExact.setVar]) (by simp [base, WordSemStateFiniteExact.setVar])]
                    rw [wordListSeq]
                    exact seqAfter _ _ _ _ callEval afterClock afterDepth
                  have headPeakBound : optionLe headPeak
                      (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack)
                        (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) := by
                    have maxBelow : optionLe
                        (Option.map₂ max (sptLookup equalLocation t.stackSize)
                          (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize)))
                        (DataSem.eqCodeStackMax clock t.stackSize) := by
                      unfold DataSem.eqCodeStackMax
                      cases hmax : Option.map₂ max (sptLookup equalLocation t.stackSize)
                          (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize)) with
                      | none => simp [optionLe]
                      | some value =>
                        simp only [Option.map_some, optionLe]
                        nlinarith
                    simp only [entry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                      WordSemStateFiniteExact.decClock, envEq, base, wordSemStackSize,
                      List.foldr_cons, wordSemStackSizeFrame, Nat.sub_add_cancel clockPos] at headStack
                    change optionLe headPeak
                      (Option.map₂ max
                        (wordSemOptionMax
                          (wordSemOptionMax t.stackMax (wordSemOptionAdd t.localsSize (wordSemStackSize t.stack)))
                          (wordSemOptionAdd (wordSemOptionAdd t.localsSize (wordSemStackSize t.stack))
                            (sptLookup equalLocation t.stackSize)))
                        (Option.map₂ (· + ·) (wordSemOptionAdd t.localsSize (wordSemStackSize t.stack))
                          (DataSem.eqCodeStackMax clock t.stackSize))) at headStack
                    have recurrence := eqCodeStackMax_sub1 (clock + 1) t.stackSize (by omega)
                    simp only [Nat.add_sub_cancel] at recurrence
                    rw [recurrence]
                    exact optionLe_trans _ _ _ ⟨headStack,
                      equalHeadStackBound t.stackMax (wordSemStackSize t.stack) t.localsSize
                        (sptLookup equalLocation t.stackSize) (sptLookup equal1Location t.stackSize)
                        (sptLookup compare1Location t.stackSize) (DataSem.eqCodeStackMax clock t.stackSize)
                        localSize maxBelow⟩
                  by_cases headOne : headResult = 1
                  · subst headResult
                    simp only [ne_eq, not_true_eq_false, ↓reduceIte] at run
                    by_cases exhausted : headRemaining = 0
                    · simp [exhausted] at run
                    · simp only [exhausted, ↓reduceIte] at run
                      have headBounds := (wordEq_boundsAux conf store domain memory (limit - 1)).1
                        (clock - 1) v1 v2 1 headRemaining headClock headRun
                      have headPositive : 0 < headRemaining := by omega
                      have headCkPositive : 0 < headCk := by omega
                      let tailBase := {restored with
                        locals := sptInsert 6 (.word (a2 + StackRemove.bytesInWord width))
                          (sptInsert 4 (.word (a1 + StackRemove.bytesInWord width))
                            (sptInsert 2 (.word (count - 1)) (sptInsert 5 (.word 1) restored.locals)))}
                      let tailEntry := WordSemStateFiniteExact.callEnv
                        [.loc loc1 loc2, .word (count - 1),
                          .word (a1 + StackRemove.bytesInWord width), .word (a2 + StackRemove.bytesInWord width)]
                        (sptLookup equal1Location t.stackSize) (WordSemStateFiniteExact.decClock tailBase)
                      have tailTime : headRemaining - 1 ≤ tailEntry.clock := by
                        change headRemaining - 1 ≤ headCk - 1
                        omega
                      have tailRead0 : tailEntry.getVar 0 = some (.loc loc1 loc2) := by
                        simp [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                          sptFromList2, sptLookup_sptInsert_ne,  sptLookup]
                      have tailRead2 : tailEntry.getVar 2 = some (.word (count - 1)) := by
                        simp [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                          sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                      have tailRead4 : tailEntry.getVar 4 = some (.word (a1 + StackRemove.bytesInWord width)) := by
                        simp [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                          sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                      have tailRead6 : tailEntry.getVar 6 = some (.word (a2 + StackRemove.bytesInWord width)) := by
                        simp [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
                          sptFromList2,  sptLookup_sptInsert_same]
                      have tailSize : saneLocalsSize tailEntry := by
                        right
                        rfl
                      obtain ⟨tailCk, tailPerm, tailPeak, tailEval, tailStack, tailBound⟩ :=
                        (ih (headRemaining - 1) (by omega)).2 conf store domain memory clock (count - 1)
                          (a1 + StackRemove.bytesInWord width) (a2 + StackRemove.bytesInWord width)
                          tailEntry loc1 loc2 res remaining remainingClock ⟨by simpa using run,
                            by simpa [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                              tailBase, restored, returned, entry, WordSemStateFiniteExact.pushEnv, base] using dom,
                            by simpa [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                              tailBase, restored, returned, entry, WordSemStateFiniteExact.pushEnv, base] using mem,
                            by simpa [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                              tailBase, restored, returned, entry, WordSemStateFiniteExact.pushEnv, base] using storeEq,
                            tailTime, shift,
                            by simpa [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                              tailBase, restored, returned, entry, WordSemStateFiniteExact.pushEnv, base] using code,
                            by simpa [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                              tailBase, restored, returned, entry, WordSemStateFiniteExact.pushEnv, base] using code1,
                            by simpa [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                              tailBase, restored, returned, entry, WordSemStateFiniteExact.pushEnv, base] using codeCmp,
                            tailRead0, tailRead2, tailRead4, tailRead6, tailSize, lenNe, lenLt, good⟩
                      have equal1Below : optionLe (sptLookup equal1Location t.stackSize)
                          (DataSem.eqCodeStackMax (clock + 1) t.stackSize) := by
                        have leftBound : optionLe (sptLookup equal1Location t.stackSize)
                            (Option.map₂ max (sptLookup equalLocation t.stackSize)
                              (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize))) := by
                          apply (optionLe_max_right _ _ _).2
                          right
                          exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
                        have rightBound : optionLe
                            (Option.map₂ max (sptLookup equalLocation t.stackSize)
                              (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize)))
                            (DataSem.eqCodeStackMax (clock + 1) t.stackSize) := by
                          unfold DataSem.eqCodeStackMax
                          cases hmax : Option.map₂ max (sptLookup equalLocation t.stackSize)
                              (Option.map₂ max (sptLookup equal1Location t.stackSize) (sptLookup compare1Location t.stackSize)) with
                          | none => simp [optionLe]
                          | some value =>
                            simp only [Option.map_some, optionLe]
                            nlinarith
                        exact optionLe_trans _ _ _ ⟨leftBound, rightBound⟩
                      have optMax (x y : Option Nat) : wordSemOptionMax x y = Option.map₂ max x y := by
                        cases x <;> cases y <;> rfl
                      have optAdd (x y : Option Nat) : wordSemOptionAdd x y = Option.map₂ (· + ·) x y := by
                        cases x <;> cases y <;> rfl
                      simp only [tailEntry, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
                        tailBase, restored, returned, entry, WordSemStateFiniteExact.pushEnv, envEq, base,
                        optMax, optAdd] at tailStack
                      have finalStack : optionLe tailPeak
                          (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack)
                            (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) := by
                        apply optionLe_trans _ _ _ ⟨tailStack, ?_⟩
                        exact equalTailStackBound t.stackMax (wordSemStackSize t.stack) headPeak
                          (sptLookup equal1Location t.stackSize) (DataSem.eqCodeStackMax (clock + 1) t.stackSize)
                          headPeakBound equal1Below
                      let after2 := after.setVar 2 (.word (count - 1))
                      let after4 := after2.setVar 4 (.word (a1 + StackRemove.bytesInWord width))
                      let after6 := after4.setVar 6 (.word (a2 + StackRemove.bytesInWord width))
                      have read5 : after.getVar 5 = some (.word (1 : BitVec width)) := by
                        simp [after, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_same]
                      have branchStep : WordSemStateFiniteExact.evaluate
                          (.ite .equal 5 (.imm 1) .skip (.return 0 [5])) after = (none, after) := by
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                          wordSemWordCmp, Encoders.Asm.wordCmpHOL, read5]
                      have read2After : after.getVar 2 = some (.word count) := by
                        simp [after, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          restored, sptLookup_sptInsert_ne, saved2]
                      have step2 : WordSemStateFiniteExact.evaluate (.assign 2 (.op .sub [.var 2, .const 1])) after =
                          (none, after2) := by
                        simp [after2, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          wordOpHOL, wordOp, theWords, read2After]
                      have read4After : after2.getVar 4 = some (.word a1) := by
                        simp [after2, after, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          restored, sptLookup_sptInsert_ne, saved4]
                      have step4 : WordSemStateFiniteExact.evaluate
                          (.assign 4 (.op .add [.var 4, .const (BitVec.ofNat width (width / 8))])) after2 =
                          (none, after4) := by
                        simp [after4, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          wordOpHOL, wordOp, theWords, read4After, StackRemove.bytesInWord]
                      have read6After : after4.getVar 6 = some (.word a2) := by
                        simp [after4, after2, after, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          restored, sptLookup_sptInsert_ne, saved6]
                      have step6 : WordSemStateFiniteExact.evaluate
                          (.assign 6 (.op .add [.var 6, .const (BitVec.ofNat width (width / 8))])) after4 =
                          (none, after6) := by
                        simp [after6, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
                          wordOpHOL, wordOp, theWords, read6After, StackRemove.bytesInWord]
                      have after6Eq : after6 = tailBase := by
                        rfl
                      have afterRead0 : after6.getVar 0 = some (.loc loc1 loc2) := by
                        simp [after6, after4, after2, after, WordSemStateFiniteExact.getVar,
                          WordSemStateFiniteExact.setVar, restored, sptLookup_sptInsert_ne, saved0]
                      have afterRead2 : after6.getVar 2 = some (.word (count - 1)) := by
                        simp [after6, after4, after2, WordSemStateFiniteExact.getVar,
                          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                      have afterRead4 : after6.getVar 4 = some (.word (a1 + StackRemove.bytesInWord width)) := by
                        simp [after6, after4, WordSemStateFiniteExact.getVar,
                          WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
                      have afterRead6 : after6.getVar 6 = some (.word (a2 + StackRemove.bytesInWord width)) := by
                        simp [after6, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                          sptLookup_sptInsert_same]
                      have tailEvalExpanded := tailEval
                      dsimp only [tailEntry] at tailEvalExpanded
                      rw [← show BitVec.ofNat width 1 = (1 : BitVec width) by rfl] at tailEvalExpanded
                      have tailCall : WordSemStateFiniteExact.evaluate
                          (.call none (some equal1Location) [0, 2, 4, 6] none) after6 =
                          (some (.result (.loc loc1 loc2) [.word res]),
                            {t with
                              clock := tailCk
                              locals := .ln
                              localsSize := some 0
                              permute := tailPerm
                              stackMax := tailPeak}) := by
                        have afterCode : sptLookup equal1Location after6.code = some (4, equal1Code) := by
                          simpa [after6, after4, after2, after, WordSemStateFiniteExact.setVar,
                            restored, returned, entry, WordSemStateFiniteExact.callEnv,
                            WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock, base] using code1
                        have afterSize : sptLookup equal1Location after6.stackSize = sptLookup equal1Location t.stackSize := by rfl
                        have afterClock : after6.clock ≠ 0 := by
                          simpa [after6, after4, after2, after, WordSemStateFiniteExact.setVar,
                            restored, returned] using (Nat.ne_of_gt headCkPositive)
                        simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVars,
                          afterRead0, afterRead2, afterRead4, afterRead6, wordSemBadDestArgs,
                          wordSemAddRetLoc, wordSemFindCode, afterCode, afterSize, afterClock]
                        rw [after6Eq]
                        rw [tailEvalExpanded]
                        simp [wordSemBadFunReturn,  WordSemStateFiniteExact.callEnv,
                          WordSemStateFiniteExact.decClock, tailBase, restored, returned, entry,
                          WordSemStateFiniteExact.pushEnv, base]
                      refine ⟨tailCk, tailPerm, tailPeak, ?_, finalStack, tailBound⟩
                      rw [prefixEval, wordListSeq]
                      rw [seqAfter _ _ _ _ branchStep (Nat.le_refl _) rfl]
                      rw [wordListSeq]
                      rw [seqAfter _ _ _ _ step2 (by simp [after2, WordSemStateFiniteExact.setVar])
                        (by simp [after2, WordSemStateFiniteExact.setVar])]
                      rw [wordListSeq]
                      rw [seqAfter _ _ _ _ step4 (by simp [after4, WordSemStateFiniteExact.setVar])
                        (by simp [after4, WordSemStateFiniteExact.setVar])]
                      rw [wordListSeq]
                      rw [seqAfter _ _ _ _ step6 (by simp [after6, WordSemStateFiniteExact.setVar])
                        (by simp [after6, WordSemStateFiniteExact.setVar])]
                      simpa [wordListSeq] using tailCall
                  · have headOneRaw : headResult ≠ BitVec.ofNat width 1 := by simpa using headOne
                    simp [headOneRaw] at run
                    obtain ⟨rfl, rfl, _⟩ := run
                    have cmp : (headResult == BitVec.ofNat width 1) = false := beq_eq_false_iff_ne.mpr headOneRaw
                    have retStep : WordSemStateFiniteExact.evaluate
                        (.ite .equal 5 (.imm 1) .skip (.return 0 [5])) after =
                        (some (.result (.loc loc1 loc2) [.word headResult]),
                          {after with locals := .ln, localsSize := some 0}) := by
                      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
                        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
                        WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.setVar,
                        wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_ne,
                        sptLookup_sptInsert_same, after, restored, saved0, cmp]
                    refine ⟨headCk, headPerm, headPeak, ?_, ?_, headTime⟩
                    · rw [prefixEval, wordListSeq]
                      rw [seqResult _ _ _ _ _ retStep (by simp) (by simp)]
                      simp [after, WordSemStateFiniteExact.setVar, restored, returned, entry,
                        WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                        WordSemStateFiniteExact.decClock, base]
                    · exact headPeakBound
  constructor
  · intro conf store domain memory limit clock v1 v2 t loc1 loc2 res remaining remainingClock h
    exact (aux limit).1 conf store domain memory clock v1 v2 t loc1 loc2 res remaining remainingClock h
  · intro conf store domain memory limit clock count a1 a2 t loc1 loc2 res remaining remainingClock h
    exact (aux limit).2 conf store domain memory clock count a1 a2 t loc1 loc2 res remaining remainingClock h

/-- The equality stub implements word equality with its declared local-size bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "Equal_code_thm"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store, store])
  (words_as_type_indexed_bitvec)]
theorem equalCode_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (limit clock : Nat) (v1 v2 : BitVec width) (t : WordSemStateFiniteExact width C F)
    (loc1 loc2 : Nat) (res : BitVec width) (remaining remainingClock : Nat)
    (h : wordEq conf store domain memory limit clock v1 v2 = some (res, remaining, remainingClock) ∧
      domain = t.mdomain ∧ memory = t.memory ∧ store = t.store ∧ limit ≤ t.clock ∧ shiftLength conf < width ∧
      t.localsSize = sptLookup equalLocation t.stackSize ∧
      sptLookup equalLocation t.code = some (3, equalCode conf) ∧
      sptLookup equal1Location t.code = some (4, equal1Code) ∧
      sptLookup compare1Location t.code = some (4, compare1Code) ∧
      t.getVar 0 = some (.loc loc1 loc2) ∧ t.getVar 2 = some (.word v1) ∧ t.getVar 4 = some (.word v2) ∧
      conf.lenSize ≠ 0 ∧ conf.lenSize < width ∧ goodDimindex width) :
    ∃ ck newP smx, WordSemStateFiniteExact.evaluate (equalCode conf) t =
      (some (.result (.loc loc1 loc2) [.word res]),
        {t with clock := ck, locals := .ln, localsSize := some 0, permute := newP, stackMax := smx}) ∧
      optionLe smx (Option.map₂ max t.stackMax
        (Option.map₂ (· + ·) (wordSemStackSize t.stack) (DataSem.eqCodeStackMax (clock + 1) t.stackSize))) ∧
      remaining ≤ ck := by
  obtain ⟨run, dom, mem, storeEq, time, shift, size, code, code1, codeCmp, r0, r2, r4,
    lenNe, lenLt, good⟩ := h
  exact (equalCodeLemma (C := C) (F := F)).1 conf store domain memory limit clock v1 v2 t loc1 loc2
    res remaining remainingClock ⟨run, dom, mem, storeEq, time, shift, code, code1, codeCmp,
      r0, r2, r4, lenNe, lenLt, Or.inl size, good⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
