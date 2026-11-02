import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SimpleEquality
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CompareLoop
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeaderInjective

/-! Word-level equality model from the data-to-word memory proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- The header reader's finite store argument has the canonical lookup codec. -/
theorem holFmapAsFiniteSupportParamWitness_wordHeader_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/-- Decode a pointer and read its in-domain word header. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_header_def"
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
def wordHeader {addressWidth : Nat} {valueWidth : Nat} [NeZero addressWidth] [NeZero valueWidth] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW addressWidth)) (address : BitVec addressWidth)
    (domain : BitVec addressWidth → Bool) (memory : BitVec addressWidth → WordLocW valueWidth) :
    Option (BitVec addressWidth × BitVec valueWidth) := do
  let real ← getRealAddr conf store address
  if domain real then
    match memory real with
    | .word header => some (real, header)
    | .loc .. => none
  else none

/-- Clamp both remaining clocks of a successful result to their input bounds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "fix_clock_def"]
def fixClock {α : Type} (clock limit : Nat) : Option (α × Nat × Nat) → Option (α × Nat × Nat)
  | none => none
  | some (value, remaining, remainingClock) =>
    some (value, if limit < remaining then limit else remaining,
      if clock < remainingClock then clock else remainingClock)

/-- A successful clamped result stays within both input bounds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "fix_clock_IMP"]
theorem fixClock_imp {α : Type} (clock limit : Nat) (x : Option (α × Nat × Nat))
    (value : α) (remaining remainingClock : Nat)
    (h : fixClock clock limit x = some (value, remaining, remainingClock)) :
    remainingClock ≤ clock ∧ remaining ≤ limit := by
  cases x with
  | none => simp [fixClock] at h
  | some result =>
    rcases result with ⟨v, l, ck⟩
    simp only [fixClock, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl, rfl⟩
    split <;> split <;> omega

/-- Recognize the two source closure tags in a word header. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_is_clos_def"
  (words_as_type_indexed_bitvec)]
def wordIsClos {width : Nat} [NeZero width] (conf : Config) (header : BitVec width) : Prop :=
  let mask := holWordSlice (width - conf.lenSize - 1) 2 (~~~(0 : BitVec width)) ||| 2
  (header &&& mask) = BitVec.ofNat width (16 * 30 + 2) ∨
    (header &&& mask) = BitVec.ofNat width (16 * 31 + 2)

instance {width : Nat} [NeZero width] (conf : Config) (header : BitVec width) :
    Decidable (wordIsClos conf header) := by
  unfold wordIsClos
  infer_instance

/-- A related pointer names a closure exactly when its stored header has a closure tag. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_isClos"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_isClos {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (w a header : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, .word w) :: vars) ∧
      w.getLsbD 0 = true ∧ getRealAddr conf store w = some a ∧ memory a = .word header ∧ goodDimindex width →
    (Flapjack.Compiler.Backend.DataSem.isClosure tag values ↔ wordIsClos conf header) := by
  rintro ⟨rel, low, addr, contents, good⟩
  obtain ⟨w', weq, cases⟩ := memoryRel_blockImp conf bigEndian next refs space store memory domain
    stamp tag values (.word w) vars ⟨rel, good⟩
  have ww : w' = w := by cases weq; rfl
  subst w'
  have nonempty : values ≠ [] := by
    intro empty
    simp only [empty, ↓reduceIte] at cases
    rw [low] at cases
    exact Bool.noConfusion cases.2.1
  simp only [nonempty, ↓reduceIte] at cases
  obtain ⟨a', h', _, _, _, addr', contents', _, _, _, encoded, _⟩ := cases
  have aa : a' = a := Option.some.inj (addr'.symm.trans addr)
  subst a'
  have hh : h' = header := WordLocW.word.inj (contents'.symm.trans contents)
  subst h'
  obtain ⟨bound, mask⟩ := encodeHeader_tagMask conf tag values.length header encoded good
  have range : 16 * tag + 2 < 2 ^ width := by
    rcases good with hw | hw <;> subst width <;> norm_num at bound ⊢ <;> omega
  have c30 : 16 * 30 + 2 < 2 ^ width := by
    rcases good with hw | hw <;> subst width <;> norm_num
  have c31 : 16 * 31 + 2 < 2 ^ width := by
    rcases good with hw | hw <;> subst width <;> norm_num
  simp only [Flapjack.Compiler.Backend.DataSem.isClosure, wordIsClos, mask]
  constructor
  · rintro ⟨(rfl | rfl), _⟩ <;> simp
  · rintro (h | h)
    · refine ⟨Or.inl ?_, nonempty⟩
      have h' := congrArg BitVec.toNat h
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt range, Nat.mod_eq_of_lt c30] at h'
      omega
    · refine ⟨Or.inr ?_, nonempty⟩
      have h' := congrArg BitVec.toNat h
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt range, Nat.mod_eq_of_lt c31] at h'
      omega


/-- The word comparator's finite store argument has the canonical lookup codec. -/
theorem holFmapAsFiniteSupportParamWitness_wordEq_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/-- The list comparator's finite store argument has the canonical lookup codec. -/
theorem holFmapAsFiniteSupportParamWitness_wordEqList_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/- Word equality and its list worker, with the source's explicit recursion
and stack clocks. -/
mutual

/-- Source word-equality evaluator, with both resource clocks. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_def" 13982
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
def wordEq {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (limit clock : Nat) (w1 w2 : BitVec width) : Option (BitVec width × Nat × Nat) :=
  if w1 = w2 then some (1, limit, clock)
  else if !(w1.getLsbD 0 && w2.getLsbD 0) then some (0, limit, clock)
  else match wordHeader conf store w1 domain memory, wordHeader conf store w2 domain memory with
    | some (a1, h1), some (a2, h2) =>
      if h1 &&& 12 = 0 then
        if wordIsClos conf h1 then some (1, limit, clock)
        else if h1 ≠ h2 then some (0, limit, clock)
        else if limit = 0 then none
        else wordEqList conf store domain memory (limit - 1) clock (WordGcFunctions.decodeLength conf h1)
          (a1 + StackRemove.bytesInWord width) (a2 + StackRemove.bytesInWord width)
      else if h1 ≠ h2 then some (0, limit, clock)
      else if !h1.getLsbD 2 then some (0, limit, clock)
      else if !h1.getLsbD 3 && h1.getLsbD 4 then some (0, limit, clock)
      else if limit ≤ (WordGcFunctions.decodeLength conf h1).toNat then none
      else match wordCmpLoop (WordGcFunctions.decodeLength conf h1)
          (a1 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h1)
          (a2 + StackRemove.bytesInWord width * WordGcFunctions.decodeLength conf h1) domain memory with
        | none => none
        | some res => some (res, limit - 1 - (WordGcFunctions.decodeLength conf h1).toNat, clock)
    | _, _ => none
termination_by limit
decreasing_by omega

/-- Source word-list equality worker, including clock clamping. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_def" 13982
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
def wordEqList {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (limit clock : Nat) (count a1 a2 : BitVec width) : Option (BitVec width × Nat × Nat) :=
  if count = 0 then some (1, limit, clock)
  else if domain a1 = false ∨ domain a2 = false ∨ limit = 0 ∨ clock = 0 then none
  else match memory a1, memory a2 with
    | .word w1, .word w2 =>
      match _resultEq : fixClock (clock - 1) (limit - 1)
          (wordEq conf store domain memory (limit - 1) (clock - 1) w1 w2) with
      | none => none
      | some (x, remaining, _) =>
        if x ≠ 1 then some (x, remaining, clock)
        else if remaining = 0 then none
        else wordEqList conf store domain memory (remaining - 1) clock (count - 1)
          (a1 + StackRemove.bytesInWord width) (a2 + StackRemove.bytesInWord width)
    | _, _ => none
termination_by limit
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have bounds := fixClock_imp _ _ _ _ _ _ _resultEq
  omega

end

/-- Both word-comparison workers return clocks bounded by their inputs. This
Flapjack helper groups the two source conjuncts at a fixed initial limit. -/
theorem wordEq_boundsAux {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width) (limit : Nat) :
    (∀ clock w1 w2 result remaining remainingClock,
      wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) →
      remaining ≤ limit ∧ remainingClock ≤ clock) ∧
    (∀ clock count a1 a2 result remaining remainingClock,
      wordEqList conf store domain memory limit clock count a1 a2 = some (result, remaining, remainingClock) →
      remaining ≤ limit ∧ remainingClock ≤ clock) := by
  induction limit using Nat.strong_induction_on with
  | h limit ih =>
    constructor
    · intro clock w1 w2 result remaining remainingClock outcome
      rw [wordEq] at outcome
      repeat' first | split at outcome | contradiction
      all_goals try simp_all
      all_goals try omega
      have bounded := (ih (limit - 1) (by omega)).2 _ _ _ _ _ _ _ outcome
      omega
    · intro clock count a1 a2 result remaining remainingClock outcome
      rw [wordEqList] at outcome
      repeat' first | split at outcome | contradiction
      all_goals try simp_all
      all_goals have clamp := @fixClock_imp (BitVec width)
      all_goals try grind
      have resultBound := (ih _ ?_).2 _ _ _ _ _ _ _ outcome
      · grind
      · grind

/-- Neither word equality nor its list worker increases either clock. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_LESS_EQ"
  (fmap_as_finite_support_relation := [store1, store2]) (words_as_type_indexed_bitvec)]
theorem wordEq_lessEq {width : Nat} [NeZero width] :
    (∀ (conf : Config) (store1 : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (limit clock : Nat) (w1 w2 result : BitVec width) (remaining remainingClock : Nat),
      wordEq conf store1 domain memory limit clock w1 w2 = some (result, remaining, remainingClock) →
      remaining ≤ limit ∧ remainingClock ≤ clock) ∧
    (∀ (conf : Config) (store2 : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (limit clock : Nat) (count a1 a2 result : BitVec width) (remaining remainingClock : Nat),
      wordEqList conf store2 domain memory limit clock count a1 a2 = some (result, remaining, remainingClock) →
      remaining ≤ limit ∧ remainingClock ≤ clock) := by
  constructor
  · intro conf store domain memory limit clock w1 w2 result remaining remainingClock outcome
    exact (wordEq_boundsAux conf store domain memory limit).1 clock w1 w2 result remaining remainingClock outcome
  · intro conf store domain memory limit clock count a1 a2 result remaining remainingClock outcome
    exact (wordEq_boundsAux conf store domain memory limit).2 clock count a1 a2 result remaining remainingClock outcome

/-- The clamp theorem's finite store argument has the canonical lookup codec. -/
theorem holFmapAsFiniteSupportParamWitness_fixClock_wordEq_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/-- The source clock clamp does not change a word-equality result. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "fix_clock_word_eq"
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
theorem fixClock_wordEq {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (limit clock : Nat) (w1 w2 : BitVec width) :
    fixClock clock limit (wordEq conf store domain memory limit clock w1 w2) =
      wordEq conf store domain memory limit clock w1 w2 := by
  cases outcome : wordEq conf store domain memory limit clock w1 w2 with
  | none => simp [fixClock]
  | some triple =>
    rcases triple with ⟨result, remaining, remainingClock⟩
    have bounds := (wordEq_boundsAux conf store domain memory limit).1 clock w1 w2 result remaining remainingClock outcome
    have limitNotLt : ¬ limit < remaining := by omega
    have clockNotLt : ¬ clock < remainingClock := by omega
    simp [fixClock, limitNotLt, clockNotLt]

/-- The rebound list equation's finite store has the canonical lookup codec. -/
theorem holFmapAsFiniteSupportParamWitness_wordEqList_unclamped_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/-- Unclamped equation for the list worker, justified by the clock bounds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_def" 14055
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqList_unclamped {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (limit clock : Nat) (count a1 a2 : BitVec width) :
    wordEqList conf store domain memory limit clock count a1 a2 =
      if count = 0 then some (1, limit, clock)
      else if domain a1 = false ∨ domain a2 = false ∨ limit = 0 ∨ clock = 0 then none
      else match memory a1, memory a2 with
        | .word w1, .word w2 =>
          match wordEq conf store domain memory (limit - 1) (clock - 1) w1 w2 with
          | none => none
          | some (x, remaining, _) =>
            if x ≠ 1 then some (x, remaining, clock)
            else if remaining = 0 then none
            else wordEqList conf store domain memory (remaining - 1) clock (count - 1)
              (a1 + StackRemove.bytesInWord width) (a2 + StackRemove.bytesInWord width)
        | _, _ => none := by
  rw [wordEqList]
  by_cases zero : count = 0
  · simp [zero]
  · simp only [zero, ↓reduceIte]
    by_cases invalid : domain a1 = false ∨ domain a2 = false ∨ limit = 0 ∨ clock = 0
    · simp [invalid]
    · simp only [invalid, ↓reduceIte]
      cases mem1 : memory a1 with
      | loc p q => rfl
      | word w1 =>
        cases mem2 : memory a2 with
        | loc p q => rfl
        | word w2 =>
          have clamp := fixClock_wordEq conf store domain memory (limit - 1) (clock - 1) w1 w2
          repeat' first | split | contradiction
          all_goals simp_all


/-- Clock extension for both equality workers at a fixed limit. This is
Flapjack induction infrastructure for the original clock theorem. -/
theorem wordEq_addClockAux {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width) (limit : Nat) :
    (∀ clock w1 w2 result remaining remainingClock extra,
      wordEq conf store domain memory limit clock w1 w2 = some (result, remaining, remainingClock) →
      wordEq conf store domain memory limit (clock + extra) w1 w2 = some (result, remaining, remainingClock + extra)) ∧
    (∀ clock count a1 a2 result remaining remainingClock extra,
      wordEqList conf store domain memory limit clock count a1 a2 = some (result, remaining, remainingClock) →
      wordEqList conf store domain memory limit (clock + extra) count a1 a2 = some (result, remaining, remainingClock + extra)) := by
  induction limit using Nat.strong_induction_on with
  | h limit ih =>
    constructor
    · intro clock w1 w2 result remaining remainingClock extra outcome
      rw [wordEq] at outcome ⊢
      repeat' first | split at outcome | contradiction
      all_goals try simp_all
      all_goals try (exact (ih (limit - 1) (by omega)).2 _ _ _ _ _ _ _ _ outcome)
      all_goals try grind
    · intro clock count a1 a2 result remaining remainingClock extra outcome
      by_cases zero : count = 0
      · simp [wordEqList_unclamped, zero] at outcome ⊢
        omega
      · have positive : 0 < limit ∧ 0 < clock := by
          by_contra missing
          have invalid : domain a1 = false ∨ domain a2 = false ∨ limit = 0 ∨ clock = 0 := by omega
          rw [wordEqList_unclamped] at outcome
          simp [invalid] at outcome
          exact zero outcome.1
        have shifted : clock + extra - 1 = (clock - 1) + extra := by omega
        rw [wordEqList_unclamped] at outcome ⊢
        repeat' first | split at outcome | contradiction
        all_goals try simp_all
        all_goals have step := (ih (limit - 1) (by omega)).1 _ _ _ _ _ _ extra (by assumption)
        all_goals simp only [step]
        all_goals try simp_all
        have bound := (wordEq_boundsAux conf store domain memory (limit - 1)).1 _ _ _ _ _ _ (by assumption)
        exact (ih _ (by omega)).2 _ _ _ _ _ _ _ extra outcome

/-- Supplying additional stack clock preserves successful results and adds
that amount to the remaining stack clock. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_add_clock"
  (fmap_as_finite_support_relation := [store1, store2]) (words_as_type_indexed_bitvec)]
theorem wordEq_addClock {width : Nat} [NeZero width] :
    (∀ (conf : Config) (store1 : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (limit clock : Nat) (w1 w2 result : BitVec width) (remaining remainingClock extra : Nat),
      wordEq conf store1 domain memory limit clock w1 w2 = some (result, remaining, remainingClock) →
      wordEq conf store1 domain memory limit (clock + extra) w1 w2 = some (result, remaining, remainingClock + extra)) ∧
    (∀ (conf : Config) (store2 : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (limit clock : Nat) (count a1 a2 result : BitVec width) (remaining remainingClock extra : Nat),
      wordEqList conf store2 domain memory limit clock count a1 a2 = some (result, remaining, remainingClock) →
      wordEqList conf store2 domain memory limit (clock + extra) count a1 a2 = some (result, remaining, remainingClock + extra)) := by
  constructor
  · intro conf store domain memory limit clock w1 w2 result remaining remainingClock extra outcome
    exact (wordEq_addClockAux conf store domain memory limit).1 clock w1 w2 result remaining remainingClock extra outcome
  · intro conf store domain memory limit clock count a1 a2 result remaining remainingClock extra outcome
    exact (wordEq_addClockAux conf store domain memory limit).2 clock count a1 a2 result remaining remainingClock extra outcome

/-- Raising the stack clock to a maximum preserves the result and adjusts the
remaining clock by the same increase. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_max_clock"
  (fmap_as_finite_support_relation := [store1, store2]) (words_as_type_indexed_bitvec)]
theorem wordEq_maxClock {width : Nat} [NeZero width] :
    (∀ (conf : Config) (store1 : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (limit clock : Nat) (w1 w2 result : BitVec width) (remaining remainingClock extra : Nat),
      wordEq conf store1 domain memory limit clock w1 w2 = some (result, remaining, remainingClock) →
      wordEq conf store1 domain memory limit (max clock extra) w1 w2 =
        some (result, remaining, remainingClock + (extra - clock))) ∧
    (∀ (conf : Config) (store2 : HolFiniteMapExact WordStoreHOL (WordLocW width))
      (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
      (limit clock : Nat) (count a1 a2 result : BitVec width) (remaining remainingClock extra : Nat),
      wordEqList conf store2 domain memory limit clock count a1 a2 = some (result, remaining, remainingClock) →
      wordEqList conf store2 domain memory limit (max clock extra) count a1 a2 =
        some (result, remaining, remainingClock + (extra - clock))) := by
  constructor
  · intro conf store domain memory limit clock w1 w2 result remaining remainingClock extra outcome
    have extended := (wordEq_addClockAux conf store domain memory limit).1
      clock w1 w2 result remaining remainingClock (extra - clock) outcome
    have clockEq : clock + (extra - clock) = max clock extra := by omega
    simpa only [clockEq] using extended
  · intro conf store domain memory limit clock count a1 a2 result remaining remainingClock extra outcome
    have extended := (wordEq_addClockAux conf store domain memory limit).2
      clock count a1 a2 result remaining remainingClock (extra - clock) outcome
    have clockEq : clock + (extra - clock) = max clock extra := by omega
    simpa only [clockEq] using extended

/-- The min/max clock theorem's finite store has the canonical lookup codec. -/
theorem holFmapAsFiniteSupportParamWitness_wordEq_minMaxClock_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/-- Increasing either input to the minimum clock preserves a successful word
or word-list comparison. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_min_max_clock"
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
theorem wordEq_minMaxClock {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (limit a b : Nat) (a1 a2 result : BitVec width) (remaining remainingClock : Nat) (count : BitVec width) :
    (∀ x y : Nat, wordEq conf store domain memory limit (min a b) a1 a2 = some (result, remaining, remainingClock) →
      ∃ finalClock, wordEq conf store domain memory limit (min (max a x) (max b y)) a1 a2 =
        some (result, remaining, finalClock)) ∧
    (∀ x y : Nat, wordEqList conf store domain memory limit (min a b) count a1 a2 = some (result, remaining, remainingClock) →
      ∃ finalClock, wordEqList conf store domain memory limit (min (max a x) (max b y)) count a1 a2 =
        some (result, remaining, finalClock)) := by
  constructor
  · intro x y outcome
    let base := min a b
    let target := min (max a x) (max b y)
    have le : base ≤ target := by dsimp [base, target]; omega
    have clockEq : base + (target - base) = target := by omega
    refine ⟨remainingClock + (target - base), ?_⟩
    have extended := (wordEq_addClockAux conf store domain memory limit).1
      base a1 a2 result remaining remainingClock (target - base) outcome
    simpa only [clockEq] using extended
  · intro x y outcome
    let base := min a b
    let target := min (max a x) (max b y)
    have le : base ≤ target := by dsimp [base, target]; omega
    have clockEq : base + (target - base) = target := by omega
    refine ⟨remainingClock + (target - base), ?_⟩
    have extended := (wordEq_addClockAux conf store domain memory limit).2
      base count a1 a2 result remaining remainingClock (target - base) outcome
    simpa only [clockEq] using extended

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
