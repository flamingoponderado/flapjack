module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.DataSem.Value
public import Flapjack.Compiler.Backend.Semantics.DataSem.Build
public import Flapjack.Compiler.Backend.DataToWord.Header
public import Flapjack.Compiler.Backend.BackendProps
public import Flapjack.Compiler.Backend.WordDepth
public import Flapjack.Misc.Alignment
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Misc.Sptree.InsertUnchanged
public import Mathlib.Tactic.Ring
public import Flapjack.Compiler.Backend.StackRemove.Proofs.WordAddressArithmetic

@[expose] public section

/-!
# Small lemmas of `data_to_word_assignProofScript.sml`

The list, arithmetic, word and sparse-tree lemmas that the assignment proof
states before and between its per-operation simulations. HOL word `<`/`<=`
are the signed `word_lt`/`word_le` (`BitVec.slt`/`sle`); `w ' 0` and
`word_bit 0 w` are `w.getLsbD 0`; `LEAST x. x ∉ domain refs` is the data
semantics' `leastUnusedRef`; `Num (ABS i)` is `Int.natAbs i`; HOL `BIT i n`
is `Nat.testBit n i`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth

namespace BasicLemmasWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end BasicLemmasWitness

/-- A successful one-value data read had exactly one name. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_vars_SING"]
theorem getVars_sing {α : Type} (args : List Nat) (s : Spt α) (w : α)
    (h : DataSem.getVars args s = some [w]) : ∃ y, args = [y] := by
  match args, h with
  | [y], _ => exact ⟨y, rfl⟩
  | [], h => simp [DataSem.getVars] at h
  | _ :: _ :: rest, h =>
    simp only [DataSem.getVars, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, _, _, ⟨_, _, _, _, rfl⟩, h⟩ := h
    simp at h

/-- Pushing a function through a conditional, in argument and function
position; the two conjuncts have independent types. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "push_if"]
theorem pushIf {α β γ δ : Type} :
    (∀ (f : α → β) (x y : α) (b : Bool), (if b then f x else f y) = f (if b then x else y)) ∧
      ∀ (f h : γ → δ) (x : γ) (b : Bool), (if b then f x else h x) = (if b then f else h) x := by
  constructor <;> intros <;> split <;> rfl

/-- Splitting a conditional application into function and argument parts. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "split_if"]
theorem splitIf {α β : Type} (b : Bool) (f h : β → α) (x y : β) :
    (if b then f x else h y) = (if b then f else h) (if b then x else y) := by
  split <;> rfl

/-- A successful cut keeps exactly the cutting set's domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "cut_env_IMP_domain"]
theorem cutNames_domain {α β : Type} (x : Spt β) (y t : Spt α)
    (h : wordSemCutNames x y = some t) : sptDomain t = sptDomain x := by
  unfold wordSemCutNames at h
  split at h <;> simp at h
  subst h
  rw [sptDomain_sptInter]
  funext k
  rename_i hs
  simp only [LoopSemStateFiniteExact.sptSubsetLive, sptMem] at hs
  exact propext ⟨fun h => h.2, fun h => ⟨hs k h, h⟩⟩

/-- Inserting a list of keys adds exactly those keys to the domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "domain_list_insert_thm"]
theorem domain_listInsert :
    ∀ (l : List Nat) (names : NumSet),
      sptDomain (sptListInsert l names) = fun k => k ∈ l ∨ sptDomain names k := by
  intro l
  induction l with
  | nil => intro names; funext k; simp [sptListInsert]
  | cons x xs ih =>
    intro names
    funext k
    rw [sptListInsert, ih]
    by_cases hk : k = x
    · subst hk; simp [sptDomain, sptLookup_sptInsert_same]
    · simp [sptDomain, sptLookup_sptInsert_ne x k () names hk, hk]

/-- Signed strict comparison is the negation of the reversed signed
non-strict comparison. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_less_lemma1"
  (words_as_type_indexed_bitvec)]
theorem wordLessLemma1 {width : Nat} [NeZero width] (v1 v2 : BitVec width) :
    v2.slt v1 = true ↔ ¬ v1.sle v2 = true := by
  simp [BitVec.slt, BitVec.sle]

/-- A two-name successful read reads each name. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_vars_2_imp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars2Imp {width : Nat} [NeZero width] {C F : Type} (x1 x2 : Nat)
    (s : WordSemStateFiniteExact width C F) (y1 y2 : WordLocW width)
    (h : WordSemStateFiniteExact.getVars [x1, x2] s = some [y1, y2]) :
    WordSemStateFiniteExact.getVar x1 s = some y1 ∧ WordSemStateFiniteExact.getVar x2 s = some y2 := by
  cases h1 : WordSemStateFiniteExact.getVar x1 s <;>
    cases h2 : WordSemStateFiniteExact.getVar x2 s <;>
    simp_all [WordSemStateFiniteExact.getVars]

/-- A one-name successful read reads that name. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "get_vars_1_imp"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVars1Imp {width : Nat} [NeZero width] {C F : Type} (x1 : Nat)
    (s : WordSemStateFiniteExact width C F) (y1 : WordLocW width)
    (h : WordSemStateFiniteExact.getVars [x1] s = some [y1]) :
    WordSemStateFiniteExact.getVar x1 s = some y1 := by
  cases h1 : WordSemStateFiniteExact.getVar x1 s <;> simp_all [WordSemStateFiniteExact.getVars]

/-- Sixteen times an index below `k / 16`, plus two, stays below `k`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "LESS_DIV_16_IMP"]
theorem lessDiv16Imp (n k : Nat) (h : n < k / 16) : 16 * n + 2 < k := by
  omega

/-- Every encoded header has its least significant bit set. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "encode_header_IMP_BIT0"
  (words_as_type_indexed_bitvec)]
theorem encodeHeader_bit0 {width : Nat} [NeZero width] (c : Config) (tag l : Nat) (w : BitVec width)
    (h : encodeHeader c tag l = some w) : w.getLsbD 0 = true := by
  unfold encodeHeader at h
  split at h <;> simp at h
  subst h
  simp [makeHeader]
  right
  have : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  simp [BitVec.getLsbD_ofNat, this]

/-- Reinserting a present binding leaves the tree unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "lookup_IMP_insert_EQ"]
theorem lookup_imp_insert_eq {α : Type} :
    ∀ (t : Spt α) (x : Nat) (y : α), sptLookup x t = some y → sptInsert x y t = t :=
  fun t x y h => sptInsertUnchanged t x y h

/-- Setting one variable through `set_vars` is `set_var`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "set_vars_sing"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVars_sing {width : Nat} [NeZero width] {C F : Type} (n : Nat) (w : WordLocW width)
    (t : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.setVars [n] [w] t = WordSemStateFiniteExact.setVar n w t := rfl

/-- A nonnegative integer is a natural number. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "NONNEG_INT"]
theorem nonnegInt (i : Int) (h : 0 ≤ i) : ∃ j : Nat, i = (j : Int) :=
  ⟨i.toNat, (Int.toNat_of_nonneg h).symm⟩

/-- Bit `i` of one is set exactly at index zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "BIT_X_1"]
theorem bitX1 (i : Nat) : Nat.testBit 1 i = true ↔ i = 0 := by
  cases i <;> simp [Nat.testBit_succ]

/-- Masking with `-2` keeps a word whose least significant bit is clear. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "minus_2_word_and_id"
  (words_as_type_indexed_bitvec)]
theorem minus2WordAndId {width : Nat} [NeZero width] (w : BitVec width)
    (h : ¬ w.getLsbD 0 = true) : -(2#width) &&& w = w := by
  have mask : -(2#width) = ~~~(1#width) := by
    rw [BitVec.not_eq_neg_add, ← BitVec.neg_add]
    congr 1
    exact BitVec.ofNat_add 1 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [mask]
  by_cases h0 : i = 0 <;> simp_all

/-- A multiple of four shifted by `k` is the quotient shifted by `k + 2`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "FOUR_MUL_LSL"
  (words_as_type_indexed_bitvec)]
theorem fourMulLsl {width : Nat} [NeZero width] (i k : Nat) :
    (BitVec.ofNat width (4 * i) <<< k : BitVec width) = BitVec.ofNat width i <<< (k + 2) := by
  rw [Nat.add_comm k 2, BitVec.shiftLeft_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]

/-- Some index lies outside every sparse tree's domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "EXISTS_NOT_IN_spt_DOMAIN"]
theorem exists_notIn_sptDomain {α : Type} (refs : Spt α) : ∃ x, ¬ sptDomain refs x :=
  ⟨DataSem.leastUnusedRef refs, by simp [sptDomain, DataSem.leastUnusedRef_unused]⟩

/-- The least index outside the domain is outside the domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "LEAST_NOTIN_spt_DOMAIN"]
theorem least_notIn_sptDomain {α : Type} :
    ∀ refs : Spt α, ¬ sptDomain refs (DataSem.leastUnusedRef refs) := by
  intro refs
  simp [sptDomain, DataSem.leastUnusedRef_unused]

/-- A bounded optional sum bounds each summand. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "option_le_add_indv"]
theorem optionLe_add_indv (n m r : Option Nat)
    (h : optionLe (optionMap₂ (· + ·) n m) r) : optionLe n r ∧ optionLe m r := by
  rcases n with _ | n <;> rcases m with _ | m <;> rcases r with _ | r <;>
    simp_all [optionMap₂, optionLe]
  all_goals omega

/-- Adding a summand on the left preserves an upper bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "option_le_add_drop_right"]
theorem optionLe_add_dropRight (x y z : Option Nat) (h : optionLe x y) :
    optionLe x (optionMap₂ (· + ·) z y) := by
  rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;>
    simp_all [optionMap₂, optionLe]
  all_goals omega

/-- Products with the byte count are byte aligned at good dimensions, on
either side. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "byte_aligned_bytes_in_word"
  (words_as_type_indexed_bitvec)]
theorem byteAligned_bytesInWord {width : Nat} [NeZero width] (w : BitVec width)
    (good : goodDimindex width) :
    holByteAligned (w * wordSemBytesInWord) = true ∧ holByteAligned (wordSemBytesInWord * w) = true := by
  have hc : ∀ x : BitVec width, holByteAligned (wordSemBytesInWord * x) = true := fun x =>
    StackRemove.WordAddressArithmetic.byteAlignedBytesInWordMult x good
  exact ⟨by rw [BitVec.mul_comm]; exact hc w, hc w⟩

/-- A data stack frame is an environment frame. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "is_env_def"]
def isEnv (st : DataSem.Stack) : Prop := ∃ n vs, st = .env n vs

/-- Adding four to the dividend increments the quotient by one. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "ADD4DIV4"]
theorem add4Div4 (i : Nat) : (i + 4) / 4 = i / 4 + 1 := by omega

/-- Adding eight to the dividend increments the quotient by one. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "ADD8DIV8"]
theorem add8Div8 (i : Nat) : (i + 8) / 8 = i / 8 + 1 := by omega

/-- Multiplying by four is two more doublings. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "EXP_LEMMA1"]
theorem expLemma1 (n k : Nat) : 4 * n * 2 ^ k = n * 2 ^ (k + 2) := by
  rw [Nat.pow_add]; ring

/-- `Num (ABS i)` recovers the magnitude of a natural and of its negation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "Num_ABS_AND"]
theorem numAbsAnd (n : Nat) : (n : Int).natAbs = n ∧ (-(n : Int)).natAbs = n := by
  simp

/-- The least significant bit is clear exactly when masking with one gives
zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_bit_test_0"
  (words_as_type_indexed_bitvec)]
theorem wordBitTest0 {width : Nat} [NeZero width] (w : BitVec width) :
    (1#width &&& w) = 0#width ↔ ¬ w.getLsbD 0 = true := by
  constructor
  · intro h hb
    have := congrArg (fun v => v.getLsbD 0) h
    simp [BitVec.getLsbD_one, hb] at this
    exact NeZero.ne width this
  · intro hb
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h0 : i = 0 <;> simp_all

/-- Encoding bytes as data numbers is injective. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "MAP_Number_11_w2n_word8"]
theorem map_number_inj (ns ns' : List (BitVec 8)) :
    ns.map (fun b => DataSem.Value.number (Int.ofNat b.toNat)) =
        ns'.map (fun b => DataSem.Value.number (Int.ofNat b.toNat)) ↔ ns = ns' := by
  constructor
  · intro h
    induction ns generalizing ns' with
    | nil => cases ns' <;> simp_all
    | cons a as ih =>
      cases ns' with
      | nil => simp at h
      | cons b bs =>
        simp only [List.map_cons, List.cons.injEq, DataSem.Value.number.injEq, Int.ofNat.injEq] at h
        rw [BitVec.eq_of_toNat_eq h.1, ih bs h.2]
  · rintro rfl; rfl

/-- Encoding 64-bit words as data values is injective. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "MAP_Word64_11"]
theorem map_word64_inj (ns ns' : List (BitVec 64)) :
    ns.map DataSem.Value.word64 = ns'.map DataSem.Value.word64 ↔ ns = ns' := by
  constructor
  · intro h
    induction ns generalizing ns' with
    | nil => cases ns' <;> simp_all
    | cons a as ih =>
      cases ns' with
      | nil => simp at h
      | cons b bs =>
        simp only [List.map_cons, List.cons.injEq, DataSem.Value.word64.injEq] at h
        rw [h.1, ih bs h.2]
  · rintro rfl; rfl

/-- A value decodes to the empty list exactly when it is a nil block. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "v_to_list_EQ_SOME_NIL"]
theorem valueToList_eq_some_nil (hv1 : DataSem.Value) :
    DataSem.valueToList hv1 = some [] ↔ ∃ ts, hv1 = .block ts 0 [] := by
  simpa [BackendCommon.nilTag] using (DataSem.valueToList_nil_iff (v := hv1))

/-- Lists of length four, in both orientations of the length equation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "LENGTH_EQ_4"]
theorem lengthEq4 {α : Type} (xs : List α) :
    (xs.length = 4 ↔ ∃ a1 a2 a3 a4, xs = [a1, a2, a3, a4]) ∧
      (4 = xs.length ↔ ∃ a1 a2 a3 a4, xs = [a1, a2, a3, a4]) := by
  have key : xs.length = 4 ↔ ∃ a1 a2 a3 a4, xs = [a1, a2, a3, a4] := by
    constructor
    · intro h
      match xs, h with
      | [a1, a2, a3, a4], _ => exact ⟨a1, a2, a3, a4, rfl⟩
    · rintro ⟨a1, a2, a3, a4, rfl⟩; rfl
  exact ⟨key, by rw [eq_comm]; exact key⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
