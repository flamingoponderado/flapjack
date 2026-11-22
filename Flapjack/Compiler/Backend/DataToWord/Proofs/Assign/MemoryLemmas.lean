module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SmallStateLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StateRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Number
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.RefArrayLemmas

@[expose] public section

/-! Loading a one-word `Word64` payload in the data-to-word assignment proof. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace LoadWord64Witness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end LoadWord64Witness

/-- On a 64-bit target, `LoadWord64` reads the payload of a related `Word64`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_LoadWord64"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_loadWord64 {width : Nat} [NeZero width] {C F : Type} (c : Config) (be : Bool)
    (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat) (t : WordSemStateFiniteExact width C F)
    (w : BitVec 64) (v : WordLocW width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (src dest : Nat)
    (h : memoryRel c be ts refs sp t.store t.memory t.mdomain ((.word64 w, v) :: vars) ∧
      shiftLength c < width ∧ width = 64 ∧ WordSemStateFiniteExact.getVar src t = some v) :
    WordSemStateFiniteExact.evaluate (loadWord64 c dest src) t =
      (none, WordSemStateFiniteExact.setVar dest (.word (w.setWidth width : BitVec width)) t) := by
  obtain ⟨rel, shift, w64, hv⟩ := h
  have good : goodDimindex width := Or.inr w64
  obtain ⟨ptr, address, header, hloc, haddr, -, -, -, -, -, hdom, rest⟩ :=
    memoryRel_word64Imp c be ts refs sp t.store t.memory t.mdomain w v vars ⟨rel, good⟩
  have notLt : ¬ width < 64 := by omega
  rw [if_neg notLt] at rest
  obtain ⟨hmem, -, -⟩ := rest
  subst hloc
  have hreal := Bignum.getRealAddr_lemma c src t _ address ⟨shift, good, hv, haddr⟩
  have hbytes : (wordSemBytesInWord : BitVec width) = StackRemove.bytesInWord width := rfl
  simp only [loadWord64]
  generalize (realAddr c src : WordLangExpHOL (BitVec width)) = e at hreal ⊢
  simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp]
  simp [hreal, WordSemStateFiniteExact.wordExp, theWords, wordOpHOL, wordOp,
    WordSemStateFiniteExact.memLoad, hbytes, hdom, hmem]

/-- The memory relation ignores the bitmap and code buffer store entries. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "memory_rel_ignore_buffers"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_ignore_buffers {width : Nat} [NeZero width] (c : Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (x : WordLocW width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    (memoryRel c be ts refs sp (st.updateEq (.bitmapBuffer, x)) m dm vars =
        memoryRel c be ts refs sp st m dm vars) ∧
      (memoryRel c be ts refs sp (st.updateEq (.codeBuffer, x)) m dm vars =
        memoryRel c be ts refs sp st m dm vars) := by
  constructor <;>
  simp [memoryRel, heapInMemoryStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- A related small natural number is its shifted immediate encoding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "memory_rel_get_num"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_getNum {width : Nat} [NeZero width] (c : Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (n : Nat) (a : WordLocW width)
    (h : memoryRel c be ts refs sp st m dm vars ∧ n < 2 ^ width / 8 ∧ goodDimindex width ∧
      (Flapjack.Compiler.Backend.DataSem.Value.number (n : Int), a) ∈ vars) :
    ∃ w : BitVec width, a = .word w ∧ w >>> (2 : Nat) = BitVec.ofNat width n := by
  obtain ⟨rel, hn, good, mem⟩ := h
  have rel1 := memoryRel_rearrange c be ts refs sp st m dm vars [(.number (n : Int), a)]
    (by intro p hp; simp at hp; subst hp; exact mem) rel
  have small : smallInt width (n : Int) := by
    unfold smallInt; simp only [Int.ofNat_eq_natCast]; constructor <;> omega
  have ha := memoryRel_numberImp c be ts refs sp st m dm (n : Int) a [] ⟨good, small, rel1⟩
  refine ⟨_, ha, ?_⟩
  have h4 : 4 * n < 2 ^ width := by omega
  simp only [smallnum, show ¬ ((n : Int) < 0) by omega, if_false]
  apply BitVec.eq_of_toNat_eq
  have e : (4 * (n : Int)).toNat = 4 * n := by omega
  simp only [e, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4,
    Nat.shiftRight_eq_div_pow]
  have hn' : n < 2 ^ width := by omega
  rw [Nat.mod_eq_of_lt hn']
  omega

/-- `smallInt` holds at zero on a good word size. Flapjack infrastructure. -/
theorem smallInt_zero_of_good {width : Nat} [NeZero width] (good : goodDimindex width) :
    smallInt width 0 := by
  rcases good with rfl | rfl <;>
  · unfold smallInt; simp only [Int.ofNat_eq_natCast]; constructor <;> omega

/-- A related source number, its adjusted target word and the empty-context
remaining roots: the joined local environment is placed first. Flapjack
factoring of the source's `memory_rel_drop`/`memory_rel_lookup` steps. -/
theorem stateRel_memoryRel_lookup {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (vs : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))) (locs : List (Nat × Nat))
    (i : Nat) (x : Flapjack.Compiler.Backend.DataSem.Value) (word : WordLocW width)
    (rel : Proofs.Gc.stateRel c l1 l2 s t vs locs)
    (hget : DataSem.getVar i s.locals = some x)
    (hword : WordSemStateFiniteExact.getVar (adjustVar i) t = some word) :
    ∃ rest, memoryRel c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
      ((x, word) :: rest) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, mem⟩ := rel
  have rel2 := memoryRel_rearrange c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
    t.mdomain _ (Proofs.Gc.joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++
      (vs.getD [] ++ [(Proofs.Gc.theGlobal s.global, holFapply t.store .globals)] ++
        Proofs.Gc.flatStack s.stack t.stack))
    (by intro p hp; simp only [List.mem_append, List.mem_cons] at hp ⊢; tauto) mem
  exact ⟨_, Bignum.memoryRel_lookup c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
    t.mdomain s.locals t.locals _ i x word ⟨rel2, hget, hword⟩⟩

/-- A source number's target word is zero exactly when the number is. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_IMP_test_zero"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_imp_test_zero {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (vs : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))) (locs : List (Nat × Nat))
    (i : Nat) (n : Int)
    (h : Proofs.Gc.stateRel c l1 l2 s t vs locs ∧ DataSem.getVar i s.locals = some (.number n)) :
    ∃ w : BitVec width, WordSemStateFiniteExact.getVar (adjustVar i) t = some (.word w) ∧
      (w = 0 ↔ n = 0) := by
  obtain ⟨rel, hget⟩ := h
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  obtain ⟨word, hword⟩ := Proofs.Gc.stateRel_getVar c l1 l2 s t vs locs i _ rel hget
  obtain ⟨rest, rel3⟩ := stateRel_memoryRel_lookup c l1 l2 s t vs locs i _ word rel hget hword
  have small0 := smallInt_zero_of_good good
  have rel4 := impMemoryRel_number c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
    t.mdomain _ 0 ⟨good, small0, rel3⟩
  obtain ⟨v1, v2, e1, e2, iff⟩ := memoryRel_numberEq c t.be (holThe s.tstamps) s.refs s.space
    t.store t.memory t.mdomain 0 n _ word rest ⟨rel4, Or.inl small0, good⟩
  have hv1 : v1 = 0 := by
    have := (WordLocW.word.inj e1).symm
    simpa [smallnum] using this
  subst hv1
  refine ⟨v2, by rw [hword, e2], ?_⟩
  constructor
  · intro hz; subst hz; exact (iff.mp rfl).symm
  · intro hn; subst hn; exact (iff.mpr rfl).symm

/-- Dropping `k` cons cells of a list value decodes to the dropped list.
HOL `THE` is the reviewed `holThe`, inhabited at data values by the data
semantics' global `Nonempty` instance. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "v_to_list_block_drop"]
theorem valueToList_blockDrop (k : Nat) (v : Flapjack.Compiler.Backend.DataSem.Value)
    (l : List Flapjack.Compiler.Backend.DataSem.Value)
    (h : DataSem.valueToList v = some l ∧ k < l.length) :
    DataSem.valueToList (holThe (blockDrop k v)) = some (l.drop k) := by
  induction k generalizing v l with
  | zero => simpa [blockDrop, holThe] using h.1
  | succ k ih =>
    obtain ⟨hv, hk⟩ := h
    cases l with
    | nil => simp at hk
    | cons x xs =>
      match v, hv with
      | .block ts tag [head, tail], hv =>
        unfold DataSem.valueToList at hv
        split at hv
        · cases htail : DataSem.valueToList tail with
          | none => simp [htail] at hv
          | some ys =>
            simp only [htail, Option.map_some, Option.some.injEq, List.cons.injEq] at hv
            obtain ⟨-, rfl⟩ := hv
            simp only [blockDrop, List.drop_succ_cons]
            exact ih tail ys ⟨htail, by simpa using hk⟩
        · simp at hv
      | .block ts tag [], hv =>
        unfold DataSem.valueToList at hv
        split at hv <;> simp at hv
      | .block ts tag (a :: b :: c :: rest), hv =>
        unfold DataSem.valueToList at hv; simp at hv
      | .block ts tag [a], hv =>
        unfold DataSem.valueToList at hv; simp at hv
      | .number _, hv => simp [DataSem.valueToList] at hv
      | .word64 _, hv => simp [DataSem.valueToList] at hv
      | .codePtr _, hv => simp [DataSem.valueToList] at hv
      | .refPtr _ _, hv => simp [DataSem.valueToList] at hv

/-- A small natural source number is read from its adjusted target local as
its immediate encoding. HOL's existential `w` (of an independent type `δ`)
does not occur in the body; as every HOL type is inhabited it is vacuous, so it
is omitted and no inhabitedness instance is needed (as for the reviewed
`memory_rel_El'` and `memory_rel_Number_bignum_header`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "state_rel_get_var_Number_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_getVar_number_imp {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (t : WordSemStateFiniteExact width C F)
    (vs : Option (List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)))
    (locs : List (Nat × Nat)) (i n : Nat)
    (h : Proofs.Gc.stateRel c l1 l2 s t vs locs ∧
      DataSem.getVar i s.locals = some (.number (n : Int)) ∧ smallInt width (n : Int)) :
    WordSemStateFiniteExact.getVar (adjustVar i) t =
      some (.word (smallnum (n : Int) : BitVec width)) := by
  obtain ⟨rel, hget, small⟩ := h
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  obtain ⟨word, hword⟩ := Proofs.Gc.stateRel_getVar c l1 l2 s t vs locs i _ rel hget
  obtain ⟨rest, rel3⟩ := stateRel_memoryRel_lookup c l1 l2 s t vs locs i _ word rel hget hword
  rw [hword, memoryRel_numberImp c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
    t.mdomain _ word rest ⟨good, small, rel3⟩]

/-- A two-operand word disjunction. Flapjack rewriting helper. -/
theorem wordOpHOL_or_two {k : Nat} [NeZero k] (x y : BitVec k) :
    wordOpHOL .or [x, y] = some (x ||| y) := by
  change some (x ||| (y ||| 0)) = some (x ||| y)
  simp

/-- `MakeBytes n` replicates the byte held (shifted) in register `n`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_MakeBytes"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_makeBytes {width : Nat} [NeZero width] {C F : Type} (n : Nat)
    (s : WordSemStateFiniteExact width C F) (good : goodDimindex width) :
    WordSemStateFiniteExact.evaluate (makeBytes n) s =
      match WordSemStateFiniteExact.getVar n s with
      | some (.word w) =>
        (none, WordSemStateFiniteExact.setVar n (.word (wordOfByte (w >>> (2 : Nat) : BitVec width))) s)
      | _ => (some .error, s) := by
  rcases good with rfl | rfl <;>
  · rcases h : WordSemStateFiniteExact.getVar n s with _ | (w | ⟨b, o⟩) <;>
      simp only [WordSemStateFiniteExact.getVar] at h <;>
      simp [makeBytes, wordListSeq, shiftN, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.fixClock,
        WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, theWords, wordOpHOL_or_two,
        wordShiftHOL, sptLookup_sptInsert_same, sptInsert_insert_shadow, wordOfByte, BitVec.or_comm, h]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
