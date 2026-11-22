module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArrayImp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.SemanticPrimitivesHOL.Array
public import Flapjack.Misc.Sptree.InsertUnchanged

@[expose] public section

/-!
# Byte-array copying

Counterparts of the byte-copy group of
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`
(`memory_rel_ByteArray_IMP_store` and the `word_copy_*` / `list_copy_*`
definitions and theorems). HOL `EL` is rendered by guarded `getElem`: every
`EL` in these definitions sits under the definition's own bounds guard, so the
index proof is discharged from that guard and no total-function inhabitant is
needed. `LUPDATE` is `List.set` (both leave the list unchanged out of range),
`OPTION_BIND` is `Option.bind`, `<₊`/`≤₊` are the unsigned `BitVec` orders,
`mem_load_byte_aux`/`mem_store_byte_aux` are the reviewed
`memLoadByteAuxExact`/`memStoreByteAuxExact`, and `dimword (:α)` is
`2 ^ width`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte
open Flapjack.Compiler.Backend.LabToTarget Flapjack.SemanticPrimitivesHOL

/-- Storing one byte of a related byte array keeps the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_ByteArray_IMP_store"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_byteArrayImpStore {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (bl : Bool) (p : Nat) (w : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (fl : Bool)
    (vals : List (BitVec 8)) (a : BitVec width) (i : Nat) (b : BitVec 8) :
    memoryRel c be ts refs sp st m dm ((.refPtr bl p, .word w) :: vars) ∧
    sptLookup p refs = some (.byteArray fl vals) ∧ goodDimindex width ∧
    getRealAddr c st w = some a ∧ i < vals.length →
    ∃ m1, memStoreByteAuxExact m dm be (a + StackRemove.bytesInWord width + BitVec.ofNat width i) b = some m1 ∧
      memoryRel c be ts (sptInsert p (.byteArray fl (vals.set i b)) refs) sp st m1 dm
        ((.refPtr bl p, .word w) :: vars) := by
  rintro ⟨related, found, good, real, bound⟩
  obtain ⟨w', a', _, _, loc, _, _, _, _, _, _, real', _, _, reads, update, _⟩ :=
    memoryRel_byteArrayImp (β := Unit) c be ts refs sp st m dm bl fl p vals (.word w) vars ⟨related, found, good⟩
  cases loc
  have aEq : a' = a := Option.some.inj (real'.symm.trans real)
  subst a'
  have read := reads i bound
  have upd := update i b bound
  simp only at upd
  generalize hAd : a + StackRemove.bytesInWord width + BitVec.ofNat width i = ad at read upd ⊢
  unfold memLoadByteAuxExact at read
  rw [riscvByteAlignHOL_eq good] at read
  cases hm : m (holByteAlign ad) with
  | loc _ _ => simp [hm] at read
  | word v =>
    rw [hm] at read upd
    have hdm : dm (holByteAlign ad) = true := by
      by_contra hne
      simp [hne] at read
    refine ⟨_, ?_, upd⟩
    simp only [memStoreByteAuxExact, riscvByteAlignHOL_eq good, hm, hdm, if_true, setByteHOL8_eq,
      wordSemTheWord]


/-- Exact HOL `word_copy_fwd_def`: forward byte copy, four bytes per round. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_fwd_def"
  (words_as_type_indexed_bitvec)]
def wordCopyFwd {width : Nat} [NeZero width] (be : Bool) (n a b : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    Option (BitVec width → WordLocW width) :=
  if _hd : 2 ^ width ≤ 4 then none else
  if _h4 : n < 4#width then
    if n < 2#width then
      if n = 0#width then some m else
        (memLoadByteAuxExact m dm be a).bind (fun w => memStoreByteAuxExact m dm be b w)
    else
      (memLoadByteAuxExact m dm be a).bind (fun w1 =>
      (memLoadByteAuxExact m dm be (a + 1#width)).bind (fun w2 =>
        if n = 2#width then
          (memStoreByteAuxExact m dm be b w1).bind (fun m =>
          (memStoreByteAuxExact m dm be (b + 1#width) w2).bind (fun m => some m))
        else
          (memLoadByteAuxExact m dm be (a + 2#width)).bind (fun w3 =>
          (memStoreByteAuxExact m dm be b w1).bind (fun m =>
          (memStoreByteAuxExact m dm be (b + 1#width) w2).bind (fun m =>
          (memStoreByteAuxExact m dm be (b + 2#width) w3).bind (fun m => some m))))))
  else
    (memLoadByteAuxExact m dm be a).bind (fun w1 =>
    (memLoadByteAuxExact m dm be (a + 1#width)).bind (fun w2 =>
    (memLoadByteAuxExact m dm be (a + 2#width)).bind (fun w3 =>
    (memLoadByteAuxExact m dm be (a + 3#width)).bind (fun w4 =>
    (memStoreByteAuxExact m dm be b w1).bind (fun m' =>
    (memStoreByteAuxExact m' dm be (b + 1#width) w2).bind (fun m' =>
    (memStoreByteAuxExact m' dm be (b + 2#width) w3).bind (fun m' =>
    (memStoreByteAuxExact m' dm be (b + 3#width) w4).bind (fun m' =>
      wordCopyFwd be (n - 4#width) (a + 4#width) (b + 4#width) m' dm))))))))
termination_by n.toNat
decreasing_by
  have big : 4 < 2 ^ width := by omega
  have h4' : 4 ≤ n.toNat := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt big] at _h4
    omega
  rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def, Nat.mod_eq_of_lt big]; omega)]
  simp [Nat.mod_eq_of_lt big]
  omega

/-- Exact HOL `list_copy_fwd_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_fwd_def"]
def listCopyFwd {α : Type} (n xp : Nat) (xs : List α) (yp : Nat) (ys : List α) : Option (List α) :=
  if h : xp + n ≤ xs.length ∧ yp + n ≤ ys.length then
    if h0 : n = 0 then some ys else
    if h1 : n = 1 then some (ys.set yp xs[xp]) else
    if h2 : n = 2 then some (((List.set · (yp + 1) xs[xp + 1]) ∘
                              (List.set · (yp + 0) xs[xp + 0])) ys) else
    if h3 : n = 3 then some (((List.set · (yp + 2) xs[xp + 2]) ∘
                              (List.set · (yp + 1) xs[xp + 1]) ∘
                              (List.set · (yp + 0) xs[xp + 0])) ys) else
      listCopyFwd (n - 4) (xp + 4) xs (yp + 4)
        (((List.set · (yp + 3) xs[xp + 3]) ∘
          (List.set · (yp + 2) xs[xp + 2]) ∘
          (List.set · (yp + 1) xs[xp + 1]) ∘
          (List.set · (yp + 0) xs[xp + 0])) ys)
  else none
termination_by n
decreasing_by omega

/-- Exact HOL `list_copy_fwd_alias_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_fwd_alias_def"]
def listCopyFwdAlias {α : Type} (n xp yp : Nat) (ys : List α) : Option (List α) :=
  if h : xp + n ≤ ys.length ∧ yp + n ≤ ys.length then
    if h0 : n = 0 then some ys else
    if h1 : n = 1 then some (ys.set yp ys[xp]) else
    if h2 : n = 2 then some (((List.set · (yp + 1) ys[xp + 1]) ∘
                              (List.set · (yp + 0) ys[xp + 0])) ys) else
    if h3 : n = 3 then some (((List.set · (yp + 2) ys[xp + 2]) ∘
                              (List.set · (yp + 1) ys[xp + 1]) ∘
                              (List.set · (yp + 0) ys[xp + 0])) ys) else
      listCopyFwdAlias (n - 4) (xp + 4) (yp + 4)
        (((List.set · (yp + 3) ys[xp + 3]) ∘
          (List.set · (yp + 2) ys[xp + 2]) ∘
          (List.set · (yp + 1) ys[xp + 1]) ∘
          (List.set · (yp + 0) ys[xp + 0])) ys)
  else none
termination_by n
decreasing_by omega

/-- Exact HOL `word_copy_bwd_def`: backward byte copy, four bytes per round. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_bwd_def"
  (words_as_type_indexed_bitvec)]
def wordCopyBwd {width : Nat} [NeZero width] (be : Bool) (n a b : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    Option (BitVec width → WordLocW width) :=
  if _hd : 2 ^ width ≤ 4 then none else
  if _h4 : n < 4#width then
    if n < 2#width then
      if n = 0#width then some m else
        (memLoadByteAuxExact m dm be a).bind (fun w => memStoreByteAuxExact m dm be b w)
    else
      (memLoadByteAuxExact m dm be a).bind (fun w1 =>
      (memLoadByteAuxExact m dm be (a - 1#width)).bind (fun w2 =>
        if n = 2#width then
          (memStoreByteAuxExact m dm be b w1).bind (fun m =>
          (memStoreByteAuxExact m dm be (b - 1#width) w2).bind (fun m => some m))
        else
          (memLoadByteAuxExact m dm be (a - 2#width)).bind (fun w3 =>
          (memStoreByteAuxExact m dm be b w1).bind (fun m =>
          (memStoreByteAuxExact m dm be (b - 1#width) w2).bind (fun m =>
          (memStoreByteAuxExact m dm be (b - 2#width) w3).bind (fun m => some m))))))
  else
    (memLoadByteAuxExact m dm be a).bind (fun w1 =>
    (memLoadByteAuxExact m dm be (a - 1#width)).bind (fun w2 =>
    (memLoadByteAuxExact m dm be (a - 2#width)).bind (fun w3 =>
    (memLoadByteAuxExact m dm be (a - 3#width)).bind (fun w4 =>
    (memStoreByteAuxExact m dm be b w1).bind (fun m' =>
    (memStoreByteAuxExact m' dm be (b - 1#width) w2).bind (fun m' =>
    (memStoreByteAuxExact m' dm be (b - 2#width) w3).bind (fun m' =>
    (memStoreByteAuxExact m' dm be (b - 3#width) w4).bind (fun m' =>
      wordCopyBwd be (n - 4#width) (a - 4#width) (b - 4#width) m' dm))))))))
termination_by n.toNat
decreasing_by
  have big : 4 < 2 ^ width := by omega
  have h4' : 4 ≤ n.toNat := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt big] at _h4
    omega
  rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def, Nat.mod_eq_of_lt big]; omega)]
  simp [Nat.mod_eq_of_lt big]
  omega

/-- Exact HOL `minus_def`: natural-number subtraction. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "minus_def"]
def minus (m n : Nat) : Nat := m - n

/-- Exact HOL `list_copy_bwd_def` (the stored definition, written with `minus`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_bwd_def" 15580]
def listCopyBwd {α : Type} (n xp : Nat) (xs : List α) (yp : Nat) (ys : List α) : Option (List α) :=
  if h : n ≤ xp + 1 ∧ xp < xs.length ∧ n ≤ yp + 1 ∧ yp < ys.length then
    if h0 : n = 0 then some ys else
    if h1 : n = 1 then some (ys.set yp xs[xp]) else
    if h2 : n = 2 then some (((List.set · (minus yp 1) (xs[minus xp 1]'(by unfold minus; omega))) ∘
                              (List.set · (minus yp 0) (xs[minus xp 0]'(by unfold minus; omega)))) ys) else
    if h3 : n = 3 then some (((List.set · (minus yp 2) (xs[minus xp 2]'(by unfold minus; omega))) ∘
                              (List.set · (minus yp 1) (xs[minus xp 1]'(by unfold minus; omega))) ∘
                              (List.set · (minus yp 0) (xs[minus xp 0]'(by unfold minus; omega)))) ys) else
      listCopyBwd (n - 4) (minus xp 4) xs (minus yp 4)
        (((List.set · (minus yp 3) (xs[minus xp 3]'(by unfold minus; omega))) ∘
          (List.set · (minus yp 2) (xs[minus xp 2]'(by unfold minus; omega))) ∘
          (List.set · (minus yp 1) (xs[minus xp 1]'(by unfold minus; omega))) ∘
          (List.set · (minus yp 0) (xs[minus xp 0]'(by unfold minus; omega)))) ys)
  else none
termination_by n
decreasing_by omega

/-- Exact HOL `list_copy_bwd_alias_def` (the stored definition, written with `minus`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_bwd_alias_def" 15600]
def listCopyBwdAlias {α : Type} (n xp yp : Nat) (ys : List α) : Option (List α) :=
  if h : n ≤ xp + 1 ∧ xp < ys.length ∧ n ≤ yp + 1 ∧ yp < ys.length then
    if h0 : n = 0 then some ys else
    if h1 : n = 1 then some (ys.set yp ys[xp]) else
    if h2 : n = 2 then some (((List.set · (minus yp 1) (ys[minus xp 1]'(by unfold minus; omega))) ∘
                              (List.set · (minus yp 0) (ys[minus xp 0]'(by unfold minus; omega)))) ys) else
    if h3 : n = 3 then some (((List.set · (minus yp 2) (ys[minus xp 2]'(by unfold minus; omega))) ∘
                              (List.set · (minus yp 1) (ys[minus xp 1]'(by unfold minus; omega))) ∘
                              (List.set · (minus yp 0) (ys[minus xp 0]'(by unfold minus; omega)))) ys) else
      listCopyBwdAlias (n - 4) (minus xp 4) (minus yp 4)
        (((List.set · (minus yp 3) (ys[minus xp 3]'(by unfold minus; omega))) ∘
          (List.set · (minus yp 2) (ys[minus xp 2]'(by unfold minus; omega))) ∘
          (List.set · (minus yp 1) (ys[minus xp 1]'(by unfold minus; omega))) ∘
          (List.set · (minus yp 0) (ys[minus xp 0]'(by unfold minus; omega)))) ys)
  else none
termination_by n
decreasing_by omega

/-- Exact HOL `list_copy_def`: copy forwards unless the target starts after the source. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_def"]
def listCopy {α : Type} (n xp : Nat) (xs : List α) (yp : Nat) (ys : List α) : Option (List α) :=
  if yp ≤ xp ∨ n + xp = 0 then listCopyFwd n xp xs yp ys
  else listCopyBwd n (xp + n - 1) xs (yp + n - 1) ys

/-- Exact HOL `list_copy_alias_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_alias_def"]
def listCopyAlias {α : Type} (n xp yp : Nat) (ys : List α) : Option (List α) :=
  if yp ≤ xp ∨ n + xp = 0 then listCopyFwdAlias n xp yp ys
  else listCopyBwdAlias n (xp + n - 1) (yp + n - 1) ys

/-- Exact HOL `word_copy_array_def`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_array_def"
  (words_as_type_indexed_bitvec)]
def wordCopyArray {width : Nat} [NeZero width] (be : Bool) (n a a1 b b1 : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    Option (BitVec width → WordLocW width) :=
  if b1 ≤ a1 then wordCopyFwd be n (a + a1) (b + b1) m dm
  else wordCopyBwd be n (a + a1 + n - 1#width) (b + b1 + n - 1#width) m dm

/-- The list `TAKE yp ys ++ TAKE n (DROP xp xs) ++ DROP (n + yp) ys` named by
the `list_copy_*_eq` theorems. Flapjack list infrastructure. -/
def spliceCopy {α : Type} (xs : List α) (xp : Nat) (ys : List α) (yp n : Nat) : List α :=
  ys.take yp ++ (xs.drop xp).take n ++ ys.drop (n + yp)

/-- Copying one more element at the bottom of the window. Flapjack list
infrastructure for the `list_copy_*_eq` theorems. -/
theorem spliceCopy_stepBottom {α : Type} (xs ys : List α) (xp yp n N k k' : Nat) (hk : k' = k + 1)
    (hN : N = n + 1) (hx : xp + k + n + 1 ≤ xs.length) (hy : yp + k + n + 1 ≤ ys.length) :
    spliceCopy xs (xp + k') (ys.set (yp + k) (xs[xp + k]'(by omega))) (yp + k') n =
      spliceCopy xs (xp + k) ys (yp + k) N := by
  subst hk hN
  unfold spliceCopy
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_append, List.length_append, List.length_take, List.length_drop,
    List.length_set, List.getElem?_take, List.getElem?_drop, List.getElem?_set]
  rw [Nat.min_eq_left (show yp + k ≤ ys.length by omega), Nat.min_eq_left (show yp + (k + 1) ≤ ys.length by omega),
    Nat.min_eq_left (show n + 1 ≤ xs.length - (xp + k) by omega),
    Nat.min_eq_left (show n ≤ xs.length - (xp + (k + 1)) by omega)]
  split_ifs <;> (try omega) <;> (try (congr 1; omega)) <;> (try (subst_vars; simp_all))

theorem spliceCopy_zero {α : Type} (xs ys : List α) (xp yp : Nat) :
    spliceCopy xs xp ys yp 0 = ys := by
  simp [spliceCopy]

/-- Exact HOL `list_copy_fwd_eq` (a `[local]` theorem). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_fwd_eq"]
theorem listCopyFwd_eq {α : Type} :
    ∀ (n xp : Nat) (xs : List α) (yp : Nat) (ys : List α),
      xp + n ≤ xs.length ∧ yp + n ≤ ys.length →
      listCopyFwd n xp xs yp ys = some (ys.take yp ++ (xs.drop xp).take n ++ ys.drop (n + yp)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro xp xs yp ys ⟨hx, hy⟩
    change _ = some (spliceCopy xs xp ys yp n)
    rw [listCopyFwd, dif_pos ⟨hx, hy⟩]
    by_cases h0 : n = 0
    · subst n; simp [spliceCopy_zero]
    rw [dif_neg h0]
    by_cases h1 : n = 1
    · subst n; rw [dif_pos rfl]
      have := spliceCopy_stepBottom xs ys xp yp 0 1 0 1 rfl rfl (by omega) (by omega)
      simp only [Nat.add_zero, spliceCopy_zero] at this
      rw [this]
    rw [dif_neg h1]
    by_cases h2 : n = 2
    · subst n; rw [dif_pos rfl]
      simp only [Function.comp_apply]
      congr 1
      refine (spliceCopy_zero xs _ (xp + 2) (yp + 2)).symm.trans ?_
      rw [spliceCopy_stepBottom (k := 1) (k' := 2) (N := 1) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 0) (k' := 1) (N := 2) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      simp
    rw [dif_neg h2]
    by_cases h3 : n = 3
    · subst n; rw [dif_pos rfl]
      simp only [Function.comp_apply]
      congr 1
      refine (spliceCopy_zero xs _ (xp + 3) (yp + 3)).symm.trans ?_
      rw [spliceCopy_stepBottom (k := 2) (k' := 3) (N := 1) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 1) (k' := 2) (N := 2) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 0) (k' := 1) (N := 3) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      simp
    rw [dif_neg h3]
    simp only [Function.comp_apply]
    rw [ih (n - 4) (by omega) (xp + 4) xs (yp + 4) _ ⟨by omega, by simp; omega⟩]
    change some (spliceCopy _ _ _ _ _) = _
    rw [spliceCopy_stepBottom (k := 3) (k' := 4) (N := n - 3) (hk := rfl) (hN := by omega)
        (hx := by omega) (hy := by simp; omega)]
    rw [spliceCopy_stepBottom (k := 2) (k' := 3) (N := n - 2) (hk := rfl) (hN := by omega)
        (hx := by omega) (hy := by simp; omega)]
    rw [spliceCopy_stepBottom (k := 1) (k' := 2) (N := n - 1) (hk := rfl) (hN := by omega)
        (hx := by omega) (hy := by simp; omega)]
    rw [spliceCopy_stepBottom (k := 0) (k' := 1) (N := n) (hk := rfl) (hN := by omega)
        (hx := by omega) (hy := by simp; omega)]
    simp

/-- Copying one more element at the top of the window. Flapjack list
infrastructure for the backward `list_copy_*_eq` theorems. -/
theorem spliceCopy_stepTop {α : Type} (xs ys : List α) (a b m M p q : Nat) (hM : M = m + 1)
    (hp : p = b + m) (hq : q = a + m) (hx : a + m < xs.length) (hy : b + m < ys.length) :
    spliceCopy xs a (ys.set p (xs[q]'(by omega))) b m = spliceCopy xs a ys b M := by
  subst hM hp hq
  unfold spliceCopy
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_append, List.length_append, List.length_take, List.length_drop,
    List.length_set, List.getElem?_take, List.getElem?_drop, List.getElem?_set]
  rw [Nat.min_eq_left (show b ≤ ys.length by omega),
    Nat.min_eq_left (show m + 1 ≤ xs.length - a by omega),
    Nat.min_eq_left (show m ≤ xs.length - a by omega)]
  split_ifs <;> (try omega) <;> (try rfl) <;> (try (congr 1; omega))
  rw [List.getElem?_eq_getElem (by omega)]
  congr 2
  omega

/-- Updating outside a read window does not change the window. Flapjack list
infrastructure. -/
theorem take_drop_set_outside {α : Type} (l : List α) (d k i : Nat) (v : α) (h : i < d ∨ d + k ≤ i) :
    ((l.set i v).drop d).take k = (l.drop d).take k := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_set]
  split_ifs <;> first | rfl | omega

/-- Only the read window of the source matters. Flapjack list infrastructure. -/
theorem spliceCopy_source {α : Type} (xs xs' ys : List α) (a b n : Nat)
    (h : (xs.drop a).take n = (xs'.drop a).take n) :
    spliceCopy xs a ys b n = spliceCopy xs' a ys b n := by
  unfold spliceCopy
  rw [h]

/-- Exact HOL `list_copy_fwd_alias_eq` (a `[local]` theorem). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_fwd_alias_eq"]
theorem listCopyFwdAlias_eq {α : Type} :
    ∀ (n xp yp : Nat) (ys : List α),
      yp ≤ xp ∧ xp + n ≤ ys.length ∧ yp + n ≤ ys.length →
      listCopyFwdAlias n xp yp ys = some (ys.take yp ++ (ys.drop xp).take n ++ ys.drop (n + yp)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro xp yp ys ⟨hle, hx, hy⟩
    change _ = some (spliceCopy ys xp ys yp n)
    rw [listCopyFwdAlias, dif_pos ⟨hx, hy⟩]
    by_cases h0 : n = 0
    · subst n; simp [spliceCopy_zero]
    rw [dif_neg h0]
    by_cases h1 : n = 1
    · subst n; rw [dif_pos rfl]
      have := spliceCopy_stepBottom ys ys xp yp 0 1 0 1 rfl rfl (by omega) (by omega)
      simp only [Nat.add_zero, spliceCopy_zero] at this
      rw [this]
    rw [dif_neg h1]
    by_cases h2 : n = 2
    · subst n; rw [dif_pos rfl]
      simp only [Function.comp_apply]
      congr 1
      refine (spliceCopy_zero ys _ (xp + 2) (yp + 2)).symm.trans ?_
      rw [spliceCopy_stepBottom (k := 1) (k' := 2) (N := 1) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 0) (k' := 1) (N := 2) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      simp
    rw [dif_neg h2]
    by_cases h3 : n = 3
    · subst n; rw [dif_pos rfl]
      simp only [Function.comp_apply]
      congr 1
      refine (spliceCopy_zero ys _ (xp + 3) (yp + 3)).symm.trans ?_
      rw [spliceCopy_stepBottom (k := 2) (k' := 3) (N := 1) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 1) (k' := 2) (N := 2) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 0) (k' := 1) (N := 3) (hk := rfl) (hN := rfl)
          (hx := by omega) (hy := by simp; omega)]
      simp
    rw [dif_neg h3]
    simp only [Function.comp_apply]
    rw [ih (n - 4) (by omega) (xp + 4) (yp + 4) _ ⟨by omega, by simp; omega, by simp; omega⟩]
    change some (spliceCopy _ _ _ _ _) = _
    rw [spliceCopy_source _ ys]
    · rw [spliceCopy_stepBottom (k := 3) (k' := 4) (N := n - 3) (hk := rfl) (hN := by omega)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 2) (k' := 3) (N := n - 2) (hk := rfl) (hN := by omega)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 1) (k' := 2) (N := n - 1) (hk := rfl) (hN := by omega)
          (hx := by omega) (hy := by simp; omega)]
      rw [spliceCopy_stepBottom (k := 0) (k' := 1) (N := n) (hk := rfl) (hN := by omega)
          (hx := by omega) (hy := by simp; omega)]
      simp
    · rw [take_drop_set_outside _ _ _ _ _ (by omega), take_drop_set_outside _ _ _ _ _ (by omega),
        take_drop_set_outside _ _ _ _ _ (by omega), take_drop_set_outside _ _ _ _ _ (by omega)]

/-- The backward window written as a `spliceCopy`. Flapjack list infrastructure. -/
theorem spliceCopy_bwdForm {α : Type} (xs ys : List α) (A B m a b : Nat)
    (h : m = 0 ∨ (A + 1 - m = a ∧ B + 1 - m = b ∧ m ≤ B + 1)) :
    ys.take (B + 1 - m) ++ (xs.drop (A + 1 - m)).take m ++ ys.drop (B + 1) = spliceCopy xs a ys b m := by
  rcases h with h | ⟨ha, hb, hm⟩
  · subst m; simp [spliceCopy_zero]
  · unfold spliceCopy
    rw [ha, hb, show B + 1 = m + b by omega]

/-- Exact HOL `list_copy_bwd_eq` (a `[local]` theorem). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_bwd_eq"]
theorem listCopyBwd_eq {α : Type} :
    ∀ (n xp : Nat) (xs : List α) (yp : Nat) (ys : List α),
      n ≤ xp + 1 ∧ xp < xs.length ∧ n ≤ yp + 1 ∧ yp < ys.length →
      listCopyBwd n xp xs yp ys =
        some (ys.take (yp + 1 - n) ++ (xs.drop (xp + 1 - n)).take n ++ ys.drop (yp + 1)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro xp xs yp ys ⟨hnx, hx, hny, hy⟩
    rw [show ys.drop (yp + 1) = ys.drop (n + (yp + 1 - n)) by congr 1; omega]
    change _ = some (spliceCopy xs (xp + 1 - n) ys (yp + 1 - n) n)
    rw [listCopyBwd, dif_pos ⟨hnx, hx, hny, hy⟩]
    by_cases h0 : n = 0
    · subst n; simp [spliceCopy_zero]
    rw [dif_neg h0]
    by_cases h1 : n = 1
    · subst n; rw [dif_pos rfl]
      congr 1
      refine (spliceCopy_zero xs _ (xp + 1 - 1) (yp + 1 - 1)).symm.trans ?_
      rw [spliceCopy_stepTop (m := 0) (M := 1) (p := yp) (q := xp) (hM := rfl)
        (hp := by omega) (hq := by omega) (hx := by omega) (hy := by omega)]
    rw [dif_neg h1]
    by_cases h2 : n = 2
    · subst n; rw [dif_pos rfl]
      simp only [Function.comp_apply]
      congr 1
      refine (spliceCopy_zero xs _ (xp + 1 - 2) (yp + 1 - 2)).symm.trans ?_
      rw [spliceCopy_stepTop (m := 0) (M := 1) (p := minus yp 1) (q := minus xp 1) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
      rw [spliceCopy_stepTop (m := 1) (M := 2) (p := minus yp 0) (q := minus xp 0) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
    rw [dif_neg h2]
    by_cases h3 : n = 3
    · subst n; rw [dif_pos rfl]
      simp only [Function.comp_apply]
      congr 1
      refine (spliceCopy_zero xs _ (xp + 1 - 3) (yp + 1 - 3)).symm.trans ?_
      rw [spliceCopy_stepTop (m := 0) (M := 1) (p := minus yp 2) (q := minus xp 2) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
      rw [spliceCopy_stepTop (m := 1) (M := 2) (p := minus yp 1) (q := minus xp 1) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
      rw [spliceCopy_stepTop (m := 2) (M := 3) (p := minus yp 0) (q := minus xp 0) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
    rw [dif_neg h3]
    simp only [Function.comp_apply]
    rw [ih (n - 4) (by omega) (minus xp 4) xs (minus yp 4) _
      ⟨by simp only [minus]; omega, by simp only [minus]; omega, by simp only [minus]; omega,
        by simp only [minus, List.length_set]; omega⟩]
    rw [spliceCopy_bwdForm (a := xp + 1 - n) (b := yp + 1 - n) (h := by simp only [minus]; omega)]
    rw [spliceCopy_stepTop (m := n - 4) (M := n - 3) (p := minus yp 3) (q := minus xp 3) (hM := by omega)
      (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
      (hy := by simp; omega)]
    rw [spliceCopy_stepTop (m := n - 3) (M := n - 2) (p := minus yp 2) (q := minus xp 2) (hM := by omega)
      (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
      (hy := by simp; omega)]
    rw [spliceCopy_stepTop (m := n - 2) (M := n - 1) (p := minus yp 1) (q := minus xp 1) (hM := by omega)
      (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
      (hy := by simp; omega)]
    rw [spliceCopy_stepTop (m := n - 1) (M := n) (p := minus yp 0) (q := minus xp 0) (hM := by omega)
      (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
      (hy := by omega)]

/-- Exact HOL `list_copy_bwd_alias_eq` (a `[local]` theorem). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_bwd_alias_eq"]
theorem listCopyBwdAlias_eq {α : Type} :
    ∀ (n xp yp : Nat) (ys : List α),
      xp ≤ yp ∧ n ≤ xp + 1 ∧ xp < ys.length ∧ n ≤ yp + 1 ∧ yp < ys.length →
      listCopyBwdAlias n xp yp ys =
        some (ys.take (yp + 1 - n) ++ (ys.drop (xp + 1 - n)).take n ++ ys.drop (yp + 1)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro xp yp ys ⟨hle, hnx, hx, hny, hy⟩
    rw [show ys.drop (yp + 1) = ys.drop (n + (yp + 1 - n)) by congr 1; omega]
    change _ = some (spliceCopy ys (xp + 1 - n) ys (yp + 1 - n) n)
    rw [listCopyBwdAlias, dif_pos ⟨hnx, hx, hny, hy⟩]
    by_cases h0 : n = 0
    · subst n; simp [spliceCopy_zero]
    rw [dif_neg h0]
    by_cases h1 : n = 1
    · subst n; rw [dif_pos rfl]
      congr 1
      refine (spliceCopy_zero ys _ (xp + 1 - 1) (yp + 1 - 1)).symm.trans ?_
      rw [spliceCopy_stepTop (m := 0) (M := 1) (p := yp) (q := xp) (hM := rfl)
        (hp := by omega) (hq := by omega) (hx := by omega) (hy := by omega)]
    rw [dif_neg h1]
    by_cases h2 : n = 2
    · subst n; rw [dif_pos rfl]
      simp only [Function.comp_apply]
      congr 1
      refine (spliceCopy_zero ys _ (xp + 1 - 2) (yp + 1 - 2)).symm.trans ?_
      rw [spliceCopy_stepTop (m := 0) (M := 1) (p := minus yp 1) (q := minus xp 1) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
      rw [spliceCopy_stepTop (m := 1) (M := 2) (p := minus yp 0) (q := minus xp 0) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
    rw [dif_neg h2]
    by_cases h3 : n = 3
    · subst n; rw [dif_pos rfl]
      simp only [Function.comp_apply]
      congr 1
      refine (spliceCopy_zero ys _ (xp + 1 - 3) (yp + 1 - 3)).symm.trans ?_
      rw [spliceCopy_stepTop (m := 0) (M := 1) (p := minus yp 2) (q := minus xp 2) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
      rw [spliceCopy_stepTop (m := 1) (M := 2) (p := minus yp 1) (q := minus xp 1) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
      rw [spliceCopy_stepTop (m := 2) (M := 3) (p := minus yp 0) (q := minus xp 0) (hM := rfl)
        (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
        (hy := by simp; omega)]
    rw [dif_neg h3]
    simp only [Function.comp_apply]
    rw [ih (n - 4) (by omega) (minus xp 4) (minus yp 4) _
      ⟨by simp only [minus]; omega, by simp only [minus]; omega,
        by simp only [minus, List.length_set]; omega, by simp only [minus]; omega,
        by simp only [minus, List.length_set]; omega⟩]
    rw [spliceCopy_bwdForm (a := xp + 1 - n) (b := yp + 1 - n) (h := by simp only [minus]; omega)]
    rw [spliceCopy_source _ ys]
    swap
    · rw [take_drop_set_outside _ _ _ _ _ (by simp only [minus]; omega),
        take_drop_set_outside _ _ _ _ _ (by simp only [minus]; omega),
        take_drop_set_outside _ _ _ _ _ (by simp only [minus]; omega),
        take_drop_set_outside _ _ _ _ _ (by simp only [minus]; omega)]
    rw [spliceCopy_stepTop (m := n - 4) (M := n - 3) (p := minus yp 3) (q := minus xp 3) (hM := by omega)
      (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
      (hy := by simp; omega)]
    rw [spliceCopy_stepTop (m := n - 3) (M := n - 2) (p := minus yp 2) (q := minus xp 2) (hM := by omega)
      (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
      (hy := by simp; omega)]
    rw [spliceCopy_stepTop (m := n - 2) (M := n - 1) (p := minus yp 1) (q := minus xp 1) (hM := by omega)
      (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
      (hy := by simp; omega)]
    rw [spliceCopy_stepTop (m := n - 1) (M := n) (p := minus yp 0) (q := minus xp 0) (hM := by omega)
      (hp := by simp only [minus]; omega) (hq := by simp only [minus]; omega) (hx := by omega)
      (hy := by omega)]

/-- The successful result of `copy_array` with a destination. Flapjack
infrastructure for `list_copy_thm` and `list_copy_alias_thm`. -/
theorem copyArray_some_eq {α : Type} (xs ys ys1 : List α) (xp yp n : Nat)
    (h : copyArray (xs, (xp : Int)) (n : Int) (some (ys, (yp : Int))) = some ys1) :
    xp + n ≤ xs.length ∧ yp + n ≤ ys.length ∧
      ys1 = ys.take yp ++ (xs.drop xp).take n ++ ys.drop (n + yp) := by
  unfold copyArray at h
  have e1 : ((xp : Int) + (n : Int)).natAbs = xp + n := by omega
  have e2 : ((yp : Int) + (n : Int)).natAbs = yp + n := by omega
  simp only [e1, e2, Int.natAbs_natCast] at h
  by_cases b1 : xs.length < xp + n
  · simp [b1] at h
  by_cases b2 : ys.length < yp + n
  · simp [b1, b2] at h
  simp [b1, b2] at h
  refine ⟨by omega, by omega, ?_⟩
  rw [← h, Nat.add_comm n yp, List.append_assoc]

/-- Exact HOL `list_copy_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_thm"]
theorem listCopy_thm {α : Type} :
    ∀ (xs ys : List α) (xp yp n : Nat) (ys1 : List α),
      copyArray (xs, (xp : Int)) (n : Int) (some (ys, (yp : Int))) = some ys1 →
      listCopy n xp xs yp ys = some ys1 := by
  intro xs ys xp yp n ys1 h
  obtain ⟨hx, hy, rfl⟩ := copyArray_some_eq xs ys ys1 xp yp n h
  unfold listCopy
  split
  · exact listCopyFwd_eq n xp xs yp ys ⟨hx, hy⟩
  · rename_i hc
    rw [listCopyBwd_eq n (xp + n - 1) xs (yp + n - 1) ys ⟨by omega, by omega, by omega, by omega⟩]
    rw [show yp + n - 1 + 1 - n = yp by omega, show xp + n - 1 + 1 - n = xp by omega,
      show yp + n - 1 + 1 = n + yp by omega]

/-- Exact HOL `list_copy_alias_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "list_copy_alias_thm"]
theorem listCopyAlias_thm {α : Type} :
    ∀ (ys : List α) (xp yp n : Nat) (ys1 : List α),
      copyArray (ys, (xp : Int)) (n : Int) (some (ys, (yp : Int))) = some ys1 →
      listCopyAlias n xp yp ys = some ys1 := by
  intro ys xp yp n ys1 h
  obtain ⟨hx, hy, rfl⟩ := copyArray_some_eq ys ys ys1 xp yp n h
  unfold listCopyAlias
  split
  · rename_i hc
    by_cases hle : yp ≤ xp
    · exact listCopyFwdAlias_eq n xp yp ys ⟨hle, hx, hy⟩
    · have : n = 0 ∧ xp = 0 := by omega
      obtain ⟨rfl, rfl⟩ := this
      unfold listCopyFwdAlias
      simp [show yp ≤ ys.length by omega]
  · rename_i hc
    rw [listCopyBwdAlias_eq n (xp + n - 1) (yp + n - 1) ys ⟨by omega, by omega, by omega, by omega, by omega⟩]
    rw [show yp + n - 1 + 1 - n = yp by omega, show xp + n - 1 + 1 - n = xp by omega,
      show yp + n - 1 + 1 = n + yp by omega]

/-- Exact HOL `copy_array_NONE_IMP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "copy_array_NONE_IMP"
  (words_as_type_indexed_bitvec)]
theorem copyArray_none_imp {width : Nat} [NeZero width] :
    ∀ (xs ys : List (BitVec width)) (xp n : Nat),
      copyArray (xs, (xp : Int)) (n : Int) none = some ys →
      listCopyFwd n xp xs 0 (List.replicate n 0#width) = some ys := by
  intro xs ys xp n h
  unfold copyArray at h
  have e1 : ((xp : Int) + (n : Int)).natAbs = xp + n := by omega
  simp only [e1, Int.natAbs_natCast] at h
  by_cases b1 : xs.length < xp + n
  · simp [b1] at h
  simp [b1] at h
  rw [listCopyFwd_eq n xp xs 0 _ ⟨by omega, by simp⟩, ← h]
  simp

/-- Address arithmetic for byte offsets. Flapjack infrastructure. -/
theorem byteAddr_add {width : Nat} (A : BitVec width) (x k : Nat) :
    A + BitVec.ofNat width x + BitVec.ofNat width k = A + BitVec.ofNat width (x + k) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

/-- Address arithmetic for backward byte offsets. Flapjack infrastructure. -/
theorem byteAddr_sub {width : Nat} (A : BitVec width) (x k : Nat) (h : k ≤ x) :
    A + BitVec.ofNat width x - BitVec.ofNat width k = A + BitVec.ofNat width (x - k) := by
  have : BitVec.ofNat width x = BitVec.ofNat width (x - k) + BitVec.ofNat width k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
    rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.sub_add_cancel h]
  rw [this, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- Small numerals compare like their naturals. Flapjack infrastructure. -/
theorem ofNat_lt_ofNat_iff {width : Nat} {n k : Nat} (hn : n < 2 ^ width) (hk : k < 2 ^ width) :
    BitVec.ofNat width n < BitVec.ofNat width k ↔ n < k := by
  simp [BitVec.lt_def, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk]

theorem ofNat_eq_ofNat_iff {width : Nat} {n k : Nat} (hn : n < 2 ^ width) (hk : k < 2 ^ width) :
    BitVec.ofNat width n = BitVec.ofNat width k ↔ n = k := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk] using this
  · rintro rfl; rfl

theorem goodDimindex_pow {width : Nat} (good : goodDimindex width) : 2 ^ 5 ≤ 2 ^ width := by
  rcases good with h | h <;> subst h <;> decide

/-- Simulation of `list_copy_fwd` by `word_copy_fwd` against an abstract
store/load interface. Flapjack infrastructure for `word_copy_fwd_thm`. -/
theorem wordCopyFwd_sim {width : Nat} [NeZero width] (good : goodDimindex width) (be : Bool)
    (dm : BitVec width → Bool) (A0 B0 : BitVec width) (xs : List (BitVec 8))
    (R : List (BitVec 8) → (BitVec width → WordLocW width) → Prop)
    (load : ∀ ys m i (h : i < xs.length), R ys m →
      memLoadByteAuxExact m dm be (A0 + BitVec.ofNat width i) = some xs[i])
    (store : ∀ ys m j v, R ys m → j < ys.length →
      ∃ m1, memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width j) v = some m1 ∧ R (ys.set j v) m1) :
    ∀ n xp yp ys ys1 m, R ys m → listCopyFwd n xp xs yp ys = some ys1 → n < 2 ^ width →
      ∃ m1, wordCopyFwd be (BitVec.ofNat width n) (A0 + BitVec.ofNat width xp)
        (B0 + BitVec.ofNat width yp) m dm = some m1 ∧ R ys1 m1 := by
  have big := goodDimindex_pow good
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xp yp ys ys1 m rel copied bound
    rw [listCopyFwd] at copied
    split at copied
    case isFalse => cases copied
    rename_i hb
    have hx := hb.1
    have hy := hb.2
    have ld : ∀ k (h : xp + k < xs.length), memLoadByteAuxExact m dm be
        (A0 + BitVec.ofNat width (xp + k)) = some xs[xp + k] := fun k h => load ys m (xp + k) h rel
    have st : ∀ zs m' k v, R zs m' → yp + k < zs.length → ∃ m1, memStoreByteAuxExact m' dm be
        (B0 + BitVec.ofNat width (yp + k)) v = some m1 ∧ R (zs.set (yp + k) v) m1 :=
      fun zs m' k v r h => store zs m' (yp + k) v r h
    have n4 := ofNat_lt_ofNat_iff (n := n) (k := 4) bound (show 4 < 2 ^ width by omega)
    have n2 := ofNat_lt_ofNat_iff (n := n) (k := 2) bound (show 2 < 2 ^ width by omega)
    have e0 := ofNat_eq_ofNat_iff (n := n) (k := 0) bound (show 0 < 2 ^ width by omega)
    have e2 := ofNat_eq_ofNat_iff (n := n) (k := 2) bound (show 2 < 2 ^ width by omega)
    rw [wordCopyFwd, dif_neg (by omega)]
    by_cases h0 : n = 0
    · subst n
      simp only [dite_true] at copied
      cases copied
      refine ⟨m, ?_, rel⟩
      simp only [show BitVec.ofNat width 0 < 4#width from n4.mpr (by omega),
        show BitVec.ofNat width 0 < 2#width from n2.mpr (by omega), dite_true, if_true]
    simp only [h0, dite_false] at copied
    have ld0 : memLoadByteAuxExact m dm be (A0 + BitVec.ofNat width xp) = some xs[xp] :=
      load ys m xp (by omega) rel
    by_cases h1 : n = 1
    · subst n
      simp only [dite_true] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := store ys m yp xs[xp] rel (by omega)
      refine ⟨m1, ?_, r1⟩
      simp only [show BitVec.ofNat width 1 < 4#width from n4.mpr (by omega),
        show BitVec.ofNat width 1 < 2#width from n2.mpr (by omega), dite_true, if_true,
        show ¬ BitVec.ofNat width 1 = 0#width from fun h => absurd (e0.mp h) (by omega), if_false,
        ld0, Option.bind_some, s1]
    simp only [h1, dite_false] at copied
    by_cases h2 : n = 2
    · subst n
      simp only [dite_true, Function.comp_apply] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := st ys m 0 xs[xp + 0] rel (by omega)
      obtain ⟨m2, s2, r2⟩ := st _ m1 1 xs[xp + 1] r1 (by simp; omega)
      refine ⟨m2, ?_, r2⟩
      have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) xs[xp] = some m1 := by
        simpa using s1
      simp only [show BitVec.ofNat width 2 < 4#width from n4.mpr (by omega),
        show ¬ BitVec.ofNat width 2 < 2#width from fun h => absurd (n2.mp h) (by omega), dite_true, if_false,
        if_true,
        ld0, ld 1 (by omega), Option.bind_some, s1', s2, byteAddr_add]
    simp only [h2, dite_false] at copied
    by_cases h3 : n = 3
    · subst n
      simp only [dite_true, Function.comp_apply] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := st ys m 0 xs[xp + 0] rel (by omega)
      obtain ⟨m2, s2, r2⟩ := st _ m1 1 xs[xp + 1] r1 (by simp; omega)
      obtain ⟨m3, s3, r3⟩ := st _ m2 2 xs[xp + 2] r2 (by simp; omega)
      refine ⟨m3, ?_, r3⟩
      have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) xs[xp] = some m1 := by
        simpa using s1
      simp only [show BitVec.ofNat width 3 < 4#width from n4.mpr (by omega),
        show ¬ BitVec.ofNat width 3 < 2#width from fun h => absurd (n2.mp h) (by omega), dite_true, if_false,
        show ¬ BitVec.ofNat width 3 = 2#width from fun h => absurd (e2.mp h) (by omega),
        ld0, ld 1 (by omega), ld 2 (by omega), Option.bind_some, s1', s2, s3, byteAddr_add]
    simp only [h3, dite_false, Function.comp_apply] at copied
    obtain ⟨m1, s1, r1⟩ := st ys m 0 xs[xp + 0] rel (by omega)
    obtain ⟨m2, s2, r2⟩ := st _ m1 1 xs[xp + 1] r1 (by simp; omega)
    obtain ⟨m3, s3, r3⟩ := st _ m2 2 xs[xp + 2] r2 (by simp; omega)
    obtain ⟨m4, s4, r4⟩ := st _ m3 3 xs[xp + 3] r3 (by simp; omega)
    obtain ⟨m5, s5, r5⟩ := ih (n - 4) (by omega) (xp + 4) (yp + 4) _ ys1 m4 r4 copied (by omega)
    refine ⟨m5, ?_, r5⟩
    have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) xs[xp] = some m1 := by
      simpa using s1
    have nsub : BitVec.ofNat width n - 4#width = BitVec.ofNat width (n - 4) := by
      have := byteAddr_sub (0 : BitVec width) n 4 (by omega)
      simpa using this
    simp only [show ¬ BitVec.ofNat width n < 4#width from fun h => absurd (n4.mp h) (by omega), dite_false,
      ld0, ld 1 (by omega), ld 2 (by omega), ld 3 (by omega), Option.bind_some, s1', s2, s3, s4,
      nsub, byteAddr_add]
    exact s5
/-- Simulation of `list_copy_fwd_alias` by `word_copy_fwd` against an abstract
store/load interface. Flapjack infrastructure for `word_copy_fwd_alias_thm`. -/
theorem wordCopyFwdAlias_sim {width : Nat} [NeZero width] (good : goodDimindex width) (be : Bool)
    (dm : BitVec width → Bool) (A0 B0 : BitVec width)
    (R : List (BitVec 8) → (BitVec width → WordLocW width) → Prop)
    (load : ∀ ys m i (h : i < ys.length), R ys m →
      memLoadByteAuxExact m dm be (A0 + BitVec.ofNat width i) = some ys[i])
    (store : ∀ ys m j v, R ys m → j < ys.length →
      ∃ m1, memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width j) v = some m1 ∧ R (ys.set j v) m1) :
    ∀ n xp yp ys ys1 m, R ys m → listCopyFwdAlias n xp yp ys = some ys1 → n < 2 ^ width →
      ∃ m1, wordCopyFwd be (BitVec.ofNat width n) (A0 + BitVec.ofNat width xp)
        (B0 + BitVec.ofNat width yp) m dm = some m1 ∧ R ys1 m1 := by
  have big := goodDimindex_pow good
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xp yp ys ys1 m rel copied bound
    rw [listCopyFwdAlias] at copied
    split at copied
    case isFalse => cases copied
    rename_i hb
    have hx := hb.1
    have hy := hb.2
    have ld : ∀ k (h : xp + k < ys.length), memLoadByteAuxExact m dm be
        (A0 + BitVec.ofNat width (xp + k)) = some ys[xp + k] := fun k h => load ys m (xp + k) h rel
    have st : ∀ zs m' k v, R zs m' → yp + k < zs.length → ∃ m1, memStoreByteAuxExact m' dm be
        (B0 + BitVec.ofNat width (yp + k)) v = some m1 ∧ R (zs.set (yp + k) v) m1 :=
      fun zs m' k v r h => store zs m' (yp + k) v r h
    have n4 := ofNat_lt_ofNat_iff (n := n) (k := 4) bound (show 4 < 2 ^ width by omega)
    have n2 := ofNat_lt_ofNat_iff (n := n) (k := 2) bound (show 2 < 2 ^ width by omega)
    have e0 := ofNat_eq_ofNat_iff (n := n) (k := 0) bound (show 0 < 2 ^ width by omega)
    have e2 := ofNat_eq_ofNat_iff (n := n) (k := 2) bound (show 2 < 2 ^ width by omega)
    rw [wordCopyFwd, dif_neg (by omega)]
    by_cases h0 : n = 0
    · subst n
      simp only [dite_true] at copied
      cases copied
      refine ⟨m, ?_, rel⟩
      simp only [show BitVec.ofNat width 0 < 4#width from n4.mpr (by omega),
        show BitVec.ofNat width 0 < 2#width from n2.mpr (by omega), dite_true, if_true]
    simp only [h0, dite_false] at copied
    have ld0 : memLoadByteAuxExact m dm be (A0 + BitVec.ofNat width xp) = some ys[xp] :=
      load ys m xp (by omega) rel
    by_cases h1 : n = 1
    · subst n
      simp only [dite_true] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := store ys m yp ys[xp] rel (by omega)
      refine ⟨m1, ?_, r1⟩
      simp only [show BitVec.ofNat width 1 < 4#width from n4.mpr (by omega),
        show BitVec.ofNat width 1 < 2#width from n2.mpr (by omega), dite_true, if_true,
        show ¬ BitVec.ofNat width 1 = 0#width from fun h => absurd (e0.mp h) (by omega), if_false,
        ld0, Option.bind_some, s1]
    simp only [h1, dite_false] at copied
    by_cases h2 : n = 2
    · subst n
      simp only [dite_true, Function.comp_apply] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := st ys m 0 ys[xp + 0] rel (by omega)
      obtain ⟨m2, s2, r2⟩ := st _ m1 1 ys[xp + 1] r1 (by simp; omega)
      refine ⟨m2, ?_, r2⟩
      have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) ys[xp] = some m1 := by
        simpa using s1
      simp only [show BitVec.ofNat width 2 < 4#width from n4.mpr (by omega),
        show ¬ BitVec.ofNat width 2 < 2#width from fun h => absurd (n2.mp h) (by omega), dite_true, if_false,
        if_true,
        ld0, ld 1 (by omega), Option.bind_some, s1', s2, byteAddr_add]
    simp only [h2, dite_false] at copied
    by_cases h3 : n = 3
    · subst n
      simp only [dite_true, Function.comp_apply] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := st ys m 0 ys[xp + 0] rel (by omega)
      obtain ⟨m2, s2, r2⟩ := st _ m1 1 ys[xp + 1] r1 (by simp; omega)
      obtain ⟨m3, s3, r3⟩ := st _ m2 2 ys[xp + 2] r2 (by simp; omega)
      refine ⟨m3, ?_, r3⟩
      have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) ys[xp] = some m1 := by
        simpa using s1
      simp only [show BitVec.ofNat width 3 < 4#width from n4.mpr (by omega),
        show ¬ BitVec.ofNat width 3 < 2#width from fun h => absurd (n2.mp h) (by omega), dite_true, if_false,
        show ¬ BitVec.ofNat width 3 = 2#width from fun h => absurd (e2.mp h) (by omega),
        ld0, ld 1 (by omega), ld 2 (by omega), Option.bind_some, s1', s2, s3, byteAddr_add]
    simp only [h3, dite_false, Function.comp_apply] at copied
    obtain ⟨m1, s1, r1⟩ := st ys m 0 ys[xp + 0] rel (by omega)
    obtain ⟨m2, s2, r2⟩ := st _ m1 1 ys[xp + 1] r1 (by simp; omega)
    obtain ⟨m3, s3, r3⟩ := st _ m2 2 ys[xp + 2] r2 (by simp; omega)
    obtain ⟨m4, s4, r4⟩ := st _ m3 3 ys[xp + 3] r3 (by simp; omega)
    obtain ⟨m5, s5, r5⟩ := ih (n - 4) (by omega) (xp + 4) (yp + 4) _ ys1 m4 r4 copied (by omega)
    refine ⟨m5, ?_, r5⟩
    have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) ys[xp] = some m1 := by
      simpa using s1
    have nsub : BitVec.ofNat width n - 4#width = BitVec.ofNat width (n - 4) := by
      have := byteAddr_sub (0 : BitVec width) n 4 (by omega)
      simpa using this
    simp only [show ¬ BitVec.ofNat width n < 4#width from fun h => absurd (n4.mp h) (by omega), dite_false,
      ld0, ld 1 (by omega), ld 2 (by omega), ld 3 (by omega), Option.bind_some, s1', s2, s3, s4,
      nsub, byteAddr_add]
    exact s5

/-- Exact HOL `word_copy_bwd_0` (a `[local]` theorem). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_bwd_0"
  (words_as_type_indexed_bitvec)]
theorem wordCopyBwd_zero {width : Nat} [NeZero width] (be : Bool) (a1 a2 : BitVec width)
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) :
    goodDimindex width → wordCopyBwd be 0#width a1 a2 m dm = some m := by
  intro good
  have big := goodDimindex_pow good
  rw [wordCopyBwd, dif_neg (by omega)]
  have n4 := ofNat_lt_ofNat_iff (n := 0) (k := 4) (width := width) (by omega) (show 4 < 2 ^ width by omega)
  have n2 := ofNat_lt_ofNat_iff (n := 0) (k := 2) (width := width) (by omega) (show 2 < 2 ^ width by omega)
  simp only [show BitVec.ofNat width 0 < 4#width from n4.mpr (by omega),
    show BitVec.ofNat width 0 < 2#width from n2.mpr (by omega), dite_true, if_true]

/-- Simulation of `list_copy_bwd` by `word_copy_bwd` against an abstract
store/load interface. Flapjack infrastructure for `word_copy_bwd_thm`. -/
theorem wordCopyBwd_sim {width : Nat} [NeZero width] (good : goodDimindex width) (be : Bool)
    (dm : BitVec width → Bool) (A0 B0 : BitVec width) (xs : List (BitVec 8))
    (R : List (BitVec 8) → (BitVec width → WordLocW width) → Prop)
    (load : ∀ ys m i (h : i < xs.length), R ys m →
      memLoadByteAuxExact m dm be (A0 + BitVec.ofNat width i) = some xs[i])
    (store : ∀ ys m j v, R ys m → j < ys.length →
      ∃ m1, memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width j) v = some m1 ∧ R (ys.set j v) m1) :
    ∀ n xp yp ys ys1 m, R ys m → listCopyBwd n xp xs yp ys = some ys1 → n < 2 ^ width →
      ∃ m1, wordCopyBwd be (BitVec.ofNat width n) (A0 + BitVec.ofNat width xp)
        (B0 + BitVec.ofNat width yp) m dm = some m1 ∧ R ys1 m1 := by
  have big := goodDimindex_pow good
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xp yp ys ys1 m rel copied bound
    rw [listCopyBwd] at copied
    split at copied
    case isFalse => cases copied
    rename_i hb
    obtain ⟨hnx, hx, hny, hy⟩ := hb
    have ld : ∀ k (h : k ≤ xp), memLoadByteAuxExact m dm be
        (A0 + BitVec.ofNat width xp - BitVec.ofNat width k) = some (xs[minus xp k]'(by unfold minus; omega)) := by
      intro k h
      rw [byteAddr_sub _ _ _ h]
      exact load ys m (xp - k) (by omega) rel
    have st : ∀ zs m' k v, R zs m' → k ≤ yp → yp < zs.length → ∃ m1, memStoreByteAuxExact m' dm be
        (B0 + BitVec.ofNat width yp - BitVec.ofNat width k) v = some m1 ∧ R (zs.set (minus yp k) v) m1 := by
      intro zs m' k v r h h'
      rw [byteAddr_sub _ _ _ h]
      exact store zs m' (yp - k) v r (by omega)
    have n4 := ofNat_lt_ofNat_iff (n := n) (k := 4) bound (show 4 < 2 ^ width by omega)
    have n2 := ofNat_lt_ofNat_iff (n := n) (k := 2) bound (show 2 < 2 ^ width by omega)
    have e0 := ofNat_eq_ofNat_iff (n := n) (k := 0) bound (show 0 < 2 ^ width by omega)
    have e2 := ofNat_eq_ofNat_iff (n := n) (k := 2) bound (show 2 < 2 ^ width by omega)
    by_cases h0 : n = 0
    · subst n
      simp only [dite_true] at copied
      cases copied
      exact ⟨m, wordCopyBwd_zero be _ _ m dm good, rel⟩
    rw [wordCopyBwd, dif_neg (by omega)]
    simp only [h0, dite_false] at copied
    have ld0 : memLoadByteAuxExact m dm be (A0 + BitVec.ofNat width xp) = some xs[xp] :=
      load ys m xp (by omega) rel
    by_cases h1 : n = 1
    · subst n
      simp only [dite_true] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := store ys m yp xs[xp] rel (by omega)
      refine ⟨m1, ?_, r1⟩
      simp only [show BitVec.ofNat width 1 < 4#width from n4.mpr (by omega),
        show BitVec.ofNat width 1 < 2#width from n2.mpr (by omega), dite_true, if_true,
        show ¬ BitVec.ofNat width 1 = 0#width from fun h => absurd (e0.mp h) (by omega), if_false,
        ld0, Option.bind_some, s1]
    simp only [h1, dite_false] at copied
    have yl : ∀ zs : List (BitVec 8), zs.length = ys.length → yp < zs.length := fun zs h => by omega
    by_cases h2 : n = 2
    · subst n
      simp only [dite_true, Function.comp_apply] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := st ys m 0 (xs[minus xp 0]'(by unfold minus; omega)) rel (by omega) (by omega)
      obtain ⟨m2, s2, r2⟩ := st _ m1 1 (xs[minus xp 1]'(by unfold minus; omega)) r1 (by omega) (yl _ (by simp))
      refine ⟨m2, ?_, r2⟩
      have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) xs[xp] = some m1 := by
        simpa [minus] using s1
      simp only [show BitVec.ofNat width 2 < 4#width from n4.mpr (by omega),
        show ¬ BitVec.ofNat width 2 < 2#width from fun h => absurd (n2.mp h) (by omega), dite_true, if_false,
        if_true, ld0, ld 1 (by omega), Option.bind_some, s1', s2]
    simp only [h2, dite_false] at copied
    by_cases h3 : n = 3
    · subst n
      simp only [dite_true, Function.comp_apply] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := st ys m 0 (xs[minus xp 0]'(by unfold minus; omega)) rel (by omega) (by omega)
      obtain ⟨m2, s2, r2⟩ := st _ m1 1 (xs[minus xp 1]'(by unfold minus; omega)) r1 (by omega) (yl _ (by simp))
      obtain ⟨m3, s3, r3⟩ := st _ m2 2 (xs[minus xp 2]'(by unfold minus; omega)) r2 (by omega) (yl _ (by simp))
      refine ⟨m3, ?_, r3⟩
      have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) xs[xp] = some m1 := by
        simpa [minus] using s1
      simp only [show BitVec.ofNat width 3 < 4#width from n4.mpr (by omega),
        show ¬ BitVec.ofNat width 3 < 2#width from fun h => absurd (n2.mp h) (by omega), dite_true, if_false,
        show ¬ BitVec.ofNat width 3 = 2#width from fun h => absurd (e2.mp h) (by omega),
        ld0, ld 1 (by omega), ld 2 (by omega), Option.bind_some, s1', s2, s3]
    simp only [h3, dite_false, Function.comp_apply] at copied
    obtain ⟨m1, s1, r1⟩ := st ys m 0 (xs[minus xp 0]'(by unfold minus; omega)) rel (by omega) (by omega)
    obtain ⟨m2, s2, r2⟩ := st _ m1 1 (xs[minus xp 1]'(by unfold minus; omega)) r1 (by omega) (yl _ (by simp))
    obtain ⟨m3, s3, r3⟩ := st _ m2 2 (xs[minus xp 2]'(by unfold minus; omega)) r2 (by omega) (yl _ (by simp))
    obtain ⟨m4, s4, r4⟩ := st _ m3 3 (xs[minus xp 3]'(by unfold minus; omega)) r3 (by omega) (yl _ (by simp))
    obtain ⟨m5, s5, r5⟩ := ih (n - 4) (by omega) (minus xp 4) (minus yp 4) _ ys1 m4 r4 copied (by omega)
    refine ⟨m5, ?_, r5⟩
    have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) xs[xp] = some m1 := by
      simpa [minus] using s1
    have nsub : BitVec.ofNat width n - 4#width = BitVec.ofNat width (n - 4) := by
      have := byteAddr_sub (0 : BitVec width) n 4 (by omega)
      simpa using this
    have rest : wordCopyBwd be (BitVec.ofNat width n - 4#width) (A0 + BitVec.ofNat width xp - 4#width)
        (B0 + BitVec.ofNat width yp - 4#width) m4 dm = some m5 := by
      rw [nsub]
      by_cases h4 : n = 4
      · subst n
        rw [wordCopyBwd_zero be _ _ m4 dm good] at s5 ⊢
        exact s5
      · rw [byteAddr_sub _ _ _ (by omega), byteAddr_sub _ _ _ (by omega)]
        exact s5
    simp only [show ¬ BitVec.ofNat width n < 4#width from fun h => absurd (n4.mp h) (by omega), dite_false,
      ld0, ld 1 (by omega), ld 2 (by omega), ld 3 (by omega), Option.bind_some, s1', s2, s3, s4]
    exact rest
/-- Simulation of `list_copy_bwd_alias` by `word_copy_bwd` against an abstract
store/load interface. Flapjack infrastructure for `word_copy_bwd_alias_thm`. -/
theorem wordCopyBwdAlias_sim {width : Nat} [NeZero width] (good : goodDimindex width) (be : Bool)
    (dm : BitVec width → Bool) (A0 B0 : BitVec width)
    (R : List (BitVec 8) → (BitVec width → WordLocW width) → Prop)
    (load : ∀ ys m i (h : i < ys.length), R ys m →
      memLoadByteAuxExact m dm be (A0 + BitVec.ofNat width i) = some ys[i])
    (store : ∀ ys m j v, R ys m → j < ys.length →
      ∃ m1, memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width j) v = some m1 ∧ R (ys.set j v) m1) :
    ∀ n xp yp ys ys1 m, R ys m → listCopyBwdAlias n xp yp ys = some ys1 → n < 2 ^ width →
      ∃ m1, wordCopyBwd be (BitVec.ofNat width n) (A0 + BitVec.ofNat width xp)
        (B0 + BitVec.ofNat width yp) m dm = some m1 ∧ R ys1 m1 := by
  have big := goodDimindex_pow good
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xp yp ys ys1 m rel copied bound
    rw [listCopyBwdAlias] at copied
    split at copied
    case isFalse => cases copied
    rename_i hb
    obtain ⟨hnx, hx, hny, hy⟩ := hb
    have ld : ∀ k (h : k ≤ xp), memLoadByteAuxExact m dm be
        (A0 + BitVec.ofNat width xp - BitVec.ofNat width k) = some (ys[minus xp k]'(by unfold minus; omega)) := by
      intro k h
      rw [byteAddr_sub _ _ _ h]
      exact load ys m (xp - k) (by omega) rel
    have st : ∀ zs m' k v, R zs m' → k ≤ yp → yp < zs.length → ∃ m1, memStoreByteAuxExact m' dm be
        (B0 + BitVec.ofNat width yp - BitVec.ofNat width k) v = some m1 ∧ R (zs.set (minus yp k) v) m1 := by
      intro zs m' k v r h h'
      rw [byteAddr_sub _ _ _ h]
      exact store zs m' (yp - k) v r (by omega)
    have n4 := ofNat_lt_ofNat_iff (n := n) (k := 4) bound (show 4 < 2 ^ width by omega)
    have n2 := ofNat_lt_ofNat_iff (n := n) (k := 2) bound (show 2 < 2 ^ width by omega)
    have e0 := ofNat_eq_ofNat_iff (n := n) (k := 0) bound (show 0 < 2 ^ width by omega)
    have e2 := ofNat_eq_ofNat_iff (n := n) (k := 2) bound (show 2 < 2 ^ width by omega)
    by_cases h0 : n = 0
    · subst n
      simp only [dite_true] at copied
      cases copied
      exact ⟨m, wordCopyBwd_zero be _ _ m dm good, rel⟩
    rw [wordCopyBwd, dif_neg (by omega)]
    simp only [h0, dite_false] at copied
    have ld0 : memLoadByteAuxExact m dm be (A0 + BitVec.ofNat width xp) = some ys[xp] :=
      load ys m xp (by omega) rel
    by_cases h1 : n = 1
    · subst n
      simp only [dite_true] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := store ys m yp ys[xp] rel (by omega)
      refine ⟨m1, ?_, r1⟩
      simp only [show BitVec.ofNat width 1 < 4#width from n4.mpr (by omega),
        show BitVec.ofNat width 1 < 2#width from n2.mpr (by omega), dite_true, if_true,
        show ¬ BitVec.ofNat width 1 = 0#width from fun h => absurd (e0.mp h) (by omega), if_false,
        ld0, Option.bind_some, s1]
    simp only [h1, dite_false] at copied
    have yl : ∀ zs : List (BitVec 8), zs.length = ys.length → yp < zs.length := fun zs h => by omega
    by_cases h2 : n = 2
    · subst n
      simp only [dite_true, Function.comp_apply] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := st ys m 0 (ys[minus xp 0]'(by unfold minus; omega)) rel (by omega) (by omega)
      obtain ⟨m2, s2, r2⟩ := st _ m1 1 (ys[minus xp 1]'(by unfold minus; omega)) r1 (by omega) (yl _ (by simp))
      refine ⟨m2, ?_, r2⟩
      have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) ys[xp] = some m1 := by
        simpa [minus] using s1
      simp only [show BitVec.ofNat width 2 < 4#width from n4.mpr (by omega),
        show ¬ BitVec.ofNat width 2 < 2#width from fun h => absurd (n2.mp h) (by omega), dite_true, if_false,
        if_true, ld0, ld 1 (by omega), Option.bind_some, s1', s2]
    simp only [h2, dite_false] at copied
    by_cases h3 : n = 3
    · subst n
      simp only [dite_true, Function.comp_apply] at copied
      cases copied
      obtain ⟨m1, s1, r1⟩ := st ys m 0 (ys[minus xp 0]'(by unfold minus; omega)) rel (by omega) (by omega)
      obtain ⟨m2, s2, r2⟩ := st _ m1 1 (ys[minus xp 1]'(by unfold minus; omega)) r1 (by omega) (yl _ (by simp))
      obtain ⟨m3, s3, r3⟩ := st _ m2 2 (ys[minus xp 2]'(by unfold minus; omega)) r2 (by omega) (yl _ (by simp))
      refine ⟨m3, ?_, r3⟩
      have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) ys[xp] = some m1 := by
        simpa [minus] using s1
      simp only [show BitVec.ofNat width 3 < 4#width from n4.mpr (by omega),
        show ¬ BitVec.ofNat width 3 < 2#width from fun h => absurd (n2.mp h) (by omega), dite_true, if_false,
        show ¬ BitVec.ofNat width 3 = 2#width from fun h => absurd (e2.mp h) (by omega),
        ld0, ld 1 (by omega), ld 2 (by omega), Option.bind_some, s1', s2, s3]
    simp only [h3, dite_false, Function.comp_apply] at copied
    obtain ⟨m1, s1, r1⟩ := st ys m 0 (ys[minus xp 0]'(by unfold minus; omega)) rel (by omega) (by omega)
    obtain ⟨m2, s2, r2⟩ := st _ m1 1 (ys[minus xp 1]'(by unfold minus; omega)) r1 (by omega) (yl _ (by simp))
    obtain ⟨m3, s3, r3⟩ := st _ m2 2 (ys[minus xp 2]'(by unfold minus; omega)) r2 (by omega) (yl _ (by simp))
    obtain ⟨m4, s4, r4⟩ := st _ m3 3 (ys[minus xp 3]'(by unfold minus; omega)) r3 (by omega) (yl _ (by simp))
    obtain ⟨m5, s5, r5⟩ := ih (n - 4) (by omega) (minus xp 4) (minus yp 4) _ ys1 m4 r4 copied (by omega)
    refine ⟨m5, ?_, r5⟩
    have s1' : memStoreByteAuxExact m dm be (B0 + BitVec.ofNat width yp) ys[xp] = some m1 := by
      simpa [minus] using s1
    have nsub : BitVec.ofNat width n - 4#width = BitVec.ofNat width (n - 4) := by
      have := byteAddr_sub (0 : BitVec width) n 4 (by omega)
      simpa using this
    have rest : wordCopyBwd be (BitVec.ofNat width n - 4#width) (A0 + BitVec.ofNat width xp - 4#width)
        (B0 + BitVec.ofNat width yp - 4#width) m4 dm = some m5 := by
      rw [nsub]
      by_cases h4 : n = 4
      · subst n
        rw [wordCopyBwd_zero be _ _ m4 dm good] at s5 ⊢
        exact s5
      · rw [byteAddr_sub _ _ _ (by omega), byteAddr_sub _ _ _ (by omega)]
        exact s5
    simp only [show ¬ BitVec.ofNat width n < 4#width from fun h => absurd (n4.mp h) (by omega), dite_false,
      ld0, ld 1 (by omega), ld 2 (by omega), ld 3 (by omega), Option.bind_some, s1', s2, s3, s4]
    exact rest

/-- Reading facts for a related byte array. Flapjack infrastructure for the
`word_copy_*_thm` theorems. -/
theorem memoryRel_byteArrayRead {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (bl : Bool) (p : Nat) (v : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (fl : Bool)
    (bs : List (BitVec 8))
    (related : memoryRel c be ts refs sp st m dm ((.refPtr bl p, v) :: vars))
    (found : sptLookup p refs = some (.byteArray fl bs)) (good : goodDimindex width) :
    ∃ w a, v = .word w ∧ getRealAddr c st w = some a ∧ bs.length < 2 ^ width ∧
      ∀ i (h : i < bs.length), memLoadByteAuxExact m dm be
        (a + StackRemove.bytesInWord width + BitVec.ofNat width i) = some bs[i] := by
  obtain ⟨w, a, _, _, loc, _, _, _, _, _, _, real, _, _, reads, _, len⟩ :=
    memoryRel_byteArrayImp (β := Unit) c be ts refs sp st m dm bl fl p bs v vars ⟨related, found, good⟩
  refine ⟨w, a, loc, real, ?_, reads⟩
  have pw : 2 ^ (width - 3) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
  split at len <;> omega

/-- Storing a byte of the related byte array at the head of the roots.
Flapjack infrastructure for the `word_copy_*_thm` theorems. -/
theorem memoryRel_byteArrayStoreHead {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (bl : Bool) (p : Nat) (w a : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (fl : Bool)
    (ys : List (BitVec 8)) (j : Nat) (b : BitVec 8)
    (related : memoryRel c be ts (sptInsert p (.byteArray fl ys) refs) sp st m dm ((.refPtr bl p, .word w) :: vars))
    (good : goodDimindex width) (real : getRealAddr c st w = some a) (bound : j < ys.length) :
    ∃ m1, memStoreByteAuxExact m dm be (a + StackRemove.bytesInWord width + BitVec.ofNat width j) b = some m1 ∧
      memoryRel c be ts (sptInsert p (.byteArray fl (ys.set j b)) refs) sp st m1 dm ((.refPtr bl p, .word w) :: vars) := by
  obtain ⟨m1, s, r⟩ := memoryRel_byteArrayImpStore c be ts _ sp st m dm bl p w vars fl ys a j b
    ⟨related, sptLookup_sptInsert_same p _ refs, good, real, bound⟩
  rw [sptInsert_insert_shadow] at r
  exact ⟨m1, s, r⟩

/-- Exact HOL `word_copy_fwd_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_fwd_thm"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem wordCopyFwd_thm {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat) (p2 : Nat) (fl_ys : Bool)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (dm : BitVec width → Bool)
    (bl1 : Bool) (p1 : Nat) (v1 : WordLocW width) (bl2 : Bool) (v2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (fl_xs : Bool)
    (xs : List (BitVec 8)) :
    ∀ (n xp yp : Nat) (ys ys1 : List (BitVec 8)) (m : BitVec width → WordLocW width),
      memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys) refs) sp st m dm
        ((.refPtr bl1 p1, v1) :: (.refPtr bl2 p2, v2) :: vars) ∧
      sptLookup p1 refs = some (.byteArray fl_xs xs) ∧
      listCopyFwd n xp xs yp ys = some ys1 ∧ goodDimindex width ∧ n < 2 ^ width ∧ p1 ≠ p2 →
      ∃ (w1 w2 a1 a2 : BitVec width) (m1 : BitVec width → WordLocW width),
        v1 = .word w1 ∧ v2 = .word w2 ∧ getRealAddr c st w1 = some a1 ∧ getRealAddr c st w2 = some a2 ∧
        wordCopyFwd be (BitVec.ofNat width n) (a1 + StackRemove.bytesInWord width + BitVec.ofNat width xp)
          (a2 + StackRemove.bytesInWord width + BitVec.ofNat width yp) m dm = some m1 ∧
        memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys1) refs) sp st m1 dm
          ((.refPtr bl1 p1, v1) :: (.refPtr bl2 p2, v2) :: vars) := by
  rintro n xp yp ys ys1 m ⟨rel, found, copied, good, bound, ne⟩
  have found' : ∀ zs, sptLookup p1 (sptInsert p2 (.byteArray fl_ys zs) refs) = some (.byteArray fl_xs xs) :=
    fun zs => (sptLookup_sptInsert_ne p2 p1 _ refs ne).trans found
  obtain ⟨w1, a1, hv1, real1, _, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl1 p1 v1 _ fl_xs xs rel (found' ys) good
  obtain ⟨w2, a2, hv2, real2, _, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl2 p2 v2 _ fl_ys ys (memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ rel)
      (sptLookup_sptInsert_same p2 _ refs) good
  subst hv1 hv2
  obtain ⟨m1, hc, hr⟩ := wordCopyFwd_sim good be dm (a1 + StackRemove.bytesInWord width)
    (a2 + StackRemove.bytesInWord width) xs
    (fun zs mm => memoryRel c be ts (sptInsert p2 (.byteArray fl_ys zs) refs) sp st mm dm
      ((.refPtr bl1 p1, .word w1) :: (.refPtr bl2 p2, .word w2) :: vars))
    (by
      intro zs mm i h r
      obtain ⟨w', a', hv, real', _, loads⟩ :=
        memoryRel_byteArrayRead c be ts _ sp st mm dm bl1 p1 _ _ fl_xs xs r (found' zs) good
      cases hv
      cases real'.symm.trans real1
      exact loads i h)
    (by
      intro zs mm j v r hj
      obtain ⟨m', s, r'⟩ := memoryRel_byteArrayStoreHead c be ts refs sp st mm dm bl2 p2 w2 a2 _ fl_ys zs j v
        (memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ r) good real2 hj
      exact ⟨m', s, memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ r'⟩)
    n xp yp ys ys1 m rel copied bound
  exact ⟨w1, w2, a1, a2, m1, rfl, rfl, real1, real2, hc, hr⟩

/-- Exact HOL `word_copy_fwd_alias_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_fwd_alias_thm"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem wordCopyFwdAlias_thm {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat) (p2 : Nat) (fl_ys : Bool)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (dm : BitVec width → Bool)
    (bl : Bool) (v2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    ∀ (n xp yp : Nat) (ys ys1 : List (BitVec 8)) (m : BitVec width → WordLocW width),
      memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys) refs) sp st m dm
        ((.refPtr bl p2, v2) :: vars) ∧
      listCopyFwdAlias n xp yp ys = some ys1 ∧ goodDimindex width ∧ n < 2 ^ width →
      ∃ (w2 a2 : BitVec width) (m1 : BitVec width → WordLocW width),
        v2 = .word w2 ∧ getRealAddr c st w2 = some a2 ∧
        wordCopyFwd be (BitVec.ofNat width n) (a2 + StackRemove.bytesInWord width + BitVec.ofNat width xp)
          (a2 + StackRemove.bytesInWord width + BitVec.ofNat width yp) m dm = some m1 ∧
        memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys1) refs) sp st m1 dm
          ((.refPtr bl p2, v2) :: vars) := by
  rintro n xp yp ys ys1 m ⟨rel, copied, good, bound⟩
  obtain ⟨w2, a2, hv2, real2, _, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl p2 v2 _ fl_ys ys rel
      (sptLookup_sptInsert_same p2 _ refs) good
  subst hv2
  obtain ⟨m1, hc, hr⟩ := wordCopyFwdAlias_sim good be dm (a2 + StackRemove.bytesInWord width)
    (a2 + StackRemove.bytesInWord width)
    (fun zs mm => memoryRel c be ts (sptInsert p2 (.byteArray fl_ys zs) refs) sp st mm dm
      ((.refPtr bl p2, .word w2) :: vars))
    (by
      intro zs mm i h r
      obtain ⟨w', a', hv, real', _, loads⟩ :=
        memoryRel_byteArrayRead c be ts _ sp st mm dm bl p2 _ _ fl_ys zs r (sptLookup_sptInsert_same p2 _ refs) good
      cases hv
      cases real'.symm.trans real2
      exact loads i h)
    (fun zs mm j v r hj => memoryRel_byteArrayStoreHead c be ts refs sp st mm dm bl p2 w2 a2 _ fl_ys zs j v
        r good real2 hj)
    n xp yp ys ys1 m rel copied bound
  exact ⟨w2, a2, m1, rfl, real2, hc, hr⟩

/-- Exact HOL `word_copy_bwd_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_bwd_thm"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem wordCopyBwd_thm {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat) (p2 : Nat) (fl_ys : Bool)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (dm : BitVec width → Bool)
    (bl1 : Bool) (p1 : Nat) (v1 : WordLocW width) (bl2 : Bool) (v2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (fl_xs : Bool)
    (xs : List (BitVec 8)) :
    ∀ (n xp yp : Nat) (ys ys1 : List (BitVec 8)) (m : BitVec width → WordLocW width),
      memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys) refs) sp st m dm
        ((.refPtr bl1 p1, v1) :: (.refPtr bl2 p2, v2) :: vars) ∧
      sptLookup p1 refs = some (.byteArray fl_xs xs) ∧
      listCopyBwd n xp xs yp ys = some ys1 ∧ goodDimindex width ∧ n < 2 ^ width ∧ p1 ≠ p2 →
      ∃ (w1 w2 a1 a2 : BitVec width) (m1 : BitVec width → WordLocW width),
        v1 = .word w1 ∧ v2 = .word w2 ∧ getRealAddr c st w1 = some a1 ∧ getRealAddr c st w2 = some a2 ∧
        wordCopyBwd be (BitVec.ofNat width n) (a1 + StackRemove.bytesInWord width + BitVec.ofNat width xp)
          (a2 + StackRemove.bytesInWord width + BitVec.ofNat width yp) m dm = some m1 ∧
        memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys1) refs) sp st m1 dm
          ((.refPtr bl1 p1, v1) :: (.refPtr bl2 p2, v2) :: vars) := by
  rintro n xp yp ys ys1 m ⟨rel, found, copied, good, bound, ne⟩
  have found' : ∀ zs, sptLookup p1 (sptInsert p2 (.byteArray fl_ys zs) refs) = some (.byteArray fl_xs xs) :=
    fun zs => (sptLookup_sptInsert_ne p2 p1 _ refs ne).trans found
  obtain ⟨w1, a1, hv1, real1, _, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl1 p1 v1 _ fl_xs xs rel (found' ys) good
  obtain ⟨w2, a2, hv2, real2, _, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl2 p2 v2 _ fl_ys ys (memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ rel)
      (sptLookup_sptInsert_same p2 _ refs) good
  subst hv1 hv2
  obtain ⟨m1, hc, hr⟩ := wordCopyBwd_sim good be dm (a1 + StackRemove.bytesInWord width)
    (a2 + StackRemove.bytesInWord width) xs
    (fun zs mm => memoryRel c be ts (sptInsert p2 (.byteArray fl_ys zs) refs) sp st mm dm
      ((.refPtr bl1 p1, .word w1) :: (.refPtr bl2 p2, .word w2) :: vars))
    (by
      intro zs mm i h r
      obtain ⟨w', a', hv, real', _, loads⟩ :=
        memoryRel_byteArrayRead c be ts _ sp st mm dm bl1 p1 _ _ fl_xs xs r (found' zs) good
      cases hv
      cases real'.symm.trans real1
      exact loads i h)
    (by
      intro zs mm j v r hj
      obtain ⟨m', s, r'⟩ := memoryRel_byteArrayStoreHead c be ts refs sp st mm dm bl2 p2 w2 a2 _ fl_ys zs j v
        (memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ r) good real2 hj
      exact ⟨m', s, memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ r'⟩)
    n xp yp ys ys1 m rel copied bound
  exact ⟨w1, w2, a1, a2, m1, rfl, rfl, real1, real2, hc, hr⟩


/-- Exact HOL `word_copy_bwd_alias_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_bwd_alias_thm"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem wordCopyBwdAlias_thm {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat) (p2 : Nat) (fl_ys : Bool)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (dm : BitVec width → Bool)
    (bl : Bool) (v2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    ∀ (n xp yp : Nat) (ys ys1 : List (BitVec 8)) (m : BitVec width → WordLocW width),
      memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys) refs) sp st m dm
        ((.refPtr bl p2, v2) :: vars) ∧
      listCopyBwdAlias n xp yp ys = some ys1 ∧ goodDimindex width ∧ n < 2 ^ width →
      ∃ (w2 a2 : BitVec width) (m1 : BitVec width → WordLocW width),
        v2 = .word w2 ∧ getRealAddr c st w2 = some a2 ∧
        wordCopyBwd be (BitVec.ofNat width n) (a2 + StackRemove.bytesInWord width + BitVec.ofNat width xp)
          (a2 + StackRemove.bytesInWord width + BitVec.ofNat width yp) m dm = some m1 ∧
        memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys1) refs) sp st m1 dm
          ((.refPtr bl p2, v2) :: vars) := by
  rintro n xp yp ys ys1 m ⟨rel, copied, good, bound⟩
  obtain ⟨w2, a2, hv2, real2, _, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl p2 v2 _ fl_ys ys rel
      (sptLookup_sptInsert_same p2 _ refs) good
  subst hv2
  obtain ⟨m1, hc, hr⟩ := wordCopyBwdAlias_sim good be dm (a2 + StackRemove.bytesInWord width)
    (a2 + StackRemove.bytesInWord width)
    (fun zs mm => memoryRel c be ts (sptInsert p2 (.byteArray fl_ys zs) refs) sp st mm dm
      ((.refPtr bl p2, .word w2) :: vars))
    (by
      intro zs mm i h r
      obtain ⟨w', a', hv, real', _, loads⟩ :=
        memoryRel_byteArrayRead c be ts _ sp st mm dm bl p2 _ _ fl_ys zs r (sptLookup_sptInsert_same p2 _ refs) good
      cases hv
      cases real'.symm.trans real2
      exact loads i h)
    (fun zs mm j v r hj => memoryRel_byteArrayStoreHead c be ts refs sp st mm dm bl p2 w2 a2 _ fl_ys zs j v
        r good real2 hj)
    n xp yp ys ys1 m rel copied bound
  exact ⟨w2, a2, m1, rfl, real2, hc, hr⟩

/-- Unsigned comparison of in-range numerals. Flapjack infrastructure. -/
theorem ofNat_le_ofNat_iff {width : Nat} {n k : Nat} (hn : n < 2 ^ width) (hk : k < 2 ^ width) :
    BitVec.ofNat width n ≤ BitVec.ofNat width k ↔ n ≤ k := by
  simp [BitVec.le_def, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hk]

/-- Exact HOL `word_copy_array_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_array_thm"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem wordCopyArray_thm {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (dm : BitVec width → Bool)
    (bl1 : Bool) (p1 : Nat) (v1 : WordLocW width) (bl2 : Bool) (p2 : Nat) (v2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (fl_xs fl_ys : Bool) :
    ∀ (n xp yp : Nat) (xs ys ys1 : List (BitVec 8)) (m : BitVec width → WordLocW width),
      memoryRel c be ts refs sp st m dm ((.refPtr bl1 p1, v1) :: (.refPtr bl2 p2, v2) :: vars) ∧
      sptLookup p1 refs = some (.byteArray fl_xs xs) ∧
      sptLookup p2 refs = some (.byteArray fl_ys ys) ∧
      copyArray (xs, (xp : Int)) (n : Int) (some (ys, (yp : Int))) = some ys1 ∧
      goodDimindex width ∧ p1 ≠ p2 →
      ∃ (w1 w2 a1 a2 : BitVec width) (m1 : BitVec width → WordLocW width),
        v1 = .word w1 ∧ v2 = .word w2 ∧ getRealAddr c st w1 = some a1 ∧ getRealAddr c st w2 = some a2 ∧
        wordCopyArray be (BitVec.ofNat width n) (a1 + StackRemove.bytesInWord width) (BitVec.ofNat width xp)
          (a2 + StackRemove.bytesInWord width) (BitVec.ofNat width yp) m dm = some m1 ∧
        memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys1) refs) sp st m1 dm
          ((.refPtr bl1 p1, v1) :: (.refPtr bl2 p2, v2) :: vars) := by
  rintro n xp yp xs ys ys1 m ⟨rel, found1, found2, copied, good, ne⟩
  obtain ⟨hx, hy, -⟩ := copyArray_some_eq xs ys ys1 xp yp n copied
  have list := listCopy_thm xs ys xp yp n ys1 copied
  have rel' : memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys) refs) sp st m dm
      ((.refPtr bl1 p1, v1) :: (.refPtr bl2 p2, v2) :: vars) := by
    rw [sptInsertUnchanged refs p2 _ found2]; exact rel
  obtain ⟨w1, a1, hv1, real1, len1, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl1 p1 v1 _ fl_xs xs rel found1 good
  obtain ⟨w2, a2, hv2, real2, len2, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl2 p2 v2 _ fl_ys ys (memoryRel_swap _ _ _ _ _ _ _ _ _ _ _ rel)
      found2 good
  have cmp := ofNat_le_ofNat_iff (width := width) (n := yp) (k := xp) (by omega) (by omega)
  unfold listCopy at list
  unfold wordCopyArray
  split at list
  · rename_i hc
    by_cases hle : yp ≤ xp
    · simp only [cmp, hle, if_true]
      obtain ⟨w1', w2', a1', a2', m1, e1, e2, r1, r2, hc', hr⟩ :=
        wordCopyFwd_thm c be ts p2 fl_ys refs sp st dm bl1 p1 v1 bl2 v2 vars fl_xs xs n xp yp ys ys1 m
          ⟨rel', found1, list, good, by omega, ne⟩
      subst hv1 hv2
      cases e1; cases e2
      cases r1.symm.trans real1; cases r2.symm.trans real2
      exact ⟨w1, w2, a1, a2, m1, rfl, rfl, real1, real2, hc', hr⟩
    · simp only [cmp, hle, if_false]
      have hn : n = 0 := by omega
      subst hn
      rw [listCopyFwd] at list
      simp only [dif_pos (show xp + 0 ≤ xs.length ∧ yp + 0 ≤ ys.length by omega), dite_true] at list
      cases list
      refine ⟨w1, w2, a1, a2, m, hv1, hv2, real1, real2, ?_, rel'⟩
      exact wordCopyBwd_zero be _ _ m dm good
  · rename_i hc
    have hle : ¬ yp ≤ xp := by omega
    simp only [cmp, hle, if_false]
    obtain ⟨w1', w2', a1', a2', m1, e1, e2, r1, r2, hc', hr⟩ :=
      wordCopyBwd_thm c be ts p2 fl_ys refs sp st dm bl1 p1 v1 bl2 v2 vars fl_xs xs n (xp + n - 1) (yp + n - 1)
        ys ys1 m ⟨rel', found1, list, good, by omega, ne⟩
    subst hv1 hv2
    cases e1; cases e2
    cases r1.symm.trans real1; cases r2.symm.trans real2
    refine ⟨w1, w2, a1, a2, m1, rfl, rfl, real1, real2, ?_, hr⟩
    rw [byteAddr_add, byteAddr_add, byteAddr_sub _ _ _ (by omega), byteAddr_sub _ _ _ (by omega)]
    exact hc'

/-- Exact HOL `word_copy_array_alias_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_copy_array_alias_thm"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem wordCopyArrayAlias_thm {width : Nat} [NeZero width]
    (c : DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (dm : BitVec width → Bool)
    (bl : Bool) (p2 : Nat) (v2 : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (fl_ys : Bool) :
    ∀ (n xp yp : Nat) (ys ys1 : List (BitVec 8)) (m : BitVec width → WordLocW width),
      memoryRel c be ts refs sp st m dm ((.refPtr bl p2, v2) :: vars) ∧
      sptLookup p2 refs = some (.byteArray fl_ys ys) ∧
      copyArray (ys, (xp : Int)) (n : Int) (some (ys, (yp : Int))) = some ys1 ∧
      goodDimindex width →
      ∃ (w2 a2 : BitVec width) (m1 : BitVec width → WordLocW width),
        v2 = .word w2 ∧ getRealAddr c st w2 = some a2 ∧
        wordCopyArray be (BitVec.ofNat width n) (a2 + StackRemove.bytesInWord width) (BitVec.ofNat width xp)
          (a2 + StackRemove.bytesInWord width) (BitVec.ofNat width yp) m dm = some m1 ∧
        memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys1) refs) sp st m1 dm
          ((.refPtr bl p2, v2) :: vars) := by
  rintro n xp yp ys ys1 m ⟨rel, found2, copied, good⟩
  obtain ⟨hx, hy, -⟩ := copyArray_some_eq ys ys ys1 xp yp n copied
  have list := listCopyAlias_thm ys xp yp n ys1 copied
  have rel' : memoryRel c be ts (sptInsert p2 (.byteArray fl_ys ys) refs) sp st m dm
      ((.refPtr bl p2, v2) :: vars) := by
    rw [sptInsertUnchanged refs p2 _ found2]; exact rel
  obtain ⟨w2, a2, hv2, real2, len2, _⟩ :=
    memoryRel_byteArrayRead c be ts _ sp st m dm bl p2 v2 _ fl_ys ys rel found2 good
  have cmp := ofNat_le_ofNat_iff (width := width) (n := yp) (k := xp) (by omega) (by omega)
  unfold listCopyAlias at list
  unfold wordCopyArray
  split at list
  · rename_i hc
    by_cases hle : yp ≤ xp
    · simp only [cmp, hle, if_true]
      obtain ⟨w2', a2', m1, e2, r2, hc', hr⟩ :=
        wordCopyFwdAlias_thm c be ts p2 fl_ys refs sp st dm bl v2 vars n xp yp ys ys1 m
          ⟨rel', list, good, by omega⟩
      subst hv2
      cases e2
      cases r2.symm.trans real2
      exact ⟨w2, a2, m1, rfl, real2, hc', hr⟩
    · simp only [cmp, hle, if_false]
      have hn : n = 0 := by omega
      subst hn
      rw [listCopyFwdAlias] at list
      simp only [dif_pos (show xp + 0 ≤ ys.length ∧ yp + 0 ≤ ys.length by omega), dite_true] at list
      cases list
      refine ⟨w2, a2, m, hv2, real2, ?_, rel'⟩
      exact wordCopyBwd_zero be _ _ m dm good
  · rename_i hc
    have hle : ¬ yp ≤ xp := by omega
    simp only [cmp, hle, if_false]
    obtain ⟨w2', a2', m1, e2, r2, hc', hr⟩ :=
      wordCopyBwdAlias_thm c be ts p2 fl_ys refs sp st dm bl v2 vars n (xp + n - 1) (yp + n - 1)
        ys ys1 m ⟨rel', list, good, by omega⟩
    subst hv2
    cases e2
    cases r2.symm.trans real2
    refine ⟨w2, a2, m1, rfl, real2, ?_, hr⟩
    rw [byteAddr_add, byteAddr_add, byteAddr_sub _ _ _ (by omega), byteAddr_sub _ _ _ (by omega)]
    exact hc'
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
