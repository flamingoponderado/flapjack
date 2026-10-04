import Flapjack.Compiler.Backend.LabToTarget.StateRel
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Compiler.Backend.LabToTarget.InstMem
import Flapjack.Compiler.Backend.LabToTarget.InstFrame
import Flapjack.Compiler.Backend.LabToTarget.CodeAppend
import Flapjack.Misc.FindIndex
import Flapjack.Misc.FindIndex.Membership

/-! FFI bytearray and I/O-name helpers of the original `lab_to_targetProof`
(lab_to_targetProofScript.sml:524-530, 1666-1785, 3027-3080), used by the
`CallFFI` case of `compile_correct`. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabLang Flapjack.Basis.Pure.MlString Flapjack.Misc
open Flapjack.HolByte

/-- Exact HOL `has_io_name_def`: some line of the code is a `CallFFI index`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def hasIoName {width : Nat} [NeZero width] (index : MlString) :
    List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) → Prop
  | [] => False
  | ⟨_, []⟩ :: xs => hasIoName index xs
  | ⟨k, y :: ys⟩ :: xs =>
      hasIoName index (⟨k, ys⟩ :: xs) ∨
        match y with
        | .labAsm (.callFFI i) _ _ _ => i = index
        | _ => False

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem imp_hasIoName {width : Nat} [NeZero width] {C F : Type}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width C F) (index : MlString)
    (l : BitVec width) (bytes : List (BitVec 8)) (n : Nat) :
    asmFetch s1 = some (.labAsm (.callFFI index) l bytes n) → hasIoName index s1.code := by
  unfold asmFetch
  generalize s1.pc = pc
  generalize s1.code = code
  intro h
  induction pc, code using asmFetchAux.induct with
  | case1 pc => simp [asmFetchAux] at h
  | case2 pc k rest ih =>
    simp only [asmFetchAux] at h
    rw [hasIoName.eq_2]; exact ih h
  | case3 pc k line lines rest hl ih =>
    simp only [asmFetchAux, hl, ↓reduceIte] at h
    rw [hasIoName.eq_def]; exact Or.inl (ih h)
  | case4 k line lines rest hl =>
    simp only [asmFetchAux, hl, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at h
    subst h
    rw [hasIoName.eq_def]; exact Or.inr rfl
  | case5 pc k line lines rest hl hp ih =>
    simp only [asmFetchAux, hl, hp, ↓reduceIte, Bool.false_eq_true] at h
    rw [hasIoName.eq_def]; exact Or.inl (ih h)

open Classical in
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem readBytearray_stateRel {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (p : BitVec width) (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (t1 : AsmState width) (ms1 : S) :
    ∀ (n : Nat) (a : BitVec width) (x : List (BitVec 8)),
      stateRel (mc, code2, labs, p) s1 t1 ms1 ∧
        readBytearrayWordHOL a n (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some x →
      readBytearrayWordHOL a n
        (fun a => if mc.progAddresses a then some (t1.mem a) else none) = some x := by
  intro n
  induction n with
  | zero => rintro a x ⟨-, h⟩; simpa [readBytearrayWordHOL] using h
  | succ n ih =>
    rintro a x ⟨hrel, h⟩
    obtain ⟨-, c2, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, c31, -⟩ := id hrel
    rw [readBytearrayWordHOL] at h ⊢
    cases hb : memLoadByteAuxExact s1.memory s1.memDomain s1.be a with
    | none => simp [hb] at h
    | some b =>
    cases hr : readBytearrayWordHOL (a + 1) n
        (memLoadByteAuxExact s1.memory s1.memDomain s1.be) with
    | none => rw [hb, hr] at h; simp at h
    | some rest =>
    rw [hb, hr] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    rw [ih (a + 1) rest ⟨hrel, hr⟩]
    simp only [memLoadByteAuxExact, riscvByteAlignHOL_eq c2] at hb
    cases hv : s1.memory (holByteAlign a) with
    | loc _ _ => simp [hv] at hb
    | word v =>
    simp only [hv] at hb
    by_cases hd : s1.memDomain (holByteAlign a) = true
    · simp only [hd, ↓reduceIte, Option.some.injEq] at hb
      obtain ⟨h1, -, h3⟩ := c31 a hd
      simp only [wordLocValByte, hv, wordLocVal, Option.some.injEq] at h3
      rw [← c3] at h1
      simp [h1, ← h3, ← hb, getByteHOL8_eq]
    · simp [hd] at hb

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "bytes_in_mem_asm_write_bytearray_lemma" (words_as_type_indexed_bitvec)]
theorem bytesInMem_asmWriteBytearray_lemma {width : Nat} [NeZero width] {Value : Type}
    (k d : BitVec width → Prop) (m1 m2 : BitVec width → Value) :
    ∀ (xs : List Value) (p : BitVec width), (∀ a, ¬ k a → m1 a = m2 a) →
      bytesInMemHOL p xs m1 d k → bytesInMemHOL p xs m2 d k :=
  fun xs p hm h => bytesInMem_frame p xs m1 m2 d k (fun a ha => (hm a ha).symm) h

/-- Writing a bytearray that the source could read leaves target memory
unchanged outside the source memory domain; Flapjack infrastructure for the
original `bytes_in_mem_asm_write_bytearray` proof. The byte-alignment is
`riscvByteAlignHOL`, the rendering of HOL `byte_align` inside
`memLoadByteAuxExact`. -/
theorem asmWriteBytearray_outside {width : Nat} [NeZero width]
    (memory : BitVec width → WordLocW width) (dom : BitVec width → Bool) (be : Bool)
    (m : BitVec width → BitVec 8)
    (hdom : ∀ a, dom (riscvByteAlignHOL a) = true → dom a = true) :
    ∀ (newBytes : List (BitVec 8)) (c1 : BitVec width) (x : List (BitVec 8)),
      readBytearrayWordHOL c1 newBytes.length (memLoadByteAuxExact memory dom be) = some x →
      ∀ a, ¬ dom a = true → asmWriteBytearrayHOL c1 newBytes m a = m a := by
  intro newBytes
  induction newBytes with
  | nil => intro _ _ _ _ _; rfl
  | cons b bs ih =>
    intro c1 x h a ha
    rw [List.length_cons, readBytearrayWordHOL] at h
    cases hb : memLoadByteAuxExact memory dom be c1 with
    | none => rw [hb] at h; simp at h
    | some b0 =>
    cases hr : readBytearrayWordHOL (c1 + 1) bs.length (memLoadByteAuxExact memory dom be) with
    | none => rw [hb, hr] at h; simp at h
    | some rest =>
    have hne : a ≠ c1 := by
      rintro rfl
      simp only [memLoadByteAuxExact] at hb
      split at hb
      · cases hb
      · split at hb
        · exact ha (hdom _ ‹_›)
        · cases hb
    simp only [asmWriteBytearrayHOL, hne, ↓reduceIte]
    exact ih (c1 + 1) rest hr a ha

/-- HOL `byte_align` in the domain-closure premise is written
`riscvByteAlignHOL`, the same rendering that `memLoadByteAuxExact` (HOL
`mem_load_byte_aux`) uses in the read premise; at a good dimension it equals
`holByteAlign` (`riscvByteAlignHOL_eq`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem bytesInMem_asmWriteBytearray {width : Nat} [NeZero width] {C F : Type}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width C F) (t1 : AsmState width)
    (c1 : BitVec width) (newBytes x : List (BitVec 8)) (p : BitVec width)
    (xs : List (BitVec 8)) :
    (∀ a, s1.memDomain (riscvByteAlignHOL a) = true → s1.memDomain a = true) ∧
      readBytearrayWordHOL c1 newBytes.length
        (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some x →
    bytesInMemHOL p xs t1.mem t1.memDomain (fun a => s1.memDomain a = true) →
    bytesInMemHOL p xs (asmWriteBytearrayHOL c1 newBytes t1.mem) t1.memDomain
      (fun a => s1.memDomain a = true) := by
  rintro ⟨hdom, hrd⟩
  exact bytesInMem_asmWriteBytearray_lemma _ _ _ _ xs p fun a ha =>
    (asmWriteBytearray_outside s1.memory s1.memDomain s1.be t1.mem hdom newBytes c1 x hrd
      a ha).symm

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem writeBytearray_not_loc {width : Nat} [NeZero width] {C F : Type} (n n0 : Nat) :
    ∀ (xs : List (BitVec 8)) (c1 : BitVec width) (s1 : Flapjack.Compiler.Backend.LabSem.State width C F)
      (a c : BitVec width),
      s1.memory a = .word c →
      writeBytearrayExact c1 xs s1.memory s1.memDomain s1.be a ≠ .loc n n0 := by
  intro xs
  induction xs with
  | nil => intro c1 s1 a c h; simp [writeBytearrayExact, h]
  | cons b bs ih =>
    intro c1 s1 a c h
    have ih' := ih (c1 + 1) s1 a c h
    simp only [writeBytearrayExact, memStoreByteAuxExact]
    split
    · split
      · dsimp only
        split
        · simp
        · exact ih'
      · simp [h]
    · simp [h]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem callFFI_bytearray_lemma {width : Nat} [NeZero width] {mw : Nat} [NeZero mw]
    {S Q C F : Type}
    (mc : MachineConfig mw S Q) (p : BitVec width) (labs : Spt (Spt Nat))
    (s1 : Flapjack.Compiler.Backend.LabSem.State width C F) (t1 : AsmState width)
    (a : BitVec width) :
    ∀ (newBytes : List (BitVec 8)) (c1 : BitVec width) (x : List (BitVec 8)),
    s1.memDomain (holByteAlign a) = true ∧ goodDimindex width ∧ t1.memDomain a ∧
      s1.memDomain a = true ∧ s1.be = mc.target.config.bigEndian ∧
      readBytearrayWordHOL c1 newBytes.length
        (memLoadByteAuxExact s1.memory s1.memDomain s1.be) = some x ∧
      wordLocValByte p labs s1.memory a mc.target.config.bigEndian = some (t1.mem a) →
    wordLocValByte p labs (writeBytearrayExact c1 newBytes s1.memory s1.memDomain s1.be) a
        mc.target.config.bigEndian =
      some (asmWriteBytearrayHOL c1 newBytes t1.mem a) := by
  intro newBytes
  induction newBytes with
  | nil => rintro c1 x ⟨-, -, -, -, -, -, h⟩; exact h
  | cons b bs ih =>
    rintro c1 x ⟨had, hg, htd, hsd, hbe, hrd, hv⟩
    rw [List.length_cons, readBytearrayWordHOL] at hrd
    cases hb : memLoadByteAuxExact s1.memory s1.memDomain s1.be c1 with
    | none => rw [hb] at hrd; simp at hrd
    | some b0 =>
    cases hr : readBytearrayWordHOL (c1 + 1) bs.length
        (memLoadByteAuxExact s1.memory s1.memDomain s1.be) with
    | none => rw [hb, hr] at hrd; simp at hrd
    | some rest =>
    have ih' := ih (c1 + 1) rest ⟨had, hg, htd, hsd, hbe, hr, hv⟩
    have hal := riscvByteAlignHOL_eq hg c1
    have hdc : s1.memDomain (holByteAlign c1) = true := by
      simp only [memLoadByteAuxExact, hal] at hb
      split at hb
      · cases hb
      · split at hb
        · assumption
        · cases hb
    set W := writeBytearrayExact (c1 + 1) bs s1.memory s1.memDomain s1.be with hW
    obtain ⟨v', hv'⟩ : ∃ v', W (holByteAlign c1) = .word v' := by
      simp only [memLoadByteAuxExact, hal] at hb
      split at hb
      · cases hb
      · next v hm =>
        cases hw : W (holByteAlign c1) with
        | word v' => exact ⟨v', rfl⟩
        | loc n n0 => exact absurd hw (writeBytearray_not_loc n n0 bs (c1 + 1) s1 _ v hm)
    have hwrite : writeBytearrayExact c1 (b :: bs) s1.memory s1.memDomain s1.be =
        fun a' => if a' = holByteAlign c1 then .word (setByte c1 b v' s1.be) else W a' := by
      simp only [writeBytearrayExact, memStoreByteAuxExact, hal, ← hW, hv', hdc, ↓reduceIte,
        setByteHOL8_eq]
    rw [hwrite]
    have h8 : 8 ≤ width := by rcases hg with h | h <;> simp [h]
    by_cases hxa : holByteAlign a = holByteAlign c1
    · rw [wordLocValByte, hxa, if_pos rfl]
      simp only [wordLocVal, asmWriteBytearrayHOL]
      by_cases hx : a = c1
      · subst hx
        rw [← hbe, getByte_setByte _ _ _ _ h8]
        simp
      · rw [← hbe, getByte_setByte_diff a c1 _ v' s1.be ⟨hg, hx, hxa⟩]
        simp only [hx, ↓reduceIte]
        rw [wordLocValByte, hxa, hv'] at ih'
        simpa [wordLocVal, hbe] using ih'
    · have hxne : a ≠ c1 := fun e => hxa (e ▸ rfl)
      rw [wordLocValByte, if_neg hxa]
      simp only [asmWriteBytearrayHOL, hxne, ↓reduceIte]
      exact ih'

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "list_add_if_fresh_simp" 3027]
theorem listAddIfFresh_simp {α : Type} [DecidableEq α] (l : List α) :
    ∀ (n : Nat) (s : α),
      listAddIfFresh s l = if findIndex s l n = none then l ++ [s] else l := by
  induction l with
  | nil => intro n s; simp [listAddIfFresh, findIndex]
  | cons y ys ih =>
    intro n s
    by_cases h : y = s
    · subst h; simp [listAddIfFresh, findIndex]
    · have h' : ¬ s = y := fun e => h e.symm
      simp only [listAddIfFresh, h', ↓reduceIte, findIndex, h, ih (n + 1) s]
      split <;> simp

@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "find_index_append"]
theorem findIndex_append {α : Type} [DecidableEq α] (s : α) (l l' : List α) :
    ∀ n, findIndex s (l ++ l') n =
      match findIndex s l n with
      | none => findIndex s l' (n + l.length)
      | some i => some i := by
  induction l with
  | nil => intro n; simp [findIndex]
  | cons y ys ih =>
    intro n
    simp only [List.cons_append, findIndex]
    split
    · rfl
    · rw [ih (n + 1)]
      simp only [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- A `CallFFI s` line puts `ExtCall s` among the FFI names; Flapjack
infrastructure for `has_io_name_find_index`. -/
theorem mem_findFfiNames_of_hasIoName {width : Nat} [NeZero width] (s : MlString) :
    ∀ l : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))),
      hasIoName s l → HolFfiName.extCall s ∈ findFfiNames l := by
  intro l
  induction l using findFfiNames.induct with
  | case1 => intro h; rw [hasIoName.eq_def] at h; exact h.elim
  | case2 k rest ih => intro h; rw [hasIoName.eq_def] at h; rw [findFfiNames]; exact ih h
  | case3 k s' xs rest p bs n ih =>
    intro h
    rw [hasIoName.eq_def] at h
    rw [findFfiNames, listAddIfFresh_thm]
    rcases h with h | h
    · have := ih h
      split <;> simp [this]
    · simp only at h
      subst h
      split
      · assumption
      · simp
  | case4 k x xs rest hx ih =>
    intro h
    rw [hasIoName.eq_def] at h
    rw [findFfiNames]
    · rcases h with h | h
      · exact ih h
      · split at h
        · exact absurd rfl (hx _ _ _ _)
        · exact h.elim
    · exact hx

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem hasIoName_findIndex {width : Nat} [NeZero width] :
    ∀ (l : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (s : MlString),
      hasIoName s l → ∃ y, findIndex (HolFfiName.extCall s) (findFfiNames l) 0 = some y := by
  intro l s h
  have : Nonempty HolFfiName := ⟨.extCall s⟩
  obtain ⟨index, hf, -, -⟩ := findIndex_mem _ _ 0 (mem_findFfiNames_of_hasIoName s l h)
  exact ⟨_, hf⟩

end Flapjack.Compiler.Backend.LabToTarget
