module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BignumSize
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Limits
public import Flapjack.Compiler.Backend.Semantics.DataSem.Limits
public import Flapjack.Compiler.Backend.DataToWord.Build

@[expose] public section

/-! Safety of constant-part lowering in assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- A safe source part lowers successfully under the bounds extracted from the
    heap and limits invariants; this is the case analysis used in the proof. -/
private theorem partWords_safe {width : Nat} [NeZero width] (conf : Config)
    (limits : DataSem.Limits) (memory : Spt (Build.Value width))
    (part : ClosLang.ConstPart) (off : BitVec width)
    (good : goodDimindex width) (hlen : conf.lenSize + 7 < width)
    (harch : limits.arch64Bit = decide (width = 64)) (hls : limits.lengthLimit = conf.lenSize)
    (safe : DataSem.limSafePart limits part) :
    ∃ output, Build.partWords conf memory part off = some output := by
  classical
  have arch : DataSem.archSize limits = width := by
    rcases good with h | h <;> subst width <;> simp [DataSem.archSize, harch]
  cases part with
  | con tag xs =>
    cases xs with
    | nil =>
      simp only [DataSem.limSafePart, ↓reduceIte, arch] at safe
      simp [Build.partWords, safe]
    | cons x xs =>
      simp only [DataSem.limSafePart, List.cons_ne_nil, ↓reduceIte, arch, hls] at safe
      simp only [List.length_cons] at safe
      simp [Build.partWords, encodeHeader, safe.1, safe.2.1, safe.2.2.1, safe.2.2.2]
  | int i =>
    by_cases small : smallInt width i
    · simp [Build.partWords, small]
    · have notSmall : ¬ DataSem.smallNum limits.arch64Bit i := by
        intro h
        exact small ((smallNum_iff_smallInt limits i good harch).mp h)
      simp only [DataSem.limSafePart, if_neg notSmall] at safe
      rw [harch, hls] at safe
      rw [Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.bignumSize_eq i good] at safe
      have lenBound : (Misc.Multiword.n2mw (width := width) i.natAbs).length < 2 ^ conf.lenSize := by omega
      have powBound : 2 ^ conf.lenSize ≤ 2 ^ (width - 4) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have lenWide : (Misc.Multiword.n2mw (width := width) i.natAbs).length < 2 ^ (width - 4) := by omega
      have tagBound : 7 < 2 ^ (width - conf.lenSize - 2) := by
        have h : 2 ^ 4 ≤ 2 ^ (width - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have tagWide : 7 < 2 ^ width / 16 := by
        rcases good with h | h <;> rw [h] <;> decide
      by_cases sign : i < 0 <;>
        simp [Build.partWords, small, Misc.Multiword.i2mw, sign, encodeHeader, lenBound, lenWide,
          show 3 < 2 ^ (width - conf.lenSize - 2) by omega,
          show 3 < 2 ^ width / 16 by omega, tagBound, tagWide]
  | w64 w =>
    have size : 1 < conf.lenSize := by simpa [DataSem.limSafePart, hls] using safe
    have sizePow : 2 < 2 ^ conf.lenSize := by
      have h : 2 ^ 2 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have tagBound : 3 < 2 ^ (width - conf.lenSize - 2) := by
      have h : 2 ^ 3 ≤ 2 ^ (width - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have tagWide : 3 < 2 ^ width / 16 := by
      rcases good with h | h <;> rw [h] <;> decide
    have lenWide : 2 < 2 ^ (width - 4) := by
      rcases good with h | h <;> rw [h] <;> decide
    by_cases narrow : width < 64 <;>
      simp [Build.partWords, narrow, encodeHeader, tagBound, tagWide,
        show 1 < 2 ^ conf.lenSize by omega, sizePow,
        show 1 < 2 ^ (width - 4) by omega, lenWide]
  | str text =>
    simp only [DataSem.limSafePart, arch, hls] at safe
    have lengthEq := Flapjack.Basis.Pure.MlString.MlString.length_explode text
    have lenConf : Build.byteLen width text.explode.length < 2 ^ conf.lenSize := by
      rcases good with hw | hw
      · simp only [Build.byteLen, hw, if_true, lengthEq]
        simpa [hw] using safe.2.1
      · simp only [Build.byteLen, hw, lengthEq]
        simpa [hw] using safe.2.1
    have lenWide : Build.byteLen width text.explode.length < 2 ^ (width - 4) := by
      have bound := safe.1
      rcases good with hw | hw
      · simp only [Build.byteLen, hw, if_true, lengthEq]
        rw [hw] at bound
        norm_num at bound ⊢
        omega
      · simp only [Build.byteLen, hw, lengthEq]
        rw [hw] at bound
        norm_num at bound ⊢
        omega
    simp [Build.partWords, lenConf, lenWide]

open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.GcCombined

namespace PartsToWordsNonePort
/-- Canonical roundtrip for the finite-map word-state fields. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end PartsToWordsNonePort

/-- Failure to lower the constant parts implies that some source part violates
    the limits, under the original heap and limits invariants. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "parts_to_words_NONE"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem partsToWords_none {width : Nat} [NeZero width] {C F : Type}
    (parts : List ClosLang.ConstPart) (off : BitVec width) (memory : Spt (Build.Value width)) (index : Nat)
    (target : WordSemStateFiniteExact width C F) (source : DataSem.State C F)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width))))
    (a sp sp1 : Nat) (gens : GenState) (conf : Config) (limit : Nat)
    (failure : Build.partsToWords conf memory index parts off = none)
    (good : goodDimindex width)
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf target.store target.memory target.mdomain limit)
    (limits : limitsInv source.limits (target.store.lookup .heapLength) target.stackLimit conf.lenSize conf.hasFpOps conf.hasFpTern) :
    ∃ part ∈ parts, ¬ DataSem.limSafePart source.limits part := by
  classical
  by_contra notUnsafe
  have allSafe : ∀ part ∈ parts, DataSem.limSafePart source.limits part := by
    intro part mem
    by_contra notSafe
    exact notUnsafe ⟨part, mem, notSafe⟩
  have bound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have hls : source.limits.lengthLimit = conf.lenSize := limits.2.1
  have harch : source.limits.arch64Bit = decide (width = 64) := limits.2.2.1
  have builds : ∀ (parts : List ClosLang.ConstPart), (∀ part ∈ parts, DataSem.limSafePart source.limits part) →
      ∀ (memory : Spt (Build.Value width)) (index : Nat) (off : BitVec width),
        ∃ result, Build.partsToWords conf memory index parts off = some result := by
    intro parts
    induction parts with
    | nil =>
      intro _ memory index off
      simp [Build.partsToWords]
    | cons part rest ih =>
      intro allSafe memory index off
      have safe : DataSem.limSafePart source.limits part := allSafe part (by simp)
      have tailSafe : ∀ part ∈ rest, DataSem.limSafePart source.limits part := by
        intro p hp
        exact allSafe p (by simp [hp])
      obtain ⟨⟨value, words⟩, donePart⟩ := partWords_safe conf source.limits memory part off good bound harch hls safe
      obtain ⟨result, doneTail⟩ := ih tailSafe (sptInsert index value memory) (index + 1)
        (off + wordSemBytesInWord * BitVec.ofNat width words.length)
      rcases result with ⟨result, restWords⟩
      simp [Build.partsToWords, donePart, doneTail]
  obtain ⟨out, success⟩ := builds parts allSafe memory index off
  rw [failure] at success
  contradiction

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
