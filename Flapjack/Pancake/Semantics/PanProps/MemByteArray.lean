import Flapjack.HolRef
import Flapjack.Misc.GoodDimindex
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.ByteRoundtrip
import Flapjack.Pancake.Semantics.LoopSem

/-!
# PanProps byte-array memory invariants

Source comparison found the equations and theorem premises for
`write_bytearray_update_byte` (`panPropsScript.sml:1098`) and
`read_write_bytearray_lemma` (`panPropsScript.sml:1119`) aligned with HOL, but
both Lean statements use `List UInt8` where HOL uses `word8 list` (Lean's exact
HOL word8 carrier is `List (BitVec 8)`). Their helper chain has the same
unqualified mismatch. These declarations are now deliberately untagged; the
faithful byte-carrier replacement is tracked by
`flapjack-4ac.5.16.5.4`. `HolWordLab` and the address-set representation remain
unchanged. -/

namespace Flapjack

private theorem panMemStoreByteHOL_preservesWordAt {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (storeAddress target : RiscV.Word width) (byte : UInt8)
    (oldWord : RiscV.Word width) (hMemory : memory target = .word oldWord) :
    match panMemStoreByteHOL memory domain bigEndian storeAddress byte with
    | some updated => ∃ newWord, updated target = .word newWord
    | none => True := by
  cases hCell : memory (panByteAlignHOL (width := width) storeAddress) with
  | word cell =>
      by_cases hDomain : domain (panByteAlignHOL (width := width) storeAddress)
      · by_cases hTarget : target = panByteAlignHOL (width := width) storeAddress
        · subst target
          simp [panMemStoreByteHOL, hCell, hDomain]
        · simp [panMemStoreByteHOL, hCell, hDomain, hTarget, hMemory]
      · simp [panMemStoreByteHOL, hDomain]

private theorem panWriteBytearrayHOL_preservesWordAt {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bytes : List UInt8)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (target oldWord : RiscV.Word width)
    (hMemory : memory target = .word oldWord) :
    ∃ newWord,
      panWriteBytearrayHOL address bytes memory domain bigEndian target = .word newWord := by
  induction bytes generalizing address memory with
  | nil =>
      exact ⟨oldWord, by simpa [panWriteBytearrayHOL] using hMemory⟩
  | cons byte rest ih =>
      have hTail : ∃ tailWord,
          panWriteBytearrayHOL (address + 1) rest memory domain bigEndian target =
            .word tailWord :=
        ih (address + 1) memory hMemory
      rcases hTail with ⟨tailWord, hTail⟩
      simp only [panWriteBytearrayHOL]
      cases hStore : panMemStoreByteHOL
          (panWriteBytearrayHOL (address + 1) rest memory domain bigEndian)
          domain bigEndian address byte with
      | none =>
          exact ⟨oldWord, by simpa [hStore] using hMemory⟩
      | some updated =>
          have hUpdated := panMemStoreByteHOL_preservesWordAt
            (panWriteBytearrayHOL (address + 1) rest memory domain bigEndian)
            domain bigEndian address target byte tailWord hTail
          simp only [hStore] at hUpdated
          rcases hUpdated with ⟨newWord, hNewWord⟩
          exact ⟨newWord, by simpa [hStore] using hNewWord⟩

/-- Flapjack-specific word-tag preservation helper related to HOL
    `panProps$write_bytearray_update_byte` (`panPropsScript.sml:1098`). This
    stronger helper assumes a selected `word` witness and proves preservation
    after any bytearray write. It is deliberately untagged: HOL's exact premise
    is one implication antecedent containing
    `byte_aligned ad ∧ (∃w, memory ad = Word w)`, while this helper currently
    presents the witness and alignment as separate binders. The faithful exact
    statement is tracked by `flapjack-4ac.4.58.1`. -/
theorem panWriteBytearrayPreservesWordAt {width : Nat} [NeZero width]
    (bytes : List UInt8) (address address' : RiscV.Word width)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (_aligned : panByteAlignHOL (width := width) address = address)
    (word : RiscV.Word width)
    (hMemory : memory address = .word word) :
    ∃ updatedWord,
      panWriteBytearrayHOL address' bytes memory domain bigEndian address =
        .word updatedWord := by
  exact panWriteBytearrayHOL_preservesWordAt address' bytes memory domain bigEndian
    address word hMemory

/-- Flapjack analogue of HOL `write_bytearray_update_byte`. Its alignment and
    word-preservation cases follow HOL, but its bytes are `List UInt8` instead
    of `word8 list = List (BitVec 8)`, so the HOL tag is intentionally absent.
    The faithful carrier replacement is tracked by
    `flapjack-4ac.5.16.5.4`. -/
theorem writeBytearrayUpdateByte {width : Nat} [NeZero width]
    (bytes : List UInt8) (address address' : RiscV.Word width)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) :
    (panByteAlignHOL address = address ∧
      (∃ word : RiscV.Word width, memory address = .word word)) →
      ∃ word : RiscV.Word width,
        panWriteBytearrayHOL address' bytes memory domain bigEndian address = .word word := by
  rintro ⟨haligned, word, hmemory⟩
  exact panWriteBytearrayPreservesWordAt bytes address address' memory domain
    bigEndian haligned word hmemory

/-- Flapjack analogue of HOL `panProps$read_write_bytearray_lemma`
    (`cakeml/pancake/semantics/panPropsScript.sml:1119`). Reading `length`
    bytes with the byte loader and then writing them back leaves memory
    unchanged on `goodDimindex` widths. Its byte list is `List UInt8`, while
    HOL uses `word8 list = List (BitVec 8)`, so it is not tagged as the HOL
    theorem. The faithful byte-carrier replacement is tracked by
    `flapjack-4ac.5.16.5.4`. -/
theorem readWriteBytearrayLemma {width : Nat} [NeZero width]
    (length : Nat) (address : RiscV.Word width) (bytes : List UInt8)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) :
    (goodDimindex width ∧
      readBytearrayHOL address length
        (panMemLoadByteHOL memory domain bigEndian) = some bytes) →
      panWriteBytearrayHOL address bytes memory domain bigEndian = memory := by
  rintro ⟨hgood, hread⟩
  have hwidth : 8 ≤ width := by
    rcases (by simpa only [goodDimindex] using hgood) with h | h <;> omega
  induction length generalizing address bytes with
  | zero =>
      simp only [readBytearrayHOL] at hread
      have hbytes : bytes = [] := by simpa using hread.symm
      subst bytes
      rfl
  | succ n ih =>
      rw [readBytearrayHOL] at hread
      cases hload : panMemLoadByteHOL memory domain bigEndian address with
      | none =>
          simp only [hload] at hread
          exact absurd hread (Option.some_ne_none bytes).symm
      | some b =>
          simp only [hload] at hread
          cases hrest : readBytearrayHOL (address + 1) n
              (panMemLoadByteHOL memory domain bigEndian) with
          | none =>
              simp only [hrest] at hread
              exact absurd hread (Option.some_ne_none bytes).symm
          | some bs =>
              simp only [hrest] at hread
              have hbytes : bytes = b :: bs := by
                injection hread with h
                exact h.symm
              subst bytes
              have htail : panWriteBytearrayHOL (address + 1) bs memory domain
                  bigEndian = memory := ih (address + 1) bs hrest
              rw [panWriteBytearrayHOL, htail]
              cases hcell : memory (panByteAlignHOL (width := width) address) with
              | word v =>
                  by_cases hdom :
                      domain (panByteAlignHOL (width := width) address)
                  · have hb : b = panGetByteHOL address v bigEndian := by
                      have hEq : some (panGetByteHOL address v bigEndian) = some b := by
                        simpa only [panMemLoadByteHOL, hcell, hdom, if_true] using hload
                      injection hEq with h
                      exact h.symm
                    have hstore : panMemStoreByteHOL memory domain bigEndian address b
                        = some (fun current =>
                            if current = panByteAlignHOL (width := width) address then
                              .word (panSetByteHOL address
                                (BitVec.ofNat width b.toNat) v bigEndian)
                            else memory current) := by
                      simp only [panMemStoreByteHOL, hcell, hdom, if_true]
                    rw [hstore]
                    dsimp only
                    funext current
                    by_cases hcur :
                        current = panByteAlignHOL (width := width) address
                    · subst hcur
                      rw [if_pos rfl, hcell]
                      congr 1
                      rw [hb]
                      exact panSetByteHOL_panGetByteHOL address v bigEndian hwidth
                    · rw [if_neg hcur]
                  · exfalso
                    simp only [panMemLoadByteHOL, hcell, hdom, if_false] at hload
                    exact absurd hload (Option.some_ne_none b).symm

end Flapjack
