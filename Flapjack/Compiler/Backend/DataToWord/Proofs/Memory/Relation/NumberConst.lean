module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordMemoryEquality
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberHeader
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeaderInjective

@[expose] public section

/-! Integer-constant comparisons in the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataSem
open Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Recover the constructed header from a successful encoding. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem encodeResult {width : Nat} [NeZero width] (conf : Config) (tag len : Nat)
    (out : BitVec width) (encoded : encodeHeader conf tag len = some out) :
    out = makeHeader conf (BitVec.ofNat width tag) len := by
  simp only [encodeHeader] at encoded
  split at encoded <;> simp_all

/-- Related integer values satisfy the complete constant-comparison test. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_const_test"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_numberConstTest {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i j : Int) (w : BitVec width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (h : memoryRel conf be next refs space store memory domain ((.number i, .word w) :: vars) ∧
      goodDimindex width) :
    if smallInt width j then ((smallnum j : BitVec width) = w ↔ i = j)
    else match bignumWords conf j with
      | none => i ≠ j
      | some words => if w.getLsbD 0 = false then i ≠ j else
          ∃ a, getRealAddr conf store w = some a ∧ wordMemEq a words domain memory = some (decide (i = j)) := by
  obtain ⟨word, eq, bit⟩ := memoryRel_anyNumberImp conf be next refs space store memory domain i (.word w) vars ⟨h.2,h.1⟩
  have same : word = w := WordLocW.word.inj eq.symm
  subst word
  by_cases smallJ : smallInt width j
  · simp only [smallJ, if_true]
    have pushed := impMemoryRel_number conf be next refs space store memory domain ((.number i,.word w)::vars) j ⟨h.2, smallJ, h.1⟩
    obtain ⟨v1, v2, v1eq, v2eq, result⟩ := memoryRel_numberEq conf be next refs space store memory domain
      j i (.word (smallnum j)) (.word w) vars ⟨pushed, Or.inl smallJ, h.2⟩
    have first := WordLocW.word.inj v1eq
    have second := WordLocW.word.inj v2eq
    subst v1
    subst v2
    exact result.trans eq_comm
  · simp only [smallJ, if_false]
    by_cases smallI : smallInt width i
    · have neq : i ≠ j := by intro ij; subst i; contradiction
      cases wordCase : bignumWords (width := width) conf j with
      | none => exact neq
      | some words =>
        simp only
        have bitClear : w.getLsbD 0 = false := by
          cases hb : w.getLsbD 0 <;> simp_all
        simp [bitClear, neq]
    · have bitSet : w.getLsbD 0 = true := bit.mpr smallI
      cases wordCase : bignumWords (width := width) conf j with
      | none =>
        intro equal
        subst j
        obtain ⟨q, address, locEq, addressEq, encoded, header⟩ :=
          memoryRel_bignumHeader conf be next refs space store memory domain i (.word w) vars ⟨h.1, smallI, h.2⟩
        have tagValue : (((if i < 0 then 1 else 0) <<< 2 ||| 3 : BitVec width)).toNat =
            if i < 0 then 7 else 3 := by
          rcases h.2 with hw | hw <;> subst width <;> by_cases neg : i < 0 <;> simp [neg]
        rw [tagValue] at encoded
        cases enc : encodeHeader (width := width) conf (if i < 0 then 7 else 3)
            (Misc.Multiword.n2mw (width := width) i.natAbs).length with
        | none => simp [enc] at encoded
        | some header => simp [bignumWords, Misc.Multiword.i2mw, enc] at wordCase
      | some words =>
        simp only [bitSet, Bool.true_eq_false, if_false]
        obtain ⟨q, address, frame, locEq, addrEq, memHead, domHead, payload, bound, low,
          header2, header3, header4, decoded⟩ :=
          memoryRel_bignumWords conf be next refs space store memory domain i (.word w) vars ⟨h.1, smallI, h.2⟩
        have qw : q = w := (WordLocW.word.inj locEq).symm
        subst q
        refine ⟨address, addrEq, ?_⟩
        obtain ⟨_, _, _, _, encodedI, _⟩ :=
          memoryRel_bignumHeader conf be next refs space store memory domain i (.word w) vars ⟨h.1, smallI, h.2⟩
        have tagValue : (((if i < 0 then 1 else 0) <<< 2 ||| 3 : BitVec width)).toNat =
            if i < 0 then 7 else 3 := by
          rcases h.2 with hw | hw <;> subst width <;> by_cases neg : i < 0 <;> simp [neg]
        rw [tagValue] at encodedI
        cases encJ : encodeHeader (width := width) conf (if j < 0 then 7 else 3)
            (Misc.Multiword.n2mw (width := width) j.natAbs).length with
        | none => simp [bignumWords, Misc.Multiword.i2mw, encJ] at wordCase
        | some headerJ =>
          have wordsEq : words = headerJ :: Misc.Multiword.n2mw (width := width) j.natAbs := by
            simpa [bignumWords, Misc.Multiword.i2mw, encJ] using wordCase.symm
          subst words
          cases encI : encodeHeader (width := width) conf (if i < 0 then 7 else 3)
              (Misc.Multiword.n2mw (width := width) i.natAbs).length with
          | none => simp [encI] at encodedI
          | some headerI =>
            have tagWord : (BitVec.ofNat width (if i < 0 then 7 else 3)) =
                (((if i < 0 then 1 else 0) <<< 2 ||| 3 : BitVec width)) := by
              rcases h.2 with hw | hw <;> subst width <;> by_cases neg : i < 0 <;> simp [neg]
            have headerEq : headerI = makeHeader conf
                (((if i < 0 then 1 else 0) <<< 2 ||| 3 : BitVec width))
                (Misc.Multiword.n2mw (width := width) i.natAbs).length := by
              rw [← tagWord]
              exact encodeResult conf _ _ _ encI
            have actualHeader : memory address = .word headerI := by simpa [headerEq] using memHead
            simp only [wordMemEq, domHead, ↓reduceIte, actualHeader]
            by_cases sameHead : headerI = headerJ
            · simp only [sameHead, if_true]
              have configBound : conf.lenSize + 2 < width := by
                obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := h.1
                have bound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
                omega
              have parts := (encodeHeader_eq conf (if i < 0 then 7 else 3)
                (Misc.Multiword.n2mw (width := width) i.natAbs).length
                (if j < 0 then 7 else 3) (Misc.Multiword.n2mw (width := width) j.natAbs).length
                headerI headerJ ⟨encI, encJ, configBound⟩).mp sameHead
              have signEq : (i < 0) ↔ (j < 0) := by
                by_cases si : i < 0 <;> by_cases sj : j < 0 <;> simp_all; omega
              have compare := wordMemEqThm (Misc.Multiword.n2mw (width := width) i.natAbs)
                (Misc.Multiword.n2mw (width := width) j.natAbs)
                (address + StackRemove.bytesInWord width) frame memory domain ⟨payload, parts.2⟩
              have digitsEq : (Misc.Multiword.n2mw (width := width) i.natAbs =
                  Misc.Multiword.n2mw (width := width) j.natAbs) ↔ i = j := by
                constructor
                · intro digits
                  have sizes := congrArg (Misc.Multiword.mw2n (width := width)) digits
                  simp only [Misc.Multiword.mw2n_n2mw] at sizes
                  cases i <;> cases j <;> simp_all [Int.natAbs_negSucc]; omega
                · intro eq; subst j; rfl
              have boolEq : decide ((Misc.Multiword.n2mw (width := width) i.natAbs) =
                  Misc.Multiword.n2mw j.natAbs) = decide (i = j) := decide_eq_decide.mpr digitsEq
              simpa only [boolEq] using compare
            · have diff : i ≠ j := by
                intro eq
                subst j
                exact sameHead (Option.some.inj (encI.symm.trans encJ))
              simp [sameHead, diff]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
