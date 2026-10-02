import Flapjack.Compiler.Backend.LabToTarget.NopInsertEncoding
import Flapjack.Compiler.Backend.LabToTarget.NopPadding
import Flapjack.Compiler.Backend.LabToTarget.PositionalEncoding
import Flapjack.Compiler.Backend.LabToTarget.PaddingLength
import Flapjack.Compiler.Backend.LabToTarget.SectionLength
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack proof factoring: derive physical/annotation sum agreement from the
actual reverse-accumulator invariant, rather than assuming an extra premise. -/
private theorem reverseNop_sum {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (aux : List (LabLineHOL width))
    (h : linesEncWithNop enc labs ffis pos aux.reverse) :
    (aux.reverse.map lineLength).sum = (aux.map lineLen).sum := by
  have hs := secLength_sumLineLength aux.reverse 0 (linesEncWithNop_lengthOk enc labs ffis pos aux.reverse h)
  simpa [secLengthSumLineLen,List.map_reverse,List.sum_reverse] using hs.symm

/-- Flapjack proof factoring for the original seven LabAsm padding clauses;
no separately named HOL original. The Call NOP invariant remains length-only. -/
private theorem paddedLabNop {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (pos : Nat) (nop : List (BitVec 8))
    (a : AsmWithLab HolCmp (HolRegImm width) MlString) (w : BitVec width)
    (bytes : List (BitVec 8)) (len : Nat)
    (hnop : nop = enc (.inst .skip)) (hone : nop.length = 1)
    (h : lineEncd enc labs ffis pos (.labAsm a w bytes len)) :
    lineEncWithNop enc labs ffis pos (.labAsm a w (padBytes bytes len nop) len) := by
  cases a <;> simp only [lineEncd] at h <;> simp only [lineEncWithNop]
  all_goals
    have hlen := lengthPadBytes bytes nop len ⟨by omega,h.2⟩
    first
    | exact ⟨by rw [← h.1]; exact encWithNop_padBytes nop enc _ len ⟨hnop,by simpa [h.1] using h.2,by simp [hone,Nat.mod_one],by simp [hone,Nat.mod_one],by omega⟩,hlen⟩
    | exact hlen

/-- Full original one-byte section-padding law. The physical/recorded sum
agreement is proved from the original accumulator predicate, not added as a guard. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml" "lines_enc_with_nop_pad_section1"
  (words_as_type_indexed_bitvec)]
theorem linesEncWithNop_padSection1 {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (nop : List (BitVec 8)) (code aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (pos : Nat) :
    nop = enc (.inst .skip) ∧ nop.length = 1 ∧
    linesEncd enc labs ffis (pos + (aux.map lineLen).sum) code ∧
    linesEncWithNop enc labs ffis pos aux.reverse ∧
    ¬(∀ line ∈ aux, isLabelHOL line = true) ∧ (∀ line ∈ code, labelOne line) →
    linesEncWithNop enc labs ffis pos (padSection nop code aux) := by
  induction code generalizing aux with
  | nil => rintro ⟨_,_,_,ha,_,_⟩; exact ha
  | cons line rest ih =>
    rintro ⟨hnop,hone,he,ha,hn,hl⟩
    have hx := hl line (by simp)
    have ht : ∀ l ∈ rest, labelOne l := fun l hm => hl l (by simp [hm])
    have hsum := reverseNop_sum enc labs ffis pos aux ha
    rcases he with ⟨he,hr⟩
    cases line with
    | label k1 k2 n =>
      have hb : n ≤ 1 := hx
      by_cases hz : n = 0
      · have ha' : linesEncWithNop enc labs ffis pos (.label k1 k2 0 :: aux).reverse := by
          simp only [List.reverse_cons,linesEncWithNop_append]
          exact ⟨ha,by simp [linesEncWithNop,lineEncWithNop]⟩
        simp only [padSection,if_pos hz]
        apply ih (.label k1 k2 0 :: aux)
        refine ⟨hnop,hone,?_,ha',?_,ht⟩
        · simpa [lineLen,hz] using hr
        · simpa [isLabelHOL] using hn
      · have hn1 : n = 1 := by omega
        have hs := lineLen_addNop_nonlabel nop aux hn
        have ha' : linesEncWithNop enc labs ffis pos (.label k1 k2 0 :: addNop nop aux).reverse := by
          simp only [List.reverse_cons,linesEncWithNop_append]
          exact ⟨by simpa [hnop] using linesEncWithNop_addNop enc labs ffis pos aux ⟨by simpa [← hnop] using hone,ha⟩,
            by simp [linesEncWithNop,lineEncWithNop]⟩
        simp only [padSection,if_neg hz]
        apply ih (.label k1 k2 0 :: addNop nop aux)
        refine ⟨hnop,hone,?_,ha',?_,ht⟩
        · simpa [lineLen,hs,hn1,Nat.add_assoc] using hr
        · intro hall
          apply hn
          apply (everyIsLabel_addNop nop aux).mp
          exact fun l hm => hall l (by simp [hm])
    | asm a bytes n =>
      change enc (cbwToAsmExact a) = bytes ∧ n = bytes.length at he
      have hp : (padBytes bytes n nop).length = n := lengthPadBytes bytes nop n ⟨by omega,by omega⟩
      have ha' : linesEncWithNop enc labs ffis pos (.asm a (padBytes bytes n nop) n :: aux).reverse := by
        simp only [List.reverse_cons,linesEncWithNop_append]
        refine ⟨ha,?_⟩
        simp only [linesEncWithNop,lineEncWithNop]
        refine ⟨⟨?_,hp⟩,trivial⟩
        have hh := encWithNop_padBytes_length enc (cbwToAsmExact a)
        simpa only [he.1,he.2,← hnop] using hh
      simp only [padSection]
      apply ih (.asm a (padBytes bytes n nop) n :: aux)
      refine ⟨hnop,hone,?_,ha',?_,ht⟩
      · simpa [lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr
      · simp [isLabelHOL]
    | labAsm a w bytes n =>
      have ha' : linesEncWithNop enc labs ffis pos (.labAsm a w (padBytes bytes n nop) n :: aux).reverse := by
        simp only [List.reverse_cons,linesEncWithNop_append]
        refine ⟨ha,?_⟩
        simp only [linesEncWithNop]
        exact ⟨by rw [hsum]; exact paddedLabNop enc labs ffis _ nop a w bytes n hnop hone he,trivial⟩
      simp only [padSection]
      apply ih (.labAsm a w (padBytes bytes n nop) n :: aux)
      refine ⟨hnop,hone,?_,ha',?_,ht⟩
      · simpa [lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr
      · simp [isLabelHOL]
end Flapjack.Compiler.Backend.LabToTarget
