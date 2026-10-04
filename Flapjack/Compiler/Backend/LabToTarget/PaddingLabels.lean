import Flapjack.Compiler.Backend.LabToTarget.PrefixZero
import Flapjack.Compiler.Backend.LabToTarget.LabelAnnotations
import Flapjack.Compiler.Backend.LabToTarget.LabelPosition
import Flapjack.Compiler.Backend.LabToTarget.AddNopProps
import Flapjack.Compiler.Backend.LabToTarget.PositionAppend
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- Flapjack infrastructure for a guarded first-line test. No total HOL HD
operation is introduced: false on [] is used only within the nonempty guard. -/
private def frontOne {width : Nat} [NeZero width] : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Prop
  | [] => False
  | line :: _ => isLabelHOL line = true ∧ lineLen line = 1

/-- Flapjack infrastructure spelling the consequent's nonempty/nonlabel guard. -/
private def frontNonlabel {width : Nat} [NeZero width] : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → Prop
  | [] => False
  | line :: _ => isLabelHOL line ≠ true

/-- Flapjack parity infrastructure, with no independently named HOL original. -/
private theorem noFrontOne {width : Nat} [NeZero width] (pos : Nat)
    (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (he : pos % 2 = 0) (h : labLenPosOk pos lines) : ¬frontOne lines := by
  cases lines with
  | nil => simp [frontOne]
  | cons line lines =>
    cases line <;> simp_all [frontOne,isLabelHOL,lineLen,labLenPosOk,lineLabLenPosOk]

/-- Flapjack accumulator infrastructure, with no independently named HOL original. -/
private theorem reversePushParity {width : Nat} [NeZero width]
    (pos : Nat) (aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))
    (ha : labLenPosOk pos aux.reverse)
    (hl : lineLabLenPosOk (pos + (aux.map lineLen).sum) line) :
    labLenPosOk pos (line :: aux).reverse := by
  rw [List.reverse_cons]
  apply (labLenPosOk_append aux.reverse pos [line]).mpr
  exact ⟨ha,by simpa [labLenPosOk] using hl⟩

/-- Full original pair equality and all four source guards. Both HD tests in
HOL occur behind explicit nonempty guards. Their constructor-case rendering
here avoids any dependence on the held unguarded total HD/EL operations. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem padSection_labels {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (lines aux : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (pos : Nat) (labs : List (Nat × Nat)) :
    labLenPosOk (pos + (aux.map lineLen).sum) lines ∧
    labLenPosOk pos aux.reverse ∧ (∀ line ∈ aux, labelZero line) ∧
    ((match lines with
      | [] => False
      | line :: _ => isLabelHOL line = true ∧ lineLen line = 1) →
     (match aux with
      | [] => False
      | line :: _ => isLabelHOL line ≠ true)) →
    sectionLabels pos (padSection nop lines aux) labs =
      sectionLabels pos (aux.reverse ++ lines) labs := by
  change labLenPosOk (pos + (aux.map lineLen).sum) lines ∧
    labLenPosOk pos aux.reverse ∧ (∀ line ∈ aux, labelZero line) ∧
    (frontOne lines → frontNonlabel aux) →
    sectionLabels pos (padSection nop lines aux) labs =
      sectionLabels pos (aux.reverse ++ lines) labs
  induction lines generalizing aux with
  | nil => simp [padSection]
  | cons line lines ih =>
    rintro ⟨hl,ha,hz,hfront⟩
    have hhead := hl.1
    have htail := hl.2
    cases line with
    | asm a bytes len =>
      have hnew := reversePushParity pos aux (.asm a (padBytes bytes len nop) len) ha trivial
      have hrest : labLenPosOk (pos + (List.map lineLen (.asm a (padBytes bytes len nop) len :: aux)).sum) lines := by
        simpa [lineLen, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htail
      have hr := ih (.asm a (padBytes bytes len nop) len :: aux)
        ⟨hrest,hnew,by simpa [labelZero] using hz,by simp [frontNonlabel,isLabelHOL]⟩
      simpa [padSection,List.reverse_cons,List.append_assoc,sectionLabelsAppend,sectionLabels,lineLen] using hr
    | labAsm a word bytes len =>
      have hnew := reversePushParity pos aux (.labAsm a word (padBytes bytes len nop) len) ha trivial
      have hrest : labLenPosOk (pos + (List.map lineLen (.labAsm a word (padBytes bytes len nop) len :: aux)).sum) lines := by
        simpa [lineLen, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htail
      have hr := ih (.labAsm a word (padBytes bytes len nop) len :: aux)
        ⟨hrest,hnew,by simpa [labelZero] using hz,by simp [frontNonlabel,isLabelHOL]⟩
      simpa [padSection,List.reverse_cons,List.append_assoc,sectionLabelsAppend,sectionLabels,lineLen] using hr
    | label k1 k2 len =>
      by_cases hlen : len = 0
      · subst len
        have he : (pos + (aux.map lineLen).sum) % 2 = 0 := by
          by_cases he : (pos + (aux.map lineLen).sum) % 2 = 0
          · exact he
          · simp [lineLabLenPosOk,he] at hhead
        have hnew := reversePushParity pos aux (.label k1 k2 0) ha
          (by simp [lineLabLenPosOk,he])
        have hrest : labLenPosOk (pos + (List.map lineLen (.label k1 k2 0 :: aux)).sum) lines := by
          simpa [lineLen] using htail
        have hn := noFrontOne (pos + (aux.map lineLen).sum) lines he
          (by simpa [lineLen] using htail)
        have hr := ih (.label k1 k2 0 :: aux)
          ⟨hrest,hnew,by simpa [labelZero] using hz,fun h => False.elim (hn h)⟩
        simpa [padSection,List.reverse_cons,List.append_assoc] using hr
      · have hlen1 : len = 1 := by
          by_cases he : (pos + (aux.map lineLen).sum) % 2 = 0
          · simp [lineLabLenPosOk,he] at hhead
            contradiction
          · simpa [lineLabLenPosOk,he] using hhead
        have hb := hfront (by simp [frontOne,isLabelHOL,lineLen,hlen1])
        cases aux with
        | nil => simp [frontNonlabel] at hb
        | cons previous rest =>
          cases previous with
          | label _ _ _ => simp [frontNonlabel,isLabelHOL] at hb
          | asm a bytes n =>
            subst len
            have he : (pos + (List.map lineLen (.asm a bytes n :: rest)).sum + 1) % 2 = 0 := by
              simp only [lineLabLenPosOk] at hhead
              split at hhead <;> omega
            have hrev : labLenPosOk pos rest.reverse :=
              ((labLenPosOk_append rest.reverse pos [.asm a bytes n]).mp
                (by simpa [List.reverse_cons] using ha)).1
            have hm := reversePushParity pos rest (.asm a (bytes ++ nop) (n+1)) hrev trivial
            have hp := reversePushParity pos (.asm a (bytes ++ nop) (n+1)::rest) (.label k1 k2 0) hm
              (by simpa [lineLabLenPosOk,lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he)
            have ht : labLenPosOk (pos + (List.map lineLen (.label k1 k2 0::.asm a (bytes++nop) (n+1)::rest)).sum) lines := by
              simpa [lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htail
            have hn := noFrontOne _ lines he (by simpa [lineLen] using htail)
            have hr := ih (.label k1 k2 0::.asm a (bytes++nop) (n+1)::rest)
              ⟨ht,hp,by simpa [labelZero] using hz,fun h => False.elim (hn h)⟩
            simpa [padSection,addNop,List.reverse_cons,List.append_assoc,sectionLabelsAppend,sectionLabels,lineLen,Nat.add_assoc] using hr
          | labAsm a word bytes n =>
            subst len
            have he : (pos + (List.map lineLen (.labAsm a word bytes n :: rest)).sum + 1) % 2 = 0 := by
              simp only [lineLabLenPosOk] at hhead
              split at hhead <;> omega
            have hrev : labLenPosOk pos rest.reverse :=
              ((labLenPosOk_append rest.reverse pos [.labAsm a word bytes n]).mp
                (by simpa [List.reverse_cons] using ha)).1
            have hm := reversePushParity pos rest (.labAsm a word (bytes ++ nop) (n+1)) hrev trivial
            have hp := reversePushParity pos (.labAsm a word (bytes ++ nop) (n+1)::rest) (.label k1 k2 0) hm
              (by simpa [lineLabLenPosOk,lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he)
            have ht : labLenPosOk (pos + (List.map lineLen (.label k1 k2 0::.labAsm a word (bytes++nop) (n+1)::rest)).sum) lines := by
              simpa [lineLen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htail
            have hn := noFrontOne _ lines he (by simpa [lineLen] using htail)
            have hr := ih (.label k1 k2 0::.labAsm a word (bytes++nop) (n+1)::rest)
              ⟨ht,hp,by simpa [labelZero] using hz,fun h => False.elim (hn h)⟩
            simpa [padSection,addNop,List.reverse_cons,List.append_assoc,sectionLabelsAppend,sectionLabels,lineLen,Nat.add_assoc] using hr

/-- Full original code-level label-map equality, with all four original
predicates retained and arbitrary initial nested-map accumulator. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem padCode_computeLabels {width : Nat} [NeZero width]
    (nop : List (BitVec 8)) (pos : Nat) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (acc : Spt (Spt Nat)) :
    (∀ sec ∈ code, secLabelOne sec) ∧
    (nop.length ≠ 1 → ∀ sec ∈ code, secLabelZero sec) ∧
    (∀ sec ∈ code, secLabelPrefixZero sec) ∧ allLabLenPosOk pos code →
    computeLabelsAlt pos (padCode nop code) acc = computeLabelsAlt pos code acc := by
  induction code generalizing pos acc with
  | nil => simp [padCode,computeLabelsAlt]
  | cons sec code ih =>
    rintro ⟨hone,hzero,hprefix,hpos⟩
    have htone : ∀ sec ∈ code,secLabelOne sec := fun s hm => hone s (by simp [hm])
    have htzero : nop.length ≠ 1 → ∀ sec ∈ code,secLabelZero sec :=
      fun hn s hm => hzero hn s (by simp [hm])
    have htprefix : ∀ sec ∈ code,secLabelPrefixZero sec :=
      fun s hm => hprefix s (by simp [hm])
    have hp : labelPrefixZero sec.lines := hprefix sec (by simp)
    have hb : (match sec.lines with
      | [] => False
      | line :: _ => isLabelHOL line = true ∧ lineLen line = 1) → False := by
      cases heq : sec.lines with
      | nil => simp
      | cons line lines =>
        have hh : isLabelHOL line = true → lineLen line = 0 ∧ labelPrefixZero lines := by
          simpa [heq] using hp
        rintro ⟨hl,hlen⟩
        have := (hh hl).1
        omega
    have heq := padSection_labels nop sec.lines [] pos []
      ⟨by simpa [allLabLenPosOk] using hpos.1,by simp [labLenPosOk],by simp,hb⟩
    simp only [List.reverse_nil,List.nil_append] at heq
    have hnew : (sectionLabels pos sec.lines []).1 = pos + secLength sec.lines 0 := by
      rw [sectionLabelsSecLength,secLengthSumLineLen,secLengthSumLineLen]
      omega
    have htpos : allLabLenPosOk (sectionLabels pos sec.lines []).1 code := by
      rw [hnew]
      exact hpos.2
    cases sec with
    | mk id lines =>
      simp only [padCode,computeLabelsAlt]
      rw [heq]
      exact ih (sectionLabels pos lines []).1
        (sptInsert id (sptFromAList ((0,pos) :: (sectionLabels pos lines []).2)) acc)
        ⟨htone,htzero,htprefix,htpos⟩

end Flapjack.Compiler.Backend.LabToTarget
