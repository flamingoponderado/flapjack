import Flapjack.Compiler.Backend.LabToTarget.SecondPass

/-! Full original encd0 byte/length invariant, including the existential
encoder word witnessing a LabAsm annotation, and its complete encoding/update
preservation chain. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def lineEncd0 {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) : Prop :=
  match line with
  | .asm b bytes len => enc (cbwToAsmExact b) = bytes ∧ len = bytes.length
  | .labAsm a w bytes len => enc (labInst w a) = bytes ∧ bytes.length ≤ len ∧
      ∃ w' : BitVec width, len = (enc (labInst w' a)).length
  | .label _ _ _ => True

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def secEncd0 {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (sec : Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) : Prop :=
  ∀ line ∈ sec.lines, lineEncd0 enc line

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def allEncd0 {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) : Prop :=
  ∀ sec ∈ code, secEncd0 enc sec

private theorem encodedLine {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (skip : Nat) (line : Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) :
    lineEncd0 enc (encLine enc skip line) := by
  cases line with
  | label => trivial
  | asm => exact ⟨rfl,rfl⟩
  | labAsm => exact ⟨rfl,Nat.le_refl _,0,rfl⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecList_encd0 {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8)) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) :
    allEncd0 enc (encSecList enc ls) := by
  intro sec hm
  simp only [encSecList,List.mem_map] at hm
  rcases hm with ⟨original,_,rfl⟩
  intro line hl
  simp only [encSec,List.mem_map] at hl
  rcases hl with ⟨originalLine,_,rfl⟩
  exact encodedLine enc _ originalLine

/-- Independent max-length witness construction: either the old annotation's
witness or the newly encoded word realizes the actual returned maximum. -/
private theorem updatedLabAsm {width : Nat} [NeZero width]
    (enc : HolAsm width → List (BitVec 8))
    (a : AsmWithLab HolCmp (HolRegImm width) MlString)
    (w newWord : BitVec width) (bytes : List (BitVec 8)) (len : Nat)
    (h : lineEncd0 enc (.labAsm a w bytes len)) :
    lineEncd0 enc (.labAsm a newWord (enc (labInst newWord a))
      (max (enc (labInst newWord a)).length len)) := by
  rcases h with ⟨_,_,oldWitness,hold⟩
  refine ⟨rfl, Nat.le_max_left _ _, ?_⟩
  by_cases hle : (enc (labInst newWord a)).length ≤ len
  · rw [Nat.max_eq_right hle]
    exact ⟨oldWitness,hold⟩
  · rw [Nat.max_eq_left (by omega)]
    exact ⟨newWord,rfl⟩

private theorem encodedLinesInvariant {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (lines : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (pos : Nat) (acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool)
    (hl : ∀ line ∈ lines, lineEncd0 enc line)
    (ha : ∀ line ∈ acc, lineEncd0 enc line) :
    ∀ line ∈ (encLinesAgain labs ffis pos enc lines acc ok).1, lineEncd0 enc line := by
  induction lines generalizing pos acc ok with
  | nil => simpa [encLinesAgain] using ha
  | cons line tail ih =>
    have hx := hl line (by simp)
    have ht : ∀ line ∈ tail, lineEncd0 enc line := fun l hm => hl l (by simp [hm])
    cases line with
    | label s l len =>
      simp only [encLinesAgain]
      apply ih _ _ _ ht
      simpa using And.intro hx ha
    | asm a bytes len =>
      simp only [encLinesAgain]
      apply ih _ _ _ ht
      simpa using And.intro hx ha
    | labAsm a w bytes len =>
      simp only [encLinesAgain]
      split
      · apply ih _ _ _ ht
        simpa using And.intro hx ha
      · apply ih _ _ _ ht
        simpa using And.intro (updatedLabAsm enc a w _ bytes len hx) ha

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encLinesAgain_encd0 {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok : Bool)
    (res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok' : Nat × Bool) :
    encLinesAgain labs ffis pos enc lines acc ok = (res,ok') ∧
      (∀ line ∈ lines, lineEncd0 enc line) ∧
      (∀ line ∈ acc, lineEncd0 enc line) →
    ∀ line ∈ res, lineEncd0 enc line := by
  intro h
  have hi := encodedLinesInvariant labs ffis enc lines pos acc ok h.2.1 h.2.2
  rw [h.1] at hi
  exact hi

private theorem encodedSecsInvariant {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (ls : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (pos : Nat)
    (h : allEncd0 enc ls) : allEncd0 enc (encSecsAgain pos labs ffis enc ls).1 := by
  induction ls generalizing pos with
  | nil => simp [encSecsAgain,allEncd0]
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    have hl := h ⟨id,lines⟩ (by simp)
    have hr := ih (encLinesAgain labs ffis pos enc lines [] true).2.1
      (fun s hm => h s (by simp [hm]))
    have ho := encodedLinesInvariant labs ffis enc lines pos [] true hl (by simp)
    simpa [encSecsAgain,allEncd0,secEncd0] using And.intro ho hr

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecsAgain_encd0 {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (ls res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))) (ok : Bool) :
    encSecsAgain pos labs ffis enc ls = (res,ok) ∧ allEncd0 enc ls →
      allEncd0 enc res := by
  intro h
  have hi := encodedSecsInvariant labs ffis enc ls pos h.2
  rw [h.1] at hi
  exact hi

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem linesUpdLabLen_encd0 {width : Nat} [NeZero width]
    (pos : Nat) (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (enc : HolAsm width → List (BitVec 8)) :
    (∀ line ∈ ls, lineEncd0 enc line) ∧
      (∀ line ∈ acc, lineEncd0 enc line) →
    ∀ line ∈ (linesUpdLabLen pos ls acc).1, lineEncd0 enc line := by
  induction ls generalizing pos acc with
  | nil =>
    intro h
    simpa [linesUpdLabLen] using h.2
  | cons line tail ih =>
    intro h
    have hx := h.1 line (by simp)
    have ht : ∀ line ∈ tail, lineEncd0 enc line := fun l hm => h.1 l (by simp [hm])
    cases line with
    | label s l len =>
      simp only [linesUpdLabLen]
      apply ih
      refine ⟨ht, ?_⟩
      intro line hm
      rcases List.mem_cons.mp hm with rfl | hm
      · trivial
      · exact h.2 line hm
    | asm a bytes len =>
      simp only [linesUpdLabLen]
      apply ih
      exact ⟨ht, by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hx h.2⟩
    | labAsm a w bytes len =>
      simp only [linesUpdLabLen]
      apply ih
      exact ⟨ht, by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hx h.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem updLabLen_encd0 {width : Nat} [NeZero width]
    (pos : Nat) (ss : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (enc : HolAsm width → List (BitVec 8)) :
    allEncd0 enc ss → allEncd0 enc (updLabLen pos ss) := by
  induction ss generalizing pos with
  | nil => simp [updLabLen,allEncd0]
  | cons sec rest ih =>
    rcases sec with ⟨id,lines⟩
    intro h
    have hs := h ⟨id,lines⟩ (by simp)
    have hr := ih (linesUpdLabLen pos lines []).2
      (fun s hm => h s (by simp [hm]))
    have hl := linesUpdLabLen_encd0 pos lines [] enc ⟨hs, by simp⟩
    simpa [updLabLen,allEncd0,secEncd0] using And.intro hl hr

end Flapjack.Compiler.Backend.LabToTarget
