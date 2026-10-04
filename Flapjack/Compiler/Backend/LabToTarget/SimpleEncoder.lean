import Flapjack.Compiler.Backend.LabToTarget.SecondPass
import Flapjack.Compiler.Backend.LabToTarget.SectionLength

/-! Original proof-side simple repeated encoding, full accumulator agreement,
and recorded-length preservation with the original successful-result guard.
The original auxiliary is defined in the proof script; the executed compiler
continues to use the reviewed accumulator encoder. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def encLinesAgainSimp {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) :
    List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) → List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)) × Bool
  | [] => ([],true)
  | .label s l len :: xs =>
      let (rest,ok) := encLinesAgainSimp labs ffis (pos + len) enc xs
      (.label s l len :: rest,ok)
  | .asm a bytes len :: xs =>
      let (rest,ok) := encLinesAgainSimp labs ffis (pos + len) enc xs
      (.asm a bytes len :: rest,ok)
  | .labAsm a w bytes len :: xs =>
      let w1 := getJumpOffset a ffis labs pos
      if w = w1 then
        let (rest,ok) := encLinesAgainSimp labs ffis (pos + len) enc xs
        (.labAsm a w bytes len :: rest,ok)
      else
        let bs := enc (labInst w1 a)
        let len1 := max bs.length len
        let (rest,ok) := encLinesAgainSimp labs ffis (pos + len1) enc xs
        (.labAsm a w1 bs len1 :: rest,decide (len1 = len) && ok)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encLinesAgainSimp_eq {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (ls acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (b : Bool) :
    let (ls',flag) := encLinesAgainSimp labs ffis pos enc ls
    encLinesAgain labs ffis pos enc ls acc b =
      (acc.reverse ++ ls',secLength ls' pos,b && flag) := by
  induction ls generalizing pos acc b with
  | nil => simp [encLinesAgainSimp,encLinesAgain,secLength]
  | cons line tail ih =>
    cases line <;>
      simp [encLinesAgainSimp,encLinesAgain,ih,secLength,List.reverse_cons,
        List.append_assoc,Bool.and_assoc]
    split <;> simp [secLength]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encLinesAgainSimp_len {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8))
    (lines res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) :
    encLinesAgainSimp labs ffis pos enc lines = (res,true) →
      res.map lineLen = lines.map lineLen := by
  induction lines generalizing pos res with
  | nil => simp [encLinesAgainSimp]
  | cons line tail ih =>
    intro heq
    cases line <;> simp only [encLinesAgainSimp] at heq
    all_goals try split at heq
    all_goals
      generalize hr : encLinesAgainSimp labs ffis _ enc tail = result at heq
      rcases result with ⟨rest,flag⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨hres,hflag⟩
      subst res
      simp only [List.map_cons,lineLen]
      try simp only [Bool.and_eq_true, decide_eq_true_eq] at hflag
      first
      | exact congrArg (List.cons _) (ih _ rest (hr.trans (congrArg (Prod.mk rest) hflag)))
      | rw [hflag.1]
        exact congrArg (List.cons _) (ih _ rest (hr.trans (congrArg (Prod.mk rest) hflag.2)))

end Flapjack.Compiler.Backend.LabToTarget
