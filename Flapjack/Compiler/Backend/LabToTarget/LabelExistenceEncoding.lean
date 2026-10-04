import Flapjack.Compiler.Backend.LabToTarget.LabelExistence
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.Encoding
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

/-- List-relation transport for the original encoder proof. This is local
Flapjack proof infrastructure with no independently named HOL declaration. -/
private theorem lineExists_of_similar {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt α)) {xs ys : List (LabLineHOL width)}
    (hrel : LinesRel lineSimilar xs ys) (hx : ∀ l ∈ xs,lineLabsExist labs l) :
    ∀ l ∈ ys,lineLabsExist labs l := by
  induction hrel with
  | nil => simp
  | @cons x y xs ys hxy ht ih =>
    intro l hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (lineSimilar_lineLabsExist labs x l hxy).mp (hx x (by simp))
    · exact ih (fun l hm => hx l (by simp [hm])) l hm

/-- Full original accumulator encoder existence preservation, with independent
polymorphic existence-map values and the full Nat × Bool returned component.
Original quantified k is vacuous: source5088-5094 and the full inferred type
show no occurrence in any premise or result. Only that unused binder is omitted. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encLinesAgain_lineLabsExist {α : Type} {width : Nat} [NeZero width]
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (pos : Nat)
    (enc : HolAsm width → List (BitVec 8)) (lines acc : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)))
    (ok : Bool) (res : List (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))) (ok' : Nat × Bool) (labs' : Spt (Spt α)) :
    encLinesAgain labs ffis pos enc lines acc ok = (res,ok') ∧
    (∀ l ∈ acc,lineLabsExist labs' l) ∧ (∀ l ∈ lines,lineLabsExist labs' l) →
    ∀ l ∈ res,lineLabsExist labs' l := by
  rintro ⟨heq,ha,hl⟩
  have hr : LinesRel lineSimilar acc.reverse acc.reverse := by
    induction acc.reverse with
    | nil => exact .nil
    | cons x xs ih => exact .cons (lineSimilar_refl x) ih
  have hsim := encLinesAgain_implies_similar labs ffis pos enc lines acc ok res ok' acc.reverse heq hr
  apply lineExists_of_similar labs' hsim
  intro l hm
  rcases List.mem_append.mp hm with hm | hm
  · exact ha l (List.mem_reverse.mp hm)
  · exact hl l hm

/-- Full original section encoder existence preservation for either returned
Bool flag. Original source5100-5105 swaps the names ffis/labs relative to their
inferred map/list types; the operation's actual argument types/order are retained.
The original independent quantified k is unused in all premises and conclusion
and is omitted, as confirmed by the complete original type capture. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem encSecsAgain_allLabsExist {α : Type} {width : Nat} [NeZero width]
    (pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) (code res : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (ok : Bool) (labs' : Spt (Spt α)) :
    encSecsAgain pos labs ffis enc code = (res,ok) ∧ allLabsExist labs' code →
    allLabsExist labs' res := by
  rintro ⟨heq,hcode⟩
  exact (codeSimilar_allLabsExist labs' code res
    (encSecsAgain_implies_similar pos labs ffis enc code res ok heq)).mp hcode
end Flapjack.Compiler.Backend.LabToTarget
