import Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
import Flapjack.Compiler.Backend.StackToLab.Proofs.InstCorrect
import Flapjack.Compiler.Backend.LabProps.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-! Statement of `flatten_correct` (`stack_to_labProofScript.sml:1207-2740`)
split along the HOL proof's own `evaluate_ind` cases. `FlattenHyps` and
`FlattenConcl` are the theorem's hypotheses and conclusion verbatim;
`FlattenProp prog s1` quantifies the remaining variables. Each constructor
case proves `FlattenProp` from an induction hypothesis for the strictly
smaller `(clock, program size)` measure of the StackSem evaluator. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers

/-- The hypotheses of `flatten_correct`, verbatim. -/
def FlattenHyps {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Prop :=
  StackSemEvaluate.evaluate (prog, s1) = (r, s2) ∧ r ≠ some .error ∧ stateRel s1 t1 ∧
    StackProps.callArgs prog t1.ptrReg t1.lenReg t1.ptr2Reg t1.len2Reg t1.linkReg ∧
    codeInstalled t1.pc (appListAppend (flattenHOL t prog n l cs bs).1) t1.code ∧
    ∀ k ∈ cs ++ bs ++ [0], (locToPc n k t1.code).isSome

/-- The conclusion of `flatten_correct`, verbatim. -/
def FlattenConcl {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
    match haltView r with
    | some res => evaluate { t1 with clock := t1.clock + ck } = (res, t2) ∧ t2.ffi = s2.ffi
    | none =>
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      match r.map (fun w => resultView w n cs bs) with
      | none =>
        t2.pc = t1.pc + ((appListAppend (flattenHOL t prog n l cs bs).1).filter
          (fun x => !isLabelHOL x)).length ∧ stateRel s2 t2
      | some (.vloc n1 n2) =>
        (∀ k, (sptLookup k s2.code).isSome → (locToPc k 0 t2.code).isSome) ∧
          ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2
      | some (.vcont n1 n2) =>
        stateRel s2 t2 ∧ codeInstalled t2.pc [.labAsm (.jump (.lab n1 n2)) 0 [] 0] t2.code
      | some .vtimeout => t2.ffi = s2.ffi ∧ t2.clock = 0
      | some .verr => False

/-- `flatten_correct` for one program and initial state. -/
def FlattenProp {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F),
    FlattenHyps prog s1 t r s2 n l cs bs t1 → FlattenConcl prog t r s2 n l cs bs t1

/-- The lexicographic `(clock, size)` order of StackSem evaluation. -/
def MeasureLt {width : Nat} [NeZero width] {C F : Type}
    (p' : HolProg width) (s' : StackSemStateFiniteExact width C F)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  s'.clock < s.clock ∨ (s'.clock = s.clock ∧ sizeOf p' < sizeOf p)

/-- The induction hypothesis available to a constructor case. -/
def FlattenIH {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (p' : HolProg width) (s' : StackSemStateFiniteExact width C F),
    MeasureLt p' s' p s → FlattenProp p' s'

theorem withSameClock {width : Nat} [NeZero width] {C F : Type}
    (t : Flapjack.Compiler.Backend.LabSem.State width C F) : { t with clock := t.clock } = t := rfl

/-- A program whose flattening is empty and that leaves the state unchanged
without a result is simulated by staying put. -/
theorem flattenConclStay {width : Nat} [NeZero width] {C F : Type} {prog : HolProg width}
    {t : Bool} {s : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (rel : stateRel s t1)
    (empty : ((appListAppend (flattenHOL t prog n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 0) :
    FlattenConcl prog t none s n l cs bs t1 := by
  refine ⟨0, t1, ?_⟩
  simp only [haltView, Option.map_none, true_and]
  exact ⟨fun ck1 => by simp, List.prefix_refl _, by omega, rel⟩

/-- `Skip` case. -/
theorem flattenCorrectSkip {width : Nat} [NeZero width] {C F : Type}
    (s1 : StackSemStateFiniteExact width C F) : FlattenProp (.skip : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, -, -⟩
  rw [StackSemEvaluate.evaluate_skip] at ev
  cases ev
  exact flattenConclStay rel (by simp [flattenHOL, (appListAppend_thm .nil .nil []).2.1])

end Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
