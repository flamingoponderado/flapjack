module

public import Flapjack.Compiler.Backend.LabLang
public import Flapjack.Compiler.Backend.LabSem
public import Flapjack.Compiler.Encoders.Asm
public import Flapjack.Pancake.WordLang
public import Flapjack.Compiler.Backend.StackToLab
public import Flapjack.Compiler.Backend.StackProps

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Cake labProps pre-encoding predicates

The source clauses are `labPropsScript.sml:1247-1257`. The section/list
traversal and treatment of each line constructor are ported directly. HOL's
imported `asm`, `asm_config`, `asm_ok`, and `cbw_to_asm` definitions are
represented by the constructor/check operations below; this file does not
claim that the callbacks are the full HOL assembler configuration.
-/

namespace Flapjack.Compiler.Backend.LabProps

open Flapjack.Compiler.Backend.LabLang

/-- Flapjack-specific Boolean section-label check over generic payloads. -/
def secEndsWithLabel {AsmOrCbw AsmWithLab Word : Type}
    (sec : Section (Line AsmOrCbw AsmWithLab Word)) : Bool :=
  match sec.lines.reverse with
  | [] => false
  | line :: _ => LabSem.isLabel line

/-- Flapjack-specific generic section-label predicate. Its arbitrary instruction
and word payload types differ from the concrete HOL LabLang carrier, so this
is not a tagged port of `labProps$sec_ends_with_label_def`. A native replacement
is tracked by bead `flapjack-1u9a`; the generic utility remains for existing callers. -/
def secEndsWithLabelHOL {AsmOrCbw AsmWithLab Word : Type}
    (sec : Section (Line AsmOrCbw AsmWithLab Word)) : Prop :=
  match sec.lines.reverse with
  | [] => False
  | line :: _ => LabSem.isLabel line = true

/-- Local compatibility fact between the generic Boolean and Prop checks;
there is no independently claimed HOL declaration at these generic carriers. -/
theorem secEndsWithLabelHOL_iff_bool {AsmOrCbw AsmWithLab Word : Type}
    (sec : Section (Line AsmOrCbw AsmWithLab Word)) :
    secEndsWithLabelHOL sec ↔ secEndsWithLabel sec = true := by
  unfold secEndsWithLabelHOL secEndsWithLabel
  cases sec.lines.reverse with
  | nil => simp
  | cons line rest => simp

/-- Concrete `FlattenOps` for the pipeline's assembler carrier: the embedded
constructors are `asm$Skip`, `asm$Inst`, `asm$JumpReg`, `asm$Reg`, `asm$Lower`
and the `negate` table from `cakeml/compiler/backend/stack_to_labScript.sml:24-32`,
all over the faithful `AsmData`/`WordLangInst`/`WordRegImm` carriers. These
constructors are independent of the `asm_config` record, so no configuration
argument is required. -/
def flattenOps {width : Nat} :
    StackToLab.FlattenOps (WordLangInst (BitVec width)) Flapjack.Cmp
      (WordRegImm (BitVec width)) (Encoders.Asm.AsmData width) where
  skip := .inst .skip
  embedInst := fun instruction => .inst instruction
  jumpReg := fun register => .jumpReg register
  reg := fun register => .reg register
  lower := .lower
  negate := fun operator =>
    match operator with
    | .less => .notLess
    | .equal => .notEqual
    | .lower => .notLower
    | .test => .notTest
    | .notLess => .less
    | .notEqual => .equal
    | .notLower => .lower
    | .notTest => .test
/-! ## `sec_ends_with_label` and the `prog_to_section` label invariant

HOL `labProps$sec_ends_with_label_def` plus the proof-script corollary
`stack_to_labProofScript.sml:3620` `EVERY_sec_ends_with_label_MAP_prog_to_section`.
The corollary is stated as an untagged Flapjack analogue because `progToSection`
is parameterised by `ops : FlattenOps ...`, whereas HOL `prog_to_section` uses the
fixed global `flatten` (the same representation gap recorded for the app-list
bridges). -/
section SecEndsWithLabel

/-- A section whose lines are an arbitrary prefix followed by a `Label` ends with
a label. Structural core of `EVERY_sec_ends_with_label_MAP_prog_to_section`,
independent of the `FlattenOps` parameterisation. -/
theorem secEndsWithLabel_append_label {AsmOrCbw AsmWithLab Word : Type}
    (lines : List (Line AsmOrCbw AsmWithLab Word)) (sectionId label length : Nat) :
    secEndsWithLabel
        ({ sectionId := sectionId
           lines := lines ++ [.label sectionId label length] } :
          Section (Line AsmOrCbw AsmWithLab Word)) = true := by
  simp [secEndsWithLabel, LabSem.isLabel]

/-- `progToSection` output ends with a label. Untagged analogue of HOL
`EVERY_sec_ends_with_label_MAP_prog_to_section` (`stack_to_labProofScript.sml:3620`). -/
theorem secEndsWithLabel_progToSection
    {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : StackToLab.FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)
    (sectionId : Nat)
    (program : StackLang.Prog Inst Cmp RegImm Binop Memop Addr MlString) :
    secEndsWithLabel
        (StackToLab.progToSection ops zero sectionId program) = true := by
  simp only [StackToLab.progToSection]
  exact secEndsWithLabel_append_label _ sectionId _ _

/-- HOL `EVERY_sec_ends_with_label_MAP_prog_to_section`
(`stack_to_labProofScript.sml:3620`): every section produced for a program list
ends with a label. Untagged because `progToSection` carries the `FlattenOps`
parameter absent from HOL's fixed global `flatten`. -/
theorem everySecEndsWithLabel_map_progToSection
    {Inst Cmp RegImm Binop Memop Addr MlString AsmInst Word : Type}
    (ops : StackToLab.FlattenOps Inst Cmp RegImm AsmInst) (zero : Word)
    (programs : List (Nat × StackLang.Prog Inst Cmp RegImm Binop Memop Addr MlString)) :
    (programs.map
        (fun entry => StackToLab.progToSection ops zero entry.1 entry.2)).all
      secEndsWithLabel = true := by
  rw [List.all_eq_true]
  intro sec hmem
  simp only [List.mem_map] at hmem
  obtain ⟨entry, _hentry, rfl⟩ := hmem
  exact secEndsWithLabel_progToSection ops zero entry.1 entry.2

end SecEndsWithLabel

end Flapjack.Compiler.Backend.LabProps
