import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackNames.NamesOk
import Flapjack.Compiler.Backend.StackProps.FixedNames
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Compiler.Backend.StackProps.ProgramValidity

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackLang

/-- Flapjack proof motive for structural children of HOL comp_ind. This is
not an independent HOL declaration: it abbreviates the original three
guards and compiler-result validity without assuming target validity. -/
def stackNamesAsmGoal {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width) (p : HolProg width) : Prop :=
  stackAsmName config p ∧ namesOkSptHOL names config.regCount config.avoidRegs ∧
    fixedNames names config → stackAsmOkExact config (progCompHOL names p)

/-- Original HOL comp_ind Seq case; hypotheses are only child motives. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml"
  "stack_names_comp_stack_asm_ok" (words_as_type_indexed_bitvec)]
theorem stackNamesCompStackAsmOk_Seq {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (first second : HolProg width)
    (ihFirst : stackNamesAsmGoal names config first)
    (ihSecond : stackNamesAsmGoal names config second) :
    stackNamesAsmGoal names config (.seq first second) := by
  intro ⟨⟨hfirst, hsecond⟩, hn, hf⟩
  exact ⟨ihFirst ⟨hfirst, hn, hf⟩, ihSecond ⟨hsecond, hn, hf⟩⟩

/-- Original HOL comp_ind If case; hypotheses are only child motives. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml"
  "stack_names_comp_stack_asm_ok" (words_as_type_indexed_bitvec)]
theorem stackNamesCompStackAsmOk_If {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (operator : Cmp) (register : Nat) (right : HolRegImm width)
    (first second : HolProg width)
    (ihFirst : stackNamesAsmGoal names config first)
    (ihSecond : stackNamesAsmGoal names config second) :
    stackNamesAsmGoal names config (.ite operator register right first second) := by
  intro ⟨⟨hfirst, hsecond⟩, hn, hf⟩
  exact ⟨ihFirst ⟨hfirst, hn, hf⟩, ihSecond ⟨hsecond, hn, hf⟩⟩

/-- Original HOL comp_ind Loop case; hypotheses are only child motives. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml"
  "stack_names_comp_stack_asm_ok" (words_as_type_indexed_bitvec)]
theorem stackNamesCompStackAsmOk_Loop {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (body : HolProg width)
    (ih : stackNamesAsmGoal names config body) :
    stackNamesAsmGoal names config (.loop body) := by
  exact ih

/-- HOL Call case with induction hypotheses only for structural return and
handler bodies. Handler obligations stay nested under a SOME return. -/
@[hol "cakeml/compiler/backend/proofs/stack_namesProofScript.sml"
  "stack_names_comp_stack_asm_ok" (words_as_type_indexed_bitvec)]
theorem stackNamesCompStackAsmOk_Call {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width)
    (returns : Option (HolProg width × Nat × Nat × Nat)) (target : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ihReturn : ∀ body link l1 l2, returns = some (body, link, l1, l2) →
      stackNamesAsmGoal names config body)
    (ihHandler : ∀ body l1 l2, handler = some (body, l1, l2) →
      stackNamesAsmGoal names config body) :
    stackNamesAsmGoal names config (.call returns target handler) := by
  have hr := namesOkImp names config
  cases returns with
  | none =>
    cases target <;> cases handler <;> simp_all [stackNamesAsmGoal, stackAsmName, progCompHOL, stackAsmOkExact, destFindNameHOL, asmRegOkExact, findNameSpt_eq_lookupHelper] <;> grind
  | some ret =>
    rcases ret with ⟨body, link, l1, l2⟩
    cases handler with
    | none =>
      cases target <;> simp_all [stackNamesAsmGoal, stackAsmName, progCompHOL, stackAsmOkExact, destFindNameHOL, asmRegOkExact, findNameSpt_eq_lookupHelper] <;> grind
    | some hand =>
      rcases hand with ⟨body2, h1, h2⟩
      cases target <;> simp_all [stackNamesAsmGoal, stackAsmName, progCompHOL, stackAsmOkExact, destFindNameHOL, asmRegOkExact, findNameSpt_eq_lookupHelper] <;> grind

end Flapjack.Compiler.Backend.StackNames
