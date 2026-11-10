module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.Syntactic

@[expose] public section

/-! Invariants of the optional multi-argument introduction pass. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- The optional multi-argument pass clears auxiliary code only when enabled. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "SND_cond_mti_compile_inc"]
theorem snd_condMtiCompileInc {α : Type} (enabled : Bool) (maxApp : Nat)
    (program : List Exp × List α) :
    (ClosMti.condCompileInc enabled maxApp program).2 =
      (if enabled then [] else program.2) := by
  cases enabled <;> rfl

/-- Uncurrying applies a binary function to the components of its argument. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "UNCURRY_EQ"]
theorem uncurry_eq {α β γ : Type} (f : α → β → γ) :
    Function.uncurry f = fun x => f x.1 x.2 := by
  funext ⟨a, b⟩
  rfl

/-- The optional multi-argument pass preserves the main program length. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "LENGTH_FST_cond_mti_compile_inc"]
theorem length_fst_condMtiCompileInc {α : Type} (enabled : Bool) (maxApp : Nat)
    (program : List Exp × List α) :
    (ClosMti.condCompileInc enabled maxApp program).1.length = program.1.length := by
  cases enabled <;> simp [ClosMti.condCompileInc, ClosMti.compileInc, ClosMti.introList_length]

/-- The optional multi-argument pass preserves the function-annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_vs_NONE_cond_mti_compile_inc"]
theorem everyFnVarsNone_condMtiCompileInc {α : Type} (enabled : Bool) (maxApp : Nat)
    (program : List Exp × List α) :
    everyFnVarsNone (ClosMti.condCompileInc enabled maxApp program).1 ↔
      everyFnVarsNone program.1 := by
  cases enabled <;> simp [ClosMti.condCompileInc, ClosMti.compileInc, ClosMti.introList_varsNone]

end Flapjack.Compiler.Backend.ClosToBvl
