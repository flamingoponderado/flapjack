import Flapjack.Compiler.Backend.WordToStack.NativePrograms
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallCompiler

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-specific single-row helper for the original program-list proof.
There is no separate original HOL theorem for this local conjunction step;
its unconditional StackAlloc prefix and full actual compiler body are retained. -/
private theorem compileProgNoInstall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (program : WordLangProgHOL (BitVec width)) (argumentCount registerCount : Nat)
    (bitmaps : AppList (BitVec width) × Nat)
    (guard : noInstallSubprogsHOL program = true) :
    noInstall (compileProgNative conf false program argumentCount registerCount bitmaps).1 = true := by
  simp only [compileProgNative, noInstall, Bool.true_and]
  exact compNoInstall conf false program bitmaps _ _ _ guard rfl rfl

/-- Full original program-list preservation. The identifier carrier is
independent of the word dimension, every source field and output component
remains arbitrary, and only the original source EVERY, compiler equality
and false-performance equality are hypotheses. Row and tail induction hypotheses are discharged internally. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_word_to_stack_no_install" (words_as_type_indexed_bitvec)]
theorem compileWordToStackNoInstall {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (registerCount : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : AppList (BitVec width) × Nat)
    (outputs : List (β × HolProg width)) (frames : List Nat)
    (residual : AppList (BitVec width) × Nat)
    (guard : (programs.all fun row => noInstallSubprogsHOL row.2.2) = true)
    (compiled : compileWordToStackNative conf perf registerCount programs bitmaps =
      (outputs,frames,residual))
    (plain : perf = false) :
    (outputs.all fun row => noInstall row.2) = true := by
  subst perf
  induction programs generalizing bitmaps outputs frames residual with
  | nil =>
      have result := congrArg Prod.fst compiled
      simp only [compileWordToStackNative] at result
      rw [← result]
      rfl
  | cons row programs ih =>
      rcases row with ⟨identifier,argumentCount,program⟩
      have guards : noInstallSubprogsHOL program = true ∧
          (programs.all fun row => noInstallSubprogsHOL row.2.2) = true := by
        apply Bool.and_eq_true_iff.mp
        simpa only [List.all_cons] using guard
      have headSafe := compileProgNoInstall conf program argumentCount registerCount bitmaps guards.1
      have tailSafe := ih
        (compileProgNative conf false program argumentCount registerCount bitmaps).2.2
        (compileWordToStackNative conf false registerCount programs
          (compileProgNative conf false program argumentCount registerCount bitmaps).2.2).1
        (compileWordToStackNative conf false registerCount programs
          (compileProgNative conf false program argumentCount registerCount bitmaps).2.2).2.1
        (compileWordToStackNative conf false registerCount programs
          (compileProgNative conf false program argumentCount registerCount bitmaps).2.2).2.2 guards.2 rfl
      have result := congrArg Prod.fst compiled
      simp only [compileWordToStackNative] at result
      rw [← result]
      simp only [List.all_cons, headSafe, tailSafe, Bool.true_and]

end Flapjack.Compiler.Backend.WordToStack.Native
