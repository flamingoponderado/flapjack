import Flapjack.Compiler.Backend.WordToStack.NativePrograms

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

/-- Projection form used internally to prove the source's output-equation
statement. This is Flapjack proof infrastructure, not a separate HOL theorem. -/
private theorem compileWordToStackKeys {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (registerCount : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : AppList (BitVec width) × Nat) :
    (compileWordToStackNative conf perf registerCount programs bitmaps).1.map Prod.fst =
      programs.map Prod.fst := by
  induction programs generalizing bitmaps with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨identifier, arguments, program⟩
      rcases hprog : compileProgNative conf perf program arguments registerCount bitmaps with
        ⟨body, frame, nextBitmaps⟩
      have hkeys := ih nextBitmaps
      rcases htail : compileWordToStackNative conf perf registerCount tail nextBitmaps with
        ⟨bodies, frames, finalBitmaps⟩
      simp only [htail] at hkeys
      simp only [compileWordToStackNative, hprog, htail, List.map_cons]
      exact congrArg (List.cons identifier) hkeys

/-- The full source key-preservation theorem. Identifiers retain HOL's
independent generic type; the output remainder is the original right-associated
pair of frame sizes and bitmap state. No frame, uniqueness or compilation
success premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem mapFstCompileWordToStack {width : Nat} [NeZero width] {β : Type} :
    ∀ (conf : AsmConfigExact width) (perf : Bool) (registerCount : Nat)
      (programs : List (β × Nat × WordLangProgHOL (BitVec width)))
      (bitmaps : AppList (BitVec width) × Nat) (bodies : List (β × HolProg width))
      (remainder : List Nat × (AppList (BitVec width) × Nat)),
      compileWordToStackNative conf perf registerCount programs bitmaps = (bodies, remainder) →
        bodies.map Prod.fst = programs.map Prod.fst := by
  intro conf perf registerCount programs bitmaps bodies remainder compiled
  have h := compileWordToStackKeys conf perf registerCount programs bitmaps
  simpa only [compiled] using h

end Flapjack.WordToStackProofs
