import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramCodeLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
import Flapjack.Compiler.Backend.StackProps.LabelSafety
import Flapjack.Pancake.WordConvs.LabelSafety

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Full source incremental code-label safety. External labels remain an arbitrary
set; only the original two stub memberships, complete compiler output equation
and source safety predicate are premises. Target label safety is derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackGoodCodeLabelsIncr {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (registers : Nat)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) (bodies : List (Nat × HolProg width))
    (frames : List Nat) (bs' : AppList (BitVec width) × Nat)
    (externalLabels : Set Nat)
    (premises : raiseStubLocation ∈ externalLabels ∧
      storeConstsStubLocation ∈ externalLabels ∧
      compileWordToStackNative conf false registers rows bs = (bodies,frames,bs'))
    (good : goodCodeLabelsHOL rows externalLabels) :
    stackGoodCodeLabels bodies externalLabels := by
  have bound := compileWordToStackCodeLabels conf false registers rows bs bodies
    (frames,bs') good.1 rfl premises.2.2
  have keys := Flapjack.WordToStackProofs.mapFstCompileWordToStack conf false registers
    rows bs bodies (frames,bs') premises.2.2
  unfold stackGoodCodeLabels
  intro label member
  rcases bound member with h | h | h | h
  · subst label
    exact Or.inl (Or.inl (Or.inr ⟨raiseStubLocation,premises.1,rfl⟩))
  · subst label
    exact Or.inl (Or.inl (Or.inr ⟨storeConstsStubLocation,premises.2.1,rfl⟩))
  · rcases h with ⟨name, referenced, equation⟩
    rcases good.2 referenced with owned | external
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨name,by simpa only [keys] using owned,equation⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨name,external,equation⟩))
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))

end Flapjack.Compiler.Backend.WordToStack.Native
