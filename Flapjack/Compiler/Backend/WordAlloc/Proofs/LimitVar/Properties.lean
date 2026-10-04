import Flapjack.Compiler.Backend.WordAlloc.LimitVar
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Arithmetic
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Maximum.MaxVar
import Flapjack.Pancake.WordConvs.ProgramMonotonicity

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Full native program limit: the original equality premise implies the
allocation class and strict bound on every original register occurrence.
Call handler traversal remains return-dependent as in the original every_var. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem limitVarProps {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (limit : Nat)
    (hlimit : limitVar program = limit) :
    isAllocVar limit ∧ everyVarHOL (fun x => decide (x < limit)) program = true := by
  subst limit
  obtain ⟨allocated, bound⟩ := limitVarArithmetic (maxVarHOL program)
  refine ⟨allocated, ?_⟩
  apply everyVarMono (fun x => decide (x ≤ maxVarHOL program)) program
    (fun x => decide (x < limitVar program))
  refine ⟨?_, maxVarMax program⟩
  intro x hx
  simp only [decide_eq_true_eq] at hx ⊢
  dsimp [limitVar]
  omega

end Flapjack.Compiler.Backend.WordAlloc
