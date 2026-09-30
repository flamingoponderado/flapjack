import Flapjack.Compiler.Backend.Semantics.WordSem.Inst

namespace Flapjack.WordSemStateFiniteExact

/-- Kernel prerequisite for HOL wordProps `inst_const` (935-942). This is
currently Flapjack infrastructure, deliberately untagged: the instruction
rendering still has the unresolved real-sqrt fidelity dependency h29l.6/dshl.
The source-shaped success premise and clock/FFI conclusions are preserved;
this invariant alone does not establish instruction semantic correspondence. -/
theorem instConst {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (state next : WordSemStateFiniteExact width C F)
    (h : inst i state = some next) :
    next.clock = state.clock ∧ next.ffi = state.ffi := by
  unfold inst at h
  repeat' split at h
  all_goals (try dsimp only at h)
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [reduceCtorEq] at h; done)
    | (cases h; exact ⟨rfl, rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (unfold assign at h; split at h
       · cases h
       · cases h; exact ⟨rfl, rfl⟩)
    | (rename_i heq; cases h
       unfold memStore at heq
       split at heq <;> cases heq <;> exact ⟨rfl, rfl⟩)

end Flapjack.WordSemStateFiniteExact
