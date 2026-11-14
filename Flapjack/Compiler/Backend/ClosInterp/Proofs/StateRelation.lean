module

public import Flapjack.Compiler.Backend.ClosInterp.Optimise
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Compiler.Backend.BackendProps.Pure
public import Flapjack.Misc.ShiftSeq

@[expose] public section

/-! State and compiler relationships for interpreter insertion. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.Compiler.Backend.BackendProps

namespace StateRelationPort
/-- The closure state uses the canonical finite-support map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end StateRelationPort

/-- Apply interpreter insertion to the executable part of a closure program. -/
def insertProgram (program : ClosSem.Program) : ClosSem.Program :=
  (insertInterp program.1, program.2)

/-- State relationship before requiring an installed interpreter closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "state_rel_1_def"
  (fmap_as_finite_support := [refs, code])]
def StateRel1 {C F : Type} (source target : ClosSem.State C F) : Prop :=
  (∀ index, (source.compileOracle index).2.2 = []) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty ∧
  target.maxApp = source.maxApp ∧ 1 ≤ source.maxApp ∧
  target.clock = source.clock ∧ target.ffi = source.ffi ∧
  source.globals = target.globals ∧ source.refs = target.refs ∧
  source.compile = pureCc insertProgram target.compile ∧
  target.compileOracle = pureCo insertProgram ∘ source.compileOracle

/-- The insertion simulation also needs the interpreter in global slot zero. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
def StateRel {C F : Type} (source target : ClosSem.State C F) : Prop :=
  StateRel1 source target ∧ source.globals.head? =
    some (some (.closure none [] [] 1 closInterpreter))

/-- Related interpreter states have equal reference stores and clocks. -/
@[hol "cakeml/compiler/backend/proofs/clos_interpProofScript.sml" "state_rel_refs_clocks_eqs"
  (fmap_as_finite_support := [refs, code])]
theorem stateRel_refs_clocks {C F : Type} {source target : ClosSem.State C F}
    (related : StateRel source target) : source.refs = target.refs ∧ source.clock = target.clock :=
  ⟨related.1.2.2.2.2.2.2.2.2.1, related.1.2.2.2.2.2.1.symm⟩

/-- States related before installing the interpreter differ only in their
compiler callback and oracle. -/
theorem stateRel1_replaceCompiler {C F : Type} (source target : ClosSem.State C F)
    (related : StateRel1 source target) :
    source = { target with compile := source.compile, compileOracle := source.compileOracle } := by
  rcases related with ⟨_, sourceCode, targetCode, maxEq, _, clockEq, ffiEq, globalsEq, refsEq, _, _⟩
  cases source
  cases target
  simp_all

/-- Giving both related states the same clock preserves the relation. -/
theorem stateRel_withClock {C F : Type} {source target : ClosSem.State C F}
    (related : StateRel source target) (clock : Nat) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  rcases related with ⟨⟨safe, sc, tc, maxEq, maxPositive, _, ffi, globals, refs, compiler, oracle⟩, interpreter⟩
  exact ⟨⟨safe, sc, tc, maxEq, maxPositive, rfl, ffi, globals, refs, compiler, oracle⟩, interpreter⟩

end Flapjack.Compiler.Backend.ClosInterp
