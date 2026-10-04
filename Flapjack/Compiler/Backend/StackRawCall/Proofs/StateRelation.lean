import Flapjack.Compiler.Backend.StackRawCall
import Flapjack.Compiler.Backend.StackRawCall.Proofs.StateOk
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompLn
import Flapjack.Compiler.Backend.Semantics.StackSem.State

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Canonical roundtrip for the imported full state carrier. This is
Flapjack representation infrastructure, with no separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Literal rawcall state relation: the full state is preserved except code,
whose domain is unchanged. Each source code entry has its own existential
frame-info witness, independent of the outer frame-info argument. The source's
commented compile/oracle clauses are inactive and impose no obligations.
The whole-state equality includes regs/fpRegs/store at the imported canonical
finite-map carrier; code itself is the native Spt, not a finite map. All 22
state fields, configuration and FFI parameters are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def stateRel {width : Nat} [NeZero width] {C F : Type} (info : Spt Nat)
    (source target : StackSemStateFiniteExact width C F) : Prop :=
  ∃ code : Spt (HolProg width),
    sptDomain code = sptDomain source.code ∧
    target = { source with code := code } ∧
    stateOk info source.code ∧
    ∀ n body, sptLookup n source.code = some body →
      ∃ entryInfo : Spt Nat, stateOk entryInfo source.code ∧
        sptLookup n code = some (compTop entryInfo body)

/-- Flapjack verification infrastructure: the independent empty entry-info
witness makes the literal relation reflexive whenever its outer frame-info
obligation holds. This does not assume a target relation or evaluation. -/
theorem stateRel_self {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source : StackSemStateFiniteExact width C F)
    (frames : stateOk info source.code) : stateRel info source source := by
  refine ⟨source.code, rfl, rfl, frames, ?_⟩
  intro n body entry
  refine ⟨.ln, stateOk_empty source.code, ?_⟩
  simpa only [(compLn info body).1] using entry

/-- Flapjack verification infrastructure: the whole-state equality in the
relation preserves the compile oracle, rather than transporting it through
the pass. The source's commented oracle clause is intentionally inactive. -/
theorem stateRel_compileOracle {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) :
    target.compileOracle = source.compileOracle := by
  obtain ⟨code, _, equality, _⟩ := relation
  subst target
  rfl

end Flapjack.Compiler.Backend.StackRawCall
