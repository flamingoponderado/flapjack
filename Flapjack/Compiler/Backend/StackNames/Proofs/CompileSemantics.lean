import Flapjack.Compiler.Backend.StackNames.Proofs.CompCorrect
import Flapjack.Compiler.Backend.Semantics.StackSem.Semantics

/-!
# stack_namesProof: `compile_semantics` and `compile_semantics_alt`

Ports of `cakeml/compiler/backend/proofs/stack_namesProofScript.sml` lines 527-555: the
observational StackSem `semantics` is unchanged by `rename_state`, from `comp_correct` at the
entry call `Call NONE (INL start) NONE` (which `comp` leaves unchanged).
-/

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps Flapjack.StackSemEvaluate

namespace CompileSemantics

/-- Canonical imported StackSem carrier roundtrip for the semantics ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- `comp_correct` at the entry call, for every clock (Flapjack infrastructure). -/
theorem evaluate_entry_renameState {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} (hf : Function.Bijective (findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ compileHOL f)) (start k : Nat) :
    evaluate ((.call none (.inl start) none : HolProg width), { renameState c f s with clock := k }) =
      ((evaluate ((.call none (.inl start) none : HolProg width), { s with clock := k })).1,
        renameState c f (evaluate ((.call none (.inl start) none : HolProg width),
          { s with clock := k })).2) :=
  compCorrect (c := c) (f := f) (.call none (.inl start) none) { s with clock := k } _ _
    ⟨rfl, hf, ha, hs, hk, hc⟩

end CompileSemantics

/-- Exact HOL `compile_semantics` (`stack_namesProofScript.sml:527-545`). HOL's free `f`, `c`,
`s` and `start` are the implicit binders. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileSemantics {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {start : Nat} {s : StackSemStateFiniteExact width C F} :
    Function.Bijective (findNameSpt f) ∧ ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack ∧
        s.compile = (fun cfg => c cfg ∘ compileHOL f) →
      semantics start (renameState c f s) = semantics start s := by
  rintro ⟨hf, ha, hs, hk, hc⟩
  have key := CompileSemantics.evaluate_entry_renameState hf ha hs hk hc start
  exact semantics_congr start s _ (renameState c f) (fun _ => rfl) key

/-- Exact HOL `compile_semantics_alt` (`stack_namesProofScript.sml:545-553`, `[local]`). HOL's
free `f` and `start` are the implicit binders. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileSemanticsAlt {width : Nat} [NeZero width] {C F : Type} {f : Spt Nat}
    {start : Nat} :
    ∀ (s t : StackSemStateFiniteExact width C F),
      Function.Bijective (findNameSpt f) ∧ renameState t.compile f s = t ∧
          s.compile = (fun c => t.compile c ∘ compileHOL f) ∧
          ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack →
        semantics start t = semantics start s := by
  rintro s t ⟨hf, ht, hc, ha, hs, hk⟩
  rw [← ht]
  exact compileSemantics ⟨hf, ha, hs, hk, hc⟩

end Flapjack.Compiler.Backend.StackNames
