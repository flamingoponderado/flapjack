import Flapjack.Compiler.Backend.StackRemove.Proofs.RelationLaws
import Flapjack.Compiler.Backend.Semantics.StackSem.Control
namespace Flapjack.Compiler.Backend.StackRemove.FindCode
open Flapjack Compiler.Backend.StackLang

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness


/-- Flapjack infrastructure: project the original code conjunct; no separate HOL declaration. -/
theorem codeLookup {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer label : Nat)
    (source target : StackSemStateFiniteExact width C F) (program : HolProg width)
    (relation : stateRelHOL jump bounds pointer source target)
    (lookup : sptLookup label source.code = some program) :
    sptLookup label target.code = some (comp jump bounds pointer program) ∧
      StackProps.regBound program pointer := by
  simp only [stateRelHOL] at relation
  have code := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact (code.1 label program lookup).symm

/-- Original231-241: full relation, original destination guard and successful source lookup prove compiled target lookup and register bound. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findCodeLemma {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (dest : Sum Nat Nat)
    (program : HolProg width)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      (match dest with | .inl _ => True | .inr register => register < pointer) ∧
      StackSemControl.findCode dest source.regs source.code = some program) :
    StackSemControl.findCode dest target.regs target.code =
      some (comp jump bounds pointer program) ∧ StackProps.regBound program pointer := by
  rcases hypothesis with ⟨relation, bound, lookup⟩
  cases dest with
  | inl label => exact codeLookup jump bounds pointer label source target program relation lookup
  | inr register =>
    have eq := RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, bound⟩
    change source.regs.lookup register = target.regs.lookup register at eq
    simp only [StackSemControl.findCode, ← eq] at lookup ⊢
    cases h : source.regs.lookup register with
    | none => simp [h] at lookup
    | some value =>
      cases value with
      | word word => simp [h] at lookup
      | loc label offset =>
        cases offset with
        | zero =>
          simp only [h] at lookup ⊢
          exact codeLookup jump bounds pointer label source target program relation lookup
        | succ offset => simp [h] at lookup

/-- Original243-255: identical successful lookup theorem after erasing any register from both maps; no alias, erasure-bound, or target-success premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findCodeLemmaErased {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (dest : Sum Nat Nat)
    (program : HolProg width) (erased : Nat)
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      (match dest with | .inl _ => True | .inr register => register < pointer) ∧
      StackSemControl.findCode dest (source.regs.eraseEq erased) source.code = some program) :
    StackSemControl.findCode dest (target.regs.eraseEq erased) target.code =
      some (comp jump bounds pointer program) ∧ StackProps.regBound program pointer := by
  rcases hypothesis with ⟨relation, bound, lookup⟩
  cases dest with
  | inl label => exact codeLookup jump bounds pointer label source target program relation lookup
  | inr register =>
    have eq := RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, bound⟩
    change source.regs.lookup register = target.regs.lookup register at eq
    have erasedEq : (source.regs.eraseEq erased).lookup register =
        (target.regs.eraseEq erased).lookup register := by
      simp only [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL, eq]
    simp only [StackSemControl.findCode, ← erasedEq] at lookup ⊢
    cases h : (source.regs.eraseEq erased).lookup register with
    | none =>
      simp only [h] at lookup
      simp at lookup
    | some value =>
      cases value with
      | word word =>
        simp only [h] at lookup
        simp at lookup
      | loc label offset =>
        cases offset with
        | zero =>
          simp only [h] at lookup ⊢
          exact codeLookup jump bounds pointer label source target program relation lookup
        | succ offset =>
          simp only [h] at lookup
          simp at lookup
end Flapjack.Compiler.Backend.StackRemove.FindCode
