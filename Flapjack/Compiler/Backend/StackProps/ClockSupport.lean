import Flapjack.Compiler.Backend.StackProps.StateConstants
import Flapjack.Compiler.Backend.Semantics.StackSem.Control

/-! Full original StackProps clock-proof prerequisites. No evaluator or
instruction callback is introduced. The word/configuration/FFI parameters of
unrelated states and the product-map carriers retain source polymorphism. -/
namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.StackSemStateOps Flapjack.StackSemControl

namespace ClockSupport
/-- Canonical imported state codec witness; qualifier infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end ClockSupport

/-- All nineteen source conjuncts. The unrelated s and z states have
independent word/configuration/FFI carriers, not a shared instantiation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem decClockConst {width otherWidth : Nat} [NeZero width] [NeZero otherWidth]
    {C F OtherC OtherF : Type} (s : StackSemStateFiniteExact width C F)
    (z : StackSemStateFiniteExact otherWidth OtherC OtherF) :
    (decClock s).ffi = s.ffi ∧
   (decClock z).useAlloc = z.useAlloc ∧
   (decClock z).useStore = z.useStore ∧
   (decClock z).useStack = z.useStack ∧
   (decClock z).stack = z.stack ∧
   (decClock z).store = z.store ∧
   (decClock z).code = z.code ∧
   (decClock z).dataBuffer = z.dataBuffer ∧
   (decClock z).codeBuffer = z.codeBuffer ∧
   (decClock z).fpRegs = z.fpRegs ∧
   (decClock z).be = z.be ∧
   (decClock z).gcFun = z.gcFun ∧
   (decClock z).memory = z.memory ∧
   (decClock z).mdomain = z.mdomain ∧
   (decClock z).shMdomain = z.shMdomain ∧
   (decClock z).bitmaps = z.bitmaps ∧
   (decClock z).stackSpace = z.stackSpace ∧
   (decClock z).compile = z.compile ∧
   (decClock z).compileOracle = z.compileOracle := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Full polymorphic pair-map iff, with four independent source types. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "pair_map_eq"]
theorem pairMapEq {A B X Y : Type} (f : A → X) (g : B → Y)
    (p : A × B) (x : X) (y : Y) :
    (f p.1, g p.2) = (x, y) ↔ ∃ q r, p = (q, r) ∧ x = f q ∧ y = g r := by
  rcases p with ⟨a, b⟩
  constructor
  · intro h
    cases h
    exact ⟨a, b, rfl, rfl, rfl⟩
  · rintro ⟨q, r, hp, hx, hy⟩
    cases hp
    subst x
    subst y
    rfl

/-- The original disjunction uses one shared existential label. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "bad_fun_return_IMP"
  (words_as_type_indexed_bitvec)]
theorem badFunReturnImp {width : Nat} [NeZero width]
    (res : Option (StackSemResult width)) (h : badFunReturn res = true) :
    res = none ∨ ∃ n, res = some (.break n) ∨ res = some (.continue n) := by
  cases res with
  | none => exact Or.inl rfl
  | some result =>
    cases result <;> simp_all [badFunReturn]

/-- Only normal completion and Continue zero permit loop reentry. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "cont_loop_IMP"
  (words_as_type_indexed_bitvec)]
theorem contLoopImp {width : Nat} [NeZero width]
    (res : Option (StackSemResult width)) (h : contLoop res = true) :
    res = none ∨ res = some (.continue 0) := by
  cases res with
  | none => exact Or.inl rfl
  | some result =>
    cases result <;> simp_all [contLoop]

/-- Full source clock-update projection statement over the imported state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem withClockFfi {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (k : Nat) :
    ({ s with clock := k } : StackSemStateFiniteExact width C F).ffi = s.ffi := rfl

/-- Full original predicate. The source program parameter indexes words in
asm instruction/immediate/address fields; the positive-width native carrier
retains that dependency even though this predicate ignores those payloads.
Only Seq/If recurse; Skip, Inst, LocValue and Halt are neutral. Every other
constructor, including Loop and Call, is false. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def clockNeutralHOL {width : Nat} [NeZero width] :
    Flapjack.Compiler.Backend.StackLang.HolProg width → Prop
  | .seq first second => clockNeutralHOL first ∧ clockNeutralHOL second
  | .locValue _ _ _ | .halt _ | .inst _ | .skip => True
  | .ite _ _ _ first second => clockNeutralHOL first ∧ clockNeutralHOL second
  | _ => False

end Flapjack.Compiler.Backend.StackProps
