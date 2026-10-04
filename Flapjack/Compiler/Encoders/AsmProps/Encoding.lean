import Flapjack.Compiler.Encoders.AsmProps.Target

namespace Flapjack
open Flapjack.Compiler.Encoders.Asm

/-- HOL offset-length monotonicity predicate (asmPropsScript.sml:19-24). Encoding payload and offset word dimension are
independent of the instruction dimension. Word comparisons are signed, as in HOL. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def offsetMonotonic {width : Nat} {offsetWidth : Nat} [NeZero width] [NeZero offsetWidth]
    {byte : Type} (enc : HolAsm width → List byte) (config : AsmConfigExact width)
    (a1 a2 : BitVec offsetWidth) (i1 i2 : HolAsm width) : Prop :=
  asmOkExact i1 config = true ∧ asmOkExact i2 config = true →
    (BitVec.sle 0 a1 = true ∧ BitVec.sle 0 a2 = true ∧ BitVec.sle a1 a2 = true →
      (enc i1).length ≤ (enc i2).length) ∧
    (BitVec.slt a1 0 = true ∧ BitVec.slt a2 0 = true ∧ BitVec.sle a2 a1 = true →
      (enc i1).length ≤ (enc i2).length)

/-- HOL encoder well-formedness predicate (asmPropsScript.sml:27-41).
All alignment, nonempty output, and four offset-length implications are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def encOk {width : Nat} [NeZero width] (config : AsmConfigExact width) : Prop :=
  2 ^ config.codeAlignment = (config.encode (.inst .skip)).length ∧
    (∀ instruction, (config.encode instruction).length % 2 ^ config.codeAlignment = 0 ∧
      (config.encode instruction).length ≠ 0) ∧
    (∀ w1 w2, offsetMonotonic config.encode config w1 w2 (.jump w1) (.jump w2)) ∧
    (∀ cmp reg ri w1 w2, offsetMonotonic config.encode config w1 w2
      (.jumpCmp cmp reg ri w1) (.jumpCmp cmp reg ri w2)) ∧
    (∀ w1 w2, offsetMonotonic config.encode config w1 w2 (.call w1) (.call w2)) ∧
    (∀ w1 w2 reg, offsetMonotonic config.encode config w1 w2 (.loc reg w1) (.loc reg w2))

/-- HOL target projection consistency predicate (asmPropsScript.sml:65-73).
HOL equality between truth values is expressed as iff between propositions;
state-ok, PC, and domain-byte equalities retain their separate conjuncts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def targetOk {width : Nat} [NeZero width] {state projection : Type}
    (target : HolAsmTarget width state projection) : Prop :=
  encOk target.config ∧ ∀ (ms1 ms2 : state) (s : AsmState width),
    target.proj s.memDomain ms1 = target.proj s.memDomain ms2 →
      (targetStateRel target s ms1 ↔ targetStateRel target s ms2) ∧
      target.stateOk ms1 = target.stateOk ms2 ∧
      target.getPc ms1 = target.getPc ms2 ∧
      (∀ address, s.memDomain address → target.getByte ms1 address = target.getByte ms2 address)

end Flapjack
