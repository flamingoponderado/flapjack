import Flapjack.Compiler.Encoders.AsmProps.Encoding

namespace Flapjack.Test
open Flapjack.Compiler.Encoders.Asm

-- Independent instruction/offset dimensions and arbitrary encoding payload.
example {width offsetWidth : Nat} [NeZero width] [NeZero offsetWidth]
    {byte : Type} (enc : HolAsm width → List byte) (c : AsmConfigExact width)
    (a1 a2 : BitVec offsetWidth) (i1 i2 : HolAsm width) :
    offsetMonotonic enc c a1 a2 i1 i2 ↔
      (asmOkExact i1 c = true ∧ asmOkExact i2 c = true →
        (BitVec.sle 0 a1 = true ∧ BitVec.sle 0 a2 = true ∧ BitVec.sle a1 a2 = true →
          (enc i1).length ≤ (enc i2).length) ∧
        (BitVec.slt a1 0 = true ∧ BitVec.slt a2 0 = true ∧ BitVec.sle a2 a1 = true →
          (enc i1).length ≤ (enc i2).length)) := Iff.rfl

-- Original HOL oracle signed_offsets_1.
example : BitVec.sle (0 : BitVec 1) 0 = true ∧
    BitVec.sle (0 : BitVec 1) 1 = false ∧
    BitVec.slt (1 : BitVec 1) 0 = true ∧
    BitVec.sle (1 : BitVec 1) 1 = true := by decide

-- Original HOL oracle signed_offsets_2.
example : BitVec.sle (0 : BitVec 2) 1 = true ∧
    BitVec.sle (0 : BitVec 2) 2 = false ∧
    BitVec.slt (2 : BitVec 2) 0 = true ∧
    BitVec.sle (2 : BitVec 2) 3 = true := by decide

-- Original HOL oracle signed_offsets_8.
example : BitVec.sle (0 : BitVec 8) 127 = true ∧
    BitVec.sle (0 : BitVec 8) 128 = false ∧
    BitVec.slt (128 : BitVec 8) 0 = true ∧
    BitVec.sle (128 : BitVec 8) 255 = true := by decide

-- Original HOL oracle signed_offsets_32.
example : BitVec.sle (0 : BitVec 32) 2147483647 = true ∧
    BitVec.sle (0 : BitVec 32) 2147483648 = false ∧
    BitVec.slt (2147483648 : BitVec 32) 0 = true ∧
    BitVec.sle (2147483648 : BitVec 32) 4294967295 = true := by decide

-- Original HOL oracle signed_offsets_64.
example : BitVec.sle (0 : BitVec 64) 9223372036854775807 = true ∧
    BitVec.sle (0 : BitVec 64) 9223372036854775808 = false ∧
    BitVec.slt (9223372036854775808 : BitVec 64) 0 = true ∧
    BitVec.sle (9223372036854775808 : BitVec 64) 18446744073709551615 = true := by decide

-- Original HOL oracle signed_offsets_80.
example : BitVec.sle (0 : BitVec 80) 604462909807314587353087 = true ∧
    BitVec.sle (0 : BitVec 80) 604462909807314587353088 = false ∧
    BitVec.slt (604462909807314587353088 : BitVec 80) 0 = true ∧
    BitVec.sle (604462909807314587353088 : BitVec 80) 1208925819614629174706175 = true := by decide

example {w o : Nat} [NeZero w] [NeZero o] (c : AsmConfigExact w)
    (a1 a2 : BitVec o) (i1 i2 : HolAsm w) :
    offsetMonotonic (fun _ => [true, false]) c a1 a2 i1 i2 := by
  simp [offsetMonotonic]

example {w : Nat} [NeZero w] (c : AsmConfigExact w) :
    encOk {c with encode := fun _ => [0], codeAlignment := 0} := by
  simp [encOk, offsetMonotonic]

example {w : Nat} [NeZero w] (c : AsmConfigExact w) :
    ¬ encOk {c with encode := fun _ => []} := by
  simp [encOk]

example {w : Nat} [NeZero w] (c : AsmConfigExact w) :
    ¬ encOk {c with encode := fun _ => [0], codeAlignment := 1} := by
  simp [encOk]

-- Full projection implication retains every separate HOL conjunct.
example {w : Nat} [NeZero w] {S P : Type} (t : HolAsmTarget w S P) :
    targetOk t ↔ encOk t.config ∧ ∀ (ms1 ms2 : S) (s : AsmState w),
      t.proj s.memDomain ms1 = t.proj s.memDomain ms2 →
        (targetStateRel t s ms1 ↔ targetStateRel t s ms2) ∧
        t.stateOk ms1 = t.stateOk ms2 ∧ t.getPc ms1 = t.getPc ms2 ∧
        (∀ a, s.memDomain a → t.getByte ms1 a = t.getByte ms2 a) := Iff.rfl

end Flapjack.Test
