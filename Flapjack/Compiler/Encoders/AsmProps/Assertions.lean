import Flapjack.HolRef

/-! Generic ASM encoder assertion iterations. The intermediate carrier of
`asserts2` is independent of its initial/iterated state carrier. -/
namespace Flapjack.Compiler.Encoders.AsmProps

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asserts_def"]
def asserts {α : Type} : Nat → (Nat → α → α) → α → (α → Prop) → (α → Prop) → Prop
  | 0, next, s, _, Q => Q (next 0 s)
  | n + 1, next, s, P, Q => P (next (n + 1) s) ∧ asserts n next (next (n + 1) s) P Q

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asserts2_def"]
def asserts2 {α β : Type} : Nat → (Nat → β → α) → (α → β) → α → (α → β → Prop) → Prop
  | 0, _, _, _, _ => True
  | n + 1, fi, fc, s, P => P s (fc s) ∧ asserts2 n fi fc (fi (n + 1) (fc s)) P

end Flapjack.Compiler.Encoders.AsmProps
