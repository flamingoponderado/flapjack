import Flapjack.RiscV.L3.Types
import Flapjack.Misc.Option
import Flapjack.Misc.Alignment

/-! Flapjack library-rendering infrastructure required by the complete L3 FP
section. These helpers implement UPDATE and the guarded in-range word operations
used by the original equations. ARB remains an uninterpreted inhabitant; no
arbitrary record field is replaced with a chosen default. General model
renderings outside this section are deliberately absent. -/
namespace Flapjack.RiscV.L3
open Flapjack.Basis.Pure.MlString

/-- HOL `ARB : α`, an uninterpreted constant (the inhabitedness every HOL type has). -/
opaque holArb (α : Type) [Inhabited α] : α

/-- HOL `combin$UPDATE a b f` (`(a =+ b) f`). -/
def holUpdate {α β : Type} [DecidableEq α] (a : α) (b : β) (f : α → β) : α → β :=
  fun c => if a = c then b else f c

/-- HOL `words$word_extract h l w : 'b word` at result width `b`. -/
def holWordExtract (b : Nat) {a : Nat} (h l : Nat) (w : BitVec a) : BitVec b :=
  BitVec.setWidth b (BitVec.ofNat a ((w.toNat >>> l) % 2 ^ (min h (a - 1) + 1 - l)))

/-- Rendering of HOL `words$bit_field_insert h l a w` for calls whose selected
input indices are in range (`h < l` or `h - l < m`). The translator checks this
bound at every model call. Raw HOL FCP indexing is unspecified outside the
input width; this helper's false result there is not an unconditional HOL port. -/
def holBitFieldInsert {m n : Nat} (h l : Nat) (a : BitVec m) (w : BitVec n) : BitVec n :=
  Flapjack.holFcpWord fun i => if l ≤ i ∧ i ≤ h then a.getLsbD (i - l) else w.getLsbD i


end Flapjack.RiscV.L3
