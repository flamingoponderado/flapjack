import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Pancake.WordLang

/-! Exact StackSem expression evaluation and assignment prerequisites.
These definitions are proof-side ports; full evaluate and its production
refinement remain tracked separately by flapjack-y19g. -/
namespace Flapjack.StackSemExpressions

/-- Flapjack-specific re-export of the accepted canonical state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- HOL word_exp: only Word payloads enter arithmetic; Loc and missing
lookups fail. Every Op operand must succeed before word_op is applied.
The attach traversal supplies structural recursion evidence only. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def wordExp {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) :
    WordLangExpHOL (BitVec width) → Option (BitVec width)
  | .const w => some w
  | .var v =>
      match s.regs.lookup v with
      | some (.word w) => some w
      | _ => none
  | .lookup name =>
      match s.store.lookup name with
      | some (.word w) => some w
      | _ => none
  | .load addr =>
      match wordExp s addr with
      | some w =>
          match StackSemStateOps.memLoad w s with
          | some (.word value) => some value
          | _ => none
      | none => none
  | .op operator args =>
      let ws := args.attach.map fun ⟨e, _⟩ => wordExp s e
      if ws.all Option.isSome then
        wordOpHOL operator (ws.map (fun x => x.getD 0))
      else none
  | .shift sh e e1 =>
      match wordExp s e, wordExp s e1 with
      | some w, some w1 => wordShiftHOL sh w w1.toNat
      | _, _ => none

/-- HOL assign: failed expressions return NONE; successful values update
only the destination register through the reviewed set_var. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def assign {width : Nat} [NeZero width] {C F : Type}
    (reg : Nat) (exp : WordLangExpHOL (BitVec width))
    (s : StackSemStateFiniteExact width C F) : Option (StackSemStateFiniteExact width C F) :=
  match wordExp s exp with
  | none => none
  | some w => some (StackSemStateOps.setVar reg (.word w) s)

end Flapjack.StackSemExpressions
