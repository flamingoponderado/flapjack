import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Misc.Option.Rel
import Mathlib.Data.List.Forall2

/-! Generic value conditions for closure-language simulations. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Recognize ordinary and recursive closure values. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "isClos_def"]
def isClos : Value → Prop
  | .closure .. | .recclosure .. => True
  | _ => False

/-- A simple value relation preserves scalar payloads and block structure,
and relates a target closure only to a source closure. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_def"]
def simpleValRel (vr : Value → Value → Prop) : Prop :=
  (∀ x n, vr x (.number n) ↔ x = .number n) ∧
  (∀ x p n, vr x (.block n p) ↔ ∃ xs, x = .block n xs ∧ List.Forall₂ vr xs p) ∧
  (∀ x p, vr x (.word64 p) ↔ x = .word64 p) ∧
  (∀ x p, vr x (.byteVector p) ↔ x = .byteVector p) ∧
  (∀ x p b, vr x (.refPtr b p) ↔ x = .refPtr b p) ∧
  (∀ body arity env args loc x, vr x (.closure loc args env arity body) → isClos x) ∧
  (∀ index funs env args loc x, vr x (.recclosure loc args env funs index) → isClos x)

/-- The closure state's canonical finite maps roundtrip through lookup and
finite-support views. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Conditions on a state relation sufficient for primitive-operation
simulation. Source and target compiler types are independent. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_def"
  (fmap_as_finite_support := [refs, code])]
def simpleStateRel {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) : Prop :=
  (∀ s t ptr, t.refs.lookup ptr = none ∧ sr s t → s.refs.lookup ptr = none) ∧
  (∀ bytes t s ptr, t.refs.lookup ptr = some (.byteArray bytes) ∧ sr s t →
    s.refs.lookup ptr = some (.byteArray bytes)) ∧
  (∀ values t s ptr, t.refs.lookup ptr = some (.valueArray values) ∧ sr s t →
    ∃ left, s.refs.lookup ptr = some (.valueArray left) ∧ List.Forall₂ vr left values) ∧
  (∀ mode value t s ptr, t.refs.lookup ptr = some (.thunk mode value) ∧ sr s t →
    ∃ left, s.refs.lookup ptr = some (.thunk mode left) ∧ vr left value) ∧
  (∀ s t, sr s t → s.ffi = t.ffi ∧
    (∀ ptr, s.refs.lookup ptr ≠ none ↔ t.refs.lookup ptr ≠ none) ∧
    List.Forall₂ (optionRel vr) s.globals t.globals) ∧
  (∀ ffi s t, sr s t → sr { s with ffi := ffi } { t with ffi := ffi }) ∧
  (∀ bytes s t ptr, sr s t →
    sr { s with refs := s.refs.updateEq (ptr, .byteArray bytes) }
      { t with refs := t.refs.updateEq (ptr, .byteArray bytes) }) ∧
  (∀ s t ptr xs ys, sr s t ∧ List.Forall₂ vr xs ys →
    sr { s with refs := s.refs.updateEq (ptr, .valueArray xs) }
      { t with refs := t.refs.updateEq (ptr, .valueArray ys) }) ∧
  (∀ s t ptr mode v w, sr s t ∧ vr v w →
    sr { s with refs := s.refs.updateEq (ptr, .thunk mode v) }
      { t with refs := t.refs.updateEq (ptr, .thunk mode w) }) ∧
  (∀ s t xs ys, sr s t ∧ List.Forall₂ (optionRel vr) xs ys →
    sr { s with globals := xs } { t with globals := ys })

end Flapjack.Compiler.Backend.ClosProps
