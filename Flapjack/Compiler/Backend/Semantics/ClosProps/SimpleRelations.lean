module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.FiniteMap.DomExact
public import Flapjack.Misc.ListEl
public import Flapjack.Misc.Option.Rel
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Generic value conditions for closure-language simulations. -/
namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- Recognize ordinary and recursive closure values. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "isClos_def"]
def isClos : Value → Prop
  | .closure .. | .recclosure .. => True
  | _ => False

/-- Recognize closure values under the source's `is_closure` spelling, which
repeats the same three clauses as its own definition. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "is_closure_def"]
def isClosureValue : Value → Prop
  | .closure .. => True
  | .recclosure .. => True
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

/-- Related nonempty lists have related HOL last values. Flapjack
infrastructure shared by the closure-simulation continuations; no separate
HOL declaration is claimed. -/
theorem forall₂_holLast {R : Value → Value → Prop} {left right : List Value}
    (related : List.Forall₂ R left right) (nonempty : left ≠ []) :
    R (@Flapjack.holLast Value ⟨unitValue⟩ left) (@Flapjack.holLast Value ⟨unitValue⟩ right) := by
  induction related with
  | nil => exact (nonempty rfl).elim
  | @cons first nextFirst rest nextRest head tail ih =>
    cases tail with
    | nil => simpa [Flapjack.holLast] using head
    | @cons second nextSecond tail nextTail nextHead restRel =>
      simp only [Flapjack.holLast]
      exact ih (by simp)

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

/-- Closure recognition is exactly the two closure constructors. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "isClos_cases"]
theorem isClos_cases (x : Value) :
    isClos x ↔
      (∃ loc args env arity body, x = .closure loc args env arity body) ∨
        ∃ loc args env funs index, x = .recclosure loc args env funs index := by
  cases x
  all_goals simp [isClos]

/-- The simple state relation keeps the FFI state identical. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_ffi"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel_ffi {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (h : simpleStateRel vr sr ∧ sr s t) : s.ffi = t.ffi := by
  obtain ⟨rel, related⟩ := h
  exact (rel.2.2.2.2.1 s t related).1

/-- The simple state relation keeps the reference-map domains equal. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_fdom"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel_fdom {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (h : simpleStateRel vr sr ∧ sr s t) : s.refs.dom = t.refs.dom := by
  obtain ⟨rel, related⟩ := h
  have pointwise := (rel.2.2.2.2.1 s t related).2.1
  ext ptr
  simp only [HolFiniteMapExact.dom]
  exact pointwise ptr

/-- The simple state relation is preserved by a matching FFI-state update. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_update_ffi"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel_update_ffi {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (f : HolFfiState F) (h : simpleStateRel vr sr ∧ sr s t) :
    sr { s with ffi := f } { t with ffi := f } := by
  obtain ⟨rel, related⟩ := h
  exact rel.2.2.2.2.2.1 f s t related

/-- The simple state relation is preserved by equal byte-array updates. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_update_bytes"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel_update_bytes {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (ptr : Nat) (bytes : List (BitVec 8)) (h : simpleStateRel vr sr ∧ sr s t) :
    sr { s with refs := s.refs.updateEq (ptr, .byteArray bytes) }
      { t with refs := t.refs.updateEq (ptr, .byteArray bytes) } := by
  obtain ⟨rel, related⟩ := h
  exact rel.2.2.2.2.2.2.1 bytes s t ptr related

/-- The simple state relation is preserved by related value-array updates. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_update_values"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel_update_values {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (xs ys : List Value) (ptr : Nat)
    (h : simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ vr xs ys) :
    sr { s with refs := s.refs.updateEq (ptr, .valueArray xs) }
      { t with refs := t.refs.updateEq (ptr, .valueArray ys) } := by
  obtain ⟨rel, related, fields⟩ := h
  exact rel.2.2.2.2.2.2.2.1 s t ptr xs ys ⟨related, fields⟩

/-- The simple state relation is preserved by related thunk updates. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_update_thunks"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel_update_thunks {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (v w : Value) (ptr : Nat) (mode : Flapjack.AstHOL.ThunkMode)
    (h : simpleStateRel vr sr ∧ sr s t ∧ vr v w) :
    sr { s with refs := s.refs.updateEq (ptr, .thunk mode v) }
      { t with refs := t.refs.updateEq (ptr, .thunk mode w) } := by
  obtain ⟨rel, related, values⟩ := h
  exact rel.2.2.2.2.2.2.2.2.1 s t ptr mode v w ⟨related, values⟩

/-- The simple state relation is preserved by related global-list updates. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_update_globals"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel_update_globals {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (xs ys : List (Option Value))
    (h : simpleStateRel vr sr ∧ sr s t ∧ List.Forall₂ (optionRel vr) xs ys) :
    sr { s with globals := xs } { t with globals := ys } := by
  obtain ⟨rel, related, globals⟩ := h
  exact rel.2.2.2.2.2.2.2.2.2 s t xs ys ⟨related, globals⟩

/-- A target reference lookup is matched by the related source state. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_state_rel_FLOOKUP_refs_IMP"
  (fmap_as_finite_support := [refs, code])]
theorem simpleStateRel_lookup_refs {C D F : Type} (vr : Value → Value → Prop)
    (sr : State C F → State D F → Prop) (s : State C F) (t : State D F)
    (p : Nat) (x : Option (Ref Value))
    (h : simpleStateRel vr sr ∧ sr s t ∧ t.refs.lookup p = x) :
    (match x with
     | none => s.refs.lookup p = none
     | some (.valueArray vs) =>
       ∃ xs, s.refs.lookup p = some (.valueArray xs) ∧ List.Forall₂ vr xs vs
     | some (.byteArray bs) => s.refs.lookup p = some (.byteArray bs)
     | some (.thunk m w) => ∃ v, s.refs.lookup p = some (.thunk m v) ∧ vr v w) := by
  obtain ⟨rel, related, target⟩ := h
  cases x with
  | none => exact rel.1 s t p ⟨target, related⟩
  | some ref =>
    cases ref with
    | valueArray vs => exact rel.2.2.1 vs t s p ⟨target, related⟩
    | byteArray bs => exact rel.2.1 bs t s p ⟨target, related⟩
    | thunk m w => exact rel.2.2.2.1 m w t s p ⟨target, related⟩

/-- A Boolean value relates only to itself under a simple value relation. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "simple_val_rel_Boolv"]
theorem simpleValRel_Boolv (vr : Value → Value → Prop) (b : Bool) (v1 : Value)
    (simple : simpleValRel vr) :
    (vr (boolValue b) v1 → v1 = boolValue b) ∧
      (vr v1 (boolValue b) → v1 = boolValue b) := by
  constructor
  · intro h
    cases v1 with
    | number n =>
      exact absurd ((simple.1 (boolValue b) n).mp h) (by simp [boolValue])
    | block n p =>
      obtain ⟨xs, eq, rel⟩ := (simple.2.1 (boolValue b) p n).mp h
      have inj := eq
      simp only [boolValue, Value.block.injEq] at inj
      obtain ⟨hn, hx⟩ := inj
      cases hx
      have hp : p = [] := List.forall₂_nil_left_iff.mp rel
      cases hp
      simp [boolValue, hn]
    | word64 w =>
      exact absurd ((simple.2.2.1 (boolValue b) w).mp h) (by simp [boolValue])
    | byteVector bs =>
      exact absurd ((simple.2.2.2.1 (boolValue b) bs).mp h) (by simp [boolValue])
    | refPtr bb p =>
      exact absurd ((simple.2.2.2.2.1 (boolValue b) p bb).mp h) (by simp [boolValue])
    | closure loc args env arity body =>
      exact absurd (simple.2.2.2.2.2.1 body arity env args loc (boolValue b) h)
        (by simp [boolValue, isClos])
    | recclosure loc args env funs index =>
      exact absurd (simple.2.2.2.2.2.2 index funs env args loc (boolValue b) h)
        (by simp [boolValue, isClos])
  · intro h
    obtain ⟨xs, eq, rel⟩ :=
      (simple.2.1 v1 [] (if b then BackendCommon.trueTag else BackendCommon.falseTag)).mp h
    have hx : xs = [] := List.forall₂_nil_right_iff.mp rel
    cases hx
    simpa [boolValue] using eq

end Flapjack.Compiler.Backend.ClosProps
