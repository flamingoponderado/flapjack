import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

/-! Source cases of flat primitive application. These cases do not establish
correspondence for the source-operation cases of the dispatcher. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL

/-- Global allocation accepts no arguments and appends empty slots. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_globalAlloc_source {C F : Type} (s : State C F) (n : Nat) (vs : List Value) :
    doApp s (.globalVarAlloc n) vs =
      match vs with
      | [] => some ({ s with globals := s.globals ++ List.replicate n none }, .val unitValue)
      | _ => none := by
  cases vs <;> rfl

/-- Global initialization accepts one value and an in-range empty slot.
Optional indexing expresses the source bound and empty-slot test together. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_globalInit_source {C F : Type} (s : State C F) (n : Nat) (vs : List Value) :
    doApp s (.globalVarInit n) vs =
      match vs, s.globals[n]? with
      | [v], some none => some ({ s with globals := s.globals.set n (some v) }, .val unitValue)
      | _, _ => none := by
  cases vs <;> rfl

/-- Global lookup accepts no arguments and an in-range populated slot. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_globalLookup_source {C F : Type} (s : State C F) (n : Nat) (vs : List Value) :
    doApp s (.globalVarLookup n) vs =
      match vs, s.globals[n]? with
      | [], some (some v) => some (s, .val v)
      | _, _ => none := by
  cases vs <;> rfl

/-- The tag-and-length operation accepts one named constructor. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_tagLenEq_source {C F : Type} (s : State C F) (n len : Nat) (vs : List Value) :
    doApp s (.tagLenEq n len) vs =
      match vs with
      | [.conv (some (tag, _)) xs] => some (s, .val (boolValue (tag == n && xs.length == len)))
      | _ => none := by
  cases vs <;> rfl

/-- The length operation accepts one constructor, including tuples. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_lenEq_source {C F : Type} (s : State C F) (len : Nat) (vs : List Value) :
    doApp s (.lenEq len) vs =
      match vs with
      | [.conv _ xs] => some (s, .val (boolValue (xs.length == len)))
      | _ => none := by
  cases vs <;> rfl

/-- Field access checks constructor bounds or reads reference field zero. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_el_source {C F : Type} (s : State C F) (n : Nat) (vs : List Value) :
    doApp s (.el n) vs =
      match vs with
      | [.conv _ fields] => (fields[n]?).map fun v => (s, .val v)
      | [.loc _ p] => if n ≠ 0 then none else
          match storeLookup p s.refs with
          | some (.refv v) => some (s, .val v)
          | _ => none
      | _ => none := by
  cases vs <;> simp only [doApp, doAppFlat, Option.getD]
  split <;> simp_all <;> rfl

/-- Identity accepts exactly one argument. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_id_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s .id vs = match vs with | [v] => some (s, .val v) | _ => none := by
  cases vs <;> rfl

end Flapjack.Compiler.Backend.FlatSem
