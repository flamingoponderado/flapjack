module

public import Flapjack.Compiler.Backend.Semantics.BviSem.Install
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply
public import Flapjack.Misc.Sptree.Map
public import Flapjack.HolArb

@[expose] public section

/-! Source-shaped BVI primitive application. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem

/-- Construct the BVL state used by the source fallback dispatcher. The
unspecified fields come from one arbitrary BVL state, as in the source record
literal; code retains its source tree shape with arbitrary BVL payloads. This
remains untagged until both state-carrier map translations are qualified. -/
noncomputable def toBvl {C F : Type} (s : BviState C F) : BvlSem.State C F :=
  let config := (s.compileOracle 0).1
  let arbitraryCode : Nat × Bvl.Exp := @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, .var 0)⟩
  let seed : BvlSem.State C F :=
    ⟨[], s.refs, 0, (fun _ _ => none), (fun _ => (config, [])), .ln, s.ffi⟩
  let arbitrary := @Flapjack.holArb (BvlSem.State C F) ⟨seed⟩
  ⟨arbitrary.globals, s.refs, s.clock, arbitrary.compile, arbitrary.compileOracle,
    sptMap (fun _ => arbitraryCode) s.code, s.ffi⟩

/-- Construct the same fallback state over explicit lookup views. The
arbitrary fields and code-tree payload follow the original record construction. -/
noncomputable def broadToBvl {C F : Type} (s : BviStateBroad C F) : BvlSem.StateBroad C F :=
  let config := (s.compileOracle 0).1
  let arbitraryCode : Nat × Bvl.Exp := @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, .var 0)⟩
  let seed : BvlSem.State C F :=
    ⟨[], ⟨s.refs, s.refsFiniteSupport⟩, 0, (fun _ _ => none),
      (fun _ => (config, [])), .ln, s.ffi⟩
  let arbitrary := @Flapjack.holArb (BvlSem.State C F) ⟨seed⟩
  ⟨arbitrary.globals, s.refs, s.refsFiniteSupport, s.clock,
    arbitrary.compile, arbitrary.compileOracle, sptMap (fun _ => arbitraryCode) s.code, s.ffi⟩

/-- Fallback-state construction commutes with exposing reference lookups. -/
theorem holFmapAsFiniteSupportConversionWitness_toBvl {C F : Type} (s : BviState C F) :
    (toBvl s).toBroad = broadToBvl s.toBroad := by
  cases s
  rfl

/-- Copying the shared fields back from the fallback input leaves the BVI
state unchanged. This is Flapjack infrastructure for dispatcher proofs. -/
theorem fromBvl_toBvl {C F : Type} (s : BviState C F) : fromBvl (toBvl s) s = s := by
  cases s
  rfl

/-- Dispatch a non-install operation through the BVI-specific cases or BVL
fallback. This is Flapjack infrastructure for the source dispatcher. -/
noncomputable def doAppFallback {C F : Type} (op : ClosLang.Op) (args : List Value) (s : BviState C F) :
    Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) ExnOrRet :=
  match doAppAux op args s with
    | none => .err (.abort .typeError)
    | some (some pair) => .val pair
    | some none => match BvlSem.doApp op args (toBvl s) with
      | .val (value, next) => .val (value, fromBvl next s)
      | .err (.abort error) => .err (.abort error)
      | .err (.raise value) => .err (.raise (.exn value))

namespace ApplyCarrier
/-- The BVI reference carrier and its finite-support view roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end ApplyCarrier

/-- The complete BVI primitive dispatcher. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "do_app_def"
  (fmap_as_finite_support := [refs])]
noncomputable def doApp {C F : Type} (op : ClosLang.Op) (args : List Value) (s : BviState C F) :
    Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) ExnOrRet :=
  match op with
  | .install => doInstall args s
  | _ => doAppFallback op args s


namespace ConversionReview

/-- The BVI reference carrier and its explicit finite-support view roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness

/-- The BVL reference carrier and its explicit finite-support view roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- The complete BVL-to-BVI state update, including the retained target fields. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "bvl_to_bvi_def"
  (fmap_as_finite_support_relation := [BvlSem.State.refs, BviState.refs])]
theorem fromBvl_def {C F : Type} (s : BvlSem.State C F) (t : BviState C F) :
    fromBvl s t = { t with refs := s.refs, clock := s.clock, ffi := s.ffi } := by rfl

/-- The complete BVI-to-BVL state, including arbitrary unspecified fields and code values. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "bvi_to_bvl_def"
  (fmap_as_finite_support_relation := [BviState.refs, BvlSem.State.refs])]
theorem toBvl_def {C F : Type} (s : BviState C F) :
    (toBvl s : BvlSem.State C F) =
      let arbitraryCode : Nat × Bvl.Exp := @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, .var 0)⟩
      let seed : BvlSem.State C F :=
        ⟨[], s.refs, 0, (fun _ _ => none), (fun _ => ((s.compileOracle 0).1, [])), .ln, s.ffi⟩
      let arbitrary : BvlSem.State C F := @Flapjack.holArb (BvlSem.State C F) ⟨seed⟩
      { arbitrary with refs := s.refs, clock := s.clock, code := sptMap (fun _ => arbitraryCode) s.code, ffi := s.ffi } := by rfl

end ConversionReview

end Flapjack.Compiler.Backend.BviSem
