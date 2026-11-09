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

/-- The complete BVI primitive dispatcher. This follows `do_app_def` but is
untagged until the two state-carrier representations and the delegated
primitive correspondence have been reviewed together. -/
noncomputable def doApp {C F : Type} (op : ClosLang.Op) (args : List Value) (s : BviState C F) :
    Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) ExnOrRet :=
  match op with
  | .install => doInstall args s
  | _ => doAppFallback op args s

end Flapjack.Compiler.Backend.BviSem
