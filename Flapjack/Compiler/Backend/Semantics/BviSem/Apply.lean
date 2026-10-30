import Flapjack.Compiler.Backend.Semantics.BviSem.Install
import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply
import Flapjack.Misc.Sptree.Map
import Flapjack.HolArb

/-! Source-shaped BVI primitive application. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem

/-- Construct the BVL state used by the source fallback dispatcher. Fields
not provided by the source record are HOL arbitrary values; the code tree
retains its source shape and replaces each payload with the same arbitrary
BVL payload. Untagged until the two state-carrier map translations are
qualified together. -/
noncomputable def toBvl {C F : Type} (s : BviState C F) : BvlSem.State C F :=
  let config := (s.compileOracle 0).1
  let arbitraryCode : Nat × Bvl.Exp := @Flapjack.holArb (Nat × Bvl.Exp) ⟨(0, .var 0)⟩
  let arbitraryCompiler : BvlSem.Compiler C :=
    @Flapjack.holArb (BvlSem.Compiler C) ⟨fun _ _ => none⟩
  let arbitraryOracle : BvlSem.CompileOracle C :=
    @Flapjack.holArb (BvlSem.CompileOracle C) ⟨fun _ => (config, [])⟩
  ⟨@Flapjack.holArb (List (Option Value)) ⟨[]⟩, s.refs, s.clock,
    arbitraryCompiler, arbitraryOracle, sptMap (fun _ => arbitraryCode) s.code, s.ffi⟩

/-- Copying the shared fields back from the fallback input leaves the BVI
state unchanged. This is Flapjack infrastructure for dispatcher proofs. -/
theorem fromBvl_toBvl {C F : Type} (s : BviState C F) : fromBvl (toBvl s) s = s := by
  cases s
  rfl

/-- The complete BVI primitive dispatcher. This follows `do_app_def` but is
untagged until the two state-carrier representations and the delegated
primitive correspondence have been reviewed together. -/
noncomputable def doApp {C F : Type} (op : ClosLang.Op) (args : List Value) (s : BviState C F) :
    Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) ExnOrRet :=
  match op with
  | .install => doInstall args s
  | _ => match doAppAux op args s with
    | none => .err (.abort .typeError)
    | some (some pair) => .val pair
    | some none => match BvlSem.doApp op args (toBvl s) with
      | .val (value, next) => .val (value, fromBvl next s)
      | .err (.abort error) => .err (.abort error)
      | .err (.raise value) => .err (.raise (.exn value))

end Flapjack.Compiler.Backend.BviSem
