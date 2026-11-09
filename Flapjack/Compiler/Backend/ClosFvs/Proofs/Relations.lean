module

public import Flapjack.Misc.Option.Rel
public import Flapjack.Compiler.Backend.ClosFvs.Source
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Compiler.Backend.BackendProps.Pure
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Source relations for closure free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

/-- Target code is the source list with free variables removed. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "code_rel_def"]
def CodeRel (bound : Nat) (source target : List ClosLang.Exp) : Prop :=
  target = removeList bound source

/-- Related recursive function bodies retain their arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "f_rel_def"]
def FunctionRel (bound : Nat) (source target : Nat × ClosLang.Exp) : Prop :=
  source.1 = target.1 ∧ CodeRel (source.1 + bound) [source.2] [target.2]

/-- Related closure values retain their data and transform closure bodies. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "v_rel"]
inductive ValueRel : Value → Value → Prop where
  | number (value : Int) : ValueRel (.number value) (.number value)
  | word64 (value : BitVec 64) : ValueRel (.word64 value) (.word64 value)
  | byteVector (bytes : List (BitVec 8)) : ValueRel (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) : ValueRel (.refPtr flag address) (.refPtr flag address)
  | block (tag : Nat) (source target : List Value) :
      List.Forall₂ ValueRel source target → ValueRel (.block tag source) (.block tag target)
  | closure (location : Option Nat) (args nextArgs env nextEnv : List Value)
      (arity : Nat) (body nextBody : ClosLang.Exp) :
      List.Forall₂ ValueRel env nextEnv → List.Forall₂ ValueRel args nextArgs →
      CodeRel (env.length + arity) [body] [nextBody] →
      ValueRel (.closure location args env arity body) (.closure location nextArgs nextEnv arity nextBody)
  | recclosure (location : Option Nat) (args nextArgs env nextEnv : List Value)
      (functions nextFunctions : List (Nat × ClosLang.Exp)) (index : Nat) :
      List.Forall₂ ValueRel env nextEnv → List.Forall₂ ValueRel args nextArgs →
      List.Forall₂ (FunctionRel (env.length + functions.length)) functions nextFunctions →
      ValueRel (.recclosure location args env functions index)
        (.recclosure location nextArgs nextEnv nextFunctions index)

/-- Reference payloads retain their kind while values remain related. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "ref_rel"]
inductive RefRel : Ref Value → Ref Value → Prop where
  | byteArray (bytes : List (BitVec 8)) : RefRel (.byteArray bytes) (.byteArray bytes)
  | valueArray (source target : List Value) :
      List.Forall₂ ValueRel source target → RefRel (.valueArray source) (.valueArray target)
  | thunk (mode : Flapjack.AstHOL.ThunkMode) (source target : Value) :
      ValueRel source target → RefRel (.thunk mode source) (.thunk mode target)

namespace StatePort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end StatePort

/-- States related across free-variable removal. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
def StateRel {C F : Type} (source target : State C F) : Prop :=
  (∀ n, (source.compileOracle n).2.2 = []) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty ∧
  target.maxApp = source.maxApp ∧ 1 ≤ source.maxApp ∧ target.clock = source.clock ∧
  target.ffi = source.ffi ∧ List.Forall₂ (optionRel ValueRel) source.globals target.globals ∧
  (∀ key, optionRel RefRel (source.refs.lookup key) (target.refs.lookup key)) ∧
  source.compile = pureCc compileInc target.compile ∧
  target.compileOracle = pureCo compileInc ∘ source.compileOracle

end Flapjack.Compiler.Backend.ClosFvs
