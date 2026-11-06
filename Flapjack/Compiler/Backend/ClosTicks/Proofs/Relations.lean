import Flapjack.Compiler.Backend.ClosTicks.Proofs.Production
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Relations

/-! Relations used by the closure tick-removal simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

/-- Target code removes the source ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "code_rel_def"]
def CodeRel (source target : List ClosLang.Exp) : Prop := target = removeList source

/-- Related recursive function bodies retain their arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "f_rel_def"]
def FunctionRel {α : Type} (source target : α × ClosLang.Exp) : Prop :=
  source.1 = target.1 ∧ CodeRel [source.2] [target.2]

/-- Related values preserve their payloads and remove ticks from closure code. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "v_rel"]
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
      CodeRel [body] [nextBody] →
      ValueRel (.closure location args env arity body) (.closure location nextArgs nextEnv arity nextBody)
  | recclosure (location : Option Nat) (args nextArgs env nextEnv : List Value)
      (functions nextFunctions : List (Nat × ClosLang.Exp)) (index : Nat) :
      List.Forall₂ ValueRel env nextEnv → List.Forall₂ ValueRel args nextArgs →
      List.Forall₂ FunctionRel functions nextFunctions →
      ValueRel (.recclosure location args env functions index)
        (.recclosure location nextArgs nextEnv nextFunctions index)

/-- Reference payloads retain their kind while values remain related. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "ref_rel"]
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

/-- States related across tick removal. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
def StateRel {C F : Type} (source target : State C F) : Prop :=
  (∀ n, (source.compileOracle n).2.2 = []) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty ∧
  target.maxApp = source.maxApp ∧ 1 ≤ source.maxApp ∧ target.clock = source.clock ∧
  target.ffi = source.ffi ∧ List.Forall₂ (ClosFvs.OptionRel ValueRel) source.globals target.globals ∧
  (∀ key, ClosFvs.OptionRel RefRel (source.refs.lookup key) (target.refs.lookup key)) ∧
  source.compile = pureCc compileInc target.compile ∧
  target.compileOracle = pureCo compileInc ∘ source.compileOracle

/-- Related code lists have equal length. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "code_rel_IMP_LENGTH"]
theorem code_rel_IMP_LENGTH (source target : List ClosLang.Exp) (related : CodeRel source target) :
    source.length = target.length := by
  change target = removeList source at related
  subst target
  simp [removeList_eq_map]

/-- Related states use the same maximum application arity. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "state_rel_IMP_max_app_EQ"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_IMP_max_app_EQ {C F : Type} (source target : State C F)
    (related : StateRel source target) : source.maxApp = target.maxApp :=
  related.2.2.2.1.symm

/-- Replacing both clocks has the same effect on the relation as aligning
the target clock with the original source clock. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "state_rel_clock"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_clock {C F : Type} (source target : State C F) (clock : Nat) :
    StateRel { source with clock := clock } { target with clock := clock } ↔
      StateRel source { target with clock := source.clock } := by
  simp [StateRel]

/-- Decrementing both clocks preserves the state relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "state_rel_dec_clock"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_dec_clock {C F : Type} (source target : State C F)
    (related : StateRel source target) : StateRel (decClock 1 source) (decClock 1 target) := by
  have clockEq : target.clock = source.clock := related.2.2.2.2.2.1
  simpa [StateRel, decClock, clockEq] using related

end Flapjack.Compiler.Backend.ClosTicks
