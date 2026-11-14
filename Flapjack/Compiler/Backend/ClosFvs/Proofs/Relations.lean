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
  target = removeSource bound source

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

/-- Constructor equations for the free-variable value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "v_rel_simps"]
theorem valueRel_simps (n : Int) (tag : Nat) (fields : List Value) (word : BitVec 64)
    (bytes : List (BitVec 8)) (flag : Bool) (ptr : Nat)
    (loc : Option Nat) (args env : List Value) (arity : Nat) (body : ClosLang.Exp)
    (recLoc : Option Nat) (recArgs recEnv : List Value) (funs : List (Nat × ClosLang.Exp))
    (index : Nat) (x : Value) :
    (ValueRel (.number n) x ↔ x = .number n) ∧
    (ValueRel (.block tag fields) x ↔ ∃ ys, x = .block tag ys ∧ List.Forall₂ ValueRel fields ys) ∧
    (ValueRel (.word64 word) x ↔ x = .word64 word) ∧
    (ValueRel (.byteVector bytes) x ↔ x = .byteVector bytes) ∧
    (ValueRel (.refPtr flag ptr) x ↔ x = .refPtr flag ptr) ∧
    (ValueRel (.closure loc args env arity body) x ↔
      ∃ args2 env2 body2, x = .closure loc args2 env2 arity body2 ∧
        List.Forall₂ ValueRel env env2 ∧ List.Forall₂ ValueRel args args2 ∧
        CodeRel (env.length + arity) [body] [body2]) ∧
    (ValueRel (.recclosure recLoc recArgs recEnv funs index) x ↔
      ∃ funs2 args2 env2, x = .recclosure recLoc args2 env2 funs2 index ∧
        List.Forall₂ ValueRel recEnv env2 ∧ List.Forall₂ ValueRel recArgs args2 ∧
        List.Forall₂ (FunctionRel (recEnv.length + funs.length)) funs funs2) ∧
    (ValueRel (boolValue flag) x ↔ x = boolValue flag) ∧
    (ValueRel unitValue x ↔ x = unitValue) := by
  repeat' constructor
  all_goals try (intro h; cases h; simp_all)
  all_goals try (intro h; subst x; constructor)
  all_goals try (rintro ⟨_, _, _, rfl, h₁, h₂, h₃⟩; exact .closure _ _ _ _ _ _ _ _ h₁ h₂ h₃)
  all_goals try simp_all [boolValue, unitValue]
  all_goals try (rename_i h; exact .block _ _ _ h.2)
  all_goals intros
  all_goals exact .recclosure _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_›

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
  source.compile = pureCc compileIncSource target.compile ∧
  target.compileOracle = pureCo compileIncSource ∘ source.compileOracle

/-- Related reference maps give related lookup results in either direction. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "state_rel_opt_rel_refs"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_opt_rel_refs {C F : Type} (source target : State C F) (key : Nat)
    (r1 r2 : Option (Ref Value)) :
    (StateRel source target ∧ source.refs.lookup key = r1 →
      ∃ r2, target.refs.lookup key = r2 ∧ optionRel RefRel r1 r2) ∧
    (StateRel source target ∧ target.refs.lookup key = r2 →
      ∃ r1, source.refs.lookup key = r1 ∧ optionRel RefRel r1 r2) := by
  constructor
  · rintro ⟨related, lookup⟩
    refine ⟨target.refs.lookup key, rfl, ?_⟩
    rw [← lookup]
    exact related.2.2.2.2.2.2.2.2.1 key
  · rintro ⟨related, lookup⟩
    refine ⟨source.refs.lookup key, rfl, ?_⟩
    rw [← lookup]
    exact related.2.2.2.2.2.2.2.2.1 key

end Flapjack.Compiler.Backend.ClosFvs
