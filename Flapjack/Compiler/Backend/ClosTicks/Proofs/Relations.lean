module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Production
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Relations

@[expose] public section

/-! Relations used by the closure tick-removal simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

/-- Target code removes the source ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "code_rel_def"]
def CodeRel (source target : List ClosLang.Exp) : Prop := target = removeSource source

/-- Tick removal preserves length whenever its result is given. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_IMP_LENGTH"]
theorem remove_ticks_IMP_LENGTH (es xs : List ClosLang.Exp) (result : xs = removeSource es) :
    es.length = xs.length := by
  subst xs
  exact (removeSource_length es).symm

/-- Tick removal maps a singleton to a singleton. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_SING"]
theorem remove_ticks_SING (e : ClosLang.Exp) : ∃ result, removeSource [e] = [result] := by
  exact ⟨removeSing e, removeSource_sing_eq.1 e⟩

/-- The head reconstructs a tick-removed singleton, whose length is one. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "HD_remove_ticks_SING"]
theorem HD_remove_ticks_SING (e : ClosLang.Exp) :
    [@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (removeSource [e])] = removeSource [e] ∧
      (removeSource [e]).length = 1 := by
  simp [removeSource_eq_list, removeList, Flapjack.holHd]

/-- A predicate on a transformed singleton agrees with its application to the head. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "EVERY_remove_ticks_sing"]
theorem EVERY_remove_ticks_sing (predicate : ClosLang.Exp → Bool) (e : ClosLang.Exp) :
    (removeSource [e]).all predicate =
      predicate (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (removeSource [e])) := by
  simp [removeSource_eq_list, removeList, Flapjack.holHd]

/-- Tick removal decomposes a nonempty input at its head. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_CONS"]
theorem remove_ticks_CONS (es : List ClosLang.Exp) (e : ClosLang.Exp) :
    removeSource (e :: es) =
      (@Flapjack.holHd ClosLang.Exp ⟨.var .none 0⟩ (removeSource [e])) :: removeSource es := by
  simp [removeSource_eq_list, removeList, Flapjack.holHd]

/-- The code relation splits at the first element in both directions. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "code_rel_CONS_CONS"]
theorem code_rel_CONS_CONS (x1 x2 : ClosLang.Exp) (xs : List ClosLang.Exp)
    (y1 y2 : ClosLang.Exp) (ys : List ClosLang.Exp) :
    CodeRel (x1 :: x2 :: xs) (y1 :: y2 :: ys) ↔
      CodeRel [x1] [y1] ∧ CodeRel (x2 :: xs) (y2 :: ys) := by
  simp [CodeRel, removeSource_eq_list, removeList]

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

/-- Constructor equations for the target side of the tick-removal value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "v_rel_simps"]
theorem valueRel_simps (n : Int) (tag : Nat) (fields : List Value) (word : BitVec 64)
    (bytes : List (BitVec 8)) (flag : Bool) (ptr : Nat)
    (loc : Option Nat) (args env : List Value) (arity : Nat) (body : ClosLang.Exp)
    (recLoc : Option Nat) (recArgs recEnv : List Value) (funs : List (Nat × ClosLang.Exp))
    (index : Nat) (x : Value) :
    (ValueRel x (.number n) ↔ x = .number n) ∧
    (ValueRel x (.block tag fields) ↔ ∃ xs, x = .block tag xs ∧ List.Forall₂ ValueRel xs fields) ∧
    (ValueRel x (.word64 word) ↔ x = .word64 word) ∧
    (ValueRel x (.byteVector bytes) ↔ x = .byteVector bytes) ∧
    (ValueRel x (.refPtr flag ptr) ↔ x = .refPtr flag ptr) ∧
    (ValueRel x (.closure loc args env arity body) ↔
      ∃ args1 env1 body1, x = .closure loc args1 env1 arity body1 ∧
        List.Forall₂ ValueRel env1 env ∧ List.Forall₂ ValueRel args1 args ∧
        CodeRel [body1] [body]) ∧
    (ValueRel x (.recclosure recLoc recArgs recEnv funs index) ↔
      ∃ funs1 args1 env1, x = .recclosure recLoc args1 env1 funs1 index ∧
        List.Forall₂ ValueRel env1 recEnv ∧ List.Forall₂ ValueRel args1 recArgs ∧
        List.Forall₂ FunctionRel funs1 funs) ∧
    (ValueRel x (boolValue flag) ↔ x = boolValue flag) ∧
    (ValueRel x unitValue ↔ x = unitValue) := by
  repeat' constructor
  all_goals try (intro h; cases h; simp_all)
  all_goals try (intro h; subst x; constructor)
  all_goals try (rintro ⟨_, _, _, rfl, h₁, h₂, h₃⟩; exact .closure _ _ _ _ _ _ _ _ h₁ h₂ h₃)
  all_goals try simp_all [boolValue, unitValue]
  all_goals try (rename_i h; exact .block _ _ _ h.2)
  all_goals intros
  all_goals exact .recclosure _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_›

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
  target.ffi = source.ffi ∧ List.Forall₂ (Flapjack.optionRel ValueRel) source.globals target.globals ∧
  (∀ key, Flapjack.optionRel RefRel (source.refs.lookup key) (target.refs.lookup key)) ∧
  source.compile = pureCc compileIncSource target.compile ∧
  target.compileOracle = pureCo compileIncSource ∘ source.compileOracle

/-- Related states have empty installed-code maps on both sides. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "state_rel_IMP_code_FEMPTY"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_IMP_code_FEMPTY {C F : Type} (source target : State C F)
    (related : StateRel source target) :
    source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty :=
  ⟨related.2.1, related.2.2.1⟩

/-- Related reference maps give related lookup results in either direction. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "state_rel_opt_rel_refs"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_opt_rel_refs {C F : Type} (source target : State C F) (key : Nat)
    (r1 r2 : Option (Ref Value)) :
    (StateRel source target ∧ source.refs.lookup key = r1 →
      ∃ r2, target.refs.lookup key = r2 ∧ Flapjack.optionRel RefRel r1 r2) ∧
    (StateRel source target ∧ target.refs.lookup key = r2 →
      ∃ r1, source.refs.lookup key = r1 ∧ Flapjack.optionRel RefRel r1 r2) := by
  constructor
  · rintro ⟨related, lookup⟩
    refine ⟨target.refs.lookup key, rfl, ?_⟩
    rw [← lookup]
    exact related.2.2.2.2.2.2.2.2.1 key
  · rintro ⟨related, lookup⟩
    refine ⟨source.refs.lookup key, rfl, ?_⟩
    rw [← lookup]
    exact related.2.2.2.2.2.2.2.2.1 key

/-- Related states have equal clocks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "state_rel_clock_eqs"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_clock_eqs {C F : Type} (source target : State C F)
    (related : StateRel source target) : source.clock = target.clock :=
  related.2.2.2.2.2.1.symm

/-- Related code lists have equal length. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "code_rel_IMP_LENGTH"]
theorem code_rel_IMP_LENGTH (source target : List ClosLang.Exp) (related : CodeRel source target) :
    source.length = target.length := by
  change target = removeSource source at related
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
  have clockEq : target.clock = source.clock := (state_rel_clock_eqs source target related).symm
  simpa [StateRel, decClock, clockEq] using related

end Flapjack.Compiler.Backend.ClosTicks
