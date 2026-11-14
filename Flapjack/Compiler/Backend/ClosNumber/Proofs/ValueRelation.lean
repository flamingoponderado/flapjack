module

public import Flapjack.Compiler.Backend.ClosNumber
public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.ListRelations
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Proof-side value relation for closure location numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.Compiler.Backend.ClosSem

/-- Values corresponding across closure numbering. Closure locations may
change, while bodies are numbered and captured environments remain related. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "v_rel"]
inductive ValueRel (maxApp : Nat) : Value → Value → Prop where
  | number (value : Int) : ValueRel maxApp (.number value) (.number value)
  | word64 (value : BitVec 64) : ValueRel maxApp (.word64 value) (.word64 value)
  | block (tag : Nat) (left right : List Value) :
      List.Forall₂ (ValueRel maxApp) left right → ValueRel maxApp (.block tag left) (.block tag right)
  | byteVector (bytes : List (BitVec 8)) : ValueRel maxApp (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) : ValueRel maxApp (.refPtr flag address) (.refPtr flag address)
  | closure (location nextLocation : Option Nat) (args nextArgs env nextEnv : List Value)
      (arity start : Nat) (body nextBody : ClosLang.Exp) :
      List.Forall₂ (ValueRel maxApp) env nextEnv →
      List.Forall₂ (ValueRel maxApp) args nextArgs →
      ¬ ClosProps.containsAppSome maxApp [body] →
      nextBody = (renumber start body).2 →
      ValueRel maxApp (.closure location args env arity body) (.closure nextLocation nextArgs nextEnv arity nextBody)
  | recclosure (location nextLocation : Option Nat) (args nextArgs env nextEnv : List Value)
      (functions nextFunctions : List (Nat × ClosLang.Exp)) (index start : Nat) :
      List.Forall₂ (ValueRel maxApp) env nextEnv →
      List.Forall₂ (ValueRel maxApp) args nextArgs →
      ¬ ClosProps.containsAppSome maxApp (functions.map Prod.snd) →
      nextFunctions = (functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2 →
      ValueRel maxApp (.recclosure location args env functions index)
        (.recclosure nextLocation nextArgs nextEnv nextFunctions index)

/-- Numbering satisfies the source simple-value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "simple_val_rel"]
theorem simpleValRel (maxApp : Nat) : ClosProps.simpleValRel (ValueRel maxApp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n
    refine ⟨fun h => by
      cases h
      rfl, fun h => by
      subst x
      exact .number n⟩
  · intro x fields tag
    refine ⟨?_, ?_⟩
    · intro h
      cases h with | block _ left _ rel => exact ⟨left, rfl, rel⟩
    · rintro ⟨left, rfl, rel⟩
      exact .block tag left fields rel
  · intro x word
    refine ⟨fun h => by
      cases h
      rfl, fun h => by
      subst x
      exact .word64 word⟩
  · intro x bytes
    refine ⟨fun h => by
      cases h
      rfl, fun h => by
      subst x
      exact .byteVector bytes⟩
  · intro x address flag
    refine ⟨fun h => by
      cases h
      rfl, fun h => by
      subst x
      exact .refPtr flag address⟩
  · intro body arity env args loc x h
    cases h
    trivial
  · intro index funs env args loc x h
    cases h
    trivial

/-- List values preserve the relation when encoded as closure blocks. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "list_to_v_v_rel"]
theorem listToValue_related (maxApp : Nat) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) :
    ValueRel maxApp (listToValue left) (listToValue right) := by
  induction related with
  | nil => exact .block _ [] [] .nil
  | cons head tail ih =>
    exact .block _ _ _ (.cons head (.cons ih .nil))

/-- Related values decode as lists together, preserving every element and
    distinguishing malformed list encodings. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "v_to_list"]
theorem valueToList_related (maxApp : Nat) (source target : Value)
    (related : ValueRel maxApp source target) :
    match valueToList source, valueToList target with
    | none, none => True
    | some left, some right => List.Forall₂ (ValueRel maxApp) left right
    | _, _ => False :=
  ClosProps.valueToList_related (ValueRel maxApp) (simpleValRel maxApp) source target related

end Flapjack.Compiler.Backend.ClosNumber
