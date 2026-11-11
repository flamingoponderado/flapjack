module

public import Flapjack.Compiler.Backend.ClosNumber
public import Flapjack.Compiler.Backend.Semantics.ClosSem
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBlock
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

/-- The number-introduction value relation meets the generic simple-value
conditions used by primitive-operation simulations. Flapjack infrastructure;
the corresponding HOL declaration is ported as the tagged ClosMti
`simpleValRel`. -/
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

/-- Numbered values preserve scalar constructors and their payloads. -/
theorem valueRel_number_iff (maxApp : Nat) (number : Int) (target : Value) :
    ValueRel maxApp (.number number) target ↔ target = .number number := by
  constructor
  · intro related
    cases related
    rfl
  · intro equal
    subst target
    exact .number number

/-- List values preserve the relation when encoded as closure blocks. -/
theorem listToValue_related (maxApp : Nat) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) :
    ValueRel maxApp (listToValue left) (listToValue right) := by
  induction related with
  | nil => exact .block _ [] [] .nil
  | cons head tail ih =>
    exact .block _ _ _ (.cons head (.cons ih .nil))

/-- Related values decode as lists together, preserving every element and
    distinguishing malformed list encodings. -/
theorem valueToList_related (maxApp : Nat) (source target : Value)
    (related : ValueRel maxApp source target) :
    match valueToList source, valueToList target with
    | none, none => True
    | some left, some right => List.Forall₂ (ValueRel maxApp) left right
    | _, _ => False := by
  cases related with
  | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure =>
    simp [valueToList]
  | block tag fields nextFields fieldsRel =>
    cases fieldsRel with
    | nil => by_cases equal : tag = BackendCommon.nilTag <;> simp [valueToList, equal]
    | @cons first nextFirst _ _ head tail =>
      cases tail with
      | nil => simp [valueToList]
      | @cons last nextLast _ _ body rest =>
        cases rest with
        | cons extra rest => simp [valueToList]
        | nil =>
          by_cases equal : tag = BackendCommon.consTag
          · have bodyRel := valueToList_related maxApp last nextLast body
            cases left : valueToList last <;> cases right : valueToList nextLast <;>
              simp_all [valueToList]
          · simp [valueToList, equal]

termination_by sizeOf source
decreasing_by simp_wf; omega

/-- Numbering preserves the result of structural equality, including closure
    and type-error cases. -/
theorem doEq_related (maxApp : Nat) (left right nextLeft nextRight : Value)
    (first : ValueRel maxApp left nextLeft) (second : ValueRel maxApp right nextRight) :
    doEq left right = doEq nextLeft nextRight := by
  cases first <;> cases second <;> try (simp only [doEq])
  case block.block tagA fieldsA targetA relA tagB fieldsB targetB relB =>
    have fieldsEq : doEqList fieldsA fieldsB = doEqList targetA targetB := by
      have worker : ∀ {as_ as' : List Value}, List.Forall₂ (ValueRel maxApp) as_ as' →
          (∀ v ∈ as_, v ∈ fieldsA) → ∀ {bs bs' : List Value},
          List.Forall₂ (ValueRel maxApp) bs bs' → doEqList as_ bs = doEqList as' bs' := by
        intro as_ as' related membership
        induction related with
        | nil =>
          intro bs bs' relatedB
          cases relatedB <;> simp [doEqList]
        | @cons a a' rest rest' head tail ih =>
          intro bs bs' relatedB
          cases relatedB with
          | nil => simp [doEqList]
          | @cons b b' tailB tailB' headB relatedTail =>
            have member : a ∈ fieldsA := membership a (by simp)
            have one := doEq_related maxApp a b a' b' head headB
            simp only [doEqList, ← one]
            cases doEq a b with
            | typeError => rfl
            | val flag =>
              cases flag with
              | false => rfl
              | true =>
                apply ih
                · intro v hv
                  exact membership v (by simp [hv])
                · exact relatedTail
      exact worker relA (by intro v h; exact h) relB
    simp [← relA.length_eq, ← relB.length_eq, fieldsEq]
termination_by sizeOf left
decreasing_by
  simp_wf
  have bound := List.sizeOf_lt_of_mem member
  omega

/-- Every closure constant evaluates to a value related to itself, including
    recursively nested constructor constants. -/
theorem makeConst_related (maxApp : Nat) (constant : ClosLang.Const) :
    ValueRel maxApp (makeConst constant) (makeConst constant) := by
  exact ClosProps.PrimitiveBlock.makeConstRelated (ValueRel maxApp) (simpleValRel maxApp) constant

end Flapjack.Compiler.Backend.ClosNumber
