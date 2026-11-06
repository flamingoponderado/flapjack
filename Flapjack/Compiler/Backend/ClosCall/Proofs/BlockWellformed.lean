import Flapjack.Compiler.Backend.ClosCall.Proofs.NumericWellformed

/-! Well-formed values produced by closure block primitives. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem

/-- Every recursively constructed closure constant is well formed. -/
theorem makeConst_wellFormedFuel (fuel : Nat) (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (constant : ClosLang.Const) :
    ValueWellFormedFuel fuel g allowed code (makeConst constant) := by
  refine ClosLang.Const.rec
    (motive_1 := fun c => ValueWellFormedFuel fuel g allowed code (makeConst c))
    (motive_2 := fun cs => ValuesWellFormedFuel fuel g allowed code (cs.map makeConst))
    ?_ ?_ ?_ ?_ ?_ ?_ constant
  · intro tag values ih; rw [makeConst]; exact .block tag ih
  · intro value; rw [makeConst]; exact .number value
  · intro value; rw [makeConst]; exact .byteVector _
  · intro value; rw [makeConst]; exact .word64 value
  · exact .nil
  · intro head tail headIH tailIH; exact .cons headIH tailIH

/-- Encoding a well-formed list into closure-language list blocks preserves
well-formedness. -/
theorem listToValue_wellFormedFuel {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} {values : List Value}
    (wf : ValuesWellFormedFuel fuel g allowed code values) :
    ValueWellFormedFuel fuel g allowed code (listToValue values) := by
  induction values with
  | nil => exact .block _ .nil
  | cons head tail ih =>
    cases wf with
    | cons headWf tailWf => exact .block _ (.cons headWf (.cons (ih tailWf) .nil))

/-- Decoding a well-formed closure list yields well-formed elements. -/
theorem valueToList_wellFormedFuel {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (value : Value) (values : List Value)
    (wf : ValueWellFormedFuel fuel g allowed code value)
    (run : valueToList value = some values) : ValuesWellFormedFuel fuel g allowed code values := by
  cases wf with
  | number | word64 | byteVector | refPtr | closure | recclosure => simp [valueToList] at run
  | @block tag fields fieldsWf =>
    cases fields with
    | nil =>
      simp [valueToList] at run
      obtain ⟨_, rfl⟩ := run
      exact .nil
    | cons head rest =>
      cases rest with
      | nil => simp [valueToList] at run
      | cons tail remaining =>
        cases remaining with
        | cons third rest => simp [valueToList] at run
        | nil =>
          cases fieldsWf with
          | cons headWf restWf =>
            cases restWf with
            | cons tailWf _ =>
              simp only [valueToList] at run
              split at run
              · cases decoded : valueToList tail with
                | none => simp [decoded] at run
                | some tailValues =>
                  simp [decoded] at run
                  subst values
                  exact .cons headWf (valueToList_wellFormedFuel tail tailValues tailWf decoded)
              · simp at run
termination_by sizeOf value
decreasing_by
  subst value
  simp_all
  omega

/-- Successful block primitives preserve well-formedness of the returned
value and leave the source state well formed. -/
theorem applyBlock_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.BlockOp)
    (args : List Value) (state next : ClosSem.State C F) (value : Value)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (run : applyBlock op args state = some (value, next)) :
    ValueWellFormedFuel fuel g allowed code value ∧ StateWellFormedFuel fuel g allowed code next := by
  unfold applyBlock at run
  repeat' split at run
  all_goals simp_all [Bind.bind, Option.bind_eq_some_iff]
  all_goals try (obtain ⟨rfl, _⟩ := run; exact .number _)
  all_goals try (obtain ⟨rfl, _⟩ := run; exact boolValue_wellFormedFuel fuel g allowed code _)
  all_goals try (obtain ⟨rfl, _⟩ := run; exact makeConst_wellFormedFuel fuel g allowed code _)
  all_goals try (obtain ⟨rfl, _⟩ := run; exact .block _ argsWf)
  all_goals try (solve | aesop (config := { warnOnNonterminal := false }) (add safe boolValue_wellFormedFuel))
  case h_3.isFalse =>
    obtain ⟨rfl, _⟩ := run
    cases argsWf with
    | cons blockWf restWf =>
      cases blockWf with
      | block _ fieldsWf =>
        cases restWf with
        | cons _ restWf =>
          cases restWf with
          | cons _ restWf =>
            cases restWf with
            | cons _ initialWf =>
              exact .block _ (valuesWellFormedFuel_append initialWf
                (valuesWellFormedFuel_take (valuesWellFormedFuel_drop fieldsWf _) _))
  case h_6 =>
    obtain ⟨found, _⟩ := run
    cases argsWf with
    | cons blockWf _ =>
      cases blockWf with
      | block _ fieldsWf =>
        obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp found
        apply valuesWellFormedFuel_mem fieldsWf
        simpa only [eq] using List.getElem_mem bound
  case h_7 =>
    obtain ⟨xs, leftRun, ys, rightRun, rfl, rfl⟩ := run
    cases argsWf with
    | cons leftWf tail =>
      cases tail with
      | cons rightWf _ =>
        exact ⟨listToValue_wellFormedFuel
          (valuesWellFormedFuel_append (valueToList_wellFormedFuel _ xs leftWf leftRun)
            (valueToList_wellFormedFuel _ ys rightWf rightRun)), stateWf⟩
  case h_9 =>
    obtain ⟨xs, decode, rfl, rfl⟩ := run
    cases argsWf with
    | cons valueWf _ => exact ⟨.block _ (valueToList_wellFormedFuel _ xs valueWf decode), stateWf⟩

/-- Block dispatch preserves the primitive result invariant for every
outcome, including malformed blocks and rejected argument lists. -/
theorem doApp_block_result_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (op : ClosLang.BlockOp)
    (args : List Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args) :
    PrimitiveResultWellFormedFuel fuel g allowed code (doApp (.blockOp op) args state) := by
  cases applied : applyBlock op args state with
  | none => simp [doApp, applied, PrimitiveResultWellFormedFuel]
  | some pair =>
    obtain ⟨value, next⟩ := pair
    simpa [doApp, applied, PrimitiveResultWellFormedFuel] using
      applyBlock_wellFormedFuel op args state next value stateWf argsWf applied

end Flapjack.Compiler.Backend.ClosCall
