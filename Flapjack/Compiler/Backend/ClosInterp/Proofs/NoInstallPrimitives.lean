import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallValues

/-! Primitive preservation of the no-install invariant. The evaluator and
state carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- The closure list encoding preserves the no-install invariant. -/
theorem listToValue_noInstall (values : List ClosSem.Value)
    (valid : valuesNoInstall values = true) : valueNoInstall (ClosSem.listToValue values) = true := by
  induction values with
  | nil => simp [ClosSem.listToValue, valueNoInstall, valuesNoInstall]
  | cons value rest ih =>
    simp [valuesNoInstall] at valid
    simp [ClosSem.listToValue, valueNoInstall, valuesNoInstall, valid.1, ih valid.2]

/-- Decoding a safe closure list produces a safe value list. -/
theorem valueToList_noInstall (value : ClosSem.Value) (values : List ClosSem.Value)
    (valid : valueNoInstall value = true) (run : ClosSem.valueToList value = some values) :
    valuesNoInstall values = true := by
  cases value with
  | block tag fields =>
    cases fields with
    | nil =>
      simp [ClosSem.valueToList] at run
      simp_all [valuesNoInstall]
    | cons head tail =>
      cases tail with
      | nil => simp [ClosSem.valueToList] at run
      | cons next tail =>
        cases tail with
        | cons other rest => simp [ClosSem.valueToList] at run
        | nil =>
          simp [valueNoInstall, valuesNoInstall] at valid
          simp only [ClosSem.valueToList] at run
          split at run
          · cases decoded : ClosSem.valueToList next with
            | none => simp [decoded] at run
            | some tailValues =>
              simp [decoded] at run
              subst values
              have tailOk := valueToList_noInstall next tailValues valid.2 decoded
              simp [valuesNoInstall, valid.1, tailOk]
          · simp at run
  | _ => simp [ClosSem.valueToList] at run
termination_by sizeOf value

/-- Runtime Boolean values are no-install values. -/
theorem boolValue_noInstall (choice : Bool) : valueNoInstall (ClosSem.boolValue choice) = true := by
  cases choice <;> simp [ClosSem.boolValue, valueNoInstall, valuesNoInstall]

/-- Block primitives return no-install values from no-install arguments. -/
theorem applyBlock_noInstall {C F : Type} (op : ClosLang.BlockOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (argsOk : valuesNoInstall args = true) (run : ClosSem.applyBlock op args state = some (value, next)) :
    valueNoInstall value = true := by
  unfold ClosSem.applyBlock at run
  repeat' split at run
  all_goals simp_all [valuesNoInstall, valueNoInstall]
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (solve | aesop (add safe apply [makeConst_noInstall, boolValue_noInstall,
    listToValue_noInstall, valueToList_noInstall, valuesNoInstall_take, valuesNoInstall_drop]))
  case h_2 =>
    rcases run with ⟨rfl, _⟩
    simpa [valueNoInstall] using argsOk
  case h_3.isFalse =>
    rcases run with ⟨rfl, _⟩
    simp only [valueNoInstall]
    apply (valuesNoInstall_append _ _).2
    exact ⟨argsOk.2, valuesNoInstall_take _ _ (valuesNoInstall_drop _ _ argsOk.1)⟩
  case h_6 =>
    rcases run with ⟨item, found, rfl, _⟩
    exact (valuesNoInstall_iff _).1 argsOk item (List.mem_of_getElem? found)
  case h_7 =>
    rcases run with ⟨left, leftRun, right, rightRun, rfl, _⟩
    apply listToValue_noInstall
    exact (valuesNoInstall_append left right).2
      ⟨valueToList_noInstall _ left argsOk.1 leftRun, valueToList_noInstall _ right argsOk.2 rightRun⟩
  case h_8 =>
    rcases run with ⟨rfl, _⟩
    simp [valueNoInstall]
  case h_9 =>
    rcases run with ⟨values, decoded, rfl, _⟩
    simpa [valueNoInstall] using valueToList_noInstall _ values argsOk decoded

/-- Successful integer primitives return no-install values. -/
theorem doIntApp_noInstall (op : ClosLang.IntOp) (args : List ClosSem.Value) (value : ClosSem.Value)
    (run : ClosSem.doIntApp op args = some value) : valueNoInstall value = true := by
  unfold ClosSem.doIntApp at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop (add simp [valueNoInstall]) (add safe apply [boolValue_noInstall])

/-- Successful integral word primitives return no-install values. -/
theorem doWordAppIntegral_noInstall (op : ClosLang.WordOp) (args : List ClosSem.Value) (value : ClosSem.Value)
    (run : ClosSem.doWordAppIntegral op args = some value) : valueNoInstall value = true := by
  unfold ClosSem.doWordAppIntegral at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq]
  all_goals try (solve | aesop (add simp [valueNoInstall]) (add safe apply [boolValue_noInstall]))

/-- Successful word primitives, including floating-point operations, return
no-install values. -/
theorem doWordApp_noInstall (op : ClosLang.WordOp) (args : List ClosSem.Value) (value : ClosSem.Value)
    (run : ClosSem.doWordApp op args = some value) : valueNoInstall value = true := by
  unfold ClosSem.doWordApp at run
  repeat' split at run
  all_goals simp_all
  all_goals try (solve | aesop (add simp [valueNoInstall]) (add safe apply [boolValue_noInstall, doWordAppIntegral_noInstall]))

/-- Successful numeric dispatch returns a no-install value. -/
theorem applyNumeric_noInstall {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyNumeric op args state = some (value, next)) : valueNoInstall value = true := by
  cases op with
  | intOp operation =>
    cases found : ClosSem.doIntApp operation args with
    | none => simp [ClosSem.applyNumeric, found] at run
    | some v =>
      simp [ClosSem.applyNumeric, found] at run
      rcases run with ⟨rfl, _⟩
      exact doIntApp_noInstall operation args v found
  | wordOp operation =>
    cases found : ClosSem.doWordApp operation args with
    | none => simp [ClosSem.applyNumeric, found] at run
    | some v =>
      simp [ClosSem.applyNumeric, found] at run
      rcases run with ⟨rfl, _⟩
      exact doWordApp_noInstall operation args v found
  | _ => simp [ClosSem.applyNumeric] at run

/-- Replacing an element of a safe list with a safe value keeps it safe. -/
theorem valuesNoInstall_set (values : List ClosSem.Value) (index : Nat) (value : ClosSem.Value)
    (valid : valuesNoInstall values = true) (valueOk : valueNoInstall value = true) :
    valuesNoInstall (values.set index value) = true := by
  induction values generalizing index with
  | nil => simp [valuesNoInstall]
  | cons head tail ih =>
    simp [valuesNoInstall] at valid
    cases index with
    | zero => simp [List.set, valuesNoInstall, valueOk, valid.2]
    | succ index => simp [List.set, valuesNoInstall, valid.1, ih index valid.2]

/-- Replicating a safe value produces a safe list. -/
theorem valuesNoInstall_replicate (count : Nat) (value : ClosSem.Value)
    (valid : valueNoInstall value = true) : valuesNoInstall (List.replicate count value) = true := by
  apply (valuesNoInstall_iff _).2
  intro item member
  simp only [List.mem_replicate] at member
  rcases member with ⟨_, rfl⟩
  exact valid

/-- A list of integer-encoded bytes contains no installation closures. -/
theorem encodedBytes_noInstall (bytes : List (BitVec 8)) :
    valuesNoInstall (bytes.map (fun b => ClosSem.Value.number b.toNat)) = true := by
  apply (valuesNoInstall_iff _).2
  intro value member
  simp only [List.mem_map] at member
  obtain ⟨byte, _, rfl⟩ := member
  simp [valueNoInstall]

/-- Looking up a value in a safe list yields a safe value. -/
theorem valuesNoInstall_lookup (values : List ClosSem.Value) (index : Nat) (value : ClosSem.Value)
    (valid : valuesNoInstall values = true) (found : values[index]? = some value) : valueNoInstall value = true :=
  (valuesNoInstall_iff values).1 valid value (List.mem_of_getElem? found)

/-- A value array in a safe store contains a safe value list. -/
theorem refsNoInstall_valueArray (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (index : Nat) (values : List ClosSem.Value) (valid : refsNoInstall refs)
    (found : refs.lookup index = some (.valueArray values)) : valuesNoInstall values = true :=
  valid index (.valueArray values) found

end Flapjack.Compiler.Backend.ClosInterp
