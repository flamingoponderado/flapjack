import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallValues
import Flapjack.Compiler.Backend.ClosInterp.Proofs.PrimitiveRelation

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

/-- Successful memory primitives preserve no-install values and references. -/
theorem applyMemory_noInstall {C F : Type} (op : ClosLang.MemOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (argsOk : valuesNoInstall args = true) (refsOk : refsNoInstall state.refs)
    (run : ClosSem.applyMemory op args state = some (value, next)) :
    valueNoInstall value = true ∧ refsNoInstall next.refs := by
  unfold ClosSem.applyMemory at run
  repeat' split at run
  all_goals simp_all [valuesNoInstall, valueNoInstall]
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals try (rcases run with ⟨_, _, _, _, rfl, rfl⟩)
  all_goals try subst value
  all_goals try (solve | simp_all [valueNoInstall, ClosSem.unitValue, valuesNoInstall])
  all_goals try (solve | constructor <;> first | exact refsOk | (apply valuesNoInstall_lookup <;> assumption))
  all_goals try (solve | simp only [valueNoInstall, ClosSem.unitValue, valuesNoInstall, true_and] <;>
    apply refsNoInstall_update <;> first | exact refsOk | (simp only [refNoInstall] <;> first | trivial | assumption | (apply valuesNoInstall_replicate <;> assumption)))
  all_goals try (solve | apply listToValue_noInstall <;> exact encodedBytes_noInstall _)
  all_goals try (solve | exact boolValue_noInstall _)
  all_goals try (have arrayOk := refsNoInstall_valueArray _ _ _ refsOk (by assumption))
  all_goals try (solve | constructor <;> first | exact refsOk | (apply valuesNoInstall_lookup <;> assumption))
  all_goals try (solve | simp only [valueNoInstall, ClosSem.unitValue, valuesNoInstall, true_and] <;>
    apply refsNoInstall_update <;> first | exact refsOk | (simp only [refNoInstall]; apply valuesNoInstall_set <;> assumption))
  case h_16 | h_17 | h_19 | h_20 =>
    rcases run with ⟨entry, _, run⟩
    cases entry <;> simp_all [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
    all_goals try (solve | rcases run with ⟨_, _, rfl, rfl⟩ <;>
      simp_all [valueNoInstall, ClosSem.unitValue, valuesNoInstall] <;>
      apply refsNoInstall_update <;> simp_all [refNoInstall])
    all_goals rcases run with ⟨entry, _, run⟩
    all_goals cases entry <;> simp_all [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
    all_goals rcases run with ⟨_, _, rfl, rfl⟩
    all_goals simp_all [valueNoInstall, ClosSem.unitValue, valuesNoInstall]
    all_goals apply refsNoInstall_update <;> simp_all [refNoInstall]

/-- Every initialized global contains a no-install value. -/
def globalsNoInstall (globals : List (Option ClosSem.Value)) : Prop :=
  ∀ entry ∈ globals, ∀ value, entry = some value → valueNoInstall value = true

/-- Updating a global with a safe value preserves the global invariant. -/
theorem globalsNoInstall_set (globals : List (Option ClosSem.Value)) (index : Nat)
    (value : ClosSem.Value) (valid : globalsNoInstall globals) (valueOk : valueNoInstall value = true) :
    globalsNoInstall (globals.set index (some value)) := by
  induction globals generalizing index with
  | nil => simp [List.set, globalsNoInstall]
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.set, globalsNoInstall, List.mem_cons] at *
      intro entry member v eq
      rcases member with rfl | member
      · cases eq; exact valueOk
      · exact valid entry (Or.inr member) v eq
    | succ index =>
      simp only [List.set, globalsNoInstall, List.mem_cons] at *
      intro entry member v eq
      rcases member with rfl | member
      · exact valid _ (Or.inl rfl) v eq
      · apply ih index (by intro e h; exact valid e (Or.inr h)) entry member v eq

/-- Extending the globals with uninitialized slots preserves the invariant. -/
theorem globalsNoInstall_append_empty (globals : List (Option ClosSem.Value)) (count : Nat)
    (valid : globalsNoInstall globals) : globalsNoInstall (globals ++ List.replicate count none) := by
  intro entry member value eq
  simp only [List.mem_append, List.mem_replicate] at member
  rcases member with member | ⟨_, rfl⟩
  · exact valid entry member value eq
  · cases eq

/-- Successful global primitives preserve safe values and globals. -/
theorem applyGlobal_noInstall {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (argsOk : valuesNoInstall args = true) (globalsOk : globalsNoInstall state.globals)
    (run : ClosSem.applyGlobal op args state = some (value, next)) :
    valueNoInstall value = true ∧ globalsNoInstall next.globals := by
  unfold ClosSem.applyGlobal at run
  repeat' split at run
  all_goals simp_all [valuesNoInstall, valueNoInstall, ClosSem.getGlobal]
  all_goals try simp_all only [Option.join_eq_some_iff]
  all_goals try (solve | rcases run with ⟨found, rfl⟩; exact globalsOk _ (List.mem_of_getElem? found) _ rfl)
  all_goals rcases run with ⟨rfl, rfl⟩
  all_goals simp only [valueNoInstall, ClosSem.unitValue, valuesNoInstall, true_and]
  all_goals first | exact globalsNoInstall_set _ _ _ globalsOk argsOk | exact globalsNoInstall_append_empty _ _ globalsOk

/-- Successful global operations leave the reference store unchanged. -/
theorem applyGlobal_refs {C F : Type} (op : ClosLang.GlobOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyGlobal op args state = some (value, next)) : next.refs = state.refs := by
  unfold ClosSem.applyGlobal at run
  repeat' split at run
  all_goals simp_all
  all_goals (rcases run with ⟨_, rfl⟩; rfl)

/-- Successful block operations leave the state unchanged. -/
theorem applyBlock_state {C F : Type} (op : ClosLang.BlockOp) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyBlock op args state = some (value, next)) : next = state := by
  unfold ClosSem.applyBlock at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- Successful numeric operations leave the state unchanged. -/
theorem applyNumeric_state {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.applyNumeric op args state = some (value, next)) : next = state := by
  unfold ClosSem.applyNumeric at run
  repeat' split at run
  all_goals simp_all

/-- Successful ordinary primitive applications preserve the no-install
invariants for their result, globals, and references. -/
theorem doApp_noInstall {C F : Type} (op : ClosLang.Op) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (value : ClosSem.Value)
    (argsOk : valuesNoInstall args = true) (globalsOk : globalsNoInstall state.globals)
    (refsOk : refsNoInstall state.refs)
    (run : ClosSem.doApp op args state = .val (value, next)) :
    valueNoInstall value = true ∧ globalsNoInstall next.globals ∧ refsNoInstall next.refs := by
  cases op with
  | globOp operation =>
    cases found : ClosSem.applyGlobal operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      obtain ⟨v, g⟩ := applyGlobal_noInstall operation args state next value argsOk globalsOk found
      exact ⟨v, g, by simpa [applyGlobal_refs operation args state next value found] using refsOk⟩
  | blockOp operation =>
    cases found : ClosSem.applyBlock operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      have unchanged := applyBlock_state operation args state next value found
      subst next
      exact ⟨applyBlock_noInstall operation args state state value argsOk found, globalsOk, refsOk⟩
  | memOp operation =>
    cases found : ClosSem.applyMemory operation args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      obtain ⟨v, r⟩ := applyMemory_noInstall operation args state next value argsOk refsOk found
      exact ⟨v, by simpa [applyMemory_globals operation args state next value found] using globalsOk, r⟩
  | intOp operation =>
    cases found : ClosSem.applyNumeric (.intOp operation) args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      have unchanged := applyNumeric_state (.intOp operation) args state next value found
      subst next
      exact ⟨applyNumeric_noInstall (.intOp operation) args state state value found, globalsOk, refsOk⟩
  | wordOp operation =>
    cases found : ClosSem.applyNumeric (.wordOp operation) args state with
    | none => simp [ClosSem.doApp, found] at run
    | some pair =>
      have equal : pair = (value, next) := by simpa [ClosSem.doApp, found] using run
      subst pair
      have unchanged := applyNumeric_state (.wordOp operation) args state next value found
      subst next
      exact ⟨applyNumeric_noInstall (.wordOp operation) args state state value found, globalsOk, refsOk⟩
  | ffi | thunkOp =>
    simp only [ClosSem.doApp] at run
    repeat' split at run
    all_goals simp_all [valueNoInstall, valuesNoInstall, ClosSem.unitValue]
    all_goals rcases run with ⟨rfl, rfl⟩
    all_goals simp only [valueNoInstall, valuesNoInstall, true_and]
    all_goals exact ⟨globalsOk, refsNoInstall_update _ _ _ refsOk (by simp_all [refNoInstall])⟩
  | label | install => simp [ClosSem.doApp] at run

end Flapjack.Compiler.Backend.ClosInterp
