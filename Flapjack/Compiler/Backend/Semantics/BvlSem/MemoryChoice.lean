import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions
import Aesop

/-! Choice predicates for BVL byte-vector primitives. -/
namespace Flapjack.Compiler.Backend.BvlSem

private theorem byteArrays_pointers (refs : HolFiniteMapExact Nat (Ref Value))
    (values : List Value) (chunks : List (List (BitVec 8)))
    (run : byteArrays refs values = some chunks) :
    ∃ ptrs : List Nat, values = ptrs.map (Value.refPtr true) := by
  induction values generalizing chunks with
  | nil => exact ⟨[], rfl⟩
  | cons value values ih =>
    cases value with
    | number | word64 | block | codePtr => simp [byteArrays] at run
    | refPtr flag ptr =>
      cases flag with
      | false => simp [byteArrays] at run
      | true =>
        cases lookup : refs.lookup ptr with
        | none => simp [byteArrays, lookup] at run
        | some cell =>
          cases cell with
          | valueArray | thunk | mutBlock => simp [byteArrays, lookup] at run
          | byteArray immutable bytes =>
            cases immutable with
            | false => simp [byteArrays, lookup] at run
            | true =>
              simp [byteArrays, lookup, Option.bind_eq_some_iff] at run
              obtain ⟨result, tailRun, _⟩ := run
              obtain ⟨ptrs, equal⟩ := ih result tailRun
              exact ⟨ptr :: ptrs, by simp [equal]⟩

private theorem byteArrays_map (refs : HolFiniteMapExact Nat (Ref Value))
    (ptrs : List Nat) (chunks : List (List (BitVec 8))) :
    byteArrays refs (ptrs.map (Value.refPtr true)) = some chunks ↔
      ptrs.map refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) := by
  induction ptrs generalizing chunks with
  | nil => cases chunks <;> simp [byteArrays]
  | cons ptr ptrs ih =>
    cases chunks with
    | nil =>
      cases lookup : refs.lookup ptr with
      | none => simp [byteArrays, lookup]
      | some cell =>
        cases cell <;> simp_all [byteArrays]
        case byteArray immutable bytes => cases immutable <;> simp_all [Option.bind_eq_some_iff]
    | cons bytes chunks =>
      cases lookup : refs.lookup ptr with
      | none => simp [byteArrays, lookup]
      | some cell =>
        cases cell with
        | valueArray | thunk | mutBlock => simp [byteArrays, lookup]
        | byteArray immutable payload =>
          cases immutable <;> simp_all [byteArrays, Option.bind_eq_some_iff, and_comm]
          aesop

/-- The deterministic traversal satisfies exactly the original pointer and
lookup predicate for a successful byte-vector concatenation. -/
theorem byteArrays_eq_some (refs : HolFiniteMapExact Nat (Ref Value))
    (values : List Value) (chunks : List (List (BitVec 8))) :
    byteArrays refs values = some chunks ↔
      ∃ ptrs : List Nat, values = ptrs.map (Value.refPtr true) ∧
        ptrs.map refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) := by
  constructor
  · intro run
    obtain ⟨ptrs, equal⟩ := byteArrays_pointers refs values chunks run
    refine ⟨ptrs, equal, ?_⟩
    subst values
    exact (byteArrays_map refs ptrs chunks).mp run
  · rintro ⟨ptrs, rfl, lookup⟩
    exact (byteArrays_map refs ptrs chunks).mpr lookup

/-- Decoding the encoded list of immutable byte-array pointers. -/
def byteArrayChunks (refs : HolFiniteMapExact Nat (Ref Value)) (value : Value) :
    Option (List (List (BitVec 8))) := (valueToList value).bind (byteArrays refs)

/-- The decoder's successful result is the original HOL choice predicate. -/
theorem byteArrayChunks_eq_some (refs : HolFiniteMapExact Nat (Ref Value))
    (value : Value) (chunks : List (List (BitVec 8))) :
    byteArrayChunks refs value = some chunks ↔
      ∃ ptrs : List Nat, valueToList value = some (ptrs.map (Value.refPtr true)) ∧
        ptrs.map refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes)) := by
  simp [byteArrayChunks, Option.bind_eq_some_iff, byteArrays_eq_some]
  aesop

/-- The deterministic decoder equals the guarded HOL choice in the
concatenation branch, including the no-witness case. -/
theorem byteArrayChunks_eq_holChoice (refs : HolFiniteMapExact Nat (Ref Value)) (value : Value) :
    byteArrayChunks refs value = Flapjack.holOptionSome
      (fun chunks : List (List (BitVec 8)) => ∃ ptrs : List Nat,
        valueToList value = some (ptrs.map (Value.refPtr true)) ∧
          ptrs.map refs.lookup = chunks.map (fun bytes => some (.byteArray true bytes))) := by
  exact option_eq_holChoice _ _ (byteArrayChunks_eq_some refs value)

/-- Natural numbers selected by the byte-list decoder. -/
def byteNaturalValues (values : List Value) : Option (List Nat) :=
  (byteNumbers values).map (List.map BitVec.toNat)

/-- Successful byte decoding is equivalent to HOL's natural-number list
predicate, including the bound on every element. -/
theorem byteNaturalValues_eq_some (values : List Value) (numbers : List Nat) :
    byteNaturalValues values = some numbers ↔
      values = numbers.map (fun n => .number n) ∧ ∀ n ∈ numbers, n < 256 := by
  simp only [byteNaturalValues, Option.map_eq_some_iff, byteNumbers_eq_some]
  constructor
  · rintro ⟨bytes, encoded, rfl⟩
    constructor
    · simpa [List.map_map, Function.comp_def] using encoded
    · intro n member
      obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
      simpa using byte.isLt
  · rintro ⟨encoded, bound⟩
    let bytes : List (BitVec 8) := numbers.map (BitVec.ofNat 8)
    have roundtrip : bytes.map BitVec.toNat = numbers := by
      simp only [bytes, List.map_map]
      conv_rhs => rw [← List.map_id numbers]
      apply List.map_congr_left
      intro n member
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bound n member)]
    refine ⟨bytes, ?_, roundtrip⟩
    have mapped : bytes.map (fun b => Value.number b.toNat) =
        numbers.map (fun (n : Nat) => Value.number n) := by
      rw [← roundtrip]
      simp [List.map_map, Function.comp_def]
    exact encoded.trans mapped.symm

/-- The natural-number list selected by `FromListByte`. -/
def byteNaturalList (value : Value) : Option (List Nat) :=
  (valueToList value).bind byteNaturalValues

/-- The selected naturals are the byte decoder's unsigned values. -/
theorem byteNaturalList_eq_byteResult (value : Value) :
    byteNaturalList value = (valueToBytes value).map (List.map BitVec.toNat) := by
  cases decoded : valueToList value <;>
    simp [byteNaturalList, byteNaturalValues, valueToBytes, decoded]

/-- Converting selected naturals back to words returns the exact bytes used
by the `FromListByte` implementation. -/
theorem byteNaturalList_reconstruct (value : Value) :
    (byteNaturalList value).map (List.map (BitVec.ofNat 8)) = valueToBytes value := by
  rw [byteNaturalList_eq_byteResult]
  cases valueToBytes value <;> simp [List.map_map, Function.comp_def]

/-- Its successful result is the source list-and-range predicate. -/
theorem byteNaturalList_eq_some (value : Value) (numbers : List Nat) :
    byteNaturalList value = some numbers ↔
      valueToList value = some (numbers.map (fun n => .number n)) ∧
        ∀ n ∈ numbers, n < 256 := by
  simp [byteNaturalList, Option.bind_eq_some_iff, byteNaturalValues_eq_some]
  aesop

/-- The natural-number decoder agrees with HOL's guarded choice, including
failure when the input is not a valid bounded integer list. -/
theorem byteNaturalList_eq_holChoice (value : Value) :
    byteNaturalList value = Flapjack.holOptionSome
      (fun numbers : List Nat => valueToList value = some (numbers.map (fun n => .number n)) ∧
        ∀ n ∈ numbers, n < 256) := by
  exact option_eq_holChoice _ _ (byteNaturalList_eq_some value)

end Flapjack.Compiler.Backend.BvlSem
