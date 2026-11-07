import Flapjack.Compiler.Backend.ClosConstant.Proofs.Flatten

/-! Index bounds for source constant flattening. -/
namespace Flapjack.Compiler.Backend.ClosConstant.Proofs
open Flapjack.Compiler.Backend.ClosLang

/-- Every part in an accumulator has an index below the next free index. -/
def indicesBelow (index : Nat) (aux : List (ConstPart × Nat)) : Prop :=
  ∀ entry ∈ aux, entry.2 < index

/-- Association-list lookup only returns an index present in the list. -/
theorem lookupPart_mem (part : ConstPart) (aux : List (ConstPart × Nat)) (index : Nat)
    (found : lookupPart part aux = some index) : (part, index) ∈ aux := by
  induction aux with
  | nil => simp [lookupPart] at found
  | cons entry rest ih =>
    obtain ⟨other, value⟩ := entry
    simp only [lookupPart] at found
    split at found
    · rename_i equal
      simp only [Option.some.injEq] at found
      subst other
      subst value
      simp
    · exact List.mem_cons_of_mem _ (ih found)

/-- Inserting or reusing one part preserves index bounds and returns an
index below the resulting next index. -/
theorem makePart_bounds (index : Nat) (part : ConstPart) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow index aux) :
    let (next, found, result) := makePart index part aux
    index ≤ next ∧ found < next ∧ indicesBelow next result := by
  unfold makePart
  cases lookup : lookupPart part aux with
  | none =>
    refine ⟨Nat.le_succ _, Nat.lt_succ_self _, ?_⟩
    intro entry member
    rcases List.mem_cons.mp member with equal | member
    · subst entry
      exact Nat.lt_succ_self _
    · exact Nat.lt_trans (bounded entry member) (Nat.lt_succ_self _)
  | some found =>
    have member := lookupPart_mem part aux found lookup
    exact ⟨Nat.le_refl _, bounded _ member, bounded⟩

mutual
/-- Flattening one constant preserves accumulator bounds and returns a valid
part index. -/
theorem parts_bounds (constant : Const) (index : Nat) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow index aux) :
    let (next, found, result) := parts constant index aux
    index ≤ next ∧ found < next ∧ indicesBelow next result := by
  cases constant with
  | constInt n => exact makePart_bounds index (.int n) aux bounded
  | constStr text => exact makePart_bounds index (.str text) aux bounded
  | constWord64 w => exact makePart_bounds index (.w64 w) aux bounded
  | constCons tag constants =>
    cases first : partsList constants index aux with
    | mk next pair =>
      cases pair with
      | mk indices nextAux =>
        have firstBounds := partsList_bounds constants index aux bounded
        rw [first] at firstBounds
        obtain ⟨initialLe, _, nextBounded⟩ := firstBounds
        have finalBounds := makePart_bounds next (.con tag indices) nextAux nextBounded
        simp only [parts, first]
        cases final : makePart next (.con tag indices) nextAux with
        | mk last pair =>
          cases pair with
          | mk found result =>
            rw [final] at finalBounds
            obtain ⟨nextLe, foundLt, finalBounded⟩ := finalBounds
            exact ⟨Nat.le_trans initialLe nextLe, foundLt, finalBounded⟩

/-- Flattening a constant list preserves bounds and returns only indices
below the resulting next index. -/
theorem partsList_bounds (constants : List Const) (index : Nat) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow index aux) :
    let (next, found, result) := partsList constants index aux
    index ≤ next ∧ (∀ item ∈ found, item < next) ∧ indicesBelow next result := by
  cases constants with
  | nil => exact ⟨Nat.le_refl _, by simp, bounded⟩
  | cons constant rest =>
    cases first : parts constant index aux with
    | mk next pair =>
      cases pair with
      | mk found nextAux =>
        have firstBounds := parts_bounds constant index aux bounded
        rw [first] at firstBounds
        obtain ⟨initialLe, foundLt, nextBounded⟩ := firstBounds
        cases second : partsList rest next nextAux with
        | mk last pair =>
          cases pair with
          | mk foundRest finalAux =>
            have restBounds := partsList_bounds rest next nextAux nextBounded
            rw [second] at restBounds
            obtain ⟨nextLe, restLt, finalBounded⟩ := restBounds
            simp only [partsList, first, second]
            refine ⟨Nat.le_trans initialLe nextLe, ?_, finalBounded⟩
            intro item member
            rcases List.mem_cons.mp member with rfl | member
            · exact Nat.lt_of_lt_of_le foundLt nextLe
            · exact restLt item member
end

/-- Flattening preserves the number of elements in a constant list. -/
theorem partsList_length (constants : List Const) (index : Nat) (aux : List (ConstPart × Nat)) :
    (partsList constants index aux).2.1.length = constants.length := by
  induction constants generalizing index aux with
  | nil => rfl
  | cons constant rest ih =>
    cases first : parts constant index aux with
    | mk next pair =>
      cases pair with
      | mk found nextAux =>
        cases second : partsList rest next nextAux with
        | mk last pair =>
          cases pair with
          | mk foundRest finalAux =>
            have length := ih next nextAux
            rw [second] at length
            simp only [partsList, first, second, List.length_cons]
            exact congrArg Nat.succ length

/-- Constructor parts may refer only to earlier built parts. -/
def dependenciesBelow (aux : List (ConstPart × Nat)) : Prop :=
  ∀ tag children index, (.con tag children, index) ∈ aux → ∀ child ∈ children, child < index

/-- Inserting a part with earlier dependencies preserves the ordering invariant. -/
theorem makePart_dependencies (index : Nat) (part : ConstPart) (aux : List (ConstPart × Nat))
    (ordered : dependenciesBelow aux)
    (childrenBelow : ∀ tag children, part = .con tag children → ∀ child ∈ children, child < index) :
    dependenciesBelow (makePart index part aux).2.2 := by
  unfold makePart
  cases lookup : lookupPart part aux with
  | some found => exact ordered
  | none =>
    intro tag children resultIndex member child childMem
    rcases List.mem_cons.mp member with equal | member
    · have partEq : part = .con tag children := congrArg Prod.fst equal.symm
      have indexEq : index = resultIndex := congrArg Prod.snd equal.symm
      subst resultIndex
      exact childrenBelow tag children partEq child childMem
    · exact ordered tag children resultIndex member child childMem

mutual
/-- Flattening a constant preserves the ordering of constructor dependencies. -/
theorem parts_dependencies (constant : Const) (index : Nat) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow index aux) (ordered : dependenciesBelow aux) :
    dependenciesBelow (parts constant index aux).2.2 := by
  cases constant with
  | constInt n => exact makePart_dependencies index (.int n) aux ordered (by simp)
  | constStr text => exact makePart_dependencies index (.str text) aux ordered (by simp)
  | constWord64 word => exact makePart_dependencies index (.w64 word) aux ordered (by simp)
  | constCons tag constants =>
    cases first : partsList constants index aux with
    | mk next pair =>
      cases pair with
      | mk indices nextAux =>
        have bounds := partsList_bounds constants index aux bounded
        rw [first] at bounds
        obtain ⟨_, indicesBounded, _⟩ := bounds
        have nextOrdered := partsList_dependencies constants index aux bounded ordered
        rw [first] at nextOrdered
        simp only [parts, first]
        apply makePart_dependencies next (.con tag indices) nextAux nextOrdered
        intro other children equal child member
        cases equal
        exact indicesBounded child member

/-- Flattening a list preserves the ordering of constructor dependencies. -/
theorem partsList_dependencies (constants : List Const) (index : Nat) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow index aux) (ordered : dependenciesBelow aux) :
    dependenciesBelow (partsList constants index aux).2.2 := by
  cases constants with
  | nil => exact ordered
  | cons constant rest =>
    cases first : parts constant index aux with
    | mk next pair =>
      cases pair with
      | mk found nextAux =>
        have bounds := parts_bounds constant index aux bounded
        rw [first] at bounds
        obtain ⟨_, _, nextBounded⟩ := bounds
        have nextOrdered := parts_dependencies constant index aux bounded ordered
        rw [first] at nextOrdered
        simp only [partsList, first]
        cases second : partsList rest next nextAux with
        | mk last pair =>
          cases pair with
          | mk indices finalAux =>
            have finalOrdered := partsList_dependencies rest next nextAux nextBounded nextOrdered
            rw [second] at finalOrdered
            exact finalOrdered
end

/-- Accumulator indices are distinct. -/
def distinctIndices (aux : List (ConstPart × Nat)) : Prop := (aux.map Prod.snd).Nodup

/-- Inserting a fresh index preserves distinctness; reusing a part leaves the
accumulator unchanged. -/
theorem makePart_distinct (index : Nat) (part : ConstPart) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow index aux) (distinct : distinctIndices aux) :
    distinctIndices (makePart index part aux).2.2 := by
  unfold makePart
  cases lookup : lookupPart part aux with
  | some found => exact distinct
  | none =>
    simp only [distinctIndices, List.map_cons, List.nodup_cons]
    constructor
    · intro member
      obtain ⟨entry, inAux, equal⟩ := List.mem_map.mp member
      have bound := bounded entry inAux
      omega
    · exact distinct

mutual
/-- Flattening one constant preserves distinct accumulator indices. -/
theorem parts_distinct (constant : Const) (index : Nat) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow index aux) (distinct : distinctIndices aux) :
    distinctIndices (parts constant index aux).2.2 := by
  cases constant with
  | constInt n => exact makePart_distinct index (.int n) aux bounded distinct
  | constStr text => exact makePart_distinct index (.str text) aux bounded distinct
  | constWord64 word => exact makePart_distinct index (.w64 word) aux bounded distinct
  | constCons tag constants =>
    cases first : partsList constants index aux with
    | mk next pair =>
      cases pair with
      | mk indices nextAux =>
        have bounds := partsList_bounds constants index aux bounded
        rw [first] at bounds
        have nextDistinct := partsList_distinct constants index aux bounded distinct
        rw [first] at nextDistinct
        simp only [parts, first]
        exact makePart_distinct next (.con tag indices) nextAux bounds.2.2 nextDistinct

/-- Flattening a list preserves distinct accumulator indices. -/
theorem partsList_distinct (constants : List Const) (index : Nat) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow index aux) (distinct : distinctIndices aux) :
    distinctIndices (partsList constants index aux).2.2 := by
  cases constants with
  | nil => exact distinct
  | cons constant rest =>
    cases first : parts constant index aux with
    | mk next pair =>
      cases pair with
      | mk found nextAux =>
        have bounds := parts_bounds constant index aux bounded
        rw [first] at bounds
        have nextDistinct := parts_distinct constant index aux bounded distinct
        rw [first] at nextDistinct
        simp only [partsList, first]
        cases second : partsList rest next nextAux with
        | mk last pair =>
          cases pair with
          | mk indices finalAux =>
            have finalDistinct := partsList_distinct rest next nextAux bounds.2.2 nextDistinct
            rw [second] at finalDistinct
            exact finalDistinct
end

/-- Accumulator entries enumerate the allocated indices in reverse order. -/
def canonicalIndices (aux : List (ConstPart × Nat)) : Prop :=
  aux.map Prod.snd = (List.range aux.length).reverse

/-- Allocation maintains the canonical enumeration, including reuse. -/
theorem makePart_indices (index : Nat) (part : ConstPart) (aux : List (ConstPart × Nat))
    (matching : index = aux.length) (canonical : canonicalIndices aux) :
    let (next, _, result) := makePart index part aux
    next = result.length ∧ canonicalIndices result := by
  unfold makePart
  cases lookup : lookupPart part aux with
  | some found => exact ⟨matching, canonical⟩
  | none =>
    constructor
    · simp [matching]
    · simp only [canonicalIndices, List.map_cons, List.length_cons, List.range_succ,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [canonical, matching]
      rfl

mutual
/-- Flattening preserves the canonical allocation sequence. -/
theorem parts_indices (constant : Const) (index : Nat) (aux : List (ConstPart × Nat))
    (matching : index = aux.length) (canonical : canonicalIndices aux) :
    let (next, _, result) := parts constant index aux
    next = result.length ∧ canonicalIndices result := by
  cases constant with
  | constInt n => exact makePart_indices index (.int n) aux matching canonical
  | constStr text => exact makePart_indices index (.str text) aux matching canonical
  | constWord64 word => exact makePart_indices index (.w64 word) aux matching canonical
  | constCons tag constants =>
    cases first : partsList constants index aux with
    | mk next pair =>
      cases pair with
      | mk indices nextAux =>
        have invariant := partsList_indices constants index aux matching canonical
        rw [first] at invariant
        simp only [parts, first]
        exact makePart_indices next (.con tag indices) nextAux invariant.1 invariant.2

/-- Flattening a list preserves the canonical allocation sequence. -/
theorem partsList_indices (constants : List Const) (index : Nat) (aux : List (ConstPart × Nat))
    (matching : index = aux.length) (canonical : canonicalIndices aux) :
    let (next, _, result) := partsList constants index aux
    next = result.length ∧ canonicalIndices result := by
  cases constants with
  | nil => exact ⟨matching, canonical⟩
  | cons constant rest =>
    cases first : parts constant index aux with
    | mk next pair =>
      cases pair with
      | mk found nextAux =>
        have invariant := parts_indices constant index aux matching canonical
        rw [first] at invariant
        simp only [partsList, first]
        cases second : partsList rest next nextAux with
        | mk last pair =>
          cases pair with
          | mk indices finalAux =>
            have final := partsList_indices rest next nextAux invariant.1 invariant.2
            rw [second] at final
            exact final
end

end Flapjack.Compiler.Backend.ClosConstant.Proofs
