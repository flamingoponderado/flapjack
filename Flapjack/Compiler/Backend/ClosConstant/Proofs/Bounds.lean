module

public import Flapjack.Compiler.Backend.ClosConstant.Proofs.Flatten
public import Flapjack.Misc.ListEl

@[expose] public section

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

/-- Accumulator indices follow allocation order, and constructor parts refer
only to earlier entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "conses_ok_def"]
noncomputable def consesOk (aux : List (ConstPart × Nat)) : Prop :=
  (∀ n, n < aux.length → ∃ p,
    @Flapjack.holEl (ConstPart × Nat) ⟨(.int 0, 0)⟩ n aux.reverse = (p, n)) ∧
  ∀ tag children child index,
    (.con tag children, index) ∈ aux ∧ child ∈ children → child < index

/-- HOL's bounded indexing invariant is equivalent to the canonical index
and dependency invariants used by the reconstruction proof. -/
theorem consesOk_iff (aux : List (ConstPart × Nat)) :
    consesOk aux ↔ canonicalIndices aux ∧ dependenciesBelow aux := by
  letI : Nonempty (ConstPart × Nat) := ⟨(.int 0, 0)⟩
  have indexEquiv : (∀ n, n < aux.length → ∃ p,
      @Flapjack.holEl (ConstPart × Nat) ⟨(.int 0, 0)⟩ n aux.reverse = (p, n)) ↔
      canonicalIndices aux := by
    constructor
    · intro h
      have mapped : aux.reverse.map Prod.snd = List.range aux.length := by
        apply List.ext_getElem (by simp)
        intro i hi _
        have bound : i < aux.reverse.length := by simpa using hi
        obtain ⟨p, hp⟩ := h i (by simpa using bound)
        rw [Flapjack.holEl_eq_getElem i aux.reverse bound] at hp
        simpa using congrArg Prod.snd hp
      unfold canonicalIndices
      have reversed := congrArg List.reverse mapped
      simpa using reversed
    · intro canonical n hn
      have mapped : aux.reverse.map Prod.snd = List.range aux.length := by
        have h := congrArg List.reverse canonical
        simpa [canonicalIndices] using h
      have bound : n < aux.reverse.length := by simpa using hn
      refine ⟨aux.reverse[n].1, ?_⟩
      rw [Flapjack.holEl_eq_getElem n aux.reverse bound]
      apply Prod.ext
      · rfl
      · have h := congrArg (fun xs : List Nat => xs[n]?) mapped
        simpa [List.getElem?_eq_getElem bound, hn] using h
  simp only [consesOk, indexEquiv, dependenciesBelow]
  constructor
  · rintro ⟨indices, h⟩
    exact ⟨indices, fun tag children index mem child childMem => h tag children child index ⟨mem, childMem⟩⟩
  · rintro ⟨indices, h⟩
    exact ⟨indices, fun tag children child index hs => h tag children index hs.1 child hs.2⟩

/-- Appending the next allocation preserves the accumulator invariant when
the new constructor's children refer to earlier entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "IMP_conses_ok_CONS"]
theorem consesOk_cons (x : ConstPart) (aux : List (ConstPart × Nat))
    (children : ∀ tag rs, x = .con tag rs → rs.all (fun m => decide (m < aux.length)) = true)
    (ok : consesOk aux) : consesOk ((x, aux.length) :: aux) := by
  obtain ⟨canonical, ordered⟩ := (consesOk_iff aux).1 ok
  apply (consesOk_iff _).2
  constructor
  · simp only [canonicalIndices, List.map_cons, List.length_cons, List.range_succ,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [canonical]
    rfl
  · intro tag rs index member child childMem
    rcases List.mem_cons.mp member with equal | member
    · have partEq : x = .con tag rs := congrArg Prod.fst equal.symm
      have indexEq : aux.length = index := congrArg Prod.snd equal.symm
      subst index
      have allChildren := children tag rs partEq
      simpa using (List.all_eq_true.mp allChildren child childMem)
    · exact ordered tag rs index member child childMem

/-- A successful association-list lookup in a valid accumulator gives the
original allocation position, list decomposition, and dependency bound. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "ALOOKUP_conses_ok_IMP"]
theorem lookupConses (aux : List (ConstPart × Nat)) (x : ConstPart) (r : Nat)
    (premises : lookupPart x aux = some r ∧ consesOk aux) :
    ∃ xs ys : List (ConstPart × Nat),
      aux.reverse.map Prod.fst = xs.reverse.map Prod.fst ++ [x] ++ ys.reverse.map Prod.fst ∧
      xs.length = r ∧ r < aux.length ∧
      ∀ t children y, x = .con t children ∧ y ∈ children → y < r := by
  induction aux generalizing r with
  | nil => simp [lookupPart] at premises
  | cons head tail ih =>
    obtain ⟨p, i⟩ := head
    obtain ⟨found, ok⟩ := premises
    obtain ⟨canonical, ordered⟩ := (consesOk_iff _).1 ok
    have canonParts : i = tail.length ∧ canonicalIndices tail := by
      simp only [canonicalIndices, List.map_cons, List.length_cons, List.range_succ,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.cons.injEq] at canonical
      exact canonical
    obtain ⟨rfl, tailCanonical⟩ := canonParts
    have tailOrdered : dependenciesBelow tail := by
      intro tag children index member child childMem
      exact ordered tag children index (List.mem_cons_of_mem _ member) child childMem
    have tailOk := (consesOk_iff tail).2 ⟨tailCanonical, tailOrdered⟩
    simp only [lookupPart] at found
    split at found
    · rename_i equal
      simp only [Option.some.injEq] at found
      subst r
      subst p
      refine ⟨tail, [], ?_, rfl, by simp, ?_⟩
      · simp
      · intro tag children child ⟨partEq, member⟩
        subst x
        exact ordered tag children tail.length (by simp) child member
    · obtain ⟨xs, ys, sequence, length, bound, dependencies⟩ := ih r ⟨found, tailOk⟩
      refine ⟨xs, (p, tail.length) :: ys, ?_, length, by simpa using Nat.lt_succ_of_lt bound, dependencies⟩
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
      rw [sequence]
      simp only [List.append_assoc]

end Flapjack.Compiler.Backend.ClosConstant.Proofs
