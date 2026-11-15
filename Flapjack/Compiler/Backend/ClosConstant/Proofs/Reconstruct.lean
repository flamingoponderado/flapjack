module

public import Flapjack.Compiler.Backend.ClosConstant.Proofs.Bounds
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Nodup

@[expose] public section

/-! Memory invariants for reconstructing flattened constants. -/
namespace Flapjack.Compiler.Backend.ClosConstant.Proofs
open Flapjack.Compiler.Backend.ClosLang

/-- Interpret all allocated parts in their allocation order. -/
def builtMemory (aux : List (ConstPart × Nat)) : Nat → Const :=
  buildMap (fun _ => .constInt 0) 0 (aux.reverse.map Prod.fst)

/-- Adding an accumulator entry appends one operation to the built memory. -/
theorem builtMemory_cons (part : ConstPart) (index : Nat) (aux : List (ConstPart × Nat)) :
    builtMemory ((part, index) :: aux) =
      fun key => if key = aux.length then buildPartSyntax (builtMemory aux) part else builtMemory aux key := by
  simp [builtMemory, List.reverse_cons, List.map_append, buildMap_append, buildMap]

/-- A part whose references lie below a boundary is insensitive to memory changes above it. -/
theorem buildPartSyntax_congr_below (part : ConstPart) (first second : Nat → Const) (bound : Nat)
    (same : ∀ index, index < bound → first index = second index)
    (dependencies : ∀ tag children, part = .con tag children → ∀ index ∈ children, index < bound) :
    buildPartSyntax first part = buildPartSyntax second part := by
  cases part with
  | int n => rfl
  | str s => rfl
  | w64 w => rfl
  | con tag children =>
    simp only [buildPartSyntax, Const.constCons.injEq, true_and]
    apply List.map_congr_left
    intro index member
    exact same index (dependencies tag children rfl index member)

/-- Each allocated part agrees with its interpretation in the final memory. -/
def entriesBuilt (aux : List (ConstPart × Nat)) : Prop :=
  ∀ part index, (part, index) ∈ aux → builtMemory aux index = buildPartSyntax (builtMemory aux) part

/-- Extending an ordered accumulator preserves all previously built parts. -/
theorem entriesBuilt_cons (part : ConstPart) (aux : List (ConstPart × Nat))
    (bounded : indicesBelow aux.length aux) (ordered : dependenciesBelow aux)
    (built : entriesBuilt aux)
    (newDependencies : ∀ tag children, part = .con tag children →
      ∀ index ∈ children, index < aux.length) :
    entriesBuilt ((part, aux.length) :: aux) := by
  intro other index member
  have same : ∀ key, key < aux.length →
      builtMemory ((part, aux.length) :: aux) key = builtMemory aux key := by
    intro key keyBound
    rw [builtMemory_cons]
    simp [show key ≠ aux.length by omega]
  rcases List.mem_cons.mp member with equal | member
  · cases equal
    calc
      builtMemory ((part, aux.length) :: aux) aux.length = buildPartSyntax (builtMemory aux) part := by
        rw [builtMemory_cons]
        simp
      _ = buildPartSyntax (builtMemory ((part, aux.length) :: aux)) part :=
        (buildPartSyntax_congr_below part _ _ aux.length same newDependencies).symm
  · have indexBound := bounded (other, index) member
    rw [same index indexBound, built other index member]
    apply (buildPartSyntax_congr_below other _ _ aux.length same ?_).symm
    intro tag children equal child childMem
    subst other
    exact Nat.lt_trans (ordered tag children index member child childMem) indexBound

/-- Canonical allocation indices bound every entry. This Flapjack helper
connects the HOL accumulator invariant to the reconstruction proof. -/
theorem canonicalIndices_bounds (aux : List (ConstPart × Nat))
    (canonical : canonicalIndices aux) : indicesBelow aux.length aux := by
  intro entry member
  have found : entry.2 ∈ aux.map Prod.snd := List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [canonical] at found
  simpa using found

/-- The canonical and dependency invariants imply the memory invariant used
by Flapjack's reconstruction proof. -/
theorem entriesBuilt_of_canonical (aux : List (ConstPart × Nat))
    (canonical : canonicalIndices aux) (ordered : dependenciesBelow aux) : entriesBuilt aux := by
  induction aux with
  | nil => simp [entriesBuilt]
  | cons head tail ih =>
    obtain ⟨part, index⟩ := head
    have canonParts : index = tail.length ∧ canonicalIndices tail := by
      simp only [canonicalIndices, List.map_cons, List.length_cons, List.range_succ,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.cons.injEq] at canonical
      exact canonical
    obtain ⟨rfl, tailCanonical⟩ := canonParts
    have tailOrdered : dependenciesBelow tail := by
      intro tag children idx mem child childMem
      exact ordered tag children idx (List.mem_cons_of_mem _ mem) child childMem
    have built := ih tailCanonical tailOrdered
    apply entriesBuilt_cons part tail (canonicalIndices_bounds tail tailCanonical) tailOrdered built
    intro tag children partEq child childMem
    subst part
    exact ordered tag children tail.length (by simp) child childMem

/-- Later allocations cannot change an index in an existing accumulator. -/
theorem builtMemory_suffix (added aux : List (ConstPart × Nat)) (key : Nat)
    (earlier : key < aux.length) : builtMemory (added ++ aux) key = builtMemory aux key := by
  simp only [builtMemory, List.reverse_append, List.map_append, buildMap_append,
    List.length_map, List.length_reverse, Nat.zero_add]
  exact buildMap_ignore _ _ _ _ earlier

/-- Allocation returns the meaning of the requested part and preserves the
memory invariant, whether the part is new or shared. -/
theorem makePart_built (index : Nat) (part : ConstPart) (aux : List (ConstPart × Nat))
    (matching : index = aux.length) (bounded : indicesBelow index aux)
    (ordered : dependenciesBelow aux) (built : entriesBuilt aux)
    (children : ∀ tag children, part = .con tag children → ∀ child ∈ children, child < index) :
    let (_, found, result) := makePart index part aux
    builtMemory result found = buildPartSyntax (builtMemory aux) part ∧ entriesBuilt result := by
  subst index
  unfold makePart
  cases lookup : lookupPart part aux with
  | some found => exact ⟨built part found (lookupPart_mem part aux found lookup), built⟩
  | none =>
    constructor
    · rw [builtMemory_cons]
      simp
    · exact entriesBuilt_cons part aux bounded ordered built children

mutual
/-- Every index returned by flattening reconstructs the original constant. -/
theorem parts_reconstruct (constant : Const) (index : Nat) (aux : List (ConstPart × Nat))
    (matching : index = aux.length) (canonical : canonicalIndices aux)
    (bounded : indicesBelow index aux) (ordered : dependenciesBelow aux) (built : entriesBuilt aux) :
    let (_, found, result) := parts constant index aux
    builtMemory result found = constant ∧ entriesBuilt result := by
  cases constant with
  | constInt n =>
    simpa [parts, buildPartSyntax] using makePart_built index (.int n) aux matching bounded ordered built (by simp)
  | constStr text =>
    simpa [parts, buildPartSyntax] using makePart_built index (.str text) aux matching bounded ordered built (by simp)
  | constWord64 word =>
    simpa [parts, buildPartSyntax] using makePart_built index (.w64 word) aux matching bounded ordered built (by simp)
  | constCons tag constants =>
    cases first : partsList constants index aux with
    | mk next pair =>
      cases pair with
      | mk indices nextAux =>
        have inductionResult := partsList_reconstruct constants index aux matching canonical bounded ordered built
        have bounds := partsList_bounds constants index aux bounded
        have indexes := partsList_indices constants index aux matching canonical
        have nextOrdered := partsList_dependencies constants index aux bounded ordered
        rw [first] at inductionResult bounds indexes nextOrdered
        have out := makePart_built next (.con tag indices) nextAux indexes.1 bounds.2.2 nextOrdered inductionResult.2 (by
          intro t children eq child mem
          cases eq
          exact bounds.2.1 child mem)
        simp only [parts, first]
        simpa [buildPartSyntax, inductionResult.1] using out

/-- Returned indices reconstruct a flattened list in source order. -/
theorem partsList_reconstruct (constants : List Const) (index : Nat) (aux : List (ConstPart × Nat))
    (matching : index = aux.length) (canonical : canonicalIndices aux)
    (bounded : indicesBelow index aux) (ordered : dependenciesBelow aux) (built : entriesBuilt aux) :
    let (_, found, result) := partsList constants index aux
    found.map (builtMemory result) = constants ∧ entriesBuilt result := by
  cases constants with
  | nil => exact ⟨rfl, built⟩
  | cons constant rest =>
    cases first : parts constant index aux with
    | mk next pair =>
      cases pair with
      | mk found nextAux =>
        have inductionResult := parts_reconstruct constant index aux matching canonical bounded ordered built
        have bounds := parts_bounds constant index aux bounded
        have nextOrdered := parts_dependencies constant index aux bounded ordered
        have indexes := parts_indices constant index aux matching canonical
        rw [first] at inductionResult bounds nextOrdered indexes
        cases second : partsList rest next nextAux with
        | mk last pair =>
          cases pair with
          | mk indices finalAux =>
            have restRec := partsList_reconstruct rest next nextAux indexes.1 indexes.2 bounds.2.2 nextOrdered inductionResult.2
            rw [second] at restRec
            obtain ⟨added, suffix⟩ := partsList_suffix rest next nextAux
            rw [second] at suffix
            change finalAux = added ++ nextAux at suffix
            have unchanged : builtMemory finalAux found = builtMemory nextAux found := by
              rw [suffix]
              apply builtMemory_suffix
              omega
            simp only [partsList, first, second, List.map_cons]
            exact ⟨by rw [unchanged, inductionResult.1, restRec.1], restRec.2⟩
end

/-- A functional list relation is equality with the mapped list. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "LIST_REL_eq"]
theorem listRel_eq {α β : Type} (f : β → α) (xs : List α) (ys : List β) :
    List.Forall₂ (fun x y => f y = x) xs ys ↔ xs = ys.map f := by
  have h := List.forall₂_map_right_iff (R := (· = ·)) (f := f) (l := xs) (u := ys)
  rw [List.forall₂_eq_eq_eq] at h
  constructor
  · intro rel
    apply h.mpr
    exact rel.imp (fun _ _ eq => eq.symm)
  · intro eq
    exact (h.mp eq).imp (fun _ _ eq => eq.symm)

/-- Flattening constants and lists preserves the complete HOL accumulator
invariants and reconstructs each original constant. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "parts_thm"]
theorem partsFull :
    (∀ (c : Const) (n : Nat) (aux : List (ConstPart × Nat)) (m r : Nat)
      (res : List (ConstPart × Nat)),
      parts c n aux = (m, r, res) ∧ (aux.map Prod.snd).Nodup ∧ consesOk aux ∧
        n = aux.length ∧ aux.all (fun p => decide (p.2 < n)) = true →
      (buildMap (fun _ => .constInt 0) 0 (res.reverse.map Prod.fst)) r = c ∧ n ≤ m ∧ r < m ∧ (res.map Prod.snd).Nodup ∧
        consesOk res ∧ m = res.length ∧ res.all (fun p => decide (p.2 < m)) = true) ∧
    (∀ (cs : List Const) (n : Nat) (aux : List (ConstPart × Nat)) (m : Nat)
      (rs : List Nat) (res : List (ConstPart × Nat)),
      partsList cs n aux = (m, rs, res) ∧ (aux.map Prod.snd).Nodup ∧ consesOk aux ∧
        n = aux.length ∧ aux.all (fun p => decide (p.2 < n)) = true →
      List.Forall₂ (fun c r => (buildMap (fun _ => .constInt 0) 0 (res.reverse.map Prod.fst)) r = c) cs rs ∧ n ≤ m ∧
        (res.map Prod.snd).Nodup ∧ rs.all (fun k => decide (k < m)) = true ∧
        consesOk res ∧ m = res.length ∧ res.all (fun p => decide (p.2 < m)) = true) := by
  constructor
  · intro c n aux m r res ⟨run, distinct, ok, matching, allBound⟩
    obtain ⟨canonical, ordered⟩ := (consesOk_iff aux).1 ok
    have bounded : indicesBelow n aux := by
      intro entry mem
      simpa using (List.all_eq_true.mp allBound entry mem)
    have built := entriesBuilt_of_canonical aux canonical ordered
    have reconstruction := parts_reconstruct c n aux matching canonical bounded ordered built
    have bounds := parts_bounds c n aux bounded
    have orderedResult := parts_dependencies c n aux bounded ordered
    have canonicalResult := parts_indices c n aux matching canonical
    rw [run] at reconstruction bounds orderedResult canonicalResult
    refine ⟨reconstruction.1, bounds.1, bounds.2.1, ?_, ?_, canonicalResult.1, ?_⟩
    · rw [canonicalResult.2]
      exact List.nodup_reverse.mpr List.nodup_range
    · exact (consesOk_iff res).2 ⟨canonicalResult.2, orderedResult⟩
    · apply List.all_eq_true.mpr
      intro entry mem
      simpa using bounds.2.2 entry mem
  · intro cs n aux m rs res ⟨run, distinct, ok, matching, allBound⟩
    obtain ⟨canonical, ordered⟩ := (consesOk_iff aux).1 ok
    have bounded : indicesBelow n aux := by
      intro entry mem
      simpa using (List.all_eq_true.mp allBound entry mem)
    have built := entriesBuilt_of_canonical aux canonical ordered
    have reconstruction := partsList_reconstruct cs n aux matching canonical bounded ordered built
    have bounds := partsList_bounds cs n aux bounded
    have orderedResult := partsList_dependencies cs n aux bounded ordered
    have canonicalResult := partsList_indices cs n aux matching canonical
    rw [run] at reconstruction bounds orderedResult canonicalResult
    refine ⟨?_, bounds.1, ?_, ?_, ?_, canonicalResult.1, ?_⟩
    · exact (listRel_eq _ cs rs).2 reconstruction.1.symm
    · rw [canonicalResult.2]
      exact List.nodup_reverse.mpr List.nodup_range
    · apply List.all_eq_true.mpr
      intro entry mem
      simpa using bounds.2.1 entry mem
    · exact (consesOk_iff res).2 ⟨canonicalResult.2, orderedResult⟩
    · apply List.all_eq_true.mpr
      intro entry mem
      simpa using bounds.2.2 entry mem

/-- Flattening and rebuilding a constant recovers the original syntax tree. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "build_const_to_parts"]
theorem buildConst_toParts (constant : Const) : buildConstSyntax (toParts constant) = constant := by
  cases constant with
  | constInt n => simp [toParts, buildConstSyntax, buildSyntax, buildPartSyntax]
  | constStr text => simp [toParts, buildConstSyntax, buildSyntax, buildPartSyntax]
  | constWord64 word => simp [toParts, buildConstSyntax, buildSyntax, buildPartSyntax]
  | constCons tag constants =>
    cases first : partsList constants 0 [] with
    | mk next pair =>
      cases pair with
      | mk indices aux =>
        have reconstructed := partsList_reconstruct constants 0 [] rfl (by simp [canonicalIndices])
          (by simp [indicesBelow]) (by simp [dependenciesBelow]) (by simp [entriesBuilt])
        rw [first] at reconstructed
        simp only [toParts, first, List.reverse_cons, buildConstSyntax, buildSyntax_append_one,
          Nat.zero_add, buildSyntax, buildPartSyntax]
        simp only [List.length_reverse, List.length_map]
        simp only [Nat.add_sub_cancel, ↓reduceIte, ← List.map_reverse]
        change Const.constCons tag (indices.map (builtMemory aux)) = Const.constCons tag constants
        rw [reconstructed.1]

/-- Interpreting a constant agrees with interpreting its flattened parts. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "make_const_thm"]
theorem makeConst_toParts (constant : Const) :
    ClosSem.makeConst constant = buildConst (toParts constant) := by
  calc
    ClosSem.makeConst constant = ClosSem.makeConst (buildConstSyntax (toParts constant)) :=
      congrArg ClosSem.makeConst (buildConst_toParts constant).symm
    _ = buildConst (toParts constant) := by
      simpa [buildConstSyntax, buildConst, ClosSem.makeConst] using
        makeConst_buildSyntax (toParts constant) (fun _ => .constInt 0) 0

end Flapjack.Compiler.Backend.ClosConstant.Proofs
