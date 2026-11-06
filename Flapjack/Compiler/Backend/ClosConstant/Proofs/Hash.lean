import Flapjack.Compiler.Backend.ClosConstant.Proofs.Flatten

/-! Correspondence between association-list and hash-consed constants. -/
namespace Flapjack.Compiler.Backend.ClosConstant.Proofs
open Flapjack.Compiler.Backend.ClosLang
open Flapjack.Compiler.Backend.ClosToBvl

/-- A hash table returns exactly the entries in the source association list. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "good_hash_table_def"]
def goodHashTable (tree : Spt (List (ConstPart × Nat))) (aux : List (ConstPart × Nat)) : Prop :=
  ∀ key value, lookupPart key aux = some value ↔
    ∃ bucket, sptLookup (partHash (updateTag key)) tree = some bucket ∧
      ClosToBvl.lookupPart (updateTag key) bucket = some value

/-- Lookup equivalence, in the option form convenient for executable code. -/
theorem goodHashTable_lookup {tree : Spt (List (ConstPart × Nat))} {aux : List (ConstPart × Nat)}
    (good : goodHashTable tree aux) (key : ConstPart) :
    lookupPart key aux = (sptLookup (partHash (updateTag key)) tree).bind (ClosToBvl.lookupPart (updateTag key)) := by
  cases source : lookupPart key aux with
  | none =>
    cases bucket : sptLookup (partHash (updateTag key)) tree with
    | none => rfl
    | some contents =>
      cases result : ClosToBvl.lookupPart (updateTag key) contents with
      | none => simp [result]
      | some value =>
        have contradiction := (good key value).2 ⟨contents, bucket, result⟩
        simp [source] at contradiction
  | some value =>
    cases bucket : sptLookup (partHash (updateTag key)) tree with
    | none =>
      obtain ⟨contents, found, _⟩ := (good key value).1 source
      simp [bucket] at found
    | some contents =>
      obtain ⟨other, found, result⟩ := (good key value).1 source
      rw [bucket] at found
      cases found
      simp [result]

/-- Option lookup equivalence implies the source-shaped hash invariant. -/
theorem goodHashTable_of_lookup (tree : Spt (List (ConstPart × Nat))) (aux : List (ConstPart × Nat))
    (agree : ∀ key, lookupPart key aux =
      (sptLookup (partHash (updateTag key)) tree).bind (ClosToBvl.lookupPart (updateTag key))) :
    goodHashTable tree aux := by
  intro key value
  rw [agree key]
  cases h : sptLookup (partHash (updateTag key)) tree with
  | none => simp
  | some bucket => simp

/-- Adding a part to its hash bucket preserves lookup equivalence, including
hash collisions and repeated parts. -/
theorem goodHashTable_insert (tree : Spt (List (ConstPart × Nat))) (aux : List (ConstPart × Nat))
    (part : ConstPart) (index : Nat) (good : goodHashTable tree aux) :
    goodHashTable
      (sptInsert (partHash (updateTag part))
        ((updateTag part, index) :: (sptLookup (partHash (updateTag part)) tree).getD []) tree)
      ((part, index) :: aux) := by
  apply goodHashTable_of_lookup
  intro key
  by_cases same : key = part
  · subst key
    simp [lookupPart, ClosToBvl.lookupPart, sptLookup_sptInsert_same]
  · have shifted : updateTag key ≠ updateTag part := by
      intro eq
      exact same ((updateTag_eq_iff _ _).1 eq)
    by_cases hashEq : partHash (updateTag key) = partHash (updateTag part)
    · have old := goodHashTable_lookup good key
      rw [hashEq] at old
      simp only [lookupPart, if_neg same]
      rw [hashEq, sptLookup_sptInsert_same]
      cases bucket : sptLookup (partHash (updateTag part)) tree <;>
        simp_all [ClosToBvl.lookupPart]
    · simp only [lookupPart, if_neg same]
      rw [sptLookup_sptInsert_ne _ _ _ _ hashEq]
      exact goodHashTable_lookup good key

/-- One hash-consed insertion has the same result as the association-list
model and maintains the hash invariant. -/
theorem addPart_related (index : Nat) (part : ConstPart) (tree : Spt (List (ConstPart × Nat)))
    (aux : List (ConstPart × Nat)) (good : goodHashTable tree aux) :
    let (n1, r1, tree1, acc1) := addPart index (updateTag part) tree (aux.map (updateTag ∘ Prod.fst))
    let (n2, r2, aux2) := makePart index part aux
    n1 = n2 ∧ r1 = r2 ∧ aux2.map (updateTag ∘ Prod.fst) = acc1 ∧ goodHashTable tree1 aux2 := by
  have agree := goodHashTable_lookup good part
  cases bucket : sptLookup (partHash (updateTag part)) tree with
  | none =>
    have sourceNone : lookupPart part aux = none := by simpa [bucket] using agree
    have nextGood := goodHashTable_insert tree aux part index good
    simpa [addPart, makePart, bucket, sourceNone] using nextGood
  | some entries =>
    cases entry : ClosToBvl.lookupPart (updateTag part) entries with
    | none =>
      have sourceNone : lookupPart part aux = none := by simpa [bucket, entry] using agree
      have nextGood := goodHashTable_insert tree aux part index good
      simpa [addPart, makePart, bucket, entry, sourceNone] using nextGood
    | some old =>
      have sourceSome : lookupPart part aux = some old := by simpa [bucket, entry] using agree
      simp [addPart, makePart, bucket, entry, sourceSome, good]

/-- The hash-consed and association-list insertion steps agree. -/
@[hol "cakeml/compiler/backend/proofs/clos_constantProofScript.sml" "add_part_thm"]
theorem addPart_thm (index : Nat) (part : ConstPart) (tree : Spt (List (ConstPart × Nat)))
    (aux : List (ConstPart × Nat)) (n1 r1 : Nat) (tree1 : Spt (List (ConstPart × Nat)))
    (acc1 : List ConstPart) (n2 r2 : Nat) (aux1 : List (ConstPart × Nat))
    (targetRun : addPart index (updateTag part) tree (aux.map (updateTag ∘ Prod.fst)) =
      (n1, r1, tree1, acc1))
    (sourceRun : makePart index part aux = (n2, r2, aux1)) (good : goodHashTable tree aux) :
    n1 = n2 ∧ r1 = r2 ∧ aux1.map (updateTag ∘ Prod.fst) = acc1 ∧ goodHashTable tree1 aux1 := by
  have result := addPart_related index part tree aux good
  rw [targetRun, sourceRun] at result
  exact result

end Flapjack.Compiler.Backend.ClosConstant.Proofs
