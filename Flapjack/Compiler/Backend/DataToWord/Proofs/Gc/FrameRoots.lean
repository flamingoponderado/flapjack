import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeSoundness
import Flapjack.Misc.Sptree.ToList
import Flapjack.Misc.Sptree.ToAList

/-! Relating paired stack-frame roots to source environment traversal. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack
local instance : Nonempty DataSem.Value := ⟨.number 0⟩

/-- Flapjack infrastructure: the source sparse-tree value traversal prepends
its collected values to any supplied accumulator. -/
theorem sptToListA_append {α : Type} (tree : Spt α) (acc : List α) :
    sptToListA acc tree = sptToList tree ++ acc := by
  change sptToListA acc tree = sptToListA [] tree ++ acc
  induction tree generalizing acc with
  | ln => rfl
  | ls value => rfl
  | bn left right ihl ihr =>
    simp only [sptToListA]
    rw [ihl (sptToListA acc right), ihl (sptToListA [] right), ihr acc]
    simp [List.append_assoc]
  | bs left value right ihl ihr =>
    simp only [sptToListA]
    rw [ihl (value :: sptToListA acc right), ihl (value :: sptToListA [] right), ihr acc]
    simp [List.append_assoc]

/-- Flapjack infrastructure: forgetting keys in the exact sparse-tree
association traversal preserves the multiset of source values. -/
theorem sptFoldi_values_perm {α : Type} (tree : Spt α) (index : Nat) (acc : List (Nat × α)) :
    ((sptFoldi (fun k v entries => (k, v) :: entries) index acc tree).map Prod.snd).Perm
      (sptToList tree ++ acc.map Prod.snd) := by
  induction tree generalizing index acc with
  | ln => simp [sptFoldi, sptToList, sptToListA]
  | ls value => simp [sptFoldi, sptToList, sptToListA]
  | bn left right ihl ihr =>
    simp only [sptFoldi]
    apply (ihr _ _).trans
    apply (List.Perm.append_left _ (ihl _ _)).trans
    change (sptToList right ++ (sptToList left ++ acc.map Prod.snd)).Perm
      (sptToListA (sptToListA [] right) left ++ acc.map Prod.snd)
    rw [sptToListA_append]
    change (sptToList right ++ (sptToList left ++ acc.map Prod.snd)).Perm
      ((sptToList left ++ sptToList right) ++ acc.map Prod.snd)
    simp only [List.append_assoc]
    have swapped : (sptToList right ++ sptToList left).Perm (sptToList left ++ sptToList right) :=
      List.perm_append_comm
    simpa only [List.append_assoc] using swapped.append_right (acc.map Prod.snd)
  | bs left value right ihl ihr =>
    simp only [sptFoldi]
    apply (ihr _ _).trans
    apply (List.Perm.append_left _ ((ihl _ _).cons value)).trans
    change (sptToList right ++ value :: (sptToList left ++ acc.map Prod.snd)).Perm
      (sptToListA (value :: sptToListA [] right) left ++ acc.map Prod.snd)
    rw [sptToListA_append]
    change (sptToList right ++ value :: (sptToList left ++ acc.map Prod.snd)).Perm
      ((sptToList left ++ value :: sptToList right) ++ acc.map Prod.snd)
    simp only [List.append_assoc]
    have swapped : (sptToList right ++ value :: sptToList left).Perm
        ((value :: sptToList left) ++ sptToList right) := List.perm_append_comm
    have rearranged : ((value :: sptToList left) ++ sptToList right).Perm
        (sptToList left ++ value :: sptToList right) := by
      simpa using List.perm_cons_append_cons value (List.Perm.refl (sptToList left ++ sptToList right))
    simpa only [List.append_assoc, List.cons_append] using (swapped.trans rearranged).append_right (acc.map Prod.snd)


/-- Flapjack infrastructure: `toAList` and `toList` enumerate the same values
with multiplicity, though their traversal orders differ. -/
theorem sptToAList_values_perm {α : Type} (tree : Spt α) :
    ((sptToAList tree).map Prod.snd).Perm (sptToList tree) := by
  simpa [sptToAList] using sptFoldi_values_perm tree 0 []

/-- Flapjack infrastructure: distinct keys imply distinct keyed pairs. -/
theorem pairList_nodup_of_keys {α β : Type} (pairs : List (α × β))
    (unique : (pairs.map Prod.fst).Nodup) : pairs.Nodup := by
  induction pairs with
  | nil => exact List.nodup_nil
  | cons pair rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique ⊢
    exact ⟨fun member => unique.1 (List.mem_map.mpr ⟨pair, member, rfl⟩), ih unique.2⟩

/-- Flapjack infrastructure: rebuilding keyed entries from any duplicate-free
enumeration of a sparse-tree domain preserves the tree's association list. -/
theorem sptToAList_perm_of_keys {α : Type} [Nonempty α] (tree : Spt α) (keys : List Nat)
    (unique : keys.Nodup)
    (domain : ∀ key, key ∈ keys ↔ (sptLookup key tree).isSome = true) :
    (keys.map fun key => (key, holThe (sptLookup key tree))).Perm (sptToAList tree) := by
  have keyMap : (keys.map fun key => (key, holThe (sptLookup key tree))).map Prod.fst = keys := by
    rw [List.map_map]
    change keys.map (fun k => k) = keys
    exact List.map_id keys
  have leftUnique := pairList_nodup_of_keys _ (by rw [keyMap]; exact unique)
  have rightUnique := pairList_nodup_of_keys _ (sptAllDistinctMapFstToAList tree)
  apply (List.perm_ext_iff_of_nodup leftUnique rightUnique).mpr
  intro pair
  obtain ⟨key, value⟩ := pair
  constructor
  · intro member
    obtain ⟨k, present, equal⟩ := List.mem_map.mp member
    have same : k = key := congrArg Prod.fst equal
    subst k
    have existsValue := Option.isSome_iff_exists.mp ((domain key).mp present)
    obtain ⟨foundValue, lookup⟩ := existsValue
    have valueEq : foundValue = value := by simpa [lookup, holThe] using congrArg Prod.snd equal
    subst value
    exact (sptMemToAList tree key foundValue).mpr lookup
  · intro member
    have lookup := (sptMemToAList tree key value).mp member
    apply List.mem_map.mpr
    refine ⟨key, (domain key).mpr ?_, ?_⟩
    · simp [lookup]
    · simp [lookup, holThe]

/-- Flapjack infrastructure: a nonzero even machine variable is the adjusted
form of its decoded source variable. -/
theorem adjustVar_decode (key : Nat) (valid : key ≠ 0 ∧ key % 2 = 0) :
    DataToWord.adjustVar ((key - 2) / 2) = key := by
  simp only [DataToWord.adjustVar]
  omega

/-- Flapjack infrastructure: decoding distinct live word-frame keys retains
uniqueness when those keys are nonzero and even. -/
theorem decodedFrameKeys_nodup {β : Type} (entries : List (Nat × β))
    (valid : ∀ pair ∈ entries, pair.1 ≠ 0 ∧ pair.1 % 2 = 0)
    (unique : (entries.map Prod.fst).Nodup) :
    (entries.map fun pair => (pair.1 - 2) / 2).Nodup := by
  induction entries with
  | nil => simp
  | cons pair rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique ⊢
    refine ⟨?_, ih (fun p member => valid p (List.mem_cons_of_mem _ member)) unique.2⟩
    intro member
    obtain ⟨other, otherMem, equal⟩ := List.mem_map.mp member
    have firstValid := valid pair (by simp)
    have otherValid := valid other (by simp [otherMem])
    have keyEq : other.1 = pair.1 := by
      have both := congrArg DataToWord.adjustVar equal
      simpa [adjustVar_decode other.1 otherValid, adjustVar_decode pair.1 firstValid] using both
    exact unique.1 (List.mem_map.mpr ⟨other, otherMem, keyEq⟩)

/-- Flapjack infrastructure: decoding live word-frame names enumerates exactly
the source environment domain under the frame relation. -/
theorem decodedFrameKeys_domain {width : Nat} [NeZero width]
    (env : Spt DataSem.Value) (dataSize wordSize : Option Nat)
    (nonGc gc : List (Nat × WordLocW width)) (related : stackEnvRel dataSize wordSize env nonGc gc) :
    ∀ key, key ∈ gc.map (fun pair => (pair.1 - 2) / 2) ↔ (sptLookup key env).isSome = true := by
  intro key
  have targetDomain : ∀ n, (sptLookup (DataToWord.adjustVar n) (sptFromAList gc)).isSome = true ↔
      DataToWord.adjustVar n ∈ gc.map Prod.fst := by
    intro n
    change sptDomain (sptFromAList gc) (DataToWord.adjustVar n) ↔ _
    rw [sptDomainFromAList]
  rw [related.2.2.2.2 key, targetDomain key]
  constructor
  · intro member
    obtain ⟨pair, inGc, decoded⟩ := List.mem_map.mp member
    have valid := related.1 pair inGc
    have original := adjustVar_decode pair.1 valid
    apply List.mem_map.mpr
    exact ⟨pair, inGc, by rw [← decoded, original]⟩
  · intro member
    obtain ⟨pair, inGc, keyEq⟩ := List.mem_map.mp member
    apply List.mem_map.mpr
    refine ⟨pair, inGc, ?_⟩
    rw [keyEq]
    simp [DataToWord.adjustVar]

/-- Flapjack infrastructure: a related frame's paired source roots enumerate
the same multiset as the source sparse environment. -/
theorem joinEnv_values_perm {width : Nat} [NeZero width]
    (env : Spt DataSem.Value) (dataSize wordSize : Option Nat)
    (nonGc gc : List (Nat × WordLocW width)) (related : stackEnvRel dataSize wordSize env nonGc gc) :
    (joinEnv env gc).map Prod.fst |>.Perm (sptToList env) := by
  let keys := gc.map fun pair => (pair.1 - 2) / 2
  have unique : keys.Nodup := decodedFrameKeys_nodup gc related.1 related.2.2.2.1
  have domain := decodedFrameKeys_domain env dataSize wordSize nonGc gc related
  have entries := sptToAList_perm_of_keys env keys unique domain
  have values := (entries.map Prod.snd).trans (sptToAList_values_perm env)
  have filterEq : gc.filter (fun pair => pair.1 ≠ 0 ∧ pair.1 % 2 = 0) = gc := by
    apply List.filter_eq_self.mpr
    intro pair member
    simp [related.1 pair member]
  have same : (joinEnv env gc).map Prod.fst =
      (keys.map fun key => (key, holThe (sptLookup key env))).map Prod.snd := by
    simp only [joinEnv, filterEq, List.map_map, keys]
    rfl
  rw [same]
  exact values

/-- Flapjack infrastructure: flattening paired stacks preserves the
multiplicity of every value extracted from source frames. -/
theorem flatStack_values_perm {width : Nat} [NeZero width]
    (source : List DataSem.Stack) (target : List (WordSemStackFrame width))
    (related : List.Forall₂ stackRel source target) :
    ((flatStack source target).map Prod.fst).Perm (source.flatMap DataSem.extractStack) := by
  induction related with
  | nil => simp [flatStack]
  | @cons frame wordFrame frames wordFrames frameRel restRel ih =>
    cases frame with
    | env dataSize env =>
      rcases wordFrame with ⟨wordSize, nonGc, gc, handler⟩
      cases handler with
      | none =>
        have envRel : stackEnvRel dataSize wordSize env nonGc gc := frameRel
        simpa [flatStack, DataSem.extractStack] using
          (joinEnv_values_perm env dataSize wordSize nonGc gc envRel).append ih
      | some handler => simp [stackRel] at frameRel
    | exc dataSize env handler =>
      rcases wordFrame with ⟨wordSize, nonGc, gc, wordHandler⟩
      cases wordHandler with
      | none => simp [stackRel] at frameRel
      | some info =>
        rcases info with ⟨loc, x, y⟩
        have envRel : stackEnvRel dataSize wordSize env nonGc gc := frameRel.1
        simpa [flatStack, DataSem.extractStack] using
          (joinEnv_values_perm env dataSize wordSize nonGc gc envRel).append ih

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
