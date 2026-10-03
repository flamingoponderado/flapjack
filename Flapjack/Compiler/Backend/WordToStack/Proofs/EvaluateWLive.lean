import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocStateRel
import Flapjack.Compiler.Backend.WordToStack.NativeLive
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWrite
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapInsert
import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapAppend
import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedKeys
import Flapjack.Compiler.Backend.WordToStack.Proofs.KeyValueOrder
import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexListLemmas
import Flapjack.Basis.Pure.MlList.SortPerm
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef

/-!
# Word-to-Stack `evaluate_wLive`

Running the `wLive` frame header (`word_to_stackProofScript.sml:1339-1598`)
pushes the live variables' frame: afterwards the target relates both to the
source state with the cut environment pushed (frame sizes `0`) and to the
unchanged source state.
-/

namespace Flapjack.WordToStackProofs.EvaluateWLive
open Flapjack.StackSem Flapjack.Compiler.Encoders.Asm Flapjack.WordSemStateFiniteExact
  Flapjack.Compiler.Backend.WordToStack Flapjack.Compiler.Backend.WordToStack.Native

/-- Canonical source-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Canonical target-state relation codec re-export; no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Inhabitation of the source frame carrier for total HOL `EL`, as in `stackRelAux`. -/
local instance {width : Nat} [NeZero width] : Nonempty (WordSemStackFrame width) :=
  ⟨.stackFrame none [] [] none⟩

theorem listRearrange_id {α : Type} (xs : List α) : wordSemListRearrange id xs = xs := by
  unfold wordSemListRearrange
  split
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  · rfl

theorem envToList_fst {width : Nat} [NeZero width] (env : Spt (WordLocW width))
    (p : Nat → Nat → Nat) (hp : p 0 = id) :
    (wordSemEnvToList env p).1 =
      Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList env) := by
  simp only [wordSemEnvToList, hp, listRearrange_id]

theorem holSorted_chain {α : Type} (R : α → α → Prop) :
    ∀ l : List α, holSorted R l → List.IsChain R l
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | _ :: y :: rest, h => List.IsChain.cons_cons h.1 (holSorted_chain R (y :: rest) h.2)

/-- The `env_to_list` list of an environment has strictly descending keys. -/
theorem sortEnv_pairwise {width : Nat} [NeZero width] (env : Spt (WordLocW width)) :
    (Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList env)).Pairwise
      (fun a b => a.1 > b.1) := by
  have hs := Basis.Pure.MlList.sortSorted wordSemKeyValCompare (sptToAList env)
    ⟨fun x y z h => transitiveKeyValCompare x y z h.1 h.2,
     fun x y => totalKeyValCompare x y⟩
  have hc := holSorted_chain _ _ hs
  have : Trans (fun a b : Nat × WordLocW width => wordSemKeyValCompare a b = true)
      (fun a b => wordSemKeyValCompare a b = true)
      (fun a b => wordSemKeyValCompare a b = true) :=
    ⟨fun hab hbc => transitiveKeyValCompare _ _ _ hab hbc⟩
  have hp := hc.pairwise
  have hperm := (holPerm_iff _ _).mp (Basis.Pure.MlList.sortPerm wordSemKeyValCompare
    (sptToAList env))
  have hnd : ((Basis.Pure.MlList.sort wordSemKeyValCompare (sptToAList env)).map
      Prod.fst).Nodup := (hperm.map Prod.fst).nodup_iff.mp (sptAllDistinctMapFstToAList env)
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hnd
  refine (hp.and hnd).imp ?_
  rintro ⟨a, va⟩ ⟨b, vb⟩ ⟨hab, hne⟩
  simp only at hne ⊢
  simp only [wordSemKeyValCompare, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    hne, false_and, or_false] at hab
  exact hab

theorem descendingKeys_of_pairwise {α : Type} :
    ∀ xs : List (Nat × α), xs.Pairwise (fun a b => a.1 > b.1) → descendingKeys xs
  | [], _ => by simp [descendingKeys]
  | [_], _ => by simp [descendingKeys]
  | x :: y :: rest, h => by
      have hxy : x.1 > y.1 := List.rel_of_pairwise_cons h (by simp)
      have ih := descendingKeys_of_pairwise (y :: rest) h.of_cons
      simp only [descendingKeys, List.tail_cons, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
      exact ⟨hxy, ih⟩

theorem indexList_pairwise {α : Type} (k : Nat) :
    ∀ xs : List α, (indexList xs k).Pairwise (fun a b => a.1 > b.1)
  | [] => by simp [indexList]
  | x :: xs => by
      simp only [indexList, List.pairwise_cons]
      refine ⟨?_, indexList_pairwise k xs⟩
      intro a ha
      have := memIndexListLim xs a.1 a.2 k ha
      have hk : k ≤ a.1 := by
        obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
        have hil : i < xs.length := by simpa only [lengthIndexList] using hi
        rw [elIndexList xs i k hil] at he
        rw [← he]; simp only; omega
      omega

/-- The bitmap written by `wLive` selects exactly the spilled GC-live variables
from the indexed frame, in `env_to_list` order. Flapjack helper isolating the
`filter_bitmap` conjunct of HOL `evaluate_wLive`'s pushed `stack_rel_aux`; no
separate HOL original. -/
theorem wLiveFilterBitmap {width : Nat} [NeZero width] (k f' : Nat) (names2 : Spt Unit)
    (locals : Spt (WordLocW width)) (perm : Nat → Nat → Nat) (frame : List (WordLocW width))
    (hperm : perm 0 = id)
    (hsub : ∀ r, sptDomain names2 r → (sptLookup r locals).isSome)
    (hsnd : ∀ x, sptDomain names2 x → x % 2 = 0 ∧ k ≤ x / 2)
    (hframe : frame.length = f')
    (hloc : ∀ n v, sptLookup n locals = some v → n % 2 = 0 → k ≤ n / 2 →
      n / 2 < k + f' ∧ frame[f' - 1 - (n / 2 - k)]? = some v) :
    filterBitmap ((List.range f').map (fun x => decide
        (x ∈ (sptToAList names2).map (fun (r, _) => f' - 1 - (r / 2 - k)))))
      (indexList frame k) =
      some ((wordSemEnvToList (sptInter locals names2) perm).1.map
        (fun p => (adjustNames p.1, p.2)), []) := by
  set bits := (List.range f').map (fun x => decide
    (x ∈ (sptToAList names2).map (fun (r, _) => f' - 1 - (r / 2 - k)))) with hbits
  have hbl : bits.length = f' := by simp [bits]
  have hil : (indexList frame k).length = f' := by rw [lengthIndexList, hframe]
  -- entries of the cut environment
  have henv : ∀ r v, (r, v) ∈ (wordSemEnvToList (sptInter locals names2) perm).1 ↔
      sptLookup r locals = some v ∧ sptDomain names2 r := by
    intro r v
    rw [wordSemEnvToList_mem_iff, sptToAList_mem_iff_lookup, sptLookup_sptInterCases]
    unfold sptDomain
    cases sptLookup r locals <;> cases sptLookup r names2 <;> simp
  apply filterBitmapEqSomeNil bits (indexList frame k) _ (by rw [hbl, hil])
  apply sortedImpEqLists
  · -- the selected entries have descending keys
    apply descendingKeys_of_pairwise
    rw [List.pairwise_map]
    apply List.Pairwise.sublist List.filter_sublist
    have hz : ((indexList frame k).zip bits).map Prod.fst = indexList frame k :=
      List.map_fst_zip (by rw [hbl, hil])
    have := indexList_pairwise k frame
    rw [← hz, List.pairwise_map] at this
    exact this
  · -- the env_to_list entries have descending even keys, so their halves descend
    apply descendingKeys_of_pairwise
    rw [envToList_fst _ _ hperm, List.pairwise_map]
    refine (sortEnv_pairwise (sptInter locals names2)).imp_of_mem ?_
    rintro ⟨a, va⟩ ⟨b, vb⟩ ha hb hab
    rw [← envToList_fst _ perm hperm] at ha hb
    have ea := hsnd a ((henv a va).mp ha).2
    have eb := hsnd b ((henv b vb).mp hb).2
    simp only [adjustNames] at hab ⊢
    omega
  · rintro ⟨j, v⟩
    simp only [List.mem_map, List.mem_filter, Prod.exists]
    constructor
    · rintro ⟨j', v', b, ⟨hzip, hb⟩, hjv⟩
      simp only [Prod.mk.injEq] at hjv
      obtain ⟨rfl, rfl⟩ := hjv
      subst hb
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hzip
      rw [List.getElem_zip] at hget
      simp only [Prod.mk.injEq] at hget
      obtain ⟨hidx, hbit⟩ := hget
      have hif : i < f' := by simp [hbl, hil] at hi; omega
      rw [elIndexList frame i k (by omega)] at hidx
      simp only [Prod.mk.injEq] at hidx
      obtain ⟨hj, hv⟩ := hidx
      simp only [bits, List.getElem_map, List.getElem_range, decide_eq_true_eq, List.mem_map,
        Prod.exists] at hbit
      obtain ⟨r, u, hru, hri⟩ := hbit
      have hdom : sptDomain names2 r := by
        unfold sptDomain; rw [(sptToAList_mem_iff_lookup names2 r u).mp hru]; rfl
      obtain ⟨heven, hk⟩ := hsnd r hdom
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hsub r hdom)
      obtain ⟨hlt, hfr⟩ := hloc r w hw heven hk
      rw [hri] at hfr
      have hfi : frame[i]'(by omega) = w := (List.getElem?_eq_some_iff.mp hfr).2
      refine ⟨r, w, (henv r w).mpr ⟨hw, hdom⟩, ?_⟩
      simp only [Prod.mk.injEq, adjustNames]
      refine ⟨by omega, ?_⟩
      rw [← hv, hfi]
    · rintro ⟨r, v', hmem, hj⟩
      simp only [Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      obtain ⟨hlk, hdom⟩ := (henv r v').mp hmem
      obtain ⟨heven, hk⟩ := hsnd r hdom
      obtain ⟨hlt, hfr⟩ := hloc r v' hlk heven hk
      have hi : f' - 1 - (r / 2 - k) < f' := by omega
      have hfi : frame[f' - 1 - (r / 2 - k)]'(by omega) = v' :=
        (List.getElem?_eq_some_iff.mp hfr).2
      refine ⟨r / 2, v', true, ⟨?_, rfl⟩, rfl⟩
      refine List.mem_iff_getElem.mpr ⟨f' - 1 - (r / 2 - k), by simp [hbl, hil]; omega, ?_⟩
      rw [List.getElem_zip]
      congr 1
      · rw [elIndexList frame _ k (by omega), hfi]
        congr 1
        omega
      · simp only [bits, List.getElem_map, List.getElem_range, decide_eq_true_eq, List.mem_map,
          Prod.exists]
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hdom
        exact ⟨r, u, (sptToAList_mem_iff_lookup names2 r u).mpr hu, rfl⟩

end Flapjack.WordToStackProofs.EvaluateWLive
