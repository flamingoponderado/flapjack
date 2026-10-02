import Flapjack.Compiler.Backend.WordToStack.Proofs.IndexListLemmas
import Flapjack.Misc.Sptree

namespace Flapjack.WordToStackProofs
open Flapjack

/-- Full original zip reconstruction over arbitrary values and base offset. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "index_list_eq_ZIP"]
theorem indexListEqZip {α : Type} (xs : List α) (k : Nat) :
    indexList xs k = (((List.range xs.length).map (fun n => k + n)).reverse).zip xs := by
  exact List.zip_of_prod (mapFstIndexList xs k) (mapSndIndexList xs k)

/-- Full original index-list membership implies the source position limit. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MEM_index_list_LIM"]
theorem memIndexListLim {α : Type} (ls : List α) (n : Nat) (v : α) (k : Nat)
    (h : (n,v) ∈ indexList ls k) : n - k < ls.length := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  have hil : i < ls.length := by simpa only [lengthIndexList] using hi
  rw [elIndexList2 ls i k hil] at he
  have hk := congrArg Prod.fst he
  change k + ls.length - (i+1) = n at hk
  omega

/-- Full original membership recovery. The total EL access is valid as a
consequence of the original membership premise; its bound is derived here,
not added as a hypothesis or obtained from a default element. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MEM_index_list_EL"]
theorem memIndexListEl {α : Type} (ls : List α) (n : Nat) (v : α) (k : Nat)
    (h : (n,v) ∈ indexList ls k) :
    ls[ls.length - (n-k+1)]'(by have := memIndexListLim ls n v k h; omega) = v := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  have hil : i < ls.length := by simpa only [lengthIndexList] using hi
  rw [elIndexList2 ls i k hil] at he
  have hk := congrArg Prod.fst he
  change k + ls.length - (i+1) = n at hk
  have heq : ls.length - (n-k+1) = i := by omega
  simpa only [heq] using congrArg Prod.snd he

/-- Full original first-match lookup law. Its original upper-key guard allows
keys below the base k: those cases yield NONE on both sides. No lower bound,
lookup success, or range premise is added. HOL LLOOKUP is the native optional
getElem? operation, including out-of-range NONE. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_index_list"]
theorem aLookupIndexList {α : Type} (ls : List α) (n k : Nat)
    (h : n < ls.length + k) :
    sptAListLookup n (indexList ls k) = ls[(ls.length+k)-(n+1)]? := by
  induction ls generalizing n with
  | nil => simp [indexList, sptAListLookup]
  | cons x xs ih =>
    by_cases he : n = k + xs.length
    · subst n
      have hz : xs.length + 1 + k - (k + xs.length + 1) = 0 := by omega
      simp [indexList, sptAListLookup, hz]
    · have hn : n < xs.length + k := by simp only [List.length_cons] at h; omega
      simp only [indexList, sptAListLookup, if_neg he, List.length_cons]
      rw [ih n hn]
      have heq : xs.length + 1 + k - (n+1) = xs.length + k - (n+1) + 1 := by omega
      rw [heq]
      rfl

end Flapjack.WordToStackProofs
