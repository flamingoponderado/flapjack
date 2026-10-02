import Flapjack.Compiler.Backend.Semantics.WordSem.Env
import Mathlib.Data.List.Induction
import Lean.Elab.Tactic.Omega

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Flapjack infrastructure for observing the actual even-key insertion fold.
No HOL declaration is claimed for this intermediate accumulator fact. -/
private theorem foldIndex {α : Type} (ls : List α) (start : Nat) (t : Spt α) :
    (ls.foldl (fun (acc : Nat × Spt α) a => (acc.1+2, sptInsert acc.1 a acc.2))
      (start,t)).1 = start + 2*ls.length := by
  induction ls generalizing start t with
  | nil => simp
  | cons a ls ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    omega

/-- Flapjack infrastructure: optional observations of the native tagged fold,
including odd keys and indices past the list. No total EL default is used. -/
private theorem fromList2Lookup {α : Type} (ls : List α) (n : Nat) :
    sptLookup n (sptFromList2 ls) = if n%2=0 then ls[n/2]? else none := by
  induction ls using List.reverseRecOn with
  | nil => simp [sptFromList2]
  | append_singleton ls a ih =>
    have hf : sptFromList2 (ls ++ [a]) = sptInsert (2*ls.length) a (sptFromList2 ls) := by
      simp only [sptFromList2, List.foldl_append, List.foldl_cons, List.foldl_nil,
        foldIndex, Nat.zero_add]
    rw [hf]
    by_cases he : n = 2*ls.length
    · subst n
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne _ _ _ _ he, ih]
      by_cases hp : n%2=0
      · have hn : n/2 ≠ ls.length := by omega
        by_cases hb : n/2 < ls.length
        · simp [hp, List.getElem?_append, hb]
        · have hz : n/2-ls.length ≠ 0 := by omega
          simp [hp, List.getElem?_append, hb, hz]
      · simp [hp]

/-- Flapjack infrastructure for the complete optional observation of a
successful native read. No source index bound is assumed. -/
private theorem readAt {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (ns : List Nat) (xs : List (WordLocW width))
    (h : WordSemStateFiniteExact.getVars ns s = some xs) (i : Nat) :
    xs[i]? = (ns[i]?).bind (fun n => getVar n s) := by
  induction ns generalizing xs i with
  | nil => simp [WordSemStateFiniteExact.getVars] at h; subst xs; simp
  | cons n ns ih =>
    cases hv : getVar n s with
    | none => simp [WordSemStateFiniteExact.getVars, hv] at h
    | some v =>
      cases ht : WordSemStateFiniteExact.getVars ns s with
      | none => simp [WordSemStateFiniteExact.getVars, hv, ht] at h
      | some vs =>
        simp only [WordSemStateFiniteExact.getVars, hv, ht, Option.some.injEq] at h
        subst xs
        cases i with
        | zero => simp [hv]
        | succ i => simpa using ih vs ht i

namespace CallLocalRecoveryWitnesses
/-- Roundtrip for the imported native carrier; no duplicate state is declared. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : WordSemStateBroad width C F) (h : s.FiniteSupport),
      (WordSemStateBroad.ofBroad s h).toBroad = s) ∧
    (∀ s : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad s.toBroad s.toBroad_finiteSupport = s) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end CallLocalRecoveryWitnesses
open CallLocalRecoveryWitnesses

/-- Full original caller-local recovery after native even-key argument binding.
The values and valid index are derived from the two original successes. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_vars_fromList2_eq"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarsFromList2Eq {width : Nat} [NeZero width] {C F A : Type}
    (args : List A) (s : WordSemStateFiniteExact width C F)
    (xs : List (WordLocW width)) (n : Nat) (y : WordLocW width)
    (hg : WordSemStateFiniteExact.getVars ((List.range args.length).map (fun i => 2*i)) s = some xs)
    (hl : sptLookup n (sptFromList2 xs) = some y) :
    sptLookup n s.locals = some y := by
  rw [fromList2Lookup] at hl
  split at hl
  next hp =>
    have hr := readAt s _ xs hg (n/2)
    have hb : n/2 < args.length := by
      by_contra hn
      simp [hn] at hr
      have ho : xs[n/2]? = none := List.getElem?_eq_none_iff.mpr hr
      rw [ho] at hl
      contradiction
    have he : 2*(n/2) = n := by omega
    simpa [List.getElem?_map, List.getElem?_range, hb, he, getVar] using hr.symm.trans hl
  next => contradiction

/-- Full original return-local recovery. Key zero is reserved for the Loc;
the sole original nonzero guard derives the shifted source index. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "get_vars_fromList2_eq_cons"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarsFromList2EqCons {width : Nat} [NeZero width] {C F A : Type}
    (args : List A) (s : WordSemStateFiniteExact width C F)
    (xs : List (WordLocW width)) (n x3 x4 : Nat) (y : WordLocW width)
    (hg : WordSemStateFiniteExact.getVars ((List.range args.length).map (fun i => 2*(i+1))) s = some xs)
    (hl : sptLookup n (sptFromList2 (.loc x3 x4 :: xs)) = some y) (hn : n ≠ 0) :
    sptLookup n s.locals = some y := by
  rw [fromList2Lookup] at hl
  split at hl
  next hp =>
    have hd : 0 < n/2 := by omega
    have he : n/2 = (n/2-1)+1 := by omega
    rw [he, List.getElem?_cons_succ] at hl
    have hr := readAt s _ xs hg (n/2-1)
    have hb : n/2-1 < args.length := by
      by_contra hn
      simp [hn] at hr
      have ho : xs[n/2-1]? = none := List.getElem?_eq_none_iff.mpr hr
      rw [ho] at hl
      contradiction
    have hk : 2*((n/2-1)+1) = n := by omega
    simpa [List.getElem?_map, List.getElem?_range, hb, hk, getVar] using hr.symm.trans hl
  next => contradiction

/-- Full original prefix lookup preservation, over arbitrary list payloads.
HOL IS_PREFIX z x means x is a prefix of z (its argument order is reversed
from lowercase isPREFIX), represented by the same List.IsPrefix relation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "lookup_fromList2_prefix"]
theorem lookupFromList2Prefix {α : Type} (x z : List α) (n : Nat) (y : α)
    (hp : x.IsPrefix z) (hl : sptLookup n (sptFromList2 x) = some y) :
    sptLookup n (sptFromList2 z) = some y := by
  rcases hp with ⟨tail, rfl⟩
  rw [fromList2Lookup] at hl ⊢
  split at hl
  next he =>
    have hb : n/2 < x.length := by
      by_contra hn
      have ho : x[n/2]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      rw [ho] at hl
      contradiction
    simpa [he, List.getElem?_append, hb] using hl
  next => contradiction

end Flapjack.WordToStackProofs
