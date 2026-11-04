import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CallEnv
import Flapjack.Compiler.Backend.DataToWord.Proofs.JoinEnv
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack

/-! Live-environment cuts for saving caller frames. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A successful source cut establishes the corresponding source-domain
subset. -/
theorem cutEnv_source_subset (live : NumSet) (locals saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live locals = some saved) :
    ∀ n, sptMem n live → sptMem n locals := by
  unfold DataSem.cutEnv at cut
  split at cut
  · assumption
  · contradiction

/-- If the data cut succeeds in related states, the actual word cut succeeds
and produces the two expected intersections. -/
theorem stateRel64_cutEnvs {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved) :
    wordSemCutEnvs (adjustSets live) target.locals =
      some (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) := by
  have sourceSub := cutEnv_source_subset live source.locals saved cut
  have zero : sptLookup 0 target.locals = some (.loc l1 l2) := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  have zeroSub : LoopSemStateFiniteExact.sptSubsetLive (.ls ()) target.locals := by
    intro key member
    have isZero : key = 0 := by
      by_contra neq
      simp [sptMem_iff_lookup, sptLookup, neq] at member
    subst key
    exact (sptMem_iff_lookup 0 target.locals).mpr ⟨_, zero⟩
  have liveSub : LoopSemStateFiniteExact.sptSubsetLive (adjustSet live) target.locals := by
    intro key member
    obtain ⟨n, equal, liveMem⟩ := (adjustSet_domain live key).mp member
    subst key
    have localMem := sourceSub n liveMem
    obtain ⟨v, found⟩ := (sptMem_iff_lookup n source.locals).mp localMem
    have present := related.2.2.2.2.2.2.2.2.2.2.2.1 n (by simp [found])
    exact (sptMem_iff_lookup (adjustVar n) target.locals).mpr (Option.isSome_iff_exists.mp present)
  simp [wordSemCutEnvs, wordSemCutNames, adjustSets, zeroSub, liveSub]

/-- A successful source cut is the normalized intersection of locals and
live names. -/
theorem cutEnv_saved_eq (live : NumSet) (locals saved : Spt DataSem.Value)
    (cut : DataSem.cutEnv live locals = some saved) : saved = sptMkWf (sptInter locals live) := by
  unfold DataSem.cutEnv at cut
  split at cut
  · simpa using cut.symm
  · contradiction

/-- The source saved environment and adjusted word cut have identical live
name domains. -/
theorem stateRel64_cutEnv_lookup {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved)
    (n : Nat) :
    (sptLookup n saved).isSome = true ↔
      (sptLookup (adjustVar n) (sptInter target.locals (adjustSet live))).isSome = true := by
  have sourceSub := cutEnv_source_subset live source.locals saved cut
  have presence := related.2.2.2.2.2.2.2.2.2.2.2.1
  rw [cutEnv_saved_eq live source.locals saved cut, sptLookup_mkWf, sptLookup_sptInterCases,
    sptLookup_sptInterCases, lookup_adjustVar_adjustSet]
  cases sourceLookup : sptLookup n source.locals with
  | none =>
    cases liveLookup : sptLookup n live with
    | none => simp
    | some payload =>
      have memLive : sptMem n live := (sptMem_iff_lookup n live).mpr ⟨payload, liveLookup⟩
      obtain ⟨v, found⟩ := (sptMem_iff_lookup n source.locals).mp (sourceSub n memLive)
      simp [sourceLookup] at found
  | some value =>
    have wordPresent := presence n (by simp [sourceLookup])
    cases targetLookup : sptLookup (adjustVar n) target.locals with
    | none => simp [targetLookup] at wordPresent
    | some word => cases liveLookup : sptLookup n live <;> simp

/-- The two cut environments, after the word evaluator's actual ordering and
permutation, satisfy the saved-frame relation. -/
theorem stateRel64_cutEnv_stackEnvRel {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved) :
    stackEnvRel source.localsSize target.localsSize saved
      (sptToAList (sptInter target.locals (.ls ())))
      (wordSemEnvToList (sptInter target.locals (adjustSet live)) target.permute).1 := by
  let nonGc := sptInter target.locals (.ls ())
  let gc := sptInter target.locals (adjustSet live)
  have equivalent := wordSemEnvToListLookupEquiv gc target.permute
    (wordSemEnvToList gc target.permute).1 (wordSemEnvToList gc target.permute).2 (by simp)
  refine ⟨?_, related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm, ?_, envToListAllDistinctFst gc target.permute, ?_⟩
  · intro ⟨key, value⟩ member
    have found := equivalent.2 key value member
    have domain : sptDomain gc key := (sptMem_iff_lookup key gc).mpr ⟨value, found⟩
    have adjusted : sptDomain (adjustSet live) key := by
      have both : sptDomain target.locals key ∧ sptDomain (adjustSet live) key := by
        simpa [gc, sptDomain_sptInter] using domain
      exact both.2
    obtain ⟨n, rfl, _⟩ := (adjustSet_domain live key).mp adjusted
    simp [adjustVar]
  · intro ⟨key, value⟩ member
    have found := (sptMemToAList nonGc key value).mp member
    have domain : sptDomain nonGc key := (sptMem_iff_lookup key nonGc).mpr ⟨value, found⟩
    have inZero : sptDomain (.ls ()) key := by
      have both : sptDomain target.locals key ∧ sptDomain (.ls ()) key := by
        simpa [nonGc, sptDomain_sptInter] using domain
      exact both.2
    by_contra neq
    simp [sptDomain, sptLookup, neq] at inZero
  · intro n
    rw [sptLookup_sptFromAList, equivalent.1]
    exact stateRel64_cutEnv_lookup conf l1 l2 source target locs related live saved cut n

/-- The saved non-GC part retains the caller return location at local zero. -/
theorem stateRel64_cutEnv_containsLoc {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved)
    (size : Option Nat) (handler : Option (Nat × Nat × Nat)) :
    containsLoc (.stackFrame size (sptToAList (sptInter target.locals (.ls ())))
      (wordSemEnvToList (sptInter target.locals (adjustSet live)) target.permute).1 handler) (l1, l2) := by
  have _ := stateRel64_cutEnvs conf l1 l2 source target locs related live saved cut
  have zero := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  change sptAListLookup 0 (sptToAList (sptInter target.locals (.ls ()))) = some (.loc l1 l2)
  rw [← sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList, sptLookup_sptInterCases]
  simp [sptLookup, zero]

/-- Every root saved in the word GC cut was already a joined root before the
source environment was cut. -/
theorem stateRel64_cutEnv_roots {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved) :
    joinEnv saved (wordSemEnvToList (sptInter target.locals (adjustSet live)) target.permute).1 ⊆
      joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) := by
  let gc := sptInter target.locals (adjustSet live)
  have equivalent := wordSemEnvToListLookupEquiv gc target.permute
    (wordSemEnvToList gc target.permute).1 (wordSemEnvToList gc target.permute).2 (by simp)
  intro ⟨value, word⟩ member
  obtain ⟨⟨key, w⟩, filtered, eq⟩ := List.mem_map.mp member
  obtain ⟨entry, _⟩ := List.mem_filter.mp filtered
  have found := equivalent.2 key w entry
  have domain : sptDomain gc key := (sptMem_iff_lookup key gc).mpr ⟨w, found⟩
  have adjusted : sptDomain (adjustSet live) key := by
    have both : sptDomain target.locals key ∧ sptDomain (adjustSet live) key := by
      simpa [gc, sptDomain_sptInter] using domain
    exact both.2
  obtain ⟨n, equal, _⟩ := (adjustSet_domain live key).mp adjusted
  subst key
  have savedPresent : (sptLookup n saved).isSome = true :=
    (stateRel64_cutEnv_lookup conf l1 l2 source target locs related live saved cut n).mpr (by simp [gc, found])
  obtain ⟨v, savedLookup⟩ := Option.isSome_iff_exists.mp savedPresent
  have sourceLookup := Flapjack.Compiler.Backend.DataToWord.Proofs.cutEnv_lookup_retained live source.locals saved cut n v savedLookup
  have targetLookup : sptLookup (adjustVar n) target.locals = some w := by
    rw [show gc = sptInter target.locals (adjustSet live) from rfl, sptLookup_sptInterCases] at found
    cases t : sptLookup (adjustVar n) target.locals <;>
      cases l : sptLookup (adjustVar n) (adjustSet live) <;> simp_all
  simp only [Prod.mk.injEq] at eq
  have valueEq : v = value := by simpa [adjustVar, savedLookup, holThe] using eq.1
  have wordEq : w = word := eq.2
  exact localPair_mem_joinEnv source.locals target.locals n value word (by simpa [valueEq] using sourceLookup)
    (by simpa [wordEq] using targetLookup)

/-- Pushing either kind of caller frame preserves pairwise stack and saved
location relations, and every saved stack root was already represented. -/
theorem stateRel64_pushEnv_stacks {C F : Type} (conf : Config) (l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (live : NumSet) (saved : Spt DataSem.Value) (cut : DataSem.cutEnv live source.locals = some saved)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    let sourceNext := DataSem.pushEnv saved handler.isSome source
    let targetNext := WordSemStateFiniteExact.pushEnv
      (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) handler target
    List.Forall₂ stackRel sourceNext.stack targetNext.stack ∧
    List.Forall₂ containsLoc targetNext.stack ((l1, l2) :: locs) ∧
    wordSemStackSize targetNext.stack = DataSem.sizeOfStack sourceNext.stack ∧
    flatStack sourceNext.stack targetNext.stack ⊆
      joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
        flatStack source.stack target.stack := by
  have frame := stateRel64_cutEnv_stackEnvRel conf l1 l2 source target locs related live saved cut
  have contains := stateRel64_cutEnv_containsLoc conf l1 l2 source target locs related live saved cut
    target.localsSize (handler.map fun (_, _, a, b) => (target.handler, a, b))
  have roots := stateRel64_cutEnv_roots conf l1 l2 source target locs related live saved cut
  have stack := related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have locations := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have handlerEq := related.2.2.1
  cases handler with
  | none =>
    have newStack : List.Forall₂ stackRel
        (DataSem.pushEnv saved false source).stack
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) none target).stack := by
      apply List.Forall₂.cons
      · exact frame
      · exact stack
    refine ⟨newStack, ?_, stackRel_sizeOfStack newStack, ?_⟩
    · simpa [DataSem.pushEnv, WordSemStateFiniteExact.pushEnv] using List.Forall₂.cons contains locations
    · intro pair member
      change pair ∈ joinEnv saved (wordSemEnvToList (sptInter target.locals (adjustSet live)) target.permute).1 ++
        flatStack source.stack target.stack at member
      simp only [List.mem_append] at member ⊢
      exact member.elim (fun root => Or.inl (roots root)) Or.inr
  | some info =>
    obtain ⟨name, body, a, b⟩ := info
    have newStack : List.Forall₂ stackRel
        (DataSem.pushEnv saved true source).stack
        (WordSemStateFiniteExact.pushEnv (sptInter target.locals (.ls ()), sptInter target.locals (adjustSet live)) (some (name, body, a, b)) target).stack := by
      apply List.Forall₂.cons
      · exact ⟨frame, handlerEq⟩
      · exact stack
    refine ⟨newStack, ?_, stackRel_sizeOfStack newStack, ?_⟩
    · simpa [DataSem.pushEnv, WordSemStateFiniteExact.pushEnv] using List.Forall₂.cons contains locations
    · intro pair member
      change pair ∈ joinEnv saved (wordSemEnvToList (sptInter target.locals (adjustSet live)) target.permute).1 ++
        flatStack source.stack target.stack at member
      simp only [List.mem_append] at member ⊢
      exact member.elim (fun root => Or.inl (roots root)) Or.inr

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
