module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.PopEnvSetVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.JoinEnv

@[expose] public section

/-! Restoring a list of returned values after popping a related environment
(`data_to_wordProofScript.sml` lines 175-291). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- The relation only observes source locals through lookups. Flapjack-specific
helper: HOL rewrites `set_vars` lookups pointwise inside its proof. -/
theorem stateRel_sourceLocals_congr {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F)
    (values : Option (List (DataSem.Value × WordLocW width))) (locs : List (Nat × Nat))
    (locals : Spt DataSem.Value)
    (same : ∀ key, sptLookup key locals = sptLookup key source.locals)
    (related : stateRel conf l1 l2 source target values locs) :
    stateRel conf l1 l2 { source with locals := locals } target values locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    hzero, ?_, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
  · intro key present
    change (sptLookup key locals).isSome at present
    rw [same] at present
    exact hpresent key present
  · refine memoryRel_rearrange _ _ _ _ _ _ _ _ _ _ ?_ hmem
    intro pair member
    simp only [List.mem_append] at member ⊢
    rcases member with ((inValues | inJoin) | inGlobal) | inStack
    · exact Or.inl (Or.inl (Or.inl inValues))
    · refine Or.inl (Or.inl (Or.inr ?_))
      exact Assign.joinEnv_submap_mem locals source.locals target.locals target.locals pair
        ⟨fun key value h => by rw [← same]; exact h, fun _ _ h => h, inJoin⟩
    · exact Or.inl (Or.inr inGlobal)
    · exact Or.inr inStack

/-- Storing the last pending root in matching locals keeps the remaining
pending roots. Flapjack-specific generalization of the single-value update. -/
private theorem stateRel_setVar_pending {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (pre : List (DataSem.Value × WordLocW width)) (dest : Nat)
    (value : DataSem.Value) (word : WordLocW width)
    (related : stateRel conf l1 l2 source target (some (pre ++ [(value, word)])) locs) :
    stateRel conf l1 l2 (DataSem.setVar dest value source)
      (WordSemStateFiniteExact.setVar (adjustVar dest) word target) (some pre) locs := by
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, _, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    ?_, ?_, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, ?_⟩
  · intro h
    cases h
  · intro key hsource
    change (sptLookup key (sptInsert dest value source.locals)).isSome at hsource
    change (sptLookup (adjustVar key) (sptInsert (adjustVar dest) word target.locals)).isSome
    by_cases same : key = dest
    · subst key
      simp [sptLookup_sptInsert_same]
    · rw [sptLookup_sptInsert_ne dest key value source.locals same] at hsource
      have adjustNe : adjustVar key ≠ adjustVar dest := by
        simp only [adjustVar]
        omega
      rw [sptLookup_sptInsert_ne (adjustVar dest) (adjustVar key) word target.locals adjustNe]
      exact hpresent key hsource
  · refine memoryRel_rearrange _ _ _ _ _ _ _ _ _ _ ?_ hmem
    intro pair member
    simp only [Option.getD_some, List.mem_append] at member ⊢
    rcases member with ((inPre | inJoin) | inGlobal) | inStack
    · exact Or.inl (Or.inl (Or.inl (Or.inl inPre)))
    · rcases joinEnv_insert_subset source.locals target.locals dest value word pair inJoin with
        isNew | isOld
      · subst pair
        exact Or.inl (Or.inl (Or.inl (Or.inr (by simp))))
      · exact Or.inl (Or.inl (Or.inr isOld))
    · exact Or.inl (Or.inr inGlobal)
    · exact Or.inr inStack

/-- Storing every pending zipped root. Flapjack-specific induction for the
original proof's `alist_insert`/`ZIP` lookup argument. -/
private theorem stateRel_setVars_pending {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (locs : List (Nat × Nat)) :
    ∀ (ns : List Nat) (as : List DataSem.Value) (ws : List (WordLocW width))
      (source : DataSem.State C F) (target : WordSemStateFiniteExact width C F)
      (pre : List (DataSem.Value × WordLocW width)),
      as.length = ws.length → ns.length = as.length →
      stateRel conf l1 l2 source target (some (pre ++ as.zip ws)) locs →
      stateRel conf l1 l2 (DataSem.setVars ns as source)
        (WordSemStateFiniteExact.setVars (ns.map adjustVar) ws target) (some pre) locs := by
  intro ns
  induction ns with
  | nil =>
    intro as ws source target pre hlen hns related
    cases as with
    | cons _ _ => simp at hns
    | nil =>
      have hws : ws = [] := by cases ws <;> simp_all
      subst hws
      have h := stateRel_sourceLocals_congr conf l1 l2 source target (some pre) locs
        (sptUnion (sptFromAList []) source.locals)
        (fun key => by rw [sptLookup_sptUnion]; simp [sptFromAList])
        (by simpa using related)
      exact h
  | cons n ns ih =>
    intro as ws source target pre hlen hns related
    cases as with
    | nil => simp at hns
    | cons a as =>
      cases ws with
      | nil => simp at hlen
      | cons w ws =>
        have rest := ih as ws source target (pre ++ [(a, w)]) (by simpa using hlen)
          (by simpa using hns) (by simpa using related)
        have stepped := stateRel_setVar_pending conf l1 l2 _ _ locs pre n a w rest
        have congr := stateRel_sourceLocals_congr conf l1 l2 _ _ (some pre) locs
          (sptUnion (sptFromAList ((n :: ns).zip (a :: as))) source.locals) (fun key => by
            change sptLookup key (sptUnion (sptInsert n a (sptFromAList (ns.zip as))) source.locals) =
              sptLookup key (sptInsert n a (sptUnion (sptFromAList (ns.zip as)) source.locals))
            by_cases same : key = n
            · subst key
              rw [sptLookup_sptUnion]
              simp [sptLookup_sptInsert_same]
            · rw [sptLookup_sptUnion, sptLookup_sptInsert_ne n key a _ same,
                sptLookup_sptInsert_ne n key a _ same, sptLookup_sptUnion]) stepped
        exact congr

/-- Inserting adjusted names never changes the location slot zero. -/
private theorem sptLookup_zero_alistInsert {α : Type} :
    ∀ (ns : List Nat) (vs : List α) (t : Spt α),
      sptLookup 0 (LoopSemStateFiniteExact.sptAlistInsert (ns.map adjustVar) vs t) = sptLookup 0 t
  | [], _, _ => by simp [LoopSemStateFiniteExact.sptAlistInsert]
  | _ :: _, [], _ => by simp [LoopSemStateFiniteExact.sptAlistInsert]
  | n :: ns, v :: vs, t => by
    simp only [List.map_cons, LoopSemStateFiniteExact.sptAlistInsert]
    rw [sptLookup_sptInsert_ne (adjustVar n) 0 v _ (by simp [adjustVar])]
    exact sptLookup_zero_alistInsert ns vs t

/-- The location recorded in a related stack frame is restored by its pop.
Copy of the private location step of `state_rel_pop_env_set_var_IMP`. -/
private theorem popped_zero {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 l3 l4 : Nat)
    (source : DataSem.State C F) (target target' : WordSemStateFiniteExact width C F)
    (values : Option (List (DataSem.Value × WordLocW width))) (rest : List (Nat × Nat))
    (related : stateRel conf l1 l2 source target values ((l3,l4) :: rest))
    (pop : WordSemStateFiniteExact.popEnv target = some target') :
    sptLookup 0 target'.locals = some (.loc l3 l4) := by
  have hstack := related.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlocs := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cases ht : target.stack with
  | nil => simp [WordSemStateFiniteExact.popEnv, ht] at pop
  | cons tf ts =>
    rw [ht] at hstack hlocs
    cases hlocs with
    | cons locHead locTail =>
      cases hs : source.stack with
      | nil => simp [hs] at hstack
      | cons sf ss =>
        rw [hs] at hstack
        cases hstack with
        | cons frameRel tail =>
          cases tf with
          | stackFrame size nonGc gc handler =>
            have gcKeys : ∀ p ∈ gc, p.1 ≠ 0 := by
              cases sf <;> cases handler <;> simp_all [stackRel, stackEnvRel]
              all_goals intro a b member
              all_goals first | exact (frameRel.1 a b member).1 | exact (frameRel.1.1 a b member).1
            have gcZero : sptAListLookup 0 gc = none := by
              cases found : sptAListLookup 0 gc with
              | none => rfl
              | some value =>
                have member := sptAListLookup_mem 0 gc value found
                exact (gcKeys (0, value) member rfl).elim
            change sptAListLookup 0 nonGc = some (.loc l3 l4) at locHead
            cases handler <;> simp [WordSemStateFiniteExact.popEnv, ht] at pop
            all_goals subst target'
            all_goals simp [sptLookup_sptUnion, sptLookup_sptFromAList, gcZero, locHead]

namespace reviewedStateRelPopEnvSetVarsMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedStateRelPopEnvSetVarsMap

/-- Popping a source environment and storing a whole list of returned values
has a corresponding target pop and store preserving the complete relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "state_rel_pop_env_set_vars_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_popEnv_setVars {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (q l : Nat) (s1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (t1 : WordSemStateFiniteExact width C F)
    (as : List Flapjack.Compiler.Backend.DataSem.Value) (ws : List (WordLocW width))
    (locs : List (Nat × Nat)) (ns : List Nat) (s2 : Flapjack.Compiler.Backend.DataSem.State C F)
    (premises : stateRel c q l s1 t1 (some (as.zip ws)) locs ∧
      as.length = ws.length ∧ ns.length = as.length ∧ ns.Nodup ∧
      DataSem.popEnv s1 = some s2) :
    ∃ t2 l8 l9 ll, WordSemStateFiniteExact.popEnv t1 = some t2 ∧
      locs = (l8, l9) :: ll ∧
      stateRel c l8 l9 (DataSem.setVars ns as s2)
        (WordSemStateFiniteExact.setVars (ns.map adjustVar) ws t2) none ll := by
  obtain ⟨related, hlen, hns, _, pop⟩ := premises
  obtain ⟨t2, l8, l9, ll, tpop, locations, related2⟩ :=
    stateRel_popEnv c q l s1 s2 t1 (some (as.zip ws)) locs ⟨related, pop⟩
  have zero := popped_zero c q l l8 l9 s1 t1 t2 (some (as.zip ws)) ll
    (by simpa [locations] using related) tpop
  have stored := stateRel_setVars_pending c l8 l9 ll ns as ws s2 t2 [] hlen hns
    (by simpa using related2)
  refine ⟨t2, l8, l9, ll, tpop, locations, ?_⟩
  rcases stored with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, _, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  refine ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift, htstamp, hglobal,
    ?_, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, by simpa using hmem⟩
  intro _
  change sptLookup 0 (LoopSemStateFiniteExact.sptAlistInsert (ns.map adjustVar) ws t2.locals) =
    some (.loc l8 l9)
  rw [sptLookup_zero_alistInsert]
  exact zero

end Flapjack.Compiler.Backend.DataToWord.Proofs
