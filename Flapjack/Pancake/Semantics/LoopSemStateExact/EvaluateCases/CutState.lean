import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.Ffi
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.Semantics.LoopProps.UnassignedVarsExact

/-!
# Exact/production `cutState` / `cutLoopState` correspondence

Flapjack-specific bridge infrastructure (no `@[hol]` tag): it relates the exact
HOL-shaped `cutState` guard/restriction on `LoopSemStateFiniteExact` to the
production `cutLoopState` on `LoopMachineState` under `prodRel`, so the
`hcutNone`/`hcutSome` premises of
`Flapjack.LoopSemStateFiniteExact.EvaluateCases.evaluateFfi_prodRel` become
dischargeable by applying the theorem below.  It discharges the
`cutState`/`cutLoopState` half of bead `flapjack-pxn.18.5.6.30.4.1.2.2.24`;
the executed-hook refinement half remains open there.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- HOL `sptree$list_to_num_set` membership: a key is in the set built from a
    list iff it occurs in the list.  (The same lemma is `private` in
    `CallPreserveStateCodeLocalsRel.lean`; reproved here to keep this probe
    self-contained.) -/
theorem listToNumSetHOLExact_mem_iff (key : Nat) (keys : List Nat) :
    sptMem key (listToNumSetHOLExact keys) ↔ key ∈ keys := by
  induction keys with
  | nil => simp [listToNumSetHOLExact, sptMem, sptDomain]
  | cons head tail ih =>
      rw [listToNumSetHOLExact_cons, sptMem_sptInsert, ih]
      simp

/-- `sptMem` is the `isSome` characterisation of the spt lookup. -/
theorem sptMem_iff_isSome {α : Type} (key : Nat) (tree : Spt α) :
    sptMem key tree ↔ (sptLookup key tree).isSome = true := by
  rw [sptMem_iff_lookup]
  exact Option.isSome_iff_exists.symm

/-- The executable `loopLiveLocalsPresent` guard is exactly "every live name is
    present in the production local map". -/
theorem loopLiveLocalsPresent_iff {W : Type}
    (locals : Nat → Option (LoopValue W)) (live : List Nat) :
    loopLiveLocalsPresent locals live ↔
      ∀ name, name ∈ live → (locals name).isSome := by
  induction live with
  | nil => simp [loopLiveLocalsPresent]
  | cons head tail ih =>
      simp only [loopLiveLocalsPresent, List.mem_cons, Bool.and_eq_true]
      rw [ih]
      constructor
      · rintro ⟨hhead, htail⟩ name (rfl | hmem)
        · exact hhead
        · exact htail name hmem
      · intro h
        exact ⟨h head (Or.inl rfl), fun name hmem => h name (Or.inr hmem)⟩

/-- Under `prodRel`, the exact `sptSubsetLive` guard on the
    `listToNumSetHOLExact live` set coincides with the production
    `loopLiveLocalsPresent` guard on `live`. -/
theorem sptSubsetLive_iff_loopLiveLocalsPresent {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hlocals : ∀ name,
      machine.locals name = (sptLookup name state.locals).map loopValueOfWordLocW)
    (live : List Nat) :
    sptSubsetLive (listToNumSetHOLExact live) state.locals ↔
      loopLiveLocalsPresent machine.locals live := by
  rw [loopLiveLocalsPresent_iff]
  have hsome : ∀ name, (machine.locals name).isSome =
      (sptLookup name state.locals).isSome := by
    intro name
    rw [hlocals name, Option.isSome_map]
  constructor
  · intro h name hmem
    have hk : sptMem name (listToNumSetHOLExact live) :=
      (listToNumSetHOLExact_mem_iff name live).mpr hmem
    have hs : sptMem name state.locals := h name hk
    have hs' : (sptLookup name state.locals).isSome = true :=
      (sptMem_iff_isSome name state.locals).mp hs
    rw [hsome name]
    exact hs'
  · intro h key hk
    have hmem : key ∈ live := (listToNumSetHOLExact_mem_iff key live).mp hk
    have hs : (machine.locals key).isSome = true := h key hmem
    have hs' : (sptLookup key state.locals).isSome = true := by
      rwa [hsome key] at hs
    exact (sptMem_iff_isSome key state.locals).mpr hs'

/-- **Cut correspondence.**  For `prodRel`-related states, cutting the exact
    state by `listToNumSetHOLExact live` corresponds to cutting the production
    machine by `live`: the guards fail together, and on success the restricted
    states remain `prodRel`-related.  This discharges `hcutNone`/`hcutSome` of
    `evaluateFfi_prodRel`. -/
theorem cutState_cutLoopState {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (live : List Nat) :
    (cutState (listToNumSetHOLExact live) state = none →
      cutLoopState live machine = none) ∧
    (∀ s' : LoopSemStateFiniteExact width F,
      cutState (listToNumSetHOLExact live) state = some s' →
      ∃ m' : LoopMachineState (BitVec width) F,
        cutLoopState live machine = some m' ∧ s'.prodRel m') := by
  obtain ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩ := hrel
  have hguard := sptSubsetLive_iff_loopLiveLocalsPresent hlocals live
  by_cases hsub : sptSubsetLive (listToNumSetHOLExact live) state.locals
  · have hpresent : loopLiveLocalsPresent machine.locals live := hguard.mp hsub
    constructor
    · intro hcn
      rw [cutState_of_subset _ _ hsub] at hcn
      exact absurd hcn (by simp)
    · intro s' hcs
      rw [cutState_of_subset _ _ hsub] at hcs
      injection hcs with hs'
      subst hs'
      refine ⟨{ machine with locals := loopRestrictLocals machine.locals live }, ?_, ?_⟩
      · unfold cutLoopState
        rw [if_pos hpresent]
      · refine ⟨?_, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
          hbaseAddr, htopAddr, hcode, hcoverage⟩
        intro name
        unfold loopRestrictLocals
        change (if name ∈ live then machine.locals name else none) =
          (sptLookup name (sptInter state.locals (listToNumSetHOLExact live))).map
            loopValueOfWordLocW
        rw [hlocals name, sptLookup_sptInter]
        by_cases hmem : name ∈ live
        · have hsome : (sptLookup name (listToNumSetHOLExact live)).isSome = true :=
            (sptMem_iff_isSome name (listToNumSetHOLExact live)).mp
              ((listToNumSetHOLExact_mem_iff name live).mpr hmem)
          simp [hmem, hsome]
        · have hsome : (sptLookup name (listToNumSetHOLExact live)).isSome = false := by
            cases hb : (sptLookup name (listToNumSetHOLExact live)).isSome with
            | false => rfl
            | true =>
                exact absurd
                  ((listToNumSetHOLExact_mem_iff name live).mp
                    ((sptMem_iff_isSome name (listToNumSetHOLExact live)).mpr hb)) hmem
          simp [hmem, hsome]
  · have hpresent : ¬ loopLiveLocalsPresent machine.locals live :=
      fun hp => hsub (hguard.mpr hp)
    constructor
    · intro _
      unfold cutLoopState
      rw [if_neg hpresent]
    · intro s' hcs
      rw [cutState_eq_none_of_not_subset _ _ hsub] at hcs
      exact absurd hcs (by simp)

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack
