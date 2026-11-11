module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeInvariant
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateRelation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CallsWellformed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CallsExtension
public import Flapjack.Compiler.Backend.ClosCall.Proofs.SuffixReplacement
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelOrigins
public import Flapjack.FiniteMap.MapKeys
@[expose] public section

/-! Installation simulation for direct-call closure conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall.InstallSimulation
open Flapjack BackendProps ClosProps ClosCall

/-- The closure-state carrier has the canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- HOL uses distinct-key update commutation to reverse the update list in
its installation proof; this is the corresponding lookup-side calculation. -/
theorem updateList_reverse_distinct {K V : Type} [DecidableEq K] (m : FiniteMap K V)
    (xs : List (K × V)) (distinct : (xs.map Prod.fst).Nodup) :
    FUPDATE_LIST_HOL m xs = FUPDATE_LIST_HOL m xs.reverse := by
  induction xs generalizing m with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    rw [FUPDATE_LIST_HOL_cons, ih (FUPDATE_HOL m e) distinct.2, List.reverse_cons]
    simp only [FUPDATE_LIST_HOL, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact FUPDATE_LIST_HOL_single_commutes m e es.reverse (by simpa using distinct.1)
/-- The source proof identifies the updated map with the generated code
list using distinct labels; this helper establishes that identity. -/
private theorem alistUpdateDistinct {K V : Type} [DecidableEq K] (old entries : List (K × V))
    (distinct : (entries.map Prod.fst).Nodup) :
    (HolFiniteMapExact.alistToFmap old).updateListEq entries =
      HolFiniteMapExact.alistToFmap (entries ++ old) := by
  have decEq : (inferInstance : DecidableEq K) = Classical.typeDecidableEq K := Subsingleton.elim _ _
  cases decEq
  classical
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.lookup_updateListEq,
    List.reverse_append]
  have lookupEq : (HolFiniteMapExact.empty.updateListEq old.reverse).lookup =
      FUPDATE_LIST_HOL HolFiniteMapExact.empty.lookup old.reverse := rfl
  rw [lookupEq, updateList_reverse_distinct _ entries distinct]
  simp [FUPDATE_LIST_HOL, List.foldl_append]

/-- The HOL installation proof extends the value relation over globals and
references inline; this helper packages that transport. -/
private theorem stateRel_extend {C F : Type} (g g2 : State) (allowed allowed2 : Nat → Prop)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (nextCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (h : stateRel g allowed source target ∧ stateExtends g g2 ∧
      (∀ x, allowed x → allowed2 x) ∧ target.code.submap nextCode) :
    stateRel g2 allowed2 source { target with code := nextCode } := by
  obtain ⟨related, extended, allowedSub, codeSub⟩ := h
  have vmono : ∀ x y, valueRel g allowed target.code x y → valueRel g2 allowed2 nextCode x y := by
    intro x y v
    exact valueRel_submapSubg g allowed target.code x y nextCode allowed2 g2 ⟨v, codeSub, allowedSub, extended⟩
  have omono {A B : Type} {r s : A → B → Prop} (mono : ∀ x y, r x y → s x y)
      (x : Option A) (y : Option B) (rel : optionRel r x y) : optionRel s x y := by
    cases x <;> cases y <;> simp_all [optionRel]
  refine ⟨related.1, related.2.1, related.2.2.1, ?_, ?_, related.2.2.2.2.2⟩
  · exact related.2.2.2.1.imp (fun x y h => omono vmono x y h)
  · intro key
    exact omono (fun x y r => ClosProps.refRel_mono vmono r) _ _ (related.2.2.2.2.1 key)

/-- A missing association-list key has no binding in the corresponding map;
the HOL proof uses this fact while establishing code-domain disjointness. -/
private theorem alistLookupNone {K V : Type} (entries : List (K × V)) (key : K)
    (absent : key ∉ entries.map Prod.fst) : (HolFiniteMapExact.alistToFmap entries).lookup key = none := by
  classical
  rw [HolFiniteMapExact.holFmapAsFiniteSupportResultWitness_alistToFmap]
  exact FLOOKUP_FUPDATE_LIST_HOL_not_mem FEMPTY entries.reverse key (by simpa using absent)

set_option maxHeartbeats 4000000 in
/-- Installing a source oracle entry preserves the related compiler states,
code invariant and fresh generated labels, and produces the same machine code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "code_rel_state_rel_install"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code])]
theorem codeRel_stateRel_install {C F : Type} (g1 : State) (l1 : Set Nat)
    (r : ClosSem.State (NumSet × C) F) (t : ClosSem.State C F)
    (cfg : NumSet × C) (exps : List ClosLang.Exp) (aux : List (Nat × Nat × ClosLang.Exp))
    (bytes : List (BitVec 8)) (data : List (BitVec 64)) (nextCfg : NumSet × C)
    (cfg2 : C) (progs : ClosSem.Program)
    (h : codeInv (some g1) l1 r.code r.compile r.compileOracle t.code t.compile t.compileOracle ∧
      stateRel g1 l1 r t ∧ r.compile cfg (exps, aux) = some (bytes, data, nextCfg) ∧
      r.compileOracle 0 = (cfg, exps, aux) ∧ t.compileOracle 0 = (cfg2, progs) ∧
      nextCfg = (holShiftSeq 1 r.compileOracle 0).1 ∧ Disjoint l1 (sptDomain g1.1)) :
    Disjoint t.code.domain {x | x ∈ progs.2.map Prod.fst} ∧
    (progs.2.map Prod.fst).Nodup ∧
    ∃ exp1 aux1 g2 l2 nextCfg2,
      t.compile cfg2 progs = some (bytes, data, nextCfg2) ∧
      progs = (exp1, aux1) ∧ nextCfg2 = (holShiftSeq 1 t.compileOracle 0).1 ∧
      stateExtends g1 g2 ∧ l1 ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      {x | x ∈ codeLocations exps} \ sptDomain g2.1 ⊆ l2 ∧
      calls exps g1 = (exp1, g2) ∧
      stateRel g2 l2 {r with compileOracle := holShiftSeq 1 r.compileOracle, code := r.code.updateListEq aux}
        {t with compileOracle := holShiftSeq 1 t.compileOracle, code := t.code.updateListEq aux1} ∧
      codeInv (some g2) l2 (r.code.updateListEq aux) r.compile (holShiftSeq 1 r.compileOracle)
        (t.code.updateListEq aux1) t.compile (holShiftSeq 1 t.compileOracle) ∧
      t.code.submap (t.code.updateListEq aux1) ∧
      Disjoint (Set.image Nat.succ {x | x ∈ codeLocations exps}) t.code.domain := by
  classical
  obtain ⟨inv, rel, run, sourceOracle, targetOracle, next, disjoint⟩ := h
  obtain ⟨sourceEmpty, compEq, oracleEq, ⟨known, entries, wf, firstKnown, mono, targetCode, group⟩, syntaxOkAll⟩ := inv
  have groupEq : g1 = (known, entries) := by
    have h := group (by simp)
    simpa using h
  subst g1
  have cfgKnown : cfg.1 = known := by simpa [sourceOracle] using firstKnown
  have auxEmpty : aux = [] := by
    have h := (syntaxOkAll 0).2
    simpa [sourceOracle] using h
  subst aux
  have targetOracle0 := congrFun oracleEq 0
  simp only [stateCo, sourceOracle] at targetOracle0
  cases cfg with
  | mk cfgState cfgBase =>
    simp only at cfgKnown
    subst cfgState
    cases callsEq : calls exps (known, []) with
    | mk exp1 result =>
      cases result with
      | mk known2 aux1 =>
        have incEq : compileInc known (exps, ([] : List (Nat × Nat × ClosLang.Exp))) = (known2, exp1, aux1) := by
          simp [compileInc, callsEq]
        simp only [incEq] at targetOracle0
        rw [targetOracle] at targetOracle0
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj targetOracle0
        rw [compEq] at run
        simp only [stateCc, incEq] at run
        cases targetRun : t.compile cfg2 (exp1, aux1) with
        | none => simp [targetRun] at run
        | some output =>
          cases output with
          | mk outBytes rest =>
            cases rest with
            | mk outData cfgNext =>
              simp only [targetRun, Option.some.injEq, Prod.mk.injEq] at run
              obtain ⟨rfl, rfl, cfgPairEq⟩ := run
              have sourceSyntax : syntaxOk exps := by
                have h := (syntaxOkAll 0).1
                simpa [sourceOracle] using h
              have locFresh : ∀ x, x ∈ codeLocations exps → ¬ sptDomain known x := by
                intro x member knownMember
                have order := mono.2 0 x x (Or.inl knownMember) (by simpa [sourceOracle] using member)
                exact Nat.lt_irrefl _ order
              have auxBound := calls_addSucc_codeLocations exps (known, []) exp1 (known2, aux1) callsEq
              have freshLabels : ∀ label, ¬ (label ∈ Set.image Nat.succ {x | x ∈ codeLocations exps} ∧
                  label ∈ entries.map Prod.fst) := by
                intro label ⟨⟨loc, member, eq⟩, oldMem⟩
                have domMem : label ∈ Set.image Nat.succ (sptDomain known) := by
                  rw [← wf.1]
                  exact oldMem
                obtain ⟨oldLoc, dom, eq2⟩ := domMem
                have equal : loc = oldLoc := Nat.succ.inj (eq.trans eq2.symm)
                exact locFresh loc member (equal ▸ dom)
              have auxFresh : ∀ label, ¬ (label ∈ aux1.map Prod.fst ∧ label ∈ entries.map Prod.fst) := by
                intro label ⟨newMem, oldMem⟩
                have origin := auxBound (by simpa using newMem)
                simp only [Set.mem_union, Set.mem_ofPred_eq, List.map_nil, List.not_mem_nil, false_or] at origin
                exact freshLabels _ ⟨origin, oldMem⟩
              have auxDistinct : (aux1.map Prod.fst).Nodup := by
                apply calls_allDistinct exps (known, []) exp1 (known2, aux1)
                exact ⟨callsEq, by simp, sourceSyntax.2.2, by simp⟩
              have callsWithOld := calls_acc exps known entries exp1 known2 aux1 callsEq
              have ext : stateExtends (known, entries) (known2, aux1 ++ entries) := by
                apply calls_subg exps (known, entries) exp1 (known2, aux1 ++ entries)
                exact ⟨callsWithOld, wf.2, sourceSyntax.2.2, freshLabels⟩
              have mapEq : t.code.updateListEq aux1 = HolFiniteMapExact.alistToFmap (aux1 ++ entries) := by
                rw [targetCode]
                exact alistUpdateDistinct entries aux1 auxDistinct
              have oldLabel : ∀ key value, t.code.lookup key = some value → key ∈ entries.map Prod.fst := by
                intro key value found
                by_contra absent
                have none := alistLookupNone entries key absent
                rw [targetCode, none] at found
                contradiction
              have oldSub : t.code.submap (t.code.updateListEq aux1) := by
                intro key value found
                have absent : key ∉ aux1.map Prod.fst := by
                  intro newMem
                  exact auxFresh key ⟨newMem, oldLabel key value found⟩
                change FUPDATE_LIST_HOL t.code.lookup aux1 key = some value
                have unchanged := FLOOKUP_FUPDATE_LIST_HOL_not_mem t.code.lookup aux1 key absent
                simpa [FLOOKUP] using unchanged.trans found
              have targetDisjoint : Disjoint t.code.domain {x | x ∈ aux1.map Prod.fst} := by
                apply Set.disjoint_left.mpr
                intro key oldMem newMem
                change t.code.lookup key ≠ none at oldMem
                cases found : t.code.lookup key with
                | none => exact oldMem found
                | some value => exact auxFresh key ⟨newMem, oldLabel key value found⟩
              have locCodeDisjoint : Disjoint (Set.image Nat.succ {x | x ∈ codeLocations exps}) t.code.domain := by
                apply Set.disjoint_left.mpr
                intro key ⟨loc, mem, eq⟩ oldMem
                change t.code.lookup key ≠ none at oldMem
                cases found : t.code.lookup key with
                | none => exact oldMem found
                | some value =>
                  exact freshLabels _ ⟨⟨loc, mem, eq⟩, oldLabel key value found⟩
              have allowedFresh : ∀ x, x ∈ codeLocations exps → ¬ l1 x := by
                intro x member allowedMember
                have order := mono.2 0 x x (Or.inr allowedMember) (by simpa [sourceOracle] using member)
                exact Nat.lt_irrefl _ order
              have nextDomain := calls_domainLocations exps (known, []) exp1 (known2, aux1) callsEq
              let locs : Set Nat := {x | x ∈ codeLocations exps}
              let allowed2 : Set Nat := l1 ∪ (locs \ sptDomain known2)
              have subAllowed : l1 ⊆ allowed2 := fun _ h => Or.inl h
              have allowedDisjoint : Disjoint allowed2 (sptDomain known2) := by
                apply Set.disjoint_left.mpr
                intro x allowedMem knownMem
                rcases allowedMem with old | ⟨_, absent⟩
                · rcases nextDomain knownMem with oldDomain | location
                  · exact Set.disjoint_left.mp disjoint old oldDomain
                  · exact allowedFresh x location old
                · exact absent knownMem
              have missingIncluded : locs \ sptDomain known2 ⊆ allowed2 := fun _ h => Or.inr h
              have wfNext : wellFormed (known2, aux1 ++ entries) := by
                apply calls_wellFormed exps (known, entries) exp1 (known2, aux1 ++ entries)
                exact ⟨callsWithOld, sourceSyntax.2.2, freshLabels, sourceSyntax.1, wf⟩
              have nextOracle : (r.compileOracle 1).1 = (known2, cfgNext) := by
                simpa [holShiftSeq] using (cfgPairEq.trans next).symm
              have targetNext : cfgNext = (holShiftSeq 1 t.compileOracle 0).1 := by
                have component := congrArg Prod.snd nextOracle
                simpa [holShiftSeq, oracleEq, stateCo] using component.symm
              have nextKnown : (holShiftSeq 1 r.compileOracle 0).1.1 = known2 := by
                simpa [holShiftSeq] using congrArg Prod.fst nextOracle
              have shiftedMono : oracleMonotonic
                  (fun entry => {x | x ∈ codeLocations entry.2.1}) (· < ·)
                  (sptDomain known2 ∪ allowed2) (holShiftSeq 1 r.compileOracle) := by
                apply oracleMonotonic_shiftSeq _ _ _ _ _ 1
                refine ⟨mono, by omega, ?_⟩
                intro x member
                rcases member with domain | allowedMem
                · rcases nextDomain domain with old | located
                  · exact Or.inr (Or.inl old)
                  · exact Or.inl (by simpa [locs, holShiftSeq, sourceOracle] using located)
                · rcases allowedMem with old | ⟨located, _⟩
                  · exact Or.inr (Or.inr old)
                  · exact Or.inl (by simpa [locs, holShiftSeq, sourceOracle] using located)
              refine ⟨targetDisjoint, auxDistinct, exp1, aux1, (known2, aux1 ++ entries), allowed2,
                cfgNext, rfl, rfl, targetNext, ext, subAllowed, allowedDisjoint, missingIncluded,
                callsWithOld, ?_, ?_, oldSub, locCodeDisjoint⟩
              · have nextRel := stateRel_extend (known, entries) (known2, aux1 ++ entries) l1 allowed2
                  r t (t.code.updateListEq aux1) ⟨rel, ext, subAllowed, oldSub⟩
                simpa [stateRel, HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL] using nextRel
              · unfold codeInv
                refine ⟨?_, compEq, ?_, ⟨known2, aux1 ++ entries, wfNext, nextKnown, shiftedMono, mapEq, ?_⟩, ?_⟩
                · simpa [HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL] using sourceEmpty
                · funext n
                  simp [holShiftSeq, oracleEq, stateCo]
                · intro _; rfl
                · intro n
                  simpa [holShiftSeq] using syntaxOkAll (n + 1)
end Flapjack.Compiler.Backend.ClosCall.InstallSimulation
