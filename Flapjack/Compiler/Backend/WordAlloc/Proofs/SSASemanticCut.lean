import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSACutEnvsDomain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMoveDistinct
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARenameMovePreserve
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMapBounds
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnvLemma
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutEnv

/-! Shared cut-environment and rename-move helpers for the SSA semantics cases.
These are Flapjack proof infrastructure factored out of the original cases; no
separately named HOL declarations. -/
namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack factoring of the original cases' inline cut-map argument: a
strongly related cut map with bounded names yields the SSA locals relation on
the intersected map. Not a public simulation premise. -/
theorem cutLocalsRelation {α : Type} (next : Nat) (ssa : Spt Nat)
    (names : Spt Unit) (source target : Spt α)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (sourceDomain : sptDomain source = sptDomain names)
    (matching : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source target)
    (below : ∀ key, sptDomain names key → key < next) :
    ssaLocalsRel next (sptInter ssa names) source target := by
  have interRead : ∀ key register, sptLookup key (sptInter ssa names) = some register →
      sptLookup key ssa = some register ∧ sptDomain names key := by
    intro key register read
    rw [sptLookup_sptInterCases] at read
    cases left : sptLookup key ssa with
    | none => simp [left] at read
    | some value =>
      cases right : sptLookup key names with
      | none => simp [left,right] at read
      | some payload =>
        have equal : value = register := by simpa [left,right] using read
        subst value
        exact ⟨rfl,(sptMem_iff_lookup key names).mpr ⟨payload,right⟩⟩
  refine ⟨?_,?_⟩
  · intro key register read
    obtain ⟨original,inNames⟩ := interRead key register read
    have inSource : sptDomain source key := by rw [sourceDomain]; exact inNames
    obtain ⟨value,sourceRead⟩ := (sptMem_iff_lookup key source).mp inSource
    have targetRead := matching key value ⟨inNames,sourceRead⟩
    apply (sptMem_iff_lookup register target).mpr
    exact ⟨value,by simpa [optionLookup,original] using targetRead⟩
  · intro key value read
    have inNames : sptDomain names key := by
      rw [←sourceDomain]
      exact (sptMem_iff_lookup key source).mpr ⟨value,read⟩
    obtain ⟨register,original⟩ := (sptMem_iff_lookup key ssa).mp (mapped key inNames)
    obtain ⟨payload,nameRead⟩ := (sptMem_iff_lookup key names).mp inNames
    have interLookup : sptLookup key (sptInter ssa names) = some register := by
      simp [sptLookup_sptInterCases,original,nameRead]
    refine ⟨(sptMem_iff_lookup key _).mpr ⟨register,interLookup⟩,?_,fun _ => below key inNames⟩
    simpa only [interLookup,Option.getD_some,optionLookup,original] using
      matching key value ⟨inNames,read⟩

/-- The source cut guards supply exactly the names read by the first refresh. -/
theorem cutNamesPresent {α : Type} (first second : Spt Unit)
    (source output : Spt α)
    (cut : wordSemCutEnv (first,second) source = some output) :
    ∀ key, sptDomain (sptUnion first second) key → sptDomain source key := by
  cases cuts : wordSemCutEnvs (first,second) source with
  | none => simp [wordSemCutEnv,cuts] at cut
  | some pair =>
    have present := cutEnvsDomainSubset first second source pair cuts
    intro key member
    rw [sptDomain_sptUnion] at member
    exact member.elim (present.1 key) (present.2 key)

/-- A successful source lookup discharges the guarded SSA selector before
applying the scoped relation required by the original cut_env_lemma. -/
theorem scopedLocalsRelation {α : Type} (next : Nat) (ssa : Spt Nat)
    (names : Nat → Prop) (source target : Spt α)
    (related : ssaLocalsRel next ssa source target) :
    Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa) names source target := by
  intro key value found
  have matching := related.2 key value found.2
  obtain ⟨register,read⟩ := (sptMem_iff_lookup key ssa).mp matching.1
  simpa [optionLookup,read] using matching.2.1

/-- Injection is only needed on the cut names, not over the entire SSA map. -/
theorem cutNamesInjection {width : Nat} [NeZero width]
    (ssa : Spt Nat) (next : Nat) (first second : Spt Unit)
    (move : WordLangProgHOL (BitVec width)) (ssaOut : Spt Nat) (nextOut : Nat)
    (produced : listNextVarRenameMove ssa next
      ((sptToAList (sptUnion first second)).map Prod.fst) = (move,ssaOut,nextOut)) :
    ∀ x y, (sptDomain first x ∨ sptDomain second x) →
      (sptDomain first y ∨ sptDomain second y) →
      optionLookup ssaOut x = optionLookup ssaOut y → x = y := by
  intro x y inX inY equal
  apply listNextVarRenameMoveDistinct ssa next _ move ssaOut nextOut x y
  refine ⟨produced,sptAllDistinctMapFstToAList _,?_,?_,equal⟩
  · apply (sptMemMapFstToAList _ x).mpr
    rw [sptDomain_sptUnion]
    exact inX
  · apply (sptMemMapFstToAList _ y).mpr
    rw [sptDomain_sptUnion]
    exact inY

/-- Execute the actual first renaming Move from the original source cut guards.
The successful cut premise is obtained by the evaluator case split, rather than
added to the HOL statement. -/
theorem refreshCutNames {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (first second : Spt Unit)
    (sourceEnv : Spt (WordLocW width))
    (cut : wordSemCutEnv (first,second) source.locals = some sourceEnv)
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (valid : ssaMapOK next ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target) :
    let (move,mapOut,counter) := listNextVarRenameMove (width := width) ssa (next+2)
      ((sptToAList (sptUnion first second)).map Prod.fst)
    let (result,targetOut) := WordSemStateFiniteExact.evaluate move target
    result = none ∧ ssaLocalsRel counter mapOut source.locals targetOut.locals ∧
      Flapjack.WordAlloc.wordStateEqRel source targetOut := by
  have present := cutNamesPresent first second source.locals sourceEnv cut
  have result := listNextVarRenameMovePreserve source ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) target
    ⟨ssaLocalsRelMore next ssa source.locals target.locals (next+2) ⟨related,by omega⟩,
      (fun key member => present key ((sptMemMapFstToAList _ key).mp member)),
      sptAllDistinctMapFstToAList _,
      ssaMapOKMore next ssa (next+2) ⟨valid,by omega⟩,frame⟩
  generalize produced : listNextVarRenameMove (width := width) ssa (next+2)
    ((sptToAList (sptUnion first second)).map Prod.fst) = output at result ⊢
  rcases output with ⟨move,mapOut,counter⟩
  generalize evaluated : WordSemStateFiniteExact.evaluate move target = run at result ⊢
  rcases run with ⟨resultOut,targetOut⟩
  exact ⟨result.1,result.2.1,result.2.2.1⟩

/-- Combine the original cut_env_lemma with refreshed-map injection. Physical
scratch writes are handled before this lemma through the checked update law. -/
theorem refreshedCut {width : Nat} [NeZero width]
    (ssa : Spt Nat) (next : Nat) (first second : Spt Unit)
    (move : WordLangProgHOL (BitVec width)) (mapOut : Spt Nat) (counter : Nat)
    (source target sourceEnv : Spt (WordLocW width))
    (produced : listNextVarRenameMove ssa next
      ((sptToAList (sptUnion first second)).map Prod.fst) = (move,mapOut,counter))
    (cut : wordSemCutEnv (first,second) source = some sourceEnv)
    (related : ssaLocalsRel counter mapOut source target) :
    ∃ targetEnv,
      wordSemCutEnv
          (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) (first,second)) target =
        some targetEnv ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup mapOut)
        (sptDomain (sptUnion first second)) sourceEnv targetEnv ∧
      sptDomain sourceEnv = sptDomain (sptUnion first second) := by
  obtain ⟨targetEnv,targetCut,_,matching,_,sourceDomain⟩ :=
    Flapjack.WordAlloc.cutEnvLemma first second source target sourceEnv (optionLookup mapOut)
      ⟨cutNamesInjection ssa next first second move mapOut counter produced,cut,
        scopedLocalsRelation counter mapOut _ source target related⟩
  refine ⟨targetEnv,targetCut,?_,?_⟩
  · simpa only [sptDomain_sptUnion] using matching
  · simpa only [sptDomain_sptUnion] using sourceDomain

end Flapjack.Compiler.Backend.WordAlloc
