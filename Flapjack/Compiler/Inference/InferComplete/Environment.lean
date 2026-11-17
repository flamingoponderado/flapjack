module

public import Flapjack.Compiler.Inference.InferComplete.Binding
public import Flapjack.Compiler.Inference.InferProps.DbSubst
public import Flapjack.Compiler.Inference.InferProps.ClosedSubst
public import Flapjack.Compiler.Inference.EnvRel.Relation
public import Flapjack.Compiler.Inference.EnvRel.Walkstar
public import Flapjack.NamespaceProps.All
public import Flapjack.NamespaceProps.EmptyLookup
public import Flapjack.Misc.FindIndex.Bounds
public import Flapjack.Compiler.Inference.Unify.Walkstar.Empty
public import Mathlib.Data.List.Dedup

@[expose] public section

/-! Completeness relation for a single inferred binding. -/
namespace Flapjack.Compiler.Inference.InferComplete
open Flapjack Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants Flapjack.NamespaceHOL
  Flapjack.Compiler.Inference.EnvRel Flapjack.Compiler.Inference.InferProps
  Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Unify Flapjack.Misc
  Flapjack.Basis.Pure.MlString

noncomputable section
local instance : Nonempty MlString := ⟨ofString ""⟩

/-- A declarative binding and its deduplicated inferred scheme are related. -/
@[hol "cakeml/compiler/inference/proofs/inferCompleteScript.sml" "env_rel_binding"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty, Flapjack.HolFiniteMapExact.alistToFmap])]
theorem envRelBinding (fvs : List MlString) (t : SemanticT) (fvs' : List MlString) (name : MlString) :
    checkFreevars 0 fvs' t = true ∧ (∀ n ∈ fvs', n ∈ fvs) →
    let tenv : TypeEnv :=
      ⟨nsSing name (fvs.length, typeSubst (HolFiniteMapExact.alistToFmap
         (fvs.zip ((List.range fvs.length).map SemanticT.varDb))) t), nsEmpty, nsEmpty⟩
    let ienv : Env :=
      ⟨nsSing name (fvs'.dedup.length, inferTypeSubst
         (fvs'.dedup.zip ((List.range fvs'.dedup.length).map InferT.varDb)) t), nsEmpty, nsEmpty⟩
    ienvOk (fun _ => False) ienv ∧ tenvOk tenv ∧
      (∀ path, nsLookupMod ienv.infV path = none ↔ nsLookupMod tenv.v path = none) ∧
      envRelSoundModel HolFiniteMapExact.holEmpty ienv tenv .empty ∧
      envRelCompleteModel HolFiniteMapExact.holEmpty ienv tenv .empty := by
  intro ⟨free, included⟩
  change envRelModel
      ⟨nsSing name (fvs.length, typeSubst (HolFiniteMapExact.alistToFmap
         (fvs.zip ((List.range fvs.length).map SemanticT.varDb))) t), nsEmpty, nsEmpty⟩
      ⟨nsSing name (fvs'.dedup.length, inferTypeSubst
         (fvs'.dedup.zip ((List.range fvs'.dedup.length).map InferT.varDb)) t), nsEmpty, nsEmpty⟩
  have more := checkFreevarsMore 0 fvs' t free fvs included
  have large := Flapjack.TypeSysProps.checkFreevarsAdd 0 fvs t more fvs.length (by omega)
  have dcheck : checkFreevars fvs.length []
      (typeSubst (HolFiniteMapExact.alistToFmap
        (fvs.zip ((List.range fvs.length).map SemanticT.varDb))) t) = true := by
    apply Flapjack.TypeSysProps.checkFreevarsSubstSingle fvs.length fvs t [] _
    refine ⟨by simp, large, ?_⟩
    simp [List.all_eq_true, checkFreevars]
  have icheck : checkT fvs'.dedup.length (fun _ => False)
      (inferTypeSubst (fvs'.dedup.zip ((List.range fvs'.dedup.length).map InferT.varDb)) t) := by
    by_cases empty : fvs'.dedup = []
    · have oldEmpty : fvs' = [] := by simpa using empty
      subst fvs'
      simpa using inferTypeSubstEmptyCheck.1 t free
    · apply checkTInferTypeSubstDbs 0 fvs' t fvs'.dedup.length (fun _ => False) fvs'.dedup
      exact ⟨free, by simp, fun impossible => (empty impossible).elim⟩
  have unconv : unconvertT (typeSubst (HolFiniteMapExact.alistToFmap
      (fvs.zip ((List.range fvs.length).map SemanticT.varDb))) t) =
      inferTypeSubst (fvs.zip ((List.range fvs.length).map InferT.varDb)) t := by
    have keys : (fvs.zip ((List.range fvs.length).map SemanticT.varDb)).map Prod.fst = fvs :=
      List.map_fst_zip (by simp)
    have h := unconvertTypeSubst.1 t
      (fvs.zip ((List.range fvs.length).map SemanticT.varDb)) fvs' ⟨free, by simpa only [keys] using included⟩
    have mapped : (fvs.zip ((List.range fvs.length).map SemanticT.varDb)).map
        (fun p => (p.1, unconvertT p.2)) =
        fvs.zip ((List.range fvs.length).map InferT.varDb) := by
      simp only [List.zip_map_right, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro p member
      cases p
      simp [Prod.map, unconvertT]
    rw [mapped] at h
    exact h
  have freeD : checkFreevars 0 fvs'.dedup t = true :=
    checkFreevarsMore 0 fvs' t free fvs'.dedup (by intro x hx; simpa using hx)
  have includedD : ∀ x ∈ fvs'.dedup, x ∈ fvs := by
    intro x hx
    exact included x (by simpa using hx)
  have nodupD : fvs'.dedup.Nodup := List.nodup_dedup _
  have soundApprox : tschemeApproxModel 0 HolFiniteMapExact.holEmpty
      (fvs'.dedup.length, inferTypeSubst (fvs'.dedup.zip ((List.range fvs'.dedup.length).map InferT.varDb)) t)
      (fvs.length, unconvertT (typeSubst (HolFiniteMapExact.alistToFmap
        (fvs.zip ((List.range fvs.length).map SemanticT.varDb))) t)) := by
    rw [unconv]
    let choices := (List.range fvs.length).map fun n =>
      match findIndex (holEl n fvs) fvs'.dedup 0 with
      | none => InferT.app [] 0
      | some index => InferT.varDb index
    refine ⟨choices, by simp [choices], ?_, ?_⟩
    · intro v mem
      simp only [choices, List.mem_map, List.mem_range] at mem
      obtain ⟨i, hi, rfl⟩ := mem
      cases found : findIndex (holEl i fvs) fvs'.dedup 0 with
      | none => exact (checkT_app _ _ _ _).2 ((checkTList_nil _ _).2 trivial)
      | some index =>
        have inRange := (findIndexLessLength fvs'.dedup (holEl i fvs) 0 index found).2
        exact (checkT_varDb _ _ _).2 (by simpa using inRange)
    · intro inst len
      simp only [tWalkstarEmpty]
      have h := envRelBindingLemma 0 t fvs fvs'.dedup inst ⟨freeD, includedD, nodupD⟩
      simp only [choices, List.map_map, Function.comp_def]
      convert h using 1
      congr 1
  have completeApprox : tschemeApproxModel 0 HolFiniteMapExact.holEmpty
      (fvs.length, unconvertT (typeSubst (HolFiniteMapExact.alistToFmap
        (fvs.zip ((List.range fvs.length).map SemanticT.varDb))) t))
      (fvs'.dedup.length, inferTypeSubst (fvs'.dedup.zip ((List.range fvs'.dedup.length).map InferT.varDb)) t) := by
    rw [unconv]
    let choices := (List.range fvs'.dedup.length).map fun n =>
      match findIndex (holEl n fvs'.dedup) fvs 0 with
      | none => InferT.app [] 0
      | some index => InferT.varDb index
    refine ⟨choices, by simp [choices], ?_, ?_⟩
    · intro v mem
      simp only [choices, List.mem_map, List.mem_range] at mem
      obtain ⟨i, hi, rfl⟩ := mem
      cases found : findIndex (holEl i fvs'.dedup) fvs 0 with
      | none => exact (checkT_app _ _ _ _).2 ((checkTList_nil _ _).2 trivial)
      | some index =>
        have inRange := (findIndexLessLength fvs (holEl i fvs'.dedup) 0 index found).2
        exact (checkT_varDb _ _ _).2 (by simpa using inRange)
    · intro inst len
      simp only [tWalkstarEmpty]
      have h := envRelBindingLemma2 0 t fvs fvs'.dedup inst ⟨freeD, includedD, nodupD⟩
      simp only [choices, List.map_map, Function.comp_def]
      convert h using 1
      congr 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [ienvOk, ienvValOk, tenvCtorOk, tenvAbbrevOk, nsAllNsSing]
    exact ⟨icheck, by simp [nsAll, nsLookup_nsEmpty], by simp [nsAll, nsLookup_nsEmpty]⟩
  · simp only [tenvOk, tenvValOk, tenvCtorOk, tenvAbbrevOk, nsAllNsSing]
    exact ⟨dcheck, by simp [nsAll, nsLookup_nsEmpty], by simp [nsAll, nsLookup_nsEmpty]⟩
  · intro path
    cases path <;> simp [nsLookupMod, nsSing]
  · refine ⟨rfl, rfl, ?_⟩
    intro id ts found
    cases id with
    | short key =>
      by_cases same : key = name
      · subst key
        simp [nsLookup, nsSing, List.lookup] at found
        subst ts
        refine ⟨fvs.length, _, by simpa [numTvs] using dcheck, ?_, ?_⟩
        · simp [lookupVar, lookupVarE, tveLookup, nsLookup, nsSing, List.lookup]
        · simpa [numTvs] using soundApprox
      · have different : (key == name) = false := by simp [same]
        simp [nsLookup, nsSing, List.lookup, different] at found
    | long mn id => simp [nsLookup, nsSing] at found
  · refine ⟨rfl, rfl, ?_⟩
    intro id tvs ty found
    cases id with
    | short key =>
      by_cases same : key = name
      · subst key
        simp [lookupVar, lookupVarE, tveLookup, nsLookup, nsSing, List.lookup] at found
        obtain ⟨rfl, rfl⟩ := found
        refine ⟨⟨fvs.length, dcheck⟩, fvs'.dedup.length,
          inferTypeSubst (fvs'.dedup.zip ((List.range fvs'.dedup.length).map InferT.varDb)) t, ?_, ?_⟩
        · simp [nsLookup, nsSing, List.lookup]
        · simpa [numTvs] using completeApprox
      · have different : (key == name) = false := by simp [same]
        simp [lookupVar, lookupVarE, tveLookup, nsLookup, nsSing, List.lookup, different] at found
    | long mn id => simp [lookupVar, lookupVarE, nsLookup, nsSing] at found
end
end Flapjack.Compiler.Inference.InferComplete
