import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MakeVarls
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateCases

/-! Linking allocated global names to the corresponding initialized slots. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- A successful lookup in an association list identifies the same occurrence
in `allocDefs` and in its list of values, including when names repeat. -/
theorem allocDefs_lookup {α : Type} (entries : List (VarN × α)) (name : VarN) (value : α)
    (lookup : entries.lookup name = some value) (next base : Nat) :
    ∃ i, (allocDefs next base (entries.map Prod.fst)).lookup name = some (.glob omTra (base + i)) ∧
      i < entries.length ∧ (entries.map (fun p => some p.2))[i]? = some (some value) := by
  induction entries generalizing next base with
  | nil => simp at lookup
  | cons head tail ih =>
    rcases head with ⟨key, current⟩
    by_cases same : name = key
    · subst key
      simp at lookup
      subst current
      refine ⟨0, ?_, by simp, by simp⟩
      simp [allocDefs]
    · have different : (name == key) = false := by
        change decide (name = key) = false
        simp [same]
      have tailLookup : tail.lookup name = some value := by
        simpa [List.lookup_cons, different] using lookup
      obtain ⟨i, allocated, bound, slot⟩ := ih tailLookup (next + 1) (base + 1)
      refine ⟨i + 1, ?_, by simp; omega, ?_⟩
      · simpa [allocDefs, List.lookup_cons, different, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using allocated
      · simpa using slot

/-- A source binding in a related local environment becomes a related global
binding after its flat values are installed in the allocated slots. This is
infrastructure over the factored source-to-flat relations. -/
theorem globalLookup_allocDefs (genv : GlobalEnv)
    (sourceEnv : Namespace ModN VarN SemanticPrimitivesHOL.Value)
    (flatEnv : List (VarN × FlatSem.Value)) (related : EnvRel genv sourceEnv flatEnv)
    (pre post : List (Option FlatSem.Value))
    (slots : genv.v = pre ++ (flatEnv.map (fun p => some p.2) ++ post))
    (next : Nat) (name : VarN) (source : SemanticPrimitivesHOL.Value)
    (lookup : nsLookup sourceEnv (.short name) = some source) :
    GlobalLookupRel genv
      { emptyEnv with v := alistToNs (allocDefs next pre.length (flatEnv.map Prod.fst)) }
      (.short name) source := by
  obtain ⟨flat, flatLookup, valueRel⟩ := envRel_lookup genv sourceEnv flatEnv related name source lookup
  obtain ⟨i, allocated, bound, valueSlot⟩ := allocDefs_lookup flatEnv name flat flatLookup next pre.length
  have globalBound : pre.length + i < genv.v.length := by
    rw [slots]
    simp only [List.length_append, List.length_map]
    omega
  have globalSlot : genv.v[pre.length + i]?.getD none = some flat := by
    rw [slots]
    rw [List.getElem?_append_right (l₁ := pre) (by omega), Nat.add_sub_cancel_left]
    have inBlock : i < (flatEnv.map fun p => some p.2).length := by simpa using bound
    rw [List.getElem?_append_left inBlock, valueSlot]
    rfl
  apply GlobalLookupRel.intro genv _ _ source (pre.length + i) flat omTra
  · simpa [emptyEnv, alistToNs, nsLookup] using allocated
  · exact globalBound
  · exact globalSlot
  · exact valueRel

/-- Once flat bindings are written into the allocated slots, they form a
global environment invariant for a source association-list environment. The
binding order is shared with the flat environment; reversing source order, as
the original declaration proof does, additionally requires distinct names. -/
theorem globalEnvInv_allocDefs (genv : GlobalEnv)
    (source : List (VarN × SemanticPrimitivesHOL.Value))
    (flat : List (VarN × FlatSem.Value)) (related : EnvRel genv (alistToNs source) flat)
    (pre post : List (Option FlatSem.Value))
    (slots : genv.v = pre ++ (flat.map (fun p => some p.2) ++ post)) (next : Nat) :
    GlobalEnvInv genv
      { emptyEnv with v := alistToNs (allocDefs next pre.length (flat.map Prod.fst)) }
      (fun _ => False) ⟨alistToNs source, nsEmpty⟩ := by
  apply GlobalEnvInv.intro
  · intro id value _ lookup
    cases id with
    | short name => exact globalLookup_allocDefs genv _ flat related pre post slots next name value lookup
    | long moduleName id => simp [alistToNs, nsLookup] at lookup
  · intro id arity stamp lookup
    cases id <;> simp [nsEmpty, nsLookup] at lookup

private theorem lookup_mem {α : Type} (entries : List (VarN × α)) (name : VarN) (value : α)
    (lookup : entries.lookup name = some value) : (name, value) ∈ entries := by
  induction entries with
  | nil => simp at lookup
  | cons head tail ih =>
    rcases head with ⟨key, current⟩
    by_cases same : name = key
    · subst key
      simp at lookup
      subst current
      simp
    · have different : (name == key) = false := by
        change decide (name = key) = false
        simp [same]
      simp only [List.lookup_cons, different] at lookup
      exact List.mem_cons_of_mem _ (ih lookup)

private theorem lookup_of_mem_nodup {α : Type} (entries : List (VarN × α))
    (name : VarN) (value : α) (member : (name, value) ∈ entries)
    (distinct : (entries.map Prod.fst).Nodup) : entries.lookup name = some value := by
  induction entries with
  | nil => simp at member
  | cons head tail ih =>
    rcases head with ⟨key, current⟩
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with h | h
    · cases h
      simp
    · have different : name ≠ key := by
        intro equal
        subst key
        exact distinct.1 (List.mem_map.mpr ⟨(name, value), h, rfl⟩)
      have compare : (name == key) = false := by
        change decide (name = key) = false
        simp [different]
      simp [List.lookup_cons, compare, ih h distinct.2]

private theorem lookup_reverse_of_nodup {α : Type} (entries : List (VarN × α))
    (name : VarN) (distinct : (entries.map Prod.fst).Nodup) :
    entries.reverse.lookup name = entries.lookup name := by
  have reversedDistinct : (entries.reverse.map Prod.fst).Nodup := by
    rw [List.map_reverse, List.Nodup, List.pairwise_reverse]
    exact distinct.imp (fun h => Ne.symm h)
  cases lookup : entries.lookup name with
  | none =>
    cases reversed : entries.reverse.lookup name with
    | none => rfl
    | some value =>
      have member := List.mem_reverse.mp (lookup_mem _ _ _ reversed)
      have impossible := lookup_of_mem_nodup entries name value member distinct
      rw [lookup] at impossible
      cases impossible
  | some value =>
    exact lookup_of_mem_nodup entries.reverse name value
      (List.mem_reverse.mpr (lookup_mem entries name value lookup)) reversedDistinct

/-- Reversed declaration bindings produce the original source global
invariant when names are distinct. This uses the factored value relation, so
it is not yet a reviewed port of the original HOL result. -/
theorem globalEnvInv_allocDefs_reverse (genv : GlobalEnv)
    (source : List (VarN × SemanticPrimitivesHOL.Value))
    (flat : List (VarN × FlatSem.Value)) (related : EnvRel genv (alistToNs source) flat)
    (distinct : (source.map Prod.fst).Nodup)
    (pre post : List (Option FlatSem.Value))
    (slots : genv.v = pre ++ ((flat.reverse.map (fun p => some p.2)) ++ post)) (next : Nat) :
    GlobalEnvInv genv
      { emptyEnv with v := alistToNs (allocDefs next pre.length (flat.reverse.map Prod.fst)) }
      (fun _ => False) ⟨alistToNs source, nsEmpty⟩ := by
  have reversedRelated : EnvRel genv (alistToNs source.reverse) flat.reverse := by
    apply (envRel_alist_iff genv _ _).mpr
    exact List.forall₂_reverse_iff.mpr ((envRel_alist_iff genv _ _).mp related)
  have inv := globalEnvInv_allocDefs genv source.reverse flat.reverse reversedRelated pre post slots next
  cases inv with
  | intro _ _ _ values constructors =>
    apply GlobalEnvInv.intro
    · intro id value unshadowed lookup
      apply values id value unshadowed
      cases id with
      | short name =>
        simpa [alistToNs, nsLookup, lookup_reverse_of_nodup source name distinct] using lookup
      | long moduleName id => simp [alistToNs, nsLookup] at lookup
    · exact constructors

/-- Initializing a reserved block for a distinct declaration environment
produces the flat state and the global invariant needed for later code. The
factored relation and flat evaluator still await full HOL correspondence review. -/
theorem evaluate_makeVarls_globalEnvInv {C F : Type} (genv : GlobalEnv)
    (sourceEnv : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value))
    (related : EnvRel genv (alistToNs sourceEnv) flatEnv)
    (distinct : (sourceEnv.map Prod.fst).Nodup)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState) (globals : flatState.globals = genv.v)
    (pre post : List (Option FlatSem.Value))
    (slots : flatState.globals = pre ++ (List.replicate flatEnv.length none ++ post))
    (n : Nat) (trace : Tra) :
    let values := flatEnv.reverse.map Prod.snd
    let finalSlots := pre ++ (values.map some ++ post)
    let finalEnv := { genv with v := finalSlots }
    let finalState := { flatState with globals := finalSlots }
    FlatSem.evaluate ⟨flatEnv⟩ flatState
        [makeVarls n trace pre.length (flatEnv.reverse.map Prod.fst)] =
        (finalState, .val [FlatSem.unitValue]) ∧
      GlobalGrowth genv finalEnv ∧ StateRel finalEnv sourceState finalState ∧
      GlobalEnvInv finalEnv
        { emptyEnv with v := alistToNs (allocDefs n pre.length (flatEnv.reverse.map Prod.fst)) }
        (fun _ => False) ⟨alistToNs sourceEnv, nsEmpty⟩ := by
  dsimp only
  have namesEq : sourceEnv.map Prod.fst = flatEnv.map Prod.fst := by
    have pairRel := (envRel_alist_iff genv sourceEnv flatEnv).mp related
    clear related distinct slots
    induction pairRel with
    | nil => rfl
    | cons pair tail ih => simp only [List.map_cons, pair.1, ih]
  have flatDistinct : (flatEnv.map Prod.fst).Nodup := by simpa [← namesEq] using distinct
  have lookups : ∀ (i : Nat) (inValues : i < (flatEnv.reverse.map Prod.snd).length),
      flatEnv.lookup ((flatEnv.reverse.map Prod.fst)[i]'(by simp_all)) =
        some (flatEnv.reverse.map Prod.snd)[i] := by
    intro i inValues
    have inEntries : i < flatEnv.reverse.length := by simpa using inValues
    have member : flatEnv.reverse[i]'inEntries ∈ flatEnv :=
      List.mem_reverse.mp (List.getElem_mem inEntries)
    have found := lookup_of_mem_nodup flatEnv _ _ member flatDistinct
    simp only [List.getElem_map]
    exact found
  have runGrowth := evaluate_makeVarls_growth genv ⟨flatEnv⟩ flatState n trace pre.length flatEnv.length
    (flatEnv.reverse.map Prod.fst) (flatEnv.reverse.map Prod.snd) pre post globals slots
    rfl (by simp) (by simp) lookups
  refine ⟨runGrowth.1, runGrowth.2, ?_, ?_⟩
  · exact stateRel_after_global_growth genv _ runGrowth.2 sourceState flatState stateRel _
  · apply globalEnvInv_allocDefs_reverse _ sourceEnv flatEnv
      (envRel_growth genv _ runGrowth.2 _ _ related) distinct pre post
    simp [List.map_map]

end Flapjack.Compiler.Backend.SourceToFlat
