module

public import Flapjack.FiniteMap.AlistExact.LookupAgreement
public import Flapjack.Misc.ListEl
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MakeVarls
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.ValueRelCases
public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateCases

@[expose] public section

/-! Linking allocated global names to the corresponding initialized slots. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- HOL's unbounded index equation for append, including out-of-range indices. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "EL_APPEND_IF"]
theorem holEl_append_if {α : Type} [Nonempty α] (i : Nat) (xs ys : List α) :
    holEl i (xs ++ ys) = if i < xs.length then holEl i xs else holEl (i - xs.length) ys := by
  induction xs generalizing i with
  | nil => simp
  | cons head tail ih =>
    cases i with
    | zero => simp [holEl, holHd]
    | succ i => simpa [holEl, List.tail_cons] using ih i

/-- Replacing a block of absent slots by present values changes exactly that block. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "EL_add_SOME_SOME"]
theorem holEl_add_some_some {α : Type} (i : Nat) (pre : List (Option α))
    (xs : List α) (post : List (Option α)) :
    holEl i (pre ++ xs.map some ++ post) ≠ none ↔
      holEl i (pre ++ List.replicate xs.length none ++ post) ≠ none ∨
        (pre.length ≤ i ∧ i < pre.length + xs.length) := by
  by_cases before : i < pre.length
  · simp [holEl_append_if, before, Nat.not_le_of_gt before]
  · have after : pre.length ≤ i := Nat.le_of_not_gt before
    by_cases middle : i - pre.length < xs.length
    · have hsome : i - pre.length < (xs.map some).length := by simpa using middle
      have hnone : i - pre.length < (List.replicate xs.length (none : Option α)).length := by simpa using middle
      simp [holEl_append_if, before, middle, holEl_eq_getElem _ _ hsome,
        holEl_eq_getElem _ _ hnone, after, show i < pre.length + xs.length by omega]
    · have afterMiddle : pre.length + xs.length ≤ i := by omega
      simp [holEl_append_if, before, middle, Nat.not_lt_of_ge afterMiddle]

/-- The allocation counter is threaded for source correspondence but does not
affect the generated bindings. -/
theorem allocDefs_ignoreCounter {α : Type} (names : List α) (first second base : Nat) :
    allocDefs first base names = allocDefs second base names := by
  induction names generalizing first second base with
  | nil => rfl
  | cons name names ih =>
    simp only [allocDefs]
    exact congrArg (fun tail => (name, .glob omTra base) :: tail) (ih (first + 1) (second + 1) (base + 1))

private theorem allocDefs_lookup_index {K : Type} (names : List K) :
    ∀ (next base n : Nat) (bound : n < names.length), names.Nodup →
      holALookup (allocDefs next base names) names[n] = some (.glob omTra (base + n)) := by
  classical
  induction names with
  | nil => intro next base n bound; simp at bound
  | cons head tail ih =>
    intro next base n bound distinct
    obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
    cases n with
    | zero => simp [allocDefs, holALookup]
    | succ n =>
      have bound' : n < tail.length := by simpa using bound
      have different : tail[n] ≠ head := by
        intro same
        apply absent
        simpa [same] using List.getElem_mem bound'
      simpa [allocDefs, holALookup, different, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (next + 1) (base + 1) n bound' tailDistinct

/-- A distinct function's reversed allocation is found at its corresponding global slot. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "ALOOKUP_alloc_defs_EL"]
theorem aLookup_allocDefs_el {K A B : Type} [Nonempty K] :
    ∀ (funs : List (K × A × B)) (l n m : Nat),
      (funs.map fun (x, _, _) => x).Nodup ∧ n < funs.length →
      ∃ tt, holALookup (allocDefs m l (funs.reverse.map Prod.fst)) (holEl n (funs.map Prod.fst)) =
        some (.glob tt (l + funs.length - (n + 1))) := by
  classical
  intro funs l n m ⟨distinct, bound⟩
  let names := funs.map Prod.fst
  let pos := names.length - (n + 1)
  have len : names.length = funs.length := by simp [names]
  have posBound : pos < names.reverse.length := by simp [pos, len]; omega
  have reverseDistinct : names.reverse.Nodup := by
    rw [List.Nodup, List.pairwise_reverse]
    exact distinct.imp (fun h => Ne.symm h)
  have indexEq : names.reverse[pos] = names[n] := by
    rw [List.getElem_reverse]
    congr 1
    dsimp [pos]
    omega
  have sourceBound : n < names.length := by simpa [len] using bound
  have found := allocDefs_lookup_index names.reverse m l pos posBound reverseDistinct
  rw [indexEq] at found
  refine ⟨omTra, ?_⟩
  rw [holEl_eq_getElem n names sourceBound]
  have arithmetic : l + names.length - (n + 1) = l + pos := by dsimp [pos]; omega
  simpa only [names, List.map_reverse, ← len, arithmetic] using found

/-- Lookup in reversed bindings identifies the matching allocated global and
value at the same position, even when names repeat. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "ALOOKUP_alloc_defs"]
theorem allocDefs_lookup {K V : Type} (env : List (K × V)) (name : K) (value : V)
    (base next : Nat) (lookup : holALookup env.reverse name = some value) :
    ∃ n t, holALookup (allocDefs next base (env.reverse.map Prod.fst)) name =
        some (.glob t (base + n)) ∧
      n < (env.map Prod.fst).length ∧
      holEl n ((env.map Prod.snd).map some).reverse = some value := by
  classical
  have aux : ∀ (entries : List (K × V)) (next base : Nat),
      holALookup entries name = some value →
      ∃ i, holALookup (allocDefs next base (entries.map Prod.fst)) name = some (.glob omTra (base + i)) ∧
        i < entries.length ∧ (entries.map (fun p => some p.2))[i]? = some (some value) := by
    intro entries
    induction entries with
    | nil => simp [holALookup]
    | cons head tail ih =>
      intro next base found
      rcases head with ⟨key, current⟩
      by_cases same : name = key
      · subst key
        simp [holALookup] at found
        subst current
        refine ⟨0, ?_, by simp, by simp⟩
        simp [allocDefs, holALookup]
      · have tailLookup : holALookup tail name = some value := by
          simpa [holALookup, same] using found
        obtain ⟨i, allocated, bound, slot⟩ := ih (next + 1) (base + 1) tailLookup
        refine ⟨i + 1, ?_, by simp; omega, ?_⟩
        · simpa [allocDefs, holALookup, same, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using allocated
        · simpa using slot
  obtain ⟨n, allocated, bound, slot⟩ := aux env.reverse next base lookup
  have len : n < ((env.map Prod.snd).map some).reverse.length := by simpa using bound
  refine ⟨n, omTra, allocated, by simpa using bound, ?_⟩
  have slot' : ((env.map Prod.snd).map some).reverse[n]? = some (some value) := by
    simpa [List.map_reverse, List.map_map, Function.comp_def] using slot
  rw [List.getElem?_eq_getElem len] at slot'
  rw [holEl_eq_getElem n _ len]
  exact Option.some.inj slot'

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
  have reversedLookup : holALookup flatEnv.reverse.reverse name = some flat := by
    simpa [holALookup_eq_lookup] using flatLookup
  obtain ⟨i, trace, allocated, bound, valueSlot⟩ :=
    allocDefs_lookup flatEnv.reverse name flat pre.length next reversedLookup
  have boundFlat : i < flatEnv.length := by simpa using bound
  have nativeAllocated : (allocDefs next pre.length (flatEnv.map Prod.fst)).lookup name =
      some (.glob trace (pre.length + i)) := by
    simpa [holALookup_eq_lookup] using allocated
  have flatBound : i < (flatEnv.map (fun p => some p.2)).length := by simpa using boundFlat
  have valueSlot' : (flatEnv.map (fun p => some p.2))[i]? = some (some flat) := by
    rw [List.getElem?_eq_getElem flatBound]
    simpa [holEl_eq_getElem i _ flatBound, List.map_map, Function.comp_def] using valueSlot
  have globalBound : pre.length + i < genv.v.length := by
    rw [slots]
    simp only [List.length_append, List.length_map]
    omega
  have globalSlot : genv.v[pre.length + i]?.getD none = some flat := by
    rw [slots]
    rw [List.getElem?_append_right (l₁ := pre) (by omega), Nat.add_sub_cancel_left]
    have inBlock : i < (flatEnv.map fun p => some p.2).length := by simpa using boundFlat
    rw [List.getElem?_append_left inBlock, valueSlot']
    rfl
  apply GlobalLookupRel.intro genv _ _ source (pre.length + i) flat trace
  · simpa [emptyEnv, alistToNs, nsLookup] using nativeAllocated
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

/-- Distinct names make membership determine lookup; this is list infrastructure
for the original initializer proof, with no separate HOL declaration. -/
theorem lookup_of_mem_nodup {α : Type} (entries : List (VarN × α))
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
      have member := List.mem_reverse.mp (holALookup_member entries.reverse name value
        (by simpa [holALookup_eq_lookup] using reversed))
      have impossible := lookup_of_mem_nodup entries name value member distinct
      rw [lookup] at impossible
      cases impossible
  | some value =>
    exact lookup_of_mem_nodup entries.reverse name value
      (List.mem_reverse.mpr (holALookup_member entries name value (by simpa [holALookup_eq_lookup] using lookup))) reversedDistinct

namespace AllocDefsReversePort
/-- Canonical global-environment finite-map carrier roundtrip. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env
end AllocDefsReversePort

/-- Reversed declaration bindings produce the source global invariant when
names are distinct. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "global_env_inv_extend"
  (fmap_as_finite_support := [c, tys])]
theorem globalEnvInv_allocDefs_reverse (source : List (VarN × SemanticPrimitivesHOL.Value))
    (genv : GlobalEnv) (flat : List (VarN × FlatSem.Value)) (next : Nat)
    (pre post : List (Option FlatSem.Value))
    (premises : EnvRel genv (alistToNs source) flat ∧
      genv.v = (pre ++ (flat.map Prod.snd).reverse.map some) ++ post ∧
      (source.map Prod.fst).Nodup) :
    GlobalEnvInv genv
      { emptyEnv with v := alistToNs (allocDefs next pre.length ((flat.map Prod.fst).reverse)) }
      (fun _ => False) ⟨alistToNs source, nsEmpty⟩ := by
  obtain ⟨related, slots, distinct⟩ := premises
  have reversedRelated : EnvRel genv (alistToNs source.reverse) flat.reverse := by
    apply (envRel_alist_iff genv _ _).mpr
    exact List.forall₂_reverse_iff.mpr ((envRel_alist_iff genv _ _).mp related)
  have reversedSlots : genv.v = pre ++ (flat.reverse.map (fun p => some p.2) ++ post) := by
    simpa [List.map_reverse, List.map_map, Function.comp_def, List.append_assoc] using slots
  have inv := globalEnvInv_allocDefs genv source.reverse flat.reverse reversedRelated pre post reversedSlots next
  cases inv with
  | intro _ _ _ values constructors =>
    simp only [List.map_reverse] at *
    apply GlobalEnvInv.intro
    · intro id value unshadowed lookup
      apply values id value unshadowed
      cases id with
      | short name =>
        simpa [alistToNs, nsLookup, lookup_reverse_of_nodup source name distinct] using lookup
      | long moduleName id => simp [alistToNs, nsLookup] at lookup
    · exact constructors

end Flapjack.Compiler.Backend.SourceToFlat
