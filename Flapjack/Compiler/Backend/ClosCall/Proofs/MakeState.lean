module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Misc.Option
public import Flapjack.Misc.Sptree.ToAList

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Construct direct-call compiler states from a sparse map and code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- The code parameter uses the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_makeState_code {B : Type}
    (code : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Construct the auxiliary code list when every known location has code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "make_g_def"
  (fmap_as_finite_support_parameters := [code])]
noncomputable def makeState {A B : Type} [Nonempty B] (d : Spt A)
    (code : HolFiniteMapExact Nat B) : Option (Spt A × List (Nat × B)) := by
  classical
  exact if Set.image Nat.succ (sptDomain d) ⊆ code.domain then
    some (d, (sptToAList d).map (fun entry => (entry.1 + 1, holThe (code.lookup (entry.1 + 1)))))
  else none

/-- The code parameter in makeState well-formedness uses the canonical codec. -/
theorem holFmapAsFiniteSupportParamWitness_makeState_wellFormed_code {B : Type}
    (code : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_makeState_code code key

/-- Every state produced by makeState satisfies the full compiler-state invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "make_g_wfg"
  (fmap_as_finite_support_parameters := [code])]
theorem makeState_wellFormed {A B : Type} [Nonempty B] (d : Spt A)
    (code : HolFiniteMapExact Nat B) (g : Spt A × List (Nat × B))
    (h : makeState d code = some g) : wellFormed g := by
  classical
  unfold makeState at h
  split at h
  next valid =>
    simp only [Option.some.injEq] at h
    subst g
    constructor
    · funext key
      apply propext
      simp only [List.map_map, List.mem_map, Function.comp_def]
      constructor
      · rintro ⟨⟨loc, value⟩, member, eq⟩
        refine ⟨loc, ?_, ?_⟩
        · exact (sptDomain_iff_lookup d loc).2 ⟨value, (sptMemToAList d loc value).1 member⟩
        · simpa [Nat.succ_eq_add_one] using eq
      · rintro ⟨loc, member, eq⟩
        obtain ⟨value, found⟩ := (sptDomain_iff_lookup d loc).1 member
        refine ⟨(loc, value), (sptMemToAList d loc value).2 found, ?_⟩
        simpa [Nat.succ_eq_add_one] using eq
    · have distinct := sptAllDistinctMapFstToAList d
      have shifted : (((sptToAList d).map Prod.fst).map (fun k => k + 1)).Nodup :=
        (List.nodup_map_iff (fun _ _ eq => Nat.add_right_cancel eq)).2 distinct
      simpa [List.map_map, Function.comp_def] using shifted
  next invalid => simp at h

end Flapjack.Compiler.Backend.ClosCall
