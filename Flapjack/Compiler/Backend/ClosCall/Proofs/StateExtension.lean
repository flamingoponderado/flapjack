import Flapjack.Compiler.Backend.ClosCall.Proofs.KnownOrigins

/-! Extension of direct-call compiler states and their auxiliary code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

/-- HOL association-list lookup uses logical equality for an arbitrary key
type. This proof-side rendering is noncomputable because no equality
instance is assumed. -/
noncomputable def logicalAssocLookup {K V : Type} (key : K) (entries : List (K × V)) : Option V := by
  classical
  exact (entries.find? (fun entry => decide (key = entry.1))).map Prod.snd

/-- The empty association list has no binding. -/
theorem logicalAssocLookup_nil {K V : Type} (key : K) :
    logicalAssocLookup key ([] : List (K × V)) = none := rfl

/-- Association lookup chooses the first equal key, as HOL `ALOOKUP` does. -/
theorem logicalAssocLookup_cons {K V : Type} (key other : K) (value : V) (entries : List (K × V)) :
    (key = other → logicalAssocLookup key ((other, value) :: entries) = some value) ∧
      (key ≠ other → logicalAssocLookup key ((other, value) :: entries) = logicalAssocLookup key entries) := by
  classical
  constructor <;> intro equal <;> simp [logicalAssocLookup, List.find?, equal]

/-- On numeric labels, logical lookup agrees with the executable
association-list lookup. -/
theorem logicalAssocLookup_nat {V : Type} (key : Nat) (entries : List (Nat × V)) :
    logicalAssocLookup key entries = sptAListLookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨label, value⟩ := entry
    by_cases equal : key = label <;>
      simp [logicalAssocLookup, List.find?, sptAListLookup, equal, ← ih]

/-- The new state extends the old sparse map and preserves each old lookup;
its auxiliary labels are distinct. Key, payload and sparse-map value types
remain independent as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "subg_def"]
def stateExtends {A K V : Type} (g0 g1 : Spt A × List (K × V)) : Prop :=
  sptSubspt g0.1 g1.1 ∧
    (∀ key value, logicalAssocLookup key g0.2 = some value →
      logicalAssocLookup key g1.2 = some value) ∧
    (g1.2.map Prod.fst).Nodup

/-- A state with distinct labels extends itself. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "subg_refl"]
theorem stateExtends_refl {A K V : Type} (g : Spt A × List (K × V))
    (distinct : (g.2.map Prod.fst).Nodup) : stateExtends g g := by
  refine ⟨?_, ?_, distinct⟩
  · intro key member
    exact ⟨member, rfl⟩
  · intro _ _ h
    exact h

/-- Compiler-state extension is transitive. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "subg_trans"]
theorem stateExtends_trans {A K V : Type} (g1 g2 g3 : Spt A × List (K × V))
    (h12 : stateExtends g1 g2) (h23 : stateExtends g2 g3) : stateExtends g1 g3 := by
  refine ⟨?_, ?_, h23.2.2⟩
  · intro key member
    obtain ⟨middle, firstEq⟩ := h12.1 key member
    obtain ⟨last, secondEq⟩ := h23.1 key middle
    exact ⟨last, secondEq.trans firstEq⟩
  · intro key value lookup
    exact h23.2.1 key value (h12.2.1 key value lookup)

private theorem knownExt_subspt (initial final : State) (growth : KnownExt initial final) :
    sptSubspt initial.1 final.1 := by
  intro key member
  have newMember := growth key member
  refine ⟨newMember, ?_⟩
  have oldValue : sptLookup key initial.1 = some () := by
    cases lookup : sptLookup key initial.1 with
    | none => simp [sptMem, sptDomain, lookup] at member
    | some value => cases value; rfl
  have newValue : sptLookup key final.1 = some () := by
    cases lookup : sptLookup key final.1 with
    | none => simp [sptDomain, lookup] at newMember
    | some value => cases value; rfl
  rw [oldValue, newValue]

private theorem lookup_preserved_of_suffix {V : Type} (old new : List (Nat × V))
    (suffix : old <:+ new) (distinct : (new.map Prod.fst).Nodup)
    (key : Nat) (value : V) (lookup : sptAListLookup key old = some value) :
    sptAListLookup key new = some value := by
  obtain ⟨front, eq⟩ := suffix
  have oldMember := sptAListLookup_mem key old value lookup
  have member : (key, value) ∈ new := by
    rw [← eq]
    exact List.mem_append_right _ oldMember
  apply sptAListLookup_eq_of_mem_unique key value new member
  intro other otherMember
  have injective := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst distinct)).mp distinct
  have pairEq : (key, other) = (key, value) := injective _ otherMember _ member rfl
  exact congrArg Prod.snd pairEq

/-- Successful production traversal extends its incoming state when input
locations are distinct and fresh and incoming code labels are distinct. -/
theorem callsListBounded_stateExtends (fuel : Nat) (es : List ClosLang.Exp)
    (initial final : State) (out : List ClosLang.Exp)
    (run : callsListBounded fuel es initial = some (out, final))
    (distinct : (ClosProps.codeLocations es).Nodup)
    (fresh : LabelsFresh (ClosProps.codeLocations es) initial)
    (oldDistinct : (initial.2.map Prod.fst).Nodup) : stateExtends initial final := by
  have newDistinct := callsListBounded_labelsDistinct fuel es initial final out run distinct fresh oldDistinct
  refine ⟨knownExt_subspt initial final (callsListBounded_knownExt fuel es initial final out run), ?_, newDistinct⟩
  intro key value lookup
  rw [logicalAssocLookup_nat] at lookup ⊢
  exact lookup_preserved_of_suffix initial.2 final.2
    (callsListBounded_suffix fuel es initial final out run) newDistinct key value lookup

end Flapjack.Compiler.Backend.ClosCall
