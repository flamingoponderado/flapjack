import Flapjack.Compiler.Backend.ClosCall.Proofs.KnownOrigins
import Flapjack.Compiler.Backend.ClosCall.Proofs.AuxiliaryAppend

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

/-- The missing bindings for a weakly well-formed state can be taken from a
well-formed extension. The suffix contains precisely the later bindings whose
labels correspond to an already-known location but are not yet in the old
code list. This Flapjack-specific construction does not yet prove freshness
for a subsequent traversal. -/
theorem weaklyWellFormed_complete_aux (before later : State)
    (weak : weaklyWellFormed before) (beforeDistinct : (before.2.map Prod.fst).Nodup)
    (laterWf : wellFormed later) (growth : stateExtends before later) :
    ∃ suffix, wellFormed (appendAux before suffix) ∧ stateExtends (appendAux before suffix) later ∧
      List.Sublist suffix later.2 ∧
      (∀ label ∈ suffix.map Prod.fst, ∃ key, sptDomain before.1 key ∧ label = key + 1) ∧
      (∀ label ∈ suffix.map Prod.fst, label ∉ before.2.map Prod.fst) := by
  classical
  let suffix := later.2.filter (fun entry =>
    decide (entry.1 ∈ Set.image Nat.succ (sptDomain before.1) ∧ entry.1 ∉ before.2.map Prod.fst))
  have suffixMember : ∀ entry, entry ∈ suffix ↔ entry ∈ later.2 ∧
      entry.1 ∈ Set.image Nat.succ (sptDomain before.1) ∧ entry.1 ∉ before.2.map Prod.fst := by
    intro entry
    simp [suffix]
  have suffixDistinct : (suffix.map Prod.fst).Nodup := by
    have sub : List.Sublist suffix later.2 := List.filter_sublist
    exact laterWf.2.sublist (sub.map Prod.fst)
  have completedDistinct : ((before.2 ++ suffix).map Prod.fst).Nodup := by
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨beforeDistinct, suffixDistinct, ?_⟩
    intro x xmem y ymem equal
    obtain ⟨entry, entryMem, entryEq⟩ := List.mem_map.mp ymem
    have absent := ((suffixMember entry).mp entryMem).2.2
    apply absent
    have same : entry.1 = x := entryEq.trans equal.symm
    simpa [same] using xmem
  have labels : {label | label ∈ (before.2 ++ suffix).map Prod.fst} =
      Set.image Nat.succ (sptDomain before.1) := by
    ext label
    simp only [Set.mem_ofPred_eq, List.map_append, List.mem_append]
    constructor
    · intro member
      rcases member with old | new
      · exact weak old
      · obtain ⟨entry, entryMem, entryEq⟩ := List.mem_map.mp new
        simpa [← entryEq] using ((suffixMember entry).mp entryMem).2.1
    · intro member
      by_cases old : label ∈ before.2.map Prod.fst
      · exact Or.inl old
      · right
        obtain ⟨key, known, equal⟩ := member
        have laterKnown : sptDomain later.1 key := (growth.1 key known).1
        have laterLabel : label ∈ later.2.map Prod.fst := by
          have inSet : label ∈ {label | label ∈ later.2.map Prod.fst} := by
            rw [laterWf.1]
            exact ⟨key, laterKnown, equal⟩
          exact inSet
        obtain ⟨entry, entryMem, entryEq⟩ := List.mem_map.mp laterLabel
        apply List.mem_map.mpr
        refine ⟨entry, (suffixMember entry).mpr ⟨entryMem, ?_, ?_⟩, entryEq⟩
        · rw [entryEq]
          exact ⟨key, known, equal⟩
        · simpa [entryEq] using old
  refine ⟨suffix, ⟨labels, completedDistinct⟩, ⟨growth.1, ?_, laterWf.2⟩, List.filter_sublist, ?_, ?_⟩
  · intro key value found
    rw [logicalAssocLookup_nat] at found ⊢
    have member := sptAListLookup_mem key (before.2 ++ suffix) value found
    rcases List.mem_append.mp member with old | new
    · have oldLookup : sptAListLookup key before.2 = some value := by
        apply sptAListLookup_eq_of_mem_unique key value before.2 old
        intro other otherMem
        have injective := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst beforeDistinct)).mp beforeDistinct
        exact congrArg Prod.snd (injective _ otherMem _ old rfl)
      exact (logicalAssocLookup_nat key later.2).symm ▸ growth.2.1 key value
        ((logicalAssocLookup_nat key before.2).trans oldLookup)
    · have laterMember := ((suffixMember (key, value)).mp new).1
      apply sptAListLookup_eq_of_mem_unique key value later.2 laterMember
      intro other otherMem
      have injective := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst laterWf.2)).mp laterWf.2
      exact congrArg Prod.snd (injective _ otherMem _ laterMember rfl)
  · intro label member
    obtain ⟨entry, entryMem, entryEq⟩ := List.mem_map.mp member
    obtain ⟨key, known, equal⟩ := ((suffixMember entry).mp entryMem).2.1
    exact ⟨key, known, entryEq.symm.trans equal.symm⟩
  · intro label member
    obtain ⟨entry, entryMem, entryEq⟩ := List.mem_map.mp member
    simpa [entryEq] using ((suffixMember entry).mp entryMem).2.2

private theorem sptAListLookup_append {V : Type} (key : Nat) (front back : List (Nat × V)) :
    sptAListLookup key (front ++ back) =
      (match sptAListLookup key front with
       | some value => some value
       | none => sptAListLookup key back) := by
  induction front with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨label, value⟩ := entry
    by_cases same : key = label <;> simp [sptAListLookup, same, ih]

/-- Appending bindings already present in a later compiler state preserves
extension into that state. The state being appended to may have acquired new
bindings since the suffix was chosen. This is Flapjack-specific infrastructure. -/
theorem stateExtends_appendAux_of_sublist (state later : State) (suffix : List (Nat × Nat × ClosLang.Exp))
    (growth : stateExtends state later) (sub : List.Sublist suffix later.2) :
    stateExtends (appendAux state suffix) later := by
  refine ⟨growth.1, ?_, growth.2.2⟩
  intro key value found
  change logicalAssocLookup key (state.2 ++ suffix) = some value at found
  rw [logicalAssocLookup_nat, sptAListLookup_append] at found
  cases old : sptAListLookup key state.2 with
  | some oldValue =>
    simp [old] at found
    subst value
    exact growth.2.1 key oldValue ((logicalAssocLookup_nat key state.2).trans old)
  | none =>
    simp [old] at found
    have entry := sub.subset (sptAListLookup_mem key suffix value found)
    rw [logicalAssocLookup_nat]
    apply sptAListLookup_eq_of_mem_unique key value later.2 entry
    intro other otherMem
    have distinct := growth.2.2
    have injective := (List.nodup_map_iff_inj_on (List.Nodup.of_map Prod.fst distinct)).mp distinct
    exact congrArg Prod.snd (injective _ otherMem _ entry rfl)

/-- A completion drawn from a later state stays fresh for locations whose
already-known entries are present in the old code list. The same suffix
continues to extend into the later state after any intermediate state that
already extends into it. This is Flapjack-specific infrastructure. -/
theorem weaklyWellFormed_complete_aux_fresh (before after later : State) (locations : List Nat)
    (weak : weaklyWellFormed before) (beforeDistinct : (before.2.map Prod.fst).Nodup)
    (laterWf : wellFormed later) (beforeGrowth : stateExtends before later)
    (afterGrowth : stateExtends after later) (fresh : LabelsFresh locations before)
    (knownCovered : ∀ loc ∈ locations, sptDomain before.1 loc → loc + 1 ∈ before.2.map Prod.fst) :
    ∃ suffix, wellFormed (appendAux before suffix) ∧ LabelsFresh locations (appendAux before suffix) ∧
      stateExtends (appendAux after suffix) later := by
  obtain ⟨suffix, completedWf, _, sub, origins, absent⟩ :=
    weaklyWellFormed_complete_aux before later weak beforeDistinct laterWf beforeGrowth
  refine ⟨suffix, completedWf, ?_, stateExtends_appendAux_of_sublist after later suffix afterGrowth sub⟩
  intro loc locMember labelMember
  simp only [appendAux, List.map_append, List.mem_append] at labelMember
  rcases labelMember with old | new
  · exact fresh loc locMember old
  · obtain ⟨key, known, eq⟩ := origins (loc + 1) new
    have keyEq : key = loc := by omega
    subst key
    exact absent (loc + 1) new (knownCovered loc locMember known)

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

/-- Adding generated code extends the incoming compiler state when the
combined code labels are distinct. This is Flapjack-specific infrastructure
for following speculative probe states into installed code. -/
theorem codeList_stateExtends (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (state : State)
    (distinct : ((codeList loc fns state).2.map Prod.fst).Nodup) :
    stateExtends state (codeList loc fns state) := by
  refine ⟨?_, ?_, distinct⟩
  · intro key member
    have same : (codeList loc fns state).1 = state.1 := by
      rw [codeList_eq_source, codeListSource_fst]
    rw [same]
    exact ⟨member, rfl⟩
  · intro key value lookup
    rw [logicalAssocLookup_nat] at lookup ⊢
    exact lookup_preserved_of_suffix state.2 (codeList loc fns state).2
      (codeList_suffix loc fns state) distinct key value lookup

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
