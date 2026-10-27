import Flapjack.Compiler.Backend.SourceToFlat.Proofs.GlobalSlots
import Mathlib.Data.Set.Basic

/-! Index blocks and allocated indices used by the source-to-flat proof. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- The three disjoint classes of compiler indices. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "idx_types"]
inductive IndexKind where
  | variable | type | exception
  deriving DecidableEq

/-- Componentwise ordering of the source compiler's allocation counters. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "idx_prev_def"]
def idxPrev (first second : NextIndices) : Prop :=
  first.vidx ≤ second.vidx ∧ first.tidx ≤ second.tidx ∧ first.eidx ≤ second.eidx

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "idx_prev_refl"]
theorem idxPrev_refl (idx : NextIndices) : idxPrev idx idx := by
  simp [idxPrev]

@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "idx_prev_trans"]
theorem idxPrev_trans (first middle last : NextIndices)
    (related : idxPrev first middle ∧ idxPrev middle last) : idxPrev first last := by
  rcases related with ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩
  exact ⟨Nat.le_trans a d, Nat.le_trans b e, Nat.le_trans c f⟩

/-- Finite index ranges reserved by a compilation block. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "idx_block_def"]
def idxBlock (start finish : NextIndices) : Set (Nat × IndexKind) :=
  fun (i, kind) => match kind with
    | .variable => start.vidx ≤ i ∧ i < finish.vidx
    | .type => start.tidx ≤ i ∧ i < finish.tidx
    | .exception => start.eidx ≤ i ∧ i < finish.eidx

/-- Indices after the final compiler counters. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "idx_final_block_def"]
def idxFinalBlock (start : NextIndices) : Set (Nat × IndexKind) :=
  fun (i, kind) => match kind with
    | .variable => start.vidx ≤ i
    | .type => start.tidx ≤ i
    | .exception => start.eidx ≤ i

/-- Pairwise disjointness of a list of sets, with the original bounded indices. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "ALL_DISJOINT_DEF"]
def allDisjoint {α : Type} (sets : List (Set α)) : Prop :=
  ∀ i j (hi : i < sets.length) (hj : j < sets.length), i ≠ j → sets[i] ∩ sets[j] = ∅

/-- Relate global-slot length to the last counter, as in the source oracle
configuration; no oracle yields only the end-counter bound. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "fin_idx_match_def"]
def finIdxMatch (length : Nat) (finish : NextIndices) (next : Option Config) : Prop :=
  match next with
  | none => finish.vidx ≤ length
  | some config => config.next.vidx = length

/-- Canonical finite-map carrier roundtrip for the imported global environment. -/
theorem holFmapAsFiniteSupportWitness (env : GlobalEnv) :
    GlobalEnv.ofBroad (GlobalEnv.toBroad env) = env := GlobalEnv.holFmapAsFiniteSupportWitness env

/-- The allocated variable, type, and exception index sets. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "genv_allocated_idxs_def"
  (fmap_as_finite_support := [c, tys])]
def genvAllocatedIndices (genv : GlobalEnv) : Set (Nat × IndexKind) :=
  fun (i, kind) => match kind with
    | .variable => i < genv.v.length ∧ genv.v[i]?.getD none ≠ none
    | .type => (∃ cn arity, (genv.c.lookup ((cn, some i), arity)).isSome) ∨
        (genv.tys.lookup i).isSome
    | .exception => ∃ arity, (genv.c.lookup ((i, none), arity)).isSome

/-- The variable-index projection is precisely the initialized-slot predicate
used by the declaration initialization proof. -/
theorem allocatedIndices_variable (genv : GlobalEnv) (i : Nat) :
    (i, .variable) ∈ genvAllocatedIndices genv ↔ allocatedGlobalSlot genv i := by
  change (i < genv.v.length ∧ genv.v[i]?.getD none ≠ none) ↔ allocatedGlobalSlot genv i
  simp [allocatedGlobalSlot, Option.isSome_iff_ne_none]

/-- Disjointness of the current compiler block and allocated indices gives the
free-range premise needed to initialize declaration globals. -/
theorem free_variable_range (genv : GlobalEnv) (start finish : NextIndices)
    (disjoint : ∀ key, key ∈ idxBlock start finish → key ∈ genvAllocatedIndices genv → False)
    (count : Nat) (fits : start.vidx + count ≤ finish.vidx) :
    ∀ i, start.vidx ≤ i → i < start.vidx + count → ¬ allocatedGlobalSlot genv i := by
  intro i low high allocated
  have reserved : (i, .variable) ∈ idxBlock start finish := ⟨low, by omega⟩
  have used : (i, .variable) ∈ genvAllocatedIndices genv := (allocatedIndices_variable genv i).mpr allocated
  exact disjoint (i, .variable) reserved used

/-- The first and fourth sets in HOL's index-range condition are disjoint. -/
theorem currentBlock_disjoint_allocated (genv : GlobalEnv) (start finish final : NextIndices)
    (other : Set (Nat × IndexKind))
    (disjoint : allDisjoint [idxBlock start finish, idxFinalBlock final, other, genvAllocatedIndices genv]) :
    ∀ key, key ∈ idxBlock start finish → key ∈ genvAllocatedIndices genv → False := by
  intro key reserved allocated
  have h := disjoint 0 3 (by simp) (by simp) (by decide)
  have member : key ∈ idxBlock start finish ∩ genvAllocatedIndices genv := ⟨reserved, allocated⟩
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
  rw [h] at member
  exact member

/-- The original final-counter cases both place the end of a block within
the global-slot list. -/
theorem endIdx_le_length (length : Nat) (finish final : NextIndices) (next : Option Config)
    (previous : idxPrev finish final)
    (nextMatch : match next with | none => True | some config => final = config.next)
    (lengthMatch : finIdxMatch length finish next) : finish.vidx ≤ length := by
  cases next with
  | none => exact lengthMatch
  | some config =>
    change final = config.next at nextMatch
    change config.next.vidx = length at lengthMatch
    have finalLength : final.vidx = length := (congrArg NextIndices.vidx nextMatch).trans lengthMatch
    exact finalLength ▸ previous.1

/-- The disjointness and final-counter components of the original index
invariant produce the reserved blank block. The source-oracle relation itself
is still a separate obligation. -/
theorem indexInvariant_blank_block (genv : GlobalEnv) (start finish final : NextIndices)
    (other : Set (Nat × IndexKind)) (next : Option Config) (count : Nat)
    (previous : idxPrev finish final)
    (nextMatch : match next with | none => True | some config => final = config.next)
    (lengthMatch : finIdxMatch genv.v.length finish next)
    (disjoint : allDisjoint [idxBlock start finish, idxFinalBlock final, other, genvAllocatedIndices genv])
    (fits : start.vidx + count ≤ finish.vidx) :
    ∃ pre post, genv.v = pre ++ (List.replicate count none ++ post) ∧ pre.length = start.vidx := by
  have finishBound := endIdx_le_length genv.v.length finish final next previous nextMatch lengthMatch
  have rangeBound : start.vidx + count ≤ genv.v.length := Nat.le_trans fits finishBound
  have free := free_variable_range genv start finish
    (currentBlock_disjoint_allocated genv start finish final other disjoint) count fits
  exact split_blank_slots genv.v start.vidx count rangeBound
    (blank_of_unallocated genv start.vidx count rangeBound free)

/-- Index-block disjointness and the final-counter conditions supply the
reserved slots for the factored declaration initialization step. The full
source oracle invariant and remaining postconditions are not yet included. -/
theorem evaluate_makeVarls_indexInvariant {C F : Type} (genv : GlobalEnv)
    (sourceEnv : List (Flapjack.AstHOL.VarN × Flapjack.SemanticPrimitivesHOL.Value))
    (flatEnv : List (Flapjack.AstHOL.VarN × FlatSem.Value))
    (related : EnvRel genv (Flapjack.NamespaceHOL.alistToNs sourceEnv) flatEnv)
    (distinct : (sourceEnv.map Prod.fst).Nodup)
    (sourceState : Flapjack.SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState) (globals : flatState.globals = genv.v)
    (start finish final : NextIndices) (other : Set (Nat × IndexKind)) (next : Option Config)
    (previous : idxPrev finish final)
    (nextMatch : match next with | none => True | some config => final = config.next)
    (lengthMatch : finIdxMatch genv.v.length finish next)
    (disjoint : allDisjoint [idxBlock start finish, idxFinalBlock final, other, genvAllocatedIndices genv])
    (fits : start.vidx + flatEnv.length ≤ finish.vidx)
    (n : Nat) (trace : BackendCommon.Tra) :
    ∃ pre post, pre.length = start.vidx ∧
      flatState.globals = pre ++ (List.replicate flatEnv.length none ++ post) ∧
      let values := flatEnv.reverse.map Prod.snd
      let finalSlots := pre ++ (values.map some ++ post)
      let finalEnv := { genv with v := finalSlots }
      let finalState := { flatState with globals := finalSlots }
      FlatSem.evaluate ⟨flatEnv⟩ flatState
          [makeVarls n trace start.vidx (flatEnv.reverse.map Prod.fst)] =
          (finalState, .val [FlatSem.unitValue]) ∧
        GlobalGrowth genv finalEnv ∧ StateRel finalEnv sourceState finalState ∧
        GlobalEnvInv finalEnv
          { emptyEnv with v := Flapjack.NamespaceHOL.alistToNs (allocDefs n start.vidx (flatEnv.reverse.map Prod.fst)) }
          (fun _ => False) ⟨Flapjack.NamespaceHOL.alistToNs sourceEnv, Flapjack.NamespaceHOL.nsEmpty⟩ := by
  have finishBound := endIdx_le_length genv.v.length finish final next previous nextMatch lengthMatch
  have rangeBound : start.vidx + flatEnv.length ≤ genv.v.length := Nat.le_trans fits finishBound
  have free := free_variable_range genv start finish
    (currentBlock_disjoint_allocated genv start finish final other disjoint) flatEnv.length fits
  exact evaluate_makeVarls_unallocated genv sourceEnv flatEnv related distinct sourceState flatState
    stateRel globals start.vidx rangeBound free n trace

end Flapjack.Compiler.Backend.SourceToFlat
