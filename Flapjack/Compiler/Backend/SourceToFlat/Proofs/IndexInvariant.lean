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

/-- Appending uninitialized global slots does not allocate any indices. -/
theorem genvAllocatedIndices_append_none (genv : GlobalEnv) (count : Nat) :
    genvAllocatedIndices { genv with v := genv.v ++ List.replicate count none } =
      genvAllocatedIndices genv := by
  ext ⟨i, kind⟩
  cases kind with
  | «variable» =>
    change (i < (genv.v ++ List.replicate count none).length ∧
      ((genv.v ++ List.replicate count none)[i]?).getD none ≠ none) ↔
      (i < genv.v.length ∧ (genv.v[i]?).getD none ≠ none)
    by_cases bound : i < genv.v.length
    · simp [List.getElem?_append, bound]; omega
    · simp [List.getElem?_append, bound]
      intro inRange
      have index : i - genv.v.length < (List.replicate count (none : Option FlatSem.Value)).length := by
        simp; omega
      simp [List.getElem?_eq_getElem index]
  | «type» => rfl
  | «exception» => rfl

/-- Filling one blank global slot adds exactly its variable index to the
allocated-index set. -/
theorem genvAllocatedIndices_fillSlot (genv : GlobalEnv) (idx : Nat) (value : FlatSem.Value)
    (empty : genv.v[idx]? = some none) :
    genvAllocatedIndices { genv with v := genv.v.set idx (some value) } =
      genvAllocatedIndices genv ∪ {(idx, .variable)} := by
  have bound : idx < genv.v.length := (List.getElem?_eq_some_iff.mp empty).1
  ext ⟨i, kind⟩
  change genvAllocatedIndices { genv with v := genv.v.set idx (some value) } (i, kind) ↔
    genvAllocatedIndices genv (i, kind) ∨ (i, kind) = (idx, .variable)
  cases kind with
  | «variable» =>
    change (i < (genv.v.set idx (some value)).length ∧
      (genv.v.set idx (some value))[i]?.getD none ≠ none) ↔
      (i < genv.v.length ∧ genv.v[i]?.getD none ≠ none) ∨ (i, IndexKind.variable) = (idx, .variable)
    by_cases same : i = idx
    · subst i
      simp [bound]
    · simp [Ne.symm same, same]
  | «type» => simp [genvAllocatedIndices]
  | «exception» => simp [genvAllocatedIndices]

/-- Moving a single point from a reserved block into the allocated set
preserves four-way disjointness when the remaining block excludes it. -/
theorem allDisjoint_consume {α : Type} (block remaining future other allocated : Set α) (point : α)
    (old : allDisjoint [block, future, other, allocated])
    (subset : remaining ⊆ block) (inBlock : point ∈ block) (notRemaining : point ∉ remaining) :
    allDisjoint [remaining, future, other, allocated ∪ {point}] := by
  have pair (i j : Nat) (hi : i < 4) (hj : j < 4) (ne : i ≠ j) :
      ∀ x, x ∈ ([block, future, other, allocated] : List (Set α))[i] →
        x ∈ ([block, future, other, allocated] : List (Set α))[j] → False := by
    intro x xi xj
    have h := old i j (by simpa using hi) (by simpa using hj) ne
    have hx : x ∈ ([block, future, other, allocated] : List (Set α))[i] ∩
        ([block, future, other, allocated] : List (Set α))[j] := ⟨xi, xj⟩
    rw [h] at hx
    exact hx
  have p01 := pair 0 1 (by omega) (by omega) (by omega)
  have p02 := pair 0 2 (by omega) (by omega) (by omega)
  have p03 := pair 0 3 (by omega) (by omega) (by omega)
  have p12 := pair 1 2 (by omega) (by omega) (by omega)
  have p13 := pair 1 3 (by omega) (by omega) (by omega)
  have p23 := pair 2 3 (by omega) (by omega) (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at p01 p02 p03 p12 p13 p23
  have q03 : ∀ x, x ∈ remaining → x ∈ allocated ∪ {point} → False := by
    intro x h mem
    rcases mem with mem | mem
    · exact p03 x (subset h) mem
    · have eq : x = point := mem
      exact notRemaining (eq ▸ h)
  have q13 : ∀ x, x ∈ future → x ∈ allocated ∪ {point} → False := by
    intro x h mem
    rcases mem with mem | mem
    · exact p13 x h mem
    · have eq : x = point := mem
      exact p01 point inBlock (eq ▸ h)
  have q23 : ∀ x, x ∈ other → x ∈ allocated ∪ {point} → False := by
    intro x h mem
    rcases mem with mem | mem
    · exact p23 x h mem
    · have eq : x = point := mem
      exact p02 point inBlock (eq ▸ h)
  intro i j hi hj ne
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp at hj; omega
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Set.mem_inter_iff] at hx
  all_goals try omega
  all_goals rcases hx with ⟨a, b⟩
  all_goals
    first
    | exact p01 x (subset a) b
    | exact p01 x (subset b) a
    | exact p02 x (subset a) b
    | exact p02 x (subset b) a
    | exact q03 x a b
    | exact q03 x b a
    | exact p12 x a b
    | exact p12 x b a
    | exact q13 x a b
    | exact q13 x b a
    | exact q23 x a b
    | exact q23 x b a

/-- Split an old reserved block back out of the combined third set after an
incremental compilation step. -/
theorem allDisjoint_restore {α : Type} (current future oldBlock other allocated : Set α)
    (valid : allDisjoint [current, future, oldBlock ∪ other, allocated])
    (oldSeparate : ∀ x, x ∈ oldBlock → x ∈ other → False) :
    allDisjoint [oldBlock, future, other, allocated] := by
  have pair (i j : Nat) (hi : i < 4) (hj : j < 4) (ne : i ≠ j) :
      ∀ x, x ∈ ([current, future, oldBlock ∪ other, allocated] : List (Set α))[i] →
        x ∈ ([current, future, oldBlock ∪ other, allocated] : List (Set α))[j] → False := by
    intro x xi xj
    have h := valid i j (by simpa using hi) (by simpa using hj) ne
    have hx : x ∈ ([current, future, oldBlock ∪ other, allocated] : List (Set α))[i] ∩
        ([current, future, oldBlock ∪ other, allocated] : List (Set α))[j] := ⟨xi, xj⟩
    rw [h] at hx
    exact hx
  have p12 := pair 1 2 (by omega) (by omega) (by omega)
  have p13 := pair 1 3 (by omega) (by omega) (by omega)
  have p23 := pair 2 3 (by omega) (by omega) (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at p12 p13 p23
  have q01 : ∀ x, x ∈ oldBlock → x ∈ future → False := by
    intro x a b; exact p12 x b (Or.inl a)
  have q03 : ∀ x, x ∈ oldBlock → x ∈ allocated → False := by
    intro x a b; exact p23 x (Or.inl a) b
  have q12 : ∀ x, x ∈ future → x ∈ other → False := by
    intro x a b; exact p12 x a (Or.inr b)
  have q23 : ∀ x, x ∈ other → x ∈ allocated → False := by
    intro x a b; exact p23 x (Or.inr a) b
  intro i j hi hj ne
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp at hj; omega
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Set.mem_inter_iff] at hx
  all_goals try omega
  all_goals rcases hx with ⟨a, b⟩
  all_goals
    first
    | exact q01 x a b
    | exact q01 x b a
    | exact oldSeparate x a b
    | exact oldSeparate x b a
    | exact q03 x a b
    | exact q03 x b a
    | exact q12 x a b
    | exact q12 x b a
    | exact p13 x a b
    | exact p13 x b a
    | exact q23 x a b
    | exact q23 x b a

/-- Split the second of four disjoint sets, while moving the first into the
third. This is the set rearrangement required by an incremental Eval step. -/
theorem allDisjoint_four_advance {α : Type} (oldBlock oldFuture other allocated newBlock newFuture : Set α)
    (old : allDisjoint [oldBlock, oldFuture, other, allocated])
    (blockSubset : newBlock ⊆ oldFuture) (futureSubset : newFuture ⊆ oldFuture)
    (separate : ∀ x, x ∈ newBlock → x ∈ newFuture → False) :
    allDisjoint [newBlock, newFuture, oldBlock ∪ other, allocated] := by
  have pair (i j : Nat) (hi : i < 4) (hj : j < 4) (ne : i ≠ j) :
      ∀ x, x ∈ ([oldBlock, oldFuture, other, allocated] : List (Set α))[i] →
        x ∈ ([oldBlock, oldFuture, other, allocated] : List (Set α))[j] → False := by
    intro x xi xj
    have h := old i j (by simpa using hi) (by simpa using hj) ne
    have hx : x ∈ ([oldBlock, oldFuture, other, allocated] : List (Set α))[i] ∩
        ([oldBlock, oldFuture, other, allocated] : List (Set α))[j] := ⟨xi, xj⟩
    rw [h] at hx
    exact hx
  have p01 := pair 0 1 (by omega) (by omega) (by omega)
  have p03 := pair 0 3 (by omega) (by omega) (by omega)
  have p12 := pair 1 2 (by omega) (by omega) (by omega)
  have p13 := pair 1 3 (by omega) (by omega) (by omega)
  have p23 := pair 2 3 (by omega) (by omega) (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at p01 p03 p12 p13 p23
  clear pair old
  have q02 : ∀ x, x ∈ newBlock → x ∈ oldBlock ∪ other → False := by
    intro x a b
    rcases b with b | b
    · exact p01 x b (blockSubset a)
    · exact p12 x (blockSubset a) b
  have q03 : ∀ x, x ∈ newBlock → x ∈ allocated → False := by
    intro x a b; exact p13 x (blockSubset a) b
  have q12 : ∀ x, x ∈ newFuture → x ∈ oldBlock ∪ other → False := by
    intro x a b
    rcases b with b | b
    · exact p01 x b (futureSubset a)
    · exact p12 x (futureSubset a) b
  have q13 : ∀ x, x ∈ newFuture → x ∈ allocated → False := by
    intro x a b; exact p13 x (futureSubset a) b
  have q23 : ∀ x, x ∈ oldBlock ∪ other → x ∈ allocated → False := by
    intro x a b
    rcases a with a | a
    · exact p03 x a b
    · exact p23 x a b
  clear p01 p03 p12 p13 p23 blockSubset futureSubset
  intro i j hi hj ne
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp at hj; omega
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hi' with rfl | rfl | rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Set.mem_inter_iff] at hx
  all_goals try omega
  all_goals rcases hx with ⟨a, b⟩
  all_goals
    first
    | exact separate x a b
    | exact separate x b a
    | exact q02 x a b
    | exact q02 x b a
    | exact q03 x a b
    | exact q03 x b a
    | exact q12 x a b
    | exact q12 x b a
    | exact q13 x a b
    | exact q13 x b a
    | exact q23 x a b
    | exact q23 x b a

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
