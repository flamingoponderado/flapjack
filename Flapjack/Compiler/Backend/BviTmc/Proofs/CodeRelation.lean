import Flapjack.Compiler.Backend.BviTmc.Proofs.RewriteCorrespondence
import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeNames

/-! Source code and namespace invariants for the TMC simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open Bvi

/-- The source code relation records the transformed wrapper and worker
for each original function, together with its allocation precondition. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "code_rel_def"]
def codeRel (source target : Spt (Nat × Bvi.Exp)) : Prop :=
  ∀ loc arity body, sptLookup loc source = some (arity, body) →
    noMutcons body ∧ ∃ workerLoc,
      (compileExpSource loc workerLoc arity body = none → sptLookup loc target = some (arity, body)) ∧
      ∀ wrapper worker, compileExpSource loc workerLoc arity body = some (wrapper, worker) →
        sptLookup loc target = some (arity, wrapper) ∧ sptLookup workerLoc target = some (arity + 2, worker)

/-- Code related by TMC retains every original function location. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "code_rel_domain"]
theorem codeRel_domain (source target : Spt (Nat × Bvi.Exp)) (related : codeRel source target) :
    ∀ loc, sptMem loc source → sptMem loc target := by
  intro loc member
  obtain ⟨⟨arity, body⟩, found⟩ := (sptMem_iff_lookup loc source).mp member
  obtain ⟨_, workerLoc, unchanged, transformed⟩ := related loc arity body found
  cases compiled : compileExpSource loc workerLoc arity body with
  | none => exact (sptMem_iff_lookup loc target).mpr ⟨_, unchanged compiled⟩
  | some result =>
    obtain ⟨wrapper, worker⟩ := result
    exact (sptMem_iff_lookup loc target).mpr ⟨_, (transformed wrapper worker compiled).1⟩

/-- Disjoint target trees preserve the source code relation under union. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "code_rel_union"]
theorem codeRel_union (x y t s : Spt (Nat × Bvi.Exp))
    (left : codeRel x y) (right : codeRel t s)
    (disjoint : ∀ n, sptMem n s → ¬sptMem n y) : codeRel (sptUnion x t) (sptUnion y s) := by
  intro loc arity body lookup
  cases leftLookup : sptLookup loc x with
  | some old =>
    have found : sptLookup loc x = some (arity, body) := by
      simpa [sptLookup_sptUnion, leftLookup] using lookup
    obtain ⟨safe, workerLoc, unchanged, transformed⟩ := left loc arity body found
    refine ⟨safe, workerLoc, ?_, ?_⟩
    · intro rejected
      simp [sptLookup_sptUnion, unchanged rejected]
    · intro wrapper worker compiled
      obtain ⟨main, aux⟩ := transformed wrapper worker compiled
      exact ⟨by simp [sptLookup_sptUnion, main], by simp [sptLookup_sptUnion, aux]⟩
  | none =>
    have found : sptLookup loc t = some (arity, body) := by
      simpa [sptLookup_sptUnion, leftLookup] using lookup
    obtain ⟨safe, workerLoc, unchanged, transformed⟩ := right loc arity body found
    refine ⟨safe, workerLoc, ?_, ?_⟩
    · intro rejected
      exact BviTailrec.lookup_union_right_of_disjoint y s disjoint loc _ (unchanged rejected)
    · intro wrapper worker compiled
      obtain ⟨main, aux⟩ := transformed wrapper worker compiled
      exact ⟨BviTailrec.lookup_union_right_of_disjoint y s disjoint loc _ main,
        BviTailrec.lookup_union_right_of_disjoint y s disjoint workerLoc _ aux⟩

/-- TMC worker labels are new, and all other labels retain their source
membership, including labels reserved for runtime stubs. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "namespace_rel_def"]
def namespaceRel {α : Type} (source target : Spt α) : Prop :=
  (∀ n, sptMem n target ∧ Flapjack.bvlNumStubs ≤ n →
    if n % Flapjack.bvlToBviNamespaces = 3 then ¬sptMem n source else sptMem n source) ∧
  (∀ n, sptMem n source ∧ Flapjack.bvlNumStubs ≤ n → ¬inWorkerNamespace n) ∧
  (∀ n, sptMem n target ∧ n < Flapjack.bvlNumStubs → sptMem n source)

/-- Union preserves namespace relations for disjoint target domains. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "namespace_rel_union"]
theorem namespaceRel_union {α : Type} (x y t s : Spt α)
    (left : namespaceRel x y) (right : namespaceRel t s)
    (_disjoint : ∀ n, sptMem n s → ¬sptMem n y) : namespaceRel (sptUnion x t) (sptUnion y s) := by
  obtain ⟨leftTarget, leftSource, leftStub⟩ := left
  obtain ⟨rightTarget, rightSource, rightStub⟩ := right
  refine ⟨?_, ?_, ?_⟩
  · intro n ⟨member, above⟩
    rw [sptMem_sptUnion] at member ⊢
    by_cases worker : n % Flapjack.bvlToBviNamespaces = 3
    · simp only [worker, ↓reduceIte, not_or]
      exact ⟨fun source => leftSource n ⟨source, above⟩ worker,
        fun source => rightSource n ⟨source, above⟩ worker⟩
    · simp only [worker, ↓reduceIte]
      rcases member with member | member
      · left
        simpa [worker] using leftTarget n ⟨member, above⟩
      · right
        simpa [worker] using rightTarget n ⟨member, above⟩
  · intro n ⟨member, above⟩
    rw [sptMem_sptUnion] at member
    rcases member with member | member
    · exact leftSource n ⟨member, above⟩
    · exact rightSource n ⟨member, above⟩
  · intro n ⟨member, below⟩
    rw [sptMem_sptUnion] at member ⊢
    rcases member with member | member
    · exact Or.inl (leftStub n ⟨member, below⟩)
    · exact Or.inr (rightStub n ⟨member, below⟩)

/-- The decision not to rewrite a wrapper is independent of its worker
address. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "rewrite_wrapper_NONE_irrel"]
theorem rewriteWrapper_none_irrel (loc first n : Nat) (e : Bvi.Exp) (second : Nat)
    (rejected : rewriteWrapperSource loc first n e = none) : rewriteWrapperSource loc second n e = none := by
  cases e with
  | ifThenElse cond yes no =>
    rw [rewriteWrapperSource.eq_def] at rejected
    cases hy : rewriteWrapperSource loc first n yes <;>
      cases hz : rewriteWrapperSource loc first n no <;> simp [hy, hz] at rejected
    have iy := rewriteWrapper_none_irrel loc first n yes second hy
    have iz := rewriteWrapper_none_irrel loc first n no second hz
    rw [rewriteWrapperSource.eq_def]
    simp [iy, iz]
  | «let» xs body =>
    cases h : rewriteWrapperSource loc first (n + xs.length) body with
    | none =>
      have ih := rewriteWrapper_none_irrel loc first (n + xs.length) body second h
      rw [rewriteWrapperSource.eq_def]
      simp [ih]
    | some value => rw [rewriteWrapperSource.eq_def] at rejected; simp [h] at rejected
  | tick body =>
    cases h : rewriteWrapperSource loc first n body with
    | none =>
      have ih := rewriteWrapper_none_irrel loc first n body second h
      rw [rewriteWrapperSource.eq_def]
      simp [ih]
    | some value => rw [rewriteWrapperSource.eq_def] at rejected; simp [h] at rejected
  | op op xs =>
    cases h : toBlockSource n loc (.op op xs) with
    | none => rw [rewriteWrapperSource.eq_def]; simp [h]
    | some value =>
      obtain ⟨bs, cb⟩ := value
      rw [rewriteWrapperSource.eq_def] at rejected ⊢
      cases cb <;> simp_all
  | _ => rw [rewriteWrapperSource.eq_def]
termination_by sizeOf e

/-- A function rejected by TMC remains rejected at the next worker address. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_exp_next_addr"]
theorem compileExp_next_addr (loc next arity : Nat) (e : Bvi.Exp)
    (rejected : compileExpSource loc next arity e = none) :
    compileExpSource loc (next + Flapjack.bvlToBviNamespaces) arity e = none := by
  cases h : rewriteWrapperSource loc next arity e with
  | none =>
    have ih := rewriteWrapper_none_irrel loc next arity e (next + Flapjack.bvlToBviNamespaces) h
    simp [compileExpSource, ih]
  | some value => simp [compileExpSource, h] at rejected

/-- Changing a worker address cannot change whether a function is selected. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_exp_SOME_irrel"]
theorem compileExp_some_irrel (loc next arity : Nat) (e : Bvi.Exp) (result : Bvi.Exp × Bvi.Exp)
    (run : compileExpSource loc next arity e = some result) (next' : Nat) :
    ∃ result', compileExpSource loc next' arity e = some result' := by
  cases h : rewriteWrapperSource loc next' arity e with
  | none =>
    have absent := rewriteWrapper_none_irrel loc next' arity e next h
    simp [compileExpSource, absent] at run
  | some wrapper => exact ⟨(wrapper, rewriteWorkerSource loc next' arity (arity + 1) arity e), by simp [compileExpSource, h]⟩

/-- Function-list compilation never removes an input entry. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_each_LENGTH"]
theorem compileEachSource_length (next : Nat) (code : List (Nat × Nat × Bvi.Exp)) :
    code.length ≤ (compileEachSource next code).2.length := by
  induction code generalizing next with
  | nil => simp [compileEachSource]
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases decision : compileExpSource loc next arity body with
    | none =>
      cases tail : compileEachSource next rest with
      | mk last output =>
        have length := ih next
        simp only [tail] at length
        simpa [compileEachSource, decision, tail] using length
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      cases tail : compileEachSource (next + Flapjack.bvlToBviNamespaces) rest with
      | mk last output =>
        have length := ih (next + Flapjack.bvlToBviNamespaces)
        simp only [tail] at length
        simp [compileEachSource, decision, tail]
        omega

/-- Source function-list compilation advances its label counter only by
whole namespace strides. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_each_next_mono"]
theorem compileEachSource_next_mono (next last : Nat) (code output : List (Nat × Nat × Bvi.Exp))
    (run : compileEachSource next code = (last, output)) :
    ∃ k, last = next + Flapjack.bvlToBviNamespaces * k := by
  apply compileEachFuel_next_mono 0 next last code output
  simp [compileEachFuel_eq_source, run]

/-- The source program entry point has the same counter property. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_prog_next_mono"]
theorem compileProgSource_next_mono (enabled : Bool) (next last : Nat)
    (code output : List (Nat × Nat × Bvi.Exp)) (run : compileProgSource enabled next code = (last, output)) :
    ∃ k, last = next + Flapjack.bvlToBviNamespaces * k := by
  apply compileProgFuel_next_mono 0 enabled next last code output
  simp [compileProgFuel_eq_source, run]

/-- Every output label was present in the input or allocated in the worker
interval. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_each_MEM"]
theorem compileEachSource_mem (next last label : Nat) (code output : List (Nat × Nat × Bvi.Exp))
    (run : compileEachSource next code = (last, output)) (member : label ∈ output.map Prod.fst) :
    label ∈ code.map Prod.fst ∨
      (next ≤ label ∧ label < last ∧ ∃ k, label = next + k * Flapjack.bvlToBviNamespaces) := by
  exact compileEachFuel_mem 0 code next last label output (by simp [compileEachFuel_eq_source, run]) member

/-- The corresponding output-label property for the source program pass. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_prog_MEM"]
theorem compileProgSource_mem (enabled : Bool) (next last label : Nat)
    (code output : List (Nat × Nat × Bvi.Exp)) (run : compileProgSource enabled next code = (last, output))
    (member : label ∈ output.map Prod.fst) :
    label ∈ code.map Prod.fst ∨
      (next ≤ label ∧ label < last ∧ ∃ k, label = next + k * Flapjack.bvlToBviNamespaces) := by
  exact compileProgFuel_mem 0 enabled next last label code output (by simp [compileProgFuel_eq_source, run]) member

private theorem mem_fromAList_iff {α : Type} (entries : List (Nat × α)) (key : Nat) :
    sptMem key (sptFromAList entries) ↔ key ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [sptFromAList, sptMem, sptDomain]
  | cons entry rest ih =>
    obtain ⟨name, value⟩ := entry
    simpa only [sptFromAList, sptMem_sptInsert, List.map_cons, List.mem_cons, Prod.fst] using
      or_congr Iff.rfl ih

/-- Source TMC compilation preserves the namespace relation between its
input and output code trees. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "compile_each_namespace_rel"]
theorem compileEachSource_namespaceRel (next last : Nat) (program output : List (Nat × Nat × Bvi.Exp))
    (run : compileEachSource next program = (last, output))
    (worker : inWorkerNamespace next) (above : Flapjack.bvlNumStubs ≤ next)
    (outside : ∀ entry ∈ program.filter (fun p => decide (Flapjack.bvlNumStubs ≤ p.1)),
      ¬inWorkerNamespace entry.1) :
    namespaceRel (sptFromAList program) (sptFromAList output) := by
  have outsideKey : ∀ key ∈ program.map Prod.fst, Flapjack.bvlNumStubs ≤ key → ¬inWorkerNamespace key := by
    intro key member bound
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    apply outside entry
    exact List.mem_filter.mpr ⟨present, by simpa using bound⟩
  refine ⟨?_, ?_, ?_⟩
  · intro key ⟨member, bound⟩
    have outputMember := (mem_fromAList_iff output key).mp member
    rcases compileEachSource_mem next last key program output run outputMember with original | ⟨lo, _, k, fresh⟩
    · have notWorker := outsideKey key original bound
      simp only [inWorkerNamespace] at notWorker
      simp [notWorker, (mem_fromAList_iff program key).mpr original]
    · have freshWorker : inWorkerNamespace key := by
        rw [fresh]
        unfold inWorkerNamespace at worker ⊢
        simpa [Nat.add_mod, Flapjack.bvlToBviNamespaces] using worker
      have notOriginal : ¬sptMem key (sptFromAList program) := by
        intro sourceMember
        exact outsideKey key ((mem_fromAList_iff program key).mp sourceMember) (by omega) freshWorker
      simp only [inWorkerNamespace] at freshWorker
      simp [freshWorker, notOriginal]
  · intro key ⟨member, bound⟩
    exact outsideKey key ((mem_fromAList_iff program key).mp member) bound
  · intro key ⟨member, bound⟩
    have outputMember := (mem_fromAList_iff output key).mp member
    rcases compileEachSource_mem next last key program output run outputMember with original | ⟨lo, _, _, _⟩
    · exact (mem_fromAList_iff program key).mpr original
    · omega

end Flapjack.Compiler.Backend.BviTmc
