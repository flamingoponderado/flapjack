import Flapjack.Compiler.Backend.BviTailrec.Proofs.ScanSound

/-! Source-shaped code and state relations for the tail-recursion simulation.
The compilation and evaluator carriers still require HOL source review. -/
namespace Flapjack.Compiler.Backend.BviTailrec
open Bvi BvlSem

/-- Relation between an original code tree and its transformed code tree. -/
def codeRel (source target : Spt (Nat × Bvi.Exp)) : Prop :=
  ∀ loc arity body op, sptLookup loc source = some (arity, body) →
    (checkExpOriginal loc arity body = none → sptLookup loc target = some (arity, body)) ∧
    (checkExpOriginal loc arity body = some op → ∃ workerLoc,
      ∀ wrapper worker, compileExpSource loc workerLoc arity body = some (wrapper, worker) →
        sptLookup loc target = some (arity, wrapper) ∧
        sptLookup workerLoc target = some (arity + 1, worker))

/-- An optimized function and its worker are present at their designated
locations in a transformed code tree. -/
def optimizedCode (loc arity : Nat) (body : Bvi.Exp) (workerLoc : Nat)
    (code : Spt (Nat × Bvi.Exp)) (op : AssocOp) : Prop :=
  ∃ wrapper worker, compileExpSource loc workerLoc arity body = some (wrapper, worker) ∧
    checkExpOriginal loc arity body = some op ∧
    sptLookup loc code = some (arity, wrapper) ∧
    sptLookup workerLoc code = some (arity + 1, worker)

/-- An optimized entry installs the exact source-shaped rewritten worker at
the worker label and arity. -/
theorem optimizedCode_worker_lookup (loc arity : Nat) (body : Bvi.Exp) (workerLoc : Nat)
    (code : Spt (Nat × Bvi.Exp)) (op : AssocOp)
    (optimized : optimizedCode loc arity body workerLoc code op) :
    sptLookup workerLoc code = some (arity + 1,
      (rewriteSource loc workerLoc op arity (List.replicate arity .any) body).2) := by
  obtain ⟨wrapper, worker, compiled, check, _, workerFound⟩ := optimized
  simp [compileExpSource, check] at compiled
  obtain ⟨_, rfl⟩ := compiled
  exact workerFound

/-- The worker lookup resolves the original arguments with their new
accumulator appended. -/
theorem optimizedCode_find_worker (loc arity : Nat) (body : Bvi.Exp) (workerLoc : Nat)
    (code : Spt (Nat × Bvi.Exp)) (op : AssocOp) (args : List Value) (accumulator : Value)
    (optimized : optimizedCode loc arity body workerLoc code op) (length : args.length = arity) :
    findCode (some workerLoc) (args ++ [accumulator]) code =
      some (args ++ [accumulator],
        (rewriteSource loc workerLoc op arity (List.replicate arity .any) body).2) := by
  have found := optimizedCode_worker_lookup loc arity body workerLoc code op optimized
  simp [findCode, found, length]

/-- A positive source check always determines a wrapper and worker for any
chosen fresh worker location. -/
theorem compileExpSource_of_check (loc next arity : Nat) (body : Bvi.Exp) (op : AssocOp)
    (check : checkExpOriginal loc arity body = some op) :
    ∃ wrapper worker, compileExpSource loc next arity body = some (wrapper, worker) := by
  simp [compileExpSource, check]

/-- Related code retains a function at every original location. -/
theorem codeRel_lookup_exists (source target : Spt (Nat × Bvi.Exp)) (h : codeRel source target)
    (loc arity : Nat) (body : Bvi.Exp) (lookup : sptLookup loc source = some (arity, body)) :
    ∃ compiled, sptLookup loc target = some compiled := by
  cases check : checkExpOriginal loc arity body with
  | none =>
    have untouched := (h loc arity body .noop lookup).1 check
    exact ⟨(arity, body), untouched⟩
  | some op =>
    obtain ⟨workerLoc, workerLookup⟩ := (h loc arity body op lookup).2 check
    obtain ⟨wrapper, worker, compiled⟩ := compileExpSource_of_check loc workerLoc arity body op check
    exact ⟨(arity, wrapper), (workerLookup wrapper worker compiled).1⟩

/-- Related code retains the original arity at every original location. -/
theorem codeRel_lookup_arity (source target : Spt (Nat × Bvi.Exp)) (h : codeRel source target)
    (loc arity : Nat) (body : Bvi.Exp) (lookup : sptLookup loc source = some (arity, body)) :
    ∃ compiled, sptLookup loc target = some (arity, compiled) := by
  cases check : checkExpOriginal loc arity body with
  | none => exact ⟨body, (h loc arity body .noop lookup).1 check⟩
  | some op =>
    obtain ⟨workerLoc, workerLookup⟩ := (h loc arity body op lookup).2 check
    obtain ⟨wrapper, worker, compiled⟩ := compileExpSource_of_check loc workerLoc arity body op check
    exact ⟨wrapper, (workerLookup wrapper worker compiled).1⟩

/-- A direct call that resolves in the original code also resolves in the
related target code. -/
theorem codeRel_findCode_some (source target : Spt (Nat × Bvi.Exp)) (h : codeRel source target)
    (loc : Nat) (args actualArgs : List Value) (body : Bvi.Exp)
    (run : findCode (some loc) args source = some (actualArgs, body)) :
    findCode (some loc) args target ≠ none := by
  cases lookup : sptLookup loc source with
  | none => simp [findCode, lookup] at run
  | some pair =>
    obtain ⟨arity, oldBody⟩ := pair
    have length : args.length = arity := by
      by_contra wrong
      simp [findCode, lookup, wrong] at run
    obtain ⟨compiled, found⟩ := codeRel_lookup_arity source target h loc arity oldBody lookup
    simp [findCode, found, length]

/-- An indirect call that resolves through a code pointer in the original
code also resolves in the related target code. -/
theorem codeRel_findCode_none (source target : Spt (Nat × Bvi.Exp)) (h : codeRel source target)
    (args actualArgs : List Value) (body : Bvi.Exp)
    (run : findCode none args source = some (actualArgs, body)) :
    findCode none args target ≠ none := by
  cases empty : args.isEmpty with
  | true => simp [findCode, empty] at run
  | false =>
    cases last : Flapjack.holLast args with
    | codePtr loc =>
      cases lookup : sptLookup loc source with
      | none => simp [findCode, empty, last, lookup] at run
      | some pair =>
        obtain ⟨arity, oldBody⟩ := pair
        have length : args.length = arity + 1 := by
          by_contra wrong
          simp [findCode, empty, last, lookup, wrong] at run
        obtain ⟨compiled, found⟩ := codeRel_lookup_arity source target h loc arity oldBody lookup
        simp [findCode, empty, last, found, length]
    | _ => simp [findCode, empty, last] at run

/-- The source code domain is included in the related target code domain. -/
theorem codeRel_domain (source target : Spt (Nat × Bvi.Exp)) (h : codeRel source target) :
    ∀ loc, sptMem loc source → sptMem loc target := by
  intro loc mem
  obtain ⟨⟨arity, body⟩, lookup⟩ := (sptMem_iff_lookup loc source).mp mem
  obtain ⟨compiled, found⟩ := codeRel_lookup_exists source target h loc arity body lookup
  exact (sptMem_iff_lookup loc target).mpr ⟨compiled, found⟩

/-- Extending a related target tree preserves the code relation. -/
theorem codeRel_subspt (source target extended : Spt (Nat × Bvi.Exp))
    (h : codeRel source target ∧ sptSubspt target extended) : codeRel source extended := by
  obtain ⟨related, subset⟩ := h
  intro loc arity body op lookup
  obtain ⟨unchanged, optimized⟩ := related loc arity body op lookup
  constructor
  · intro check
    have found := unchanged check
    have mem := (sptMem_iff_lookup loc target).mpr ⟨_, found⟩
    exact (subset loc mem).2.trans found
  · intro check
    obtain ⟨workerLoc, worker⟩ := optimized check
    refine ⟨workerLoc, ?_⟩
    intro wrapper body' compiled
    obtain ⟨originalFound, workerFound⟩ := worker wrapper body' compiled
    have originalMem := (sptMem_iff_lookup loc target).mpr ⟨_, originalFound⟩
    have workerMem := (sptMem_iff_lookup workerLoc target).mpr ⟨_, workerFound⟩
    exact ⟨(subset loc originalMem).2.trans originalFound,
      (subset workerLoc workerMem).2.trans workerFound⟩

/-- A right-hand union lookup survives when the two tree domains are
disjoint. -/
theorem lookup_union_right_of_disjoint {α : Type} (left right : Spt α)
    (disjoint : ∀ n, sptMem n right → ¬sptMem n left) (key : Nat) (value : α)
    (found : sptLookup key right = some value) :
    sptLookup key (sptUnion left right) = some value := by
  have noLeft : ¬sptMem key left := disjoint key ((sptMem_iff_lookup key right).mpr ⟨value, found⟩)
  cases lookup : sptLookup key left with
  | none => simp [sptLookup_sptUnion, lookup, found]
  | some old => exact (noLeft ((sptMem_iff_lookup key left).mpr ⟨old, lookup⟩)).elim

/-- Disjoint target installations preserve the code relation under
left-biased code-tree union. -/
theorem codeRel_union (x y t s : Spt (Nat × Bvi.Exp))
    (h : codeRel x y ∧ codeRel t s ∧ (∀ n, sptMem n s → ¬sptMem n y)) :
    codeRel (sptUnion x t) (sptUnion y s) := by
  obtain ⟨leftRel, rightRel, disjoint⟩ := h
  intro loc arity body op lookup
  cases leftLookup : sptLookup loc x with
  | some old =>
    have found : sptLookup loc x = some (arity, body) := by
      simpa [sptLookup_sptUnion, leftLookup] using lookup
    obtain ⟨unchanged, optimized⟩ := leftRel loc arity body op found
    constructor
    · intro check
      simp [sptLookup_sptUnion, unchanged check]
    · intro check
      obtain ⟨workerLoc, workers⟩ := optimized check
      refine ⟨workerLoc, ?_⟩
      intro wrapper worker compiled
      obtain ⟨originalFound, workerFound⟩ := workers wrapper worker compiled
      exact ⟨by simp [sptLookup_sptUnion, originalFound], by simp [sptLookup_sptUnion, workerFound]⟩
  | none =>
    have found : sptLookup loc t = some (arity, body) := by
      simpa [sptLookup_sptUnion, leftLookup] using lookup
    obtain ⟨unchanged, optimized⟩ := rightRel loc arity body op found
    constructor
    · intro check
      exact lookup_union_right_of_disjoint y s disjoint loc _ (unchanged check)
    · intro check
      obtain ⟨workerLoc, workers⟩ := optimized check
      refine ⟨workerLoc, ?_⟩
      intro wrapper worker compiled
      obtain ⟨originalFound, workerFound⟩ := workers wrapper worker compiled
      exact ⟨lookup_union_right_of_disjoint y s disjoint loc _ originalFound,
        lookup_union_right_of_disjoint y s disjoint workerLoc _ workerFound⟩

/-- Function-list compilation never reduces the number of entries. -/
theorem compileEachSource_length (next : Nat) (code : List (Nat × Nat × Bvi.Exp)) :
    code.length ≤ (compileEachSource next code).2.length := by
  induction code generalizing next with
  | nil => simp [compileEachSource]
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases compiled : compileExpSource loc next arity body with
    | none =>
      cases tail : compileEachSource next rest with
      | mk last code =>
        have h := ih next
        simp only [tail] at h
        simpa [compileEachSource, compiled, tail] using h
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      cases tail : compileEachSource (next + Flapjack.bvlToBviNamespaces) rest with
      | mk last code =>
        have h := ih (next + Flapjack.bvlToBviNamespaces)
        simp only [tail] at h
        simp [compileEachSource, compiled, tail]
        omega
/-- The next worker label advances by a whole number of namespace steps. -/
theorem compileEachSource_next_mono (next : Nat) (code : List (Nat × Nat × Bvi.Exp)) :
    ∃ k, (compileEachSource next code).1 = next + Flapjack.bvlToBviNamespaces * k := by
  induction code generalizing next with
  | nil => exact ⟨0, by simp [compileEachSource]⟩
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases compiled : compileExpSource loc next arity body with
    | none =>
      cases tail : compileEachSource next rest with
      | mk last code =>
        obtain ⟨k, h⟩ := ih next
        simp only [tail] at h
        exact ⟨k, by simpa [compileEachSource, compiled, tail] using h⟩
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      cases tail : compileEachSource (next + Flapjack.bvlToBviNamespaces) rest with
      | mk last code =>
        obtain ⟨k, h⟩ := ih (next + Flapjack.bvlToBviNamespaces)
        simp only [tail] at h
        refine ⟨k + 1, ?_⟩
        simpa [compileEachSource, compiled, tail, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
/-- Each compiled label is an original label or a fresh worker allocated
in the namespace interval traversed by compilation. -/
theorem compileEachSource_mem (code : List (Nat × Nat × Bvi.Exp)) (next label : Nat)
    (member : label ∈ ((compileEachSource next code).2.map Prod.fst)) :
    label ∈ code.map Prod.fst ∨
      (next ≤ label ∧ label < (compileEachSource next code).1 ∧
        ∃ k, label = next + k * Flapjack.bvlToBviNamespaces) := by
  induction code generalizing next with
  | nil => simp [compileEachSource] at member
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    cases compiled : compileExpSource loc next arity body with
    | none =>
      cases tail : compileEachSource next rest with
      | mk last output =>
        have tailIH := ih next
        simp only [tail] at tailIH
        simp only [compileEachSource, compiled, tail, List.map_cons, List.mem_cons] at member ⊢
        rcases member with same | other
        · exact Or.inl (Or.inl same)
        · rcases tailIH other with found | new
          · exact Or.inl (Or.inr found)
          · exact Or.inr new
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      cases tail : compileEachSource (next + Flapjack.bvlToBviNamespaces) rest with
      | mk last output =>
        have tailIH := ih (next + Flapjack.bvlToBviNamespaces)
        simp only [tail] at tailIH
        have ⟨k, bound⟩ := compileEachSource_next_mono (next + Flapjack.bvlToBviNamespaces) rest
        simp only [tail] at bound
        simp only [compileEachSource, compiled, tail, List.map_cons, List.mem_cons] at member ⊢
        rcases member with same | same | other
        · exact Or.inl (Or.inl same)
        · subst label
          right
          refine ⟨by omega, ?_, 0, by simp⟩
          have positive : 0 < Flapjack.bvlToBviNamespaces := by decide
          omega
        · rcases tailIH other with found | ⟨lo, hi, j, eq⟩
          · exact Or.inl (Or.inr found)
          · right
            refine ⟨by omega, hi, j + 1, ?_⟩
            simp only [Nat.add_mul, Nat.one_mul]
            omega

/-- Compiling a function list retains every original label. -/
theorem compileEachSource_preserves_labels (code : List (Nat × Nat × Bvi.Exp)) (next label : Nat)
    (member : label ∈ code.map Prod.fst) :
    label ∈ (compileEachSource next code).2.map Prod.fst := by
  induction code generalizing next with
  | nil => simp at member
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    simp only [List.map_cons, List.mem_cons] at member
    cases compiled : compileExpSource loc next arity body with
    | none =>
      cases tail : compileEachSource next rest with
      | mk last output =>
        simp only [compileEachSource, compiled, tail, List.map_cons, List.mem_cons]
        rcases member with same | other
        · exact Or.inl same
        · exact Or.inr (by simpa [tail] using ih next other)
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      cases tail : compileEachSource (next + Flapjack.bvlToBviNamespaces) rest with
      | mk last output =>
        simp only [compileEachSource, compiled, tail, List.map_cons, List.mem_cons]
        rcases member with same | other
        · exact Or.inl same
        · exact Or.inr (Or.inr (by simpa [tail] using ih (next + Flapjack.bvlToBviNamespaces) other))

/-- A name is free if it cannot be reached by advancing the worker namespace. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "free_names_def"]
def freeNames (next name : Nat) : Prop :=
  ∀ k, next + Flapjack.bvlToBviNamespaces * k ≠ name

/-- A label free from the current worker namespace remains free after any
number of worker allocations. -/
theorem freeNames_advance (next name steps : Nat) (free : freeNames next name) :
    freeNames (next + Flapjack.bvlToBviNamespaces * steps) name := by
  intro k eq
  apply free (steps + k)
  simpa [Nat.mul_add, Nat.add_assoc] using eq

/-- The current worker label itself is not free. -/
theorem freeNames_ne_current (next name : Nat) (free : freeNames next name) : next ≠ name := by
  simpa using free 0

/-- Function-list compilation preserves a label's freedom at the resulting
next worker location. -/
theorem compileEachSource_preserves_free (next name : Nat) (code : List (Nat × Nat × Bvi.Exp))
    (free : freeNames next name) : freeNames (compileEachSource next code).1 name := by
  obtain ⟨steps, advance⟩ := compileEachSource_next_mono next code
  rw [advance]
  exact freeNames_advance next name steps free

/-- A free label absent from the input cannot be introduced by compilation. -/
theorem compileEachSource_avoids_free (next name : Nat) (code : List (Nat × Nat × Bvi.Exp))
    (free : freeNames next name) (absent : name ∉ code.map Prod.fst) :
    name ∉ (compileEachSource next code).2.map Prod.fst := by
  intro member
  rcases compileEachSource_mem code next name member with old | ⟨_, _, k, eq⟩
  · exact absent old
  · apply free k
    simpa [Nat.mul_comm] using eq.symm

/-- Any label below the next worker is free. -/
theorem freeNames_of_lt (next name : Nat) (bound : name < next) : freeNames next name := by
  intro k eq
  omega

/-- Every compiled label is free from the resulting worker namespace. -/
theorem compileEachSource_output_free (next : Nat) (code : List (Nat × Nat × Bvi.Exp))
    (free : ∀ name ∈ code.map Prod.fst, freeNames next name) :
    ∀ name ∈ (compileEachSource next code).2.map Prod.fst,
      freeNames (compileEachSource next code).1 name := by
  intro name member
  rcases compileEachSource_mem code next name member with old | ⟨_, bound, _⟩
  · exact compileEachSource_preserves_free next name code (free name old)
  · exact freeNames_of_lt _ _ bound

/-- Distinct input labels and free worker names yield distinct compiled labels. -/
theorem compileEachSource_labels_nodup (code : List (Nat × Nat × Bvi.Exp)) (next : Nat)
    (unique : (code.map Prod.fst).Nodup)
    (free : ∀ name ∈ code.map Prod.fst, freeNames next name) :
    ((compileEachSource next code).2.map Prod.fst).Nodup := by
  induction code generalizing next with
  | nil => simp [compileEachSource]
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    have unique' : loc ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
      simpa using unique
    have freeLoc : freeNames next loc := free loc (by simp)
    have freeRest : ∀ name ∈ rest.map Prod.fst, freeNames next name := by
      intro name member
      exact free name (by simp [member])
    cases compiled : compileExpSource loc next arity body with
    | none =>
      cases tail : compileEachSource next rest with
      | mk last output =>
        have avoidLoc := compileEachSource_avoids_free next loc rest freeLoc unique'.1
        have distinct := ih next unique'.2 freeRest
        simpa [compileEachSource, compiled, tail] using (List.nodup_cons.mpr ⟨by simpa [tail] using avoidLoc, by simpa [tail] using distinct⟩ :
          (loc :: output.map Prod.fst).Nodup)
    | some pair =>
      obtain ⟨wrapper, worker⟩ := pair
      cases tail : compileEachSource (next + Flapjack.bvlToBviNamespaces) rest with
      | mk last output =>
        have freeRest' : ∀ name ∈ rest.map Prod.fst, freeNames (next + Flapjack.bvlToBviNamespaces) name := by
          intro name member
          simpa using freeNames_advance next name 1 (freeRest name member)
        have locFree : freeNames (next + Flapjack.bvlToBviNamespaces) loc := by
          simpa using freeNames_advance next loc 1 freeLoc
        have workerFree : freeNames (next + Flapjack.bvlToBviNamespaces) next := by
          apply freeNames_of_lt
          have positive : 0 < Flapjack.bvlToBviNamespaces := by decide
          omega
        have workerAbsent : next ∉ rest.map Prod.fst := by
          intro h
          exact freeNames_ne_current next next (freeRest next h) rfl
        have avoidLoc := compileEachSource_avoids_free (next + Flapjack.bvlToBviNamespaces) loc rest locFree unique'.1
        have avoidWorker := compileEachSource_avoids_free (next + Flapjack.bvlToBviNamespaces) next rest workerFree workerAbsent
        have distinct := ih (next + Flapjack.bvlToBviNamespaces) unique'.2 freeRest'
        have neq : loc ≠ next := (freeNames_ne_current next loc freeLoc).symm
        have all : (loc :: next :: output.map Prod.fst).Nodup := by
          apply List.nodup_cons.mpr
          refine ⟨?_, List.nodup_cons.mpr ⟨?_, ?_⟩⟩
          · simp [neq, tail] at avoidLoc ⊢
            exact avoidLoc
          · simpa [tail] using avoidWorker
          · simpa [tail] using distinct
        simpa [compileEachSource, compiled, tail] using all

/-- Compiled code keeps distinct labels and leaves every output label free
from the next worker namespace. -/
theorem compileEachSource_distinct_and_free (next : Nat) (code : List (Nat × Nat × Bvi.Exp))
    (unique : (code.map Prod.fst).Nodup)
    (free : ∀ name ∈ code.map Prod.fst, freeNames next name) :
    ((compileEachSource next code).2.map Prod.fst).Nodup ∧
      ∀ name ∈ (compileEachSource next code).2.map Prod.fst,
        freeNames (compileEachSource next code).1 name :=
  ⟨compileEachSource_labels_nodup code next unique free, compileEachSource_output_free next code free⟩

/-- Worker labels use namespace residue two. -/
def inWorkerNamespace (name : Nat) : Prop := name % Flapjack.bvlToBviNamespaces = 2

/-- Source namespace relation between the original and transformed code. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tailrecProofScript.sml" "namespace_rel_def"]
def namespaceRel {α : Type} (source target : Spt α) : Prop :=
  (∀ n, sptMem n target ∧ Flapjack.bvlNumStubs ≤ n →
    if n % Flapjack.bvlToBviNamespaces = 2 then ¬sptMem n source else sptMem n source) ∧
  (∀ n, sptMem n source ∧ Flapjack.bvlNumStubs ≤ n → ¬inWorkerNamespace n) ∧
  (∀ n, sptMem n target ∧ n < Flapjack.bvlNumStubs → sptMem n source)

/-- Union preserves the namespace relation. This applies in particular to
the disjoint code installations used by the source simulation. -/
theorem namespaceRel_union {α : Type} (x y t s : Spt α)
    (left : namespaceRel x y) (right : namespaceRel t s) :
    namespaceRel (sptUnion x t) (sptUnion y s) := by
  obtain ⟨leftAbove, leftNoWorker, leftBelow⟩ := left
  obtain ⟨rightAbove, rightNoWorker, rightBelow⟩ := right
  refine ⟨?_, ?_, ?_⟩
  · intro n ⟨targetMem, bound⟩
    rw [sptMem_sptUnion] at targetMem
    by_cases worker : inWorkerNamespace n
    · simp only [show n % Flapjack.bvlToBviNamespaces = 2 from worker, if_true, sptMem_sptUnion, not_or]
      exact ⟨fun h => leftNoWorker n ⟨h, bound⟩ worker,
        fun h => rightNoWorker n ⟨h, bound⟩ worker⟩
    · simp only [show ¬n % Flapjack.bvlToBviNamespaces = 2 from worker, if_false, sptMem_sptUnion]
      rcases targetMem with mem | mem
      · left
        have found := leftAbove n ⟨mem, bound⟩
        simpa only [show ¬n % Flapjack.bvlToBviNamespaces = 2 from worker, if_false] using found
      · right
        have found := rightAbove n ⟨mem, bound⟩
        simpa only [show ¬n % Flapjack.bvlToBviNamespaces = 2 from worker, if_false] using found
  · intro n ⟨sourceMem, bound⟩
    rw [sptMem_sptUnion] at sourceMem
    rcases sourceMem with mem | mem
    · exact leftNoWorker n ⟨mem, bound⟩
    · exact rightNoWorker n ⟨mem, bound⟩
  · intro n ⟨targetMem, bound⟩
    rw [sptMem_sptUnion] at targetMem ⊢
    rcases targetMem with mem | mem
    · exact Or.inl (leftBelow n ⟨mem, bound⟩)
    · exact Or.inr (rightBelow n ⟨mem, bound⟩)

/-- Source side conditions for a function list and the next worker label. -/
def inputCondition (next : Nat) (program : List (Nat × Nat × Bvi.Exp)) : Prop :=
  (∀ p ∈ program, freeNames next p.1) ∧
  (program.map fun p => p.1).Nodup ∧
  (∀ p ∈ program.filter (fun p => decide (Flapjack.bvlNumStubs ≤ p.1)), ¬inWorkerNamespace p.1) ∧
  Flapjack.bvlNumStubs ≤ next ∧ inWorkerNamespace next

/-- Apply the source-shaped pass to each future compiler-oracle program. -/
def transformOracle {C : Type} (oracle : BviSem.CompileOracle (Nat × C)) : BviSem.CompileOracle C :=
  fun index =>
    let ((next, config), program) := oracle index
    (config, (compileEachSource next program).2)

/-- Adapt the target compiler callback to the source's additional worker
label state. -/
def transformCompiler {C : Type} (compiler : BviSem.Compiler C) : BviSem.Compiler (Nat × C) :=
  fun (next, config) program =>
    let (next', compiled) := compileEachSource next program
    (compiler config compiled).map fun (bytes, data, config') => (bytes, data, (next', config'))

/-- Source-shaped state relation used by the tail-recursion simulation. It is
untagged until the evaluator and the source compilation carriers are reviewed. -/
def stateRel {C F : Type} (source : BviSem.BviState (Nat × C) F) (target : BviSem.BviState C F) : Prop :=
  target.refs = source.refs ∧
  target.clock = source.clock ∧
  target.global = source.global ∧
  target.ffi = source.ffi ∧
  target.compileOracle = transformOracle source.compileOracle ∧
  source.compile = transformCompiler target.compile ∧
  codeRel source.code target.code ∧
  namespaceRel source.code target.code ∧
  (∀ n, inputCondition (source.compileOracle n).1.1 (source.compileOracle n).2) ∧
  (∀ n, sptMem n target.code ∧ inWorkerNamespace n → n < (source.compileOracle 0).1.1)

/-- Related states agree on the data fields used by primitive evaluation. -/
theorem stateRel_const {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (h : stateRel source target) :
    target.refs = source.refs ∧ target.clock = source.clock ∧
      target.global = source.global ∧ target.ffi = source.ffi := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Resetting both clocks to the same value preserves the state relation. -/
theorem stateRel_withClock {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (clock : Nat) (h : stateRel source target) :
    stateRel { source with clock := clock } { target with clock := clock } := by
  rcases h with ⟨refs, _, global, ffi, oracle, compiler, code, ns, input, bound⟩
  exact ⟨refs, rfl, global, ffi, oracle, compiler, code, ns, input, bound⟩

/-- The state relation includes the code relation. -/
theorem stateRel_codeRel {C F : Type} (source : BviSem.BviState (Nat × C) F)
    (target : BviSem.BviState C F) (h : stateRel source target) : codeRel source.code target.code :=
  h.2.2.2.2.2.2.1

end Flapjack.Compiler.Backend.BviTailrec
