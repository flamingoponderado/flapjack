import Flapjack.Compiler.Backend.RegAlloc.ProductionGraphRows

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc

/-- Admission-only projection of the reference clique traversal. This
Flapjack helper has no separate HOL original; its equations are proved below
to be the live-list projection of the actual reference graph builder. -/
def cliqueAdmission : List Nat → List Nat → List Nat
  | [], live => live
  | node :: rest, live =>
      if live.contains node then cliqueAdmission rest live
      else cliqueAdmission rest (node :: live)

private def admissionStep (state : Std.TreeSet Nat × List Nat) (node : Nat) :
    Std.TreeSet Nat × List Nat :=
  if state.1.contains node then (state.1, state.2)
  else (state.1.insert node, node :: state.2)

private theorem admissionFold (new initial : List Nat) (seen : Std.TreeSet Nat) (added : List Nat)
    (indexed : ∀ key, seen.contains key = (added ++ initial).contains key) :
    (new.foldl admissionStep (seen, added)).2 ++ initial =
      cliqueAdmission new (added ++ initial) := by
  induction new generalizing seen added with
  | nil => rfl
  | cons node rest ih =>
    simp only [List.foldl_cons, admissionStep, cliqueAdmission]
    rw [← indexed node]
    cases present : seen.contains node with
    | true => simpa only [present, ↓reduceIte] using ih seen added indexed
    | false =>
      apply ih (seen.insert node) (node :: added)
      intro key
      simp only [Std.TreeSet.contains_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        Bool.beq_eq_decide_eq, indexed, List.cons_append, List.contains_cons]
      simp only [eq_comm]

/-- Full executed batch admission keeps exactly the reference's newest-first
live list, including repeated new names and repeated initial entries. This
proves the actual TreeSet fold, without assuming its result. Untagged
production correspondence infrastructure. Graph row transport is separate. -/
theorem extendCliqueBatch_live (new initial : List Nat) (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendCliqueSetBatch new initial cache).2 = cliqueAdmission new initial := by
  have run := admissionFold new initial (Std.TreeSet.ofList initial) []
    (by intro key; simp [Std.TreeSet.contains_ofList])
  unfold cakeExtendCliqueSetBatch
  change (new.foldl admissionStep (Std.TreeSet.ofList initial, [])).2 ++ initial = _
  simpa only [List.nil_append] using run

/-- The admission projection is derived from the real recursive reference,
independently of its starting graph or intermediate edge updates. -/
theorem extendCliqueSetReference_live (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendCliqueSetReference new initial cache).2 = cliqueAdmission new initial := by
  induction new generalizing initial cache with
  | nil => simp [cakeExtendCliqueSetReference, cliqueAdmission]
  | cons node rest ih =>
    simp only [cakeExtendCliqueSetReference, cliqueAdmission]
    split <;> exact ih _ _

/-- The executed batch has exactly the reference's complete live-list result.
This alone does not establish graph correspondence or native state success. -/
theorem extendCliqueBatch_live_reference (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendCliqueSetBatch new initial cache).2 =
      (cakeExtendCliqueSetReference new initial cache).2 := by
  rw [extendCliqueBatch_live, extendCliqueSetReference_live]

/-- Missing input slots distinguish batching from recursive edge insertion:
an isolated admitted node receives an empty row in the batch. Full native
correspondence must derive present in-domain slots from the actual initializer
and bijection bounds; arbitrary missing slots cannot be assumed equivalent. -/
theorem extendCliqueBatch_missingSlot :
    ((cakeExtendCliqueSetBatch [0] [] (cakeAdjSetMapOfSize 0)).1.get 0).map cakeAdjSetList = some [] ∧
    ((cakeExtendCliqueSetReference [0] [] (cakeAdjSetMapOfSize 0)).1.get 0).map cakeAdjSetList = none := by
  simp only [cakeExtendCliqueSetReference, List.contains_nil, Bool.false_eq_true,
    ↓reduceIte, cakeListInsertEdgeSet]
  decide

/-- The actual graph seed supplies present empty rows at precisely the
initializer dimension. This is the real input-domain fact needed to avoid
the missing-slot discrepancy above, rather than a supplied graph output. -/
theorem graphSeed_get (dimension key : Nat) :
    (cakeAdjSetMapOfSize dimension).get key =
      if key < dimension then some (∅ : Std.TreeSet Nat) else none := by
  by_cases bounded : key < dimension <;>
    simp [cakeAdjSetMapOfSize, CakeNodeMap.get, bounded, cakeMapLookup, lookupNatInfo]

private def unionRow (partners : Nat → Std.TreeSet Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (node : Nat) : CakeNodeMap (Std.TreeSet Nat) :=
  cache.set node (((cache.get node).getD ∅).union (partners node))

private theorem unionRowsFold_membership (nodes : List Nat) (partners : Nat → Std.TreeSet Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (key member : Nat) :
    ((nodes.foldl (unionRow partners) cache).get key).map (fun set => set.contains member) =
      if nodes.contains key then
        some (((cache.get key).getD ∅).contains member || (partners key).contains member)
      else (cache.get key).map (fun set => set.contains member) := by
  induction nodes generalizing cache with
  | nil => rfl
  | cons node rest ih =>
    rw [List.foldl_cons, ih]
    by_cases equal : key = node
    · subst key
      simp [unionRow, CakeNodeMap.get_set_self, Std.TreeSet.contains_union]
    · simp [unionRow, CakeNodeMap.get_set_of_ne _ _ _ _ (Ne.symm equal),
        equal]

/-- The actual batch's admission tuple, including its membership set and
newest-first admitted list. Untagged proof infrastructure for the executed
fold; no desired admission output is a parameter. -/
def cliqueBatchAdmissions (new initial : List Nat) : Std.TreeSet Nat × List Nat :=
  new.foldl admissionStep (Std.TreeSet.ofList initial, [])

private theorem defaultContains (row : Option (Std.TreeSet Nat)) (member : Nat) :
    (row.getD ∅).contains member = (row.map (fun set => set.contains member)).getD false := by
  cases row <;> rfl

private theorem batchGraph_eq (new initial : List Nat) (cache : CakeNodeMap (Std.TreeSet Nat)) :
    (cakeExtendCliqueSetBatch new initial cache).1 =
      initial.foldl (unionRow (fun _ => Std.TreeSet.ofList (cliqueBatchAdmissions new initial).2))
        ((cliqueBatchAdmissions new initial).2.foldl
          (unionRow (fun node => (cliqueBatchAdmissions new initial).1.erase node)) cache) := by
  unfold cakeExtendCliqueSetBatch cliqueBatchAdmissions admissionStep unionRow
  rfl

/-- Complete all-key batch graph observation calculated from the real
admission fold and incoming graph. The two updates include missing-row
creation explicitly. This is a producer equation, not yet a proof that the
recursive reference has this result; full reference transport remains open. -/
theorem extendCliqueBatch_graphMembership (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (key member : Nat) :
    let admitted := cliqueBatchAdmissions new initial
    let afterAdded := if admitted.2.contains key then
        some (((cache.get key).getD ∅).contains member ||
          (admitted.1.erase key).contains member)
      else (cache.get key).map (fun set => set.contains member)
    ((cakeExtendCliqueSetBatch new initial cache).1.get key).map
      (fun set => set.contains member) =
      if initial.contains key then
        some (afterAdded.getD false || (Std.TreeSet.ofList admitted.2).contains member)
      else afterAdded := by
  let admitted := cliqueBatchAdmissions new initial
  let first := admitted.2.foldl (unionRow (fun node => admitted.1.erase node)) cache
  have firstRows := unionRowsFold_membership admitted.2
    (fun node => admitted.1.erase node) cache key member
  have finalRows := unionRowsFold_membership initial
    (fun _ => Std.TreeSet.ofList admitted.2) first key member
  rw [defaultContains] at finalRows
  dsimp only [first] at finalRows
  rw [firstRows] at finalRows
  rw [batchGraph_eq]
  exact finalRows

private theorem admissionFold_seed (new : List Nat)
    (first second : Std.TreeSet Nat) (firstAdded secondAdded suffix : List Nat)
    (indexed : ∀ key, first.contains key = second.contains key)
    (history : secondAdded = firstAdded ++ suffix) :
    (∀ key, (new.foldl admissionStep (first, firstAdded)).1.contains key =
      (new.foldl admissionStep (second, secondAdded)).1.contains key) ∧
    (new.foldl admissionStep (second, secondAdded)).2 =
      (new.foldl admissionStep (first, firstAdded)).2 ++ suffix := by
  induction new generalizing first second firstAdded secondAdded with
  | nil => exact ⟨indexed, history⟩
  | cons node rest ih =>
    simp only [List.foldl_cons, admissionStep, indexed node]
    cases present : second.contains node with
    | true => simpa only [present, ↓reduceIte] using ih first second firstAdded secondAdded indexed history
    | false =>
      apply ih (first.insert node) (second.insert node) (node :: firstAdded) (node :: secondAdded)
      · intro key
        simp only [Std.TreeSet.contains_insert, indexed]
      · simp only [history, List.cons_append]

/-- A fresh leading admission has the same final membership set as starting
the remaining traversal with that node in the clique. Its emitted history is
the later history followed by this first admission, as required by the
newest-first reference order. This derives both facts from executed folds. -/
theorem cliqueBatchAdmissions_cons_fresh (node : Nat) (rest initial : List Nat)
    (fresh : initial.contains node = false) :
    (∀ key, (cliqueBatchAdmissions (node :: rest) initial).1.contains key =
      (cliqueBatchAdmissions rest (node :: initial)).1.contains key) ∧
    (cliqueBatchAdmissions (node :: rest) initial).2 =
      (cliqueBatchAdmissions rest (node :: initial)).2 ++ [node] := by
  have seeds : ∀ key, (Std.TreeSet.ofList (node :: initial)).contains key =
      ((Std.TreeSet.ofList initial).insert node).contains key := by
    intro key
    simp only [Std.TreeSet.contains_ofList, Std.TreeSet.contains_insert,
      Std.LawfulEqCmp.compare_eq_iff_eq, Bool.beq_eq_decide_eq, List.contains_cons]
    simp only [eq_comm]
  have run := admissionFold_seed rest (Std.TreeSet.ofList (node :: initial))
    ((Std.TreeSet.ofList initial).insert node) [] [node] [node] seeds rfl
  unfold cliqueBatchAdmissions
  rw [List.foldl_cons]
  simp only [admissionStep, Std.TreeSet.contains_ofList, fresh]
  exact ⟨fun key => (run.1 key).symm, run.2⟩

/-- A repeated leading name leaves the complete executed admission tuple
unchanged, including its membership carrier, rather than merely its live list. -/
theorem cliqueBatchAdmissions_cons_present (node : Nat) (rest initial : List Nat)
    (present : initial.contains node = true) :
    cliqueBatchAdmissions (node :: rest) initial = cliqueBatchAdmissions rest initial := by
  unfold cliqueBatchAdmissions
  rw [List.foldl_cons]
  simp only [admissionStep, Std.TreeSet.contains_ofList, present, ↓reduceIte]

end Flapjack.RegAlloc
