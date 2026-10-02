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

end Flapjack.RegAlloc
