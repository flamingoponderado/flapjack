import Flapjack.Compiler.Backend.WordCse.ProductionKnowledge
import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
import Flapjack.Misc.BalancedMap.InsertCorrect
import Flapjack.Misc.BalancedMap.LookupSemantics

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV Misc.BalancedMap

/-- Actual fact-table insertion preserves every native lookup and the native
balanced-tree invariant. This is Flapjack representation infrastructure, with
no independent HOL declaration: it combines the original insertion and lookup
theorems with the executed TreeMap API. Only the input invariant and input
lookup correspondence are premises; no output relation or run is assumed. -/
theorem factInsert_transport
    (native : Map (List Nat) Nat) (executed : WordCseFactMap)
    (valid : invariant listCmp native)
    (related : ∀ key, lookup listCmp key native = wordCseListLookup key executed)
    (key : List Nat) (value : Nat) :
    invariant listCmp (insert listCmp key value native) ∧
      ∀ observed, lookup listCmp observed (insert listCmp key value native) =
        wordCseListLookup observed (wordCseListInsert key value executed) := by
  classical
  have : Std.TransCmp listCmp := by
    rw [listCmpFunctionEqStdCompare]
    infer_instance
  obtain ⟨outputValid, semanticUpdate⟩ := insertThm listCmp key value native
    ⟨goodCmpListCmp, valid⟩
  refine ⟨outputValid, ?_⟩
  intro observed
  rw [lookupThm listCmp observed _ ⟨goodCmpListCmp, outputValid⟩, semanticUpdate]
  have keys : keySet listCmp observed = keySet listCmp key ↔ observed = key :=
    (keySetEq listCmp observed key goodCmpListCmp).trans (listCmpEqCorrect observed key)
  have input := lookupThm listCmp observed native ⟨goodCmpListCmp, valid⟩
  by_cases same : observed = key
  · subst observed
    simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, wordCseListLookup,
      wordCseListInsert]
  · have different : keySet listCmp observed ≠ keySet listCmp key :=
      fun equality => same (keys.mp equality)
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different, if_false]
    rw [← input, related observed]
    simp [wordCseListLookup, wordCseListInsert, Std.TreeMap.getElem?_insert,
      listCmpEqCorrect, Ne.symm same]

end Flapjack.Compiler.Backend.WordCse
