import Flapjack.Compiler.Backend.RegAlloc.ProductionForcedGraph

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc

/-- Original input-node domain for the executed graph traversal. Set clauses
use the actual mixed-order enumeration, whose native codec is already proved.
This Flapjack predicate does not assume a graph output or native evaluation;
the initializer must discharge it from its real bijection bounds. -/
def ProductionGraphInputBound (ta : Nat → Nat) (dimension : Nat) : WordClashTree → Prop
  | .delta writes reads =>
      (∀ node ∈ writes, ta node < dimension) ∧ (∀ node ∈ reads, ta node < dimension)
  | .set names => ∀ node ∈ NumSet.fromAList names, ta node < dimension
  | .branch live left right =>
      ProductionGraphInputBound ta dimension left ∧ ProductionGraphInputBound ta dimension right ∧
        (∀ names, live = some names → ∀ node ∈ NumSet.fromAList names, ta node < dimension)
  | .seq left right => ProductionGraphInputBound ta dimension left ∧ ProductionGraphInputBound ta dimension right

/-- Admission preserves bounds derived solely from its original two input
lists. Untagged actual traversal infrastructure; no returned live list is
provided as a premise. -/
theorem cliqueAdmission_bound (new initial : List Nat) (dimension : Nat)
    (newBound : ∀ node ∈ new, node < dimension)
    (initialBound : ∀ node ∈ initial, node < dimension) :
    ∀ node ∈ cliqueAdmission new initial, node < dimension := by
  induction new generalizing initial with
  | nil => exact initialBound
  | cons node rest ih =>
    simp only [cliqueAdmission]
    split
    · exact ih initial (fun next belongs => newBound next (List.mem_cons_of_mem _ belongs)) initialBound
    · apply ih (node :: initial) (fun next belongs => newBound next (List.mem_cons_of_mem _ belongs))
      intro next belongs
      rcases List.mem_cons.mp belongs with rfl | belongs
      · exact newBound _ List.mem_cons_self
      · exact initialBound next belongs

/-- The executed batch caller returns a bounded live list from bounded
original input lists. The graph cache supplies no additional premise. -/
theorem extendCliqueSet_live_bound (new initial : List Nat)
    (cache : CakeNodeMap (Std.TreeSet Nat)) (dimension : Nat)
    (newBound : ∀ node ∈ new, node < dimension)
    (initialBound : ∀ node ∈ initial, node < dimension) :
    ∀ node ∈ (cakeExtendCliqueSet new initial cache).2, node < dimension := by
  simpa only [cakeExtendCliqueSet, cakeExtendCliqueSetFast, extendCliqueBatch_live] using
    cliqueAdmission_bound new initial dimension newBound initialBound

/-- Every returned live node of the complete executed graph traversal is
bounded by the original input dimension. This proves the intermediate domains
needed by Branch and Seq composition; it assumes neither graph output nor
success. Untagged actual producer infrastructure. -/
theorem mkGraphSet_live_bound (ta : Nat → Nat) (dimension : Nat) (tree : WordClashTree)
    (liveout : List Nat) (cache : CakeNodeMap (Std.TreeSet Nat))
    (inputBound : ProductionGraphInputBound ta dimension tree)
    (liveBound : ∀ node ∈ liveout, node < dimension) :
    ∀ node ∈ (cakeMkGraphSet ta tree liveout cache).2, node < dimension := by
  induction tree generalizing liveout cache with
  | delta writes reads =>
    rw [cakeMkGraphSet]
    have writeBound : ∀ node ∈ writes.map ta, node < dimension := by
      intro node belongs
      obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
      exact inputBound.1 name sourceMember
    have readBound : ∀ node ∈ reads.map ta, node < dimension := by
      intro node belongs
      obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
      exact inputBound.2 name sourceMember
    have first := extendCliqueSet_live_bound (writes.map ta) liveout cache dimension writeBound liveBound
    apply extendCliqueSet_live_bound (reads.map ta) _ _ dimension readBound
    intro node belongs
    exact first node ((List.mem_filter.mp belongs).1)
  | set names =>
    rw [cakeMkGraphSet]
    intro node belongs
    change node ∈ (NumSet.fromAList names).map ta at belongs
    obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
    exact inputBound name sourceMember
  | branch live left right ihLeft ihRight =>
    have first := ihLeft liveout cache inputBound.1 liveBound
    have second := ihRight liveout (cakeMkGraphSet ta left liveout cache).1 inputBound.2.1 liveBound
    cases live with
    | none =>
      rw [cakeMkGraphSet]
      exact extendCliqueSet_live_bound _ _ _ dimension first second
    | some names =>
      rw [cakeMkGraphSet]
      intro node belongs
      change node ∈ (NumSet.fromAList names).map ta at belongs
      obtain ⟨name, sourceMember, rfl⟩ := List.mem_map.mp belongs
      exact inputBound.2.2 names rfl name sourceMember
  | seq left right ihLeft ihRight =>
    rw [cakeMkGraphSet]
    have second := ihRight liveout cache inputBound.2 liveBound
    exact ihLeft _ _ inputBound.1 second

end Flapjack.RegAlloc
