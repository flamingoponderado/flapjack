import Flapjack.Compiler.Backend.FlatElim.Proofs.ValueGlobals
import Flapjack.Compiler.Backend.FlatElim.Proofs.Reachability

/-! State relation used by the flat dead-code elimination proof. -/
namespace Flapjack.Compiler.Backend.FlatElim

/-- The analysis roots are reachable and reachability is closed under the
program's dependency graph. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "decs_closed_def"]
def decsClosed (reachable : NumSet) (decs : List FlatLang.Exp) : Prop :=
  ∀ roots tree, analyseCode decs = (roots, tree) →
    (∀ key, sptMem key roots → sptMem key reachable) ∧
    ∀ source target, sptMem source reachable → isReachable tree source target → sptMem target reachable

/-- A closed declaration sequence remains closed after removing its head. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "decs_closed_reduce"]
theorem decsClosed_tail (reachable : NumSet) (head : FlatLang.Exp) (tail : List FlatLang.Exp)
    (closed : decsClosed reachable (head :: tail)) : decsClosed reachable tail := by
  intro roots tree analysis
  cases headAnalysis : analyseExp head with
  | mk headRoots headTree =>
    have combined : analyseCode (head :: tail) =
        (sptUnion headRoots roots, numSetTreeUnion headTree tree) := by
      simp [analyseCode, codeAnalysisUnion, headAnalysis, analysis]
    obtain ⟨rootsClosed, pathsClosed⟩ := closed _ _ combined
    constructor
    · intro key member
      exact rootsClosed key ((sptMem_sptUnion _ _ _).mpr (Or.inr member))
    · intro source target member path
      apply pathsClosed source target member
      rw [numSetTreeUnion_sym]
      exact isReachable_union tree headTree source target path

/-- A closed declaration sequence also has a closed singleton head. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "decs_closed_reduce_HD"]
theorem decsClosed_head (reachable : NumSet) (head : FlatLang.Exp) (tail : List FlatLang.Exp)
    (closed : decsClosed reachable (head :: tail)) : decsClosed reachable [head] := by
  intro roots tree analysis
  cases headAnalysis : analyseExp head with
  | mk headRoots headTree =>
    cases tailAnalysis : analyseCode tail with
    | mk tailRoots tailTree =>
      have combined : analyseCode (head :: tail) =
          (sptUnion headRoots tailRoots, numSetTreeUnion headTree tailTree) := by
        simp [analyseCode, codeAnalysisUnion, headAnalysis, tailAnalysis]
      have singleton : analyseCode [head] = (headRoots, headTree) := by
        have unionEmpty : sptUnion headRoots .ln = headRoots := by cases headRoots <;> simp [sptUnion]
        have treeEmpty : numSetTreeUnion headTree .ln = headTree := by cases headTree <;> rfl
        simp [analyseCode, codeAnalysisUnion, headAnalysis, unionEmpty, treeEmpty]
      rw [singleton] at analysis
      cases analysis
      obtain ⟨rootsClosed, pathsClosed⟩ := closed _ _ combined
      constructor
      · intro key member
        exact rootsClosed key ((sptMem_sptUnion _ _ _).mpr (Or.inl member))
      · intro source target member path
        exact pathsClosed source target member (isReachable_union _ tailTree source target path)

/-- The calculated closure satisfies the original closed-declaration
condition for the program it analyses. This is a helper for the elimination
simulation, not a separately named HOL theorem. -/
theorem decsClosed_analysisClosure (decs : List FlatLang.Exp) (roots : NumSet) (tree : Spt NumSet)
    (analysis : analyseCode decs = (roots, tree)) : decsClosed (closureTotal roots tree) decs := by
  intro roots' tree' eq
  rw [analysis] at eq
  cases eq
  have domain := closureTotal_reachable tree roots
  constructor
  · intro key member
    change sptDomain (closureTotal roots tree) key
    rw [domain]
    exact ⟨key, member, .refl⟩
  · intro source target member path
    change sptDomain (closureTotal roots tree) source at member
    rw [domain] at member
    obtain ⟨root, rootMem, prior⟩ := member
    change sptDomain (closureTotal roots tree) target
    rw [domain]
    exact ⟨root, rootMem, prior.trans path⟩

/-- Relate the original global list to the list after unreachable entries are
removed, retaining every reachable value and its closed dependency set. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "globals_rel_def"]
def globalsRel (reachable : NumSet) (source target : List (Option FlatSem.Value)) : Prop :=
  source.length = target.length ∧
  (∀ n, sptMem n reachable → n < target.length → source[n]?.getD none = target[n]?.getD none) ∧
  (∀ n value, n < target.length → target[n]?.getD none = some value → source[n]?.getD none = some value) ∧
  (∀ n, n < target.length → source[n]?.getD none = none → target[n]?.getD none = none) ∧
  (∀ n value, sptMem n reachable → n < target.length → target[n]?.getD none = some value →
    valueHasEval value = false ∧ ∀ key, sptMem key (findValueGlobals value) → sptMem key reachable)

/-- Global removal relations compose without changing the reachable set. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "globals_rel_trans"]
theorem globalsRel_trans (reachable : NumSet) (first middle last : List (Option FlatSem.Value))
    (relations : globalsRel reachable first middle ∧ globalsRel reachable middle last) :
    globalsRel reachable first last := by
  obtain ⟨⟨length1, reach1, present1, empty1, _⟩, ⟨length2, reach2, present2, empty2, closed⟩⟩ := relations
  refine ⟨length1.trans length2, ?_, ?_, ?_, closed⟩
  · intro n inReachable bound
    exact (reach1 n inReachable (by omega)).trans (reach2 n inReachable bound)
  · intro n value bound present
    exact present1 n value (by omega) (present2 n value bound present)
  · intro n bound empty
    exact empty2 n bound (empty1 n (by omega) empty)

/-- Stores contain no dynamic Eval values, including in reference and thunk
payloads. This helper expands the original store-value list traversal. -/
def storeHasNoEval (refs : List (Flapjack.SemanticPrimitivesHOL.StoreValue FlatSem.Value)) : Prop :=
  ∀ ref ∈ refs, match ref with
    | .refv value | .thunk _ value => valueHasEval value = false
    | .varray values => ∀ value ∈ values, valueHasEval value = false
    | .w8array _ => True

/-- Updating a store with an Eval-free entry preserves the store invariant.
This is a Flapjack helper for the evaluator simulation. -/
theorem storeHasNoEval_set (refs : List (Flapjack.SemanticPrimitivesHOL.StoreValue FlatSem.Value))
    (index : Nat) (value : Flapjack.SemanticPrimitivesHOL.StoreValue FlatSem.Value)
    (old : storeHasNoEval refs) (new : storeHasNoEval [value]) :
    storeHasNoEval (refs.set index value) := by
  intro ref member
  rcases List.mem_or_eq_of_mem_set member with oldMember | rfl
  · exact old ref oldMember
  · exact new ref (by simp)

/-- The original flat state relation, including all reference dependencies
and the absence of Eval in stored values. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_state_rel_def"]
def flatStateRel {C F : Type} (reachable : NumSet) (source target : FlatSem.State C F) : Prop :=
  source.clock = target.clock ∧ source.refs = target.refs ∧ source.ffi = target.ffi ∧
  globalsRel reachable source.globals target.globals ∧
  (∀ key, sptMem key (findRefsGlobals source.refs) → sptMem key reachable) ∧
  storeHasNoEval source.refs

/-- Updating the same reference in related states preserves the relation when
its replacement obeys the store invariants. This is a Flapjack simulation helper. -/
theorem flatStateRel_setRefs {C F : Type} (reachable : NumSet) (source target : FlatSem.State C F)
    (index : Nat) (value : Flapjack.SemanticPrimitivesHOL.StoreValue FlatSem.Value)
    (related : flatStateRel reachable source target)
    (valueReachable : globalsWithin (storeValueGlobals value) reachable)
    (valueSafe : storeHasNoEval [value]) :
    flatStateRel reachable { source with refs := source.refs.set index value }
      { target with refs := target.refs.set index value } := by
  obtain ⟨clock, refs, ffi, globals, refsReachable, refsSafe⟩ := related
  refine ⟨clock, by simp [refs], ffi, globals, ?_, ?_⟩
  · exact findRefsGlobals_set_within source.refs index value reachable refsReachable valueReachable
  · exact storeHasNoEval_set source.refs index value refsSafe valueSafe

/-- The flat state relation composes for a fixed reachable set. -/
@[hol "cakeml/compiler/backend/proofs/flat_elimProofScript.sml" "flat_state_rel_trans"]
theorem flatStateRel_trans {C F : Type} (reachable : NumSet) (first middle last : FlatSem.State C F)
    (relations : flatStateRel reachable first middle ∧ flatStateRel reachable middle last) :
    flatStateRel reachable first last := by
  obtain ⟨⟨clock1, refs1, ffi1, globals1, refsGlobals, noEval⟩,
    ⟨clock2, refs2, ffi2, globals2, _, _⟩⟩ := relations
  exact ⟨clock1.trans clock2, refs1.trans refs2, ffi1.trans ffi2,
    globalsRel_trans reachable first.globals middle.globals last.globals ⟨globals1, globals2⟩,
    refsGlobals, noEval⟩

end Flapjack.Compiler.Backend.FlatElim
