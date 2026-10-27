import Flapjack.Compiler.Backend.SourceToFlat.Proofs.AllocDefsLookup

/-! Extract a reserved global slot block and use it in the declaration step.
The source oracle and its complete index invariant are not yet represented here;
the free-range condition is the portion needed to extract the blank slots. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- A bounded range containing only empty slots splits into a prefix, a block
of empty slots, and a suffix. -/
theorem split_blank_slots {α : Type} (slots : List (Option α)) (start count : Nat)
    (bound : start + count ≤ slots.length)
    (blank : ∀ i, start ≤ i → i < start + count → slots[i]?.getD none = none) :
    ∃ pre post, slots = pre ++ (List.replicate count none ++ post) ∧ pre.length = start := by
  induction slots generalizing start count with
  | nil =>
    have : start = 0 ∧ count = 0 := by simp at bound; omega
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨[], [], by simp, rfl⟩
  | cons head tail ih =>
    cases start with
    | zero =>
      cases count with
      | zero => exact ⟨[], head :: tail, by simp, rfl⟩
      | succ count =>
        have emptyHead : head = none := by
          have h := blank 0 (by omega) (by omega)
          simpa using h
        have tailBound : count ≤ tail.length := by simp at bound; omega
        have tailBlank : ∀ i, 0 ≤ i → i < 0 + count → tail[i]?.getD none = none := by
          intro i _ hi
          have h := blank (i + 1) (by omega) (by omega)
          simpa using h
        obtain ⟨pre, post, split, size⟩ := ih 0 count (by simpa using tailBound) tailBlank
        have : pre = [] := by
          cases pre with
          | nil => rfl
          | cons _ _ => simp at size
        subst pre
        refine ⟨[], post, ?_, rfl⟩
        simpa [emptyHead, List.replicate_succ] using congrArg (fun xs => head :: xs) split
    | succ start =>
      have tailBound : start + count ≤ tail.length := by simp at bound; omega
      have tailBlank : ∀ i, start ≤ i → i < start + count → tail[i]?.getD none = none := by
        intro i lo hi
        have h := blank (i + 1) (by omega) (by omega)
        simpa using h
      obtain ⟨pre, post, split, size⟩ := ih start count tailBound tailBlank
      refine ⟨head :: pre, post, ?_, by simp [size]⟩
      simpa using congrArg (fun xs => head :: xs) split

/-- The variable-index part of the original allocated-index set. -/
def allocatedGlobalSlot (genv : GlobalEnv) (i : Nat) : Prop :=
  i < genv.v.length ∧ (genv.v[i]?.getD none).isSome

/-- A bounded interval disjoint from allocated variable indices contains
only empty slots. This is the variable-index consequence used by HOL's
`idx_range_rel_v_REPLICATE_NONE`. -/
theorem blank_of_unallocated (genv : GlobalEnv) (start count : Nat)
    (bound : start + count ≤ genv.v.length)
    (free : ∀ i, start ≤ i → i < start + count → ¬ allocatedGlobalSlot genv i) :
    ∀ i, start ≤ i → i < start + count → genv.v[i]?.getD none = none := by
  intro i low high
  have inRange : i < genv.v.length := by omega
  have unallocated := free i low high
  cases slot : genv.v[i]?.getD none with
  | none => rfl
  | some value =>
    exfalso
    apply unallocated
    exact ⟨inRange, by rw [slot]; rfl⟩

/-- A free bounded global range supplies the blank block needed to initialize
a distinct declaration environment. This is a factored declaration result;
the full HOL oracle and index invariants remain to be connected. -/
theorem evaluate_makeVarls_freeRange {C F : Type} (genv : GlobalEnv)
    (sourceEnv : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value))
    (related : EnvRel genv (alistToNs sourceEnv) flatEnv)
    (distinct : (sourceEnv.map Prod.fst).Nodup)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState) (globals : flatState.globals = genv.v)
    (idx : Nat) (bound : idx + flatEnv.length ≤ flatState.globals.length)
    (blank : ∀ i, idx ≤ i → i < idx + flatEnv.length → flatState.globals[i]?.getD none = none)
    (n : Nat) (trace : Tra) :
    ∃ pre post, pre.length = idx ∧
      flatState.globals = pre ++ (List.replicate flatEnv.length none ++ post) ∧
      let values := flatEnv.reverse.map Prod.snd
      let finalSlots := pre ++ (values.map some ++ post)
      let finalEnv := { genv with v := finalSlots }
      let finalState := { flatState with globals := finalSlots }
      FlatSem.evaluate ⟨flatEnv⟩ flatState
          [makeVarls n trace idx (flatEnv.reverse.map Prod.fst)] =
          (finalState, .val [FlatSem.unitValue]) ∧
        GlobalGrowth genv finalEnv ∧ StateRel finalEnv sourceState finalState ∧
        GlobalEnvInv finalEnv
          { emptyEnv with v := alistToNs (allocDefs n idx (flatEnv.reverse.map Prod.fst)) }
          (fun _ => False) ⟨alistToNs sourceEnv, nsEmpty⟩ := by
  obtain ⟨pre, post, split, size⟩ := split_blank_slots flatState.globals idx flatEnv.length bound blank
  refine ⟨pre, post, size, split, ?_⟩
  subst idx
  exact evaluate_makeVarls_globalEnvInv genv sourceEnv flatEnv related distinct sourceState flatState
    stateRel globals pre post split n trace

/-- Disjointness from allocated variable indices supplies the free-slot
premise for declaration initialization. Other parts of the HOL index and oracle
invariants are still separate obligations. -/
theorem evaluate_makeVarls_unallocated {C F : Type} (genv : GlobalEnv)
    (sourceEnv : List (VarN × SemanticPrimitivesHOL.Value))
    (flatEnv : List (VarN × FlatSem.Value))
    (related : EnvRel genv (alistToNs sourceEnv) flatEnv)
    (distinct : (sourceEnv.map Prod.fst).Nodup)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F)
    (stateRel : StateRel genv sourceState flatState) (globals : flatState.globals = genv.v)
    (idx : Nat) (bound : idx + flatEnv.length ≤ genv.v.length)
    (free : ∀ i, idx ≤ i → i < idx + flatEnv.length → ¬ allocatedGlobalSlot genv i)
    (n : Nat) (trace : Tra) :
    ∃ pre post, pre.length = idx ∧
      flatState.globals = pre ++ (List.replicate flatEnv.length none ++ post) ∧
      let values := flatEnv.reverse.map Prod.snd
      let finalSlots := pre ++ (values.map some ++ post)
      let finalEnv := { genv with v := finalSlots }
      let finalState := { flatState with globals := finalSlots }
      FlatSem.evaluate ⟨flatEnv⟩ flatState
          [makeVarls n trace idx (flatEnv.reverse.map Prod.fst)] =
          (finalState, .val [FlatSem.unitValue]) ∧
        GlobalGrowth genv finalEnv ∧ StateRel finalEnv sourceState finalState ∧
        GlobalEnvInv finalEnv
          { emptyEnv with v := alistToNs (allocDefs n idx (flatEnv.reverse.map Prod.fst)) }
          (fun _ => False) ⟨alistToNs sourceEnv, nsEmpty⟩ := by
  apply evaluate_makeVarls_freeRange genv sourceEnv flatEnv related distinct sourceState flatState
    stateRel globals idx (by simpa [globals] using bound) ?_ n trace
  simpa [globals] using blank_of_unallocated genv idx flatEnv.length bound free

end Flapjack.Compiler.Backend.SourceToFlat
