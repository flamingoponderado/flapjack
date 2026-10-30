import Flapjack.Compiler.Backend.BvlInline.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyCode

/-! Primitive simulation for the BVL tick-removal relation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps
open Flapjack.SemanticPrimitivesHOL

/-- Related states have identical code domains. -/
theorem stateRel_codeDomain {C F : Type} (s t : State C F) (related : stateRel s t) :
    sptDomain t.code = sptDomain s.code := by
  have code := congrArg (fun state : State C F => state.code) related.1
  rw [code, sptDomain_sptMap]

/-- Replace a transformed state's code fields to recover its source state. -/
theorem stateRel_unframe {C F : Type} (s t : State C F) (related : stateRel s t) :
    { t with code := s.code, compile := s.compile, compileOracle := s.compileOracle } = s := by
  have fields := stateRel_fields s t related
  cases s
  cases t
  simp_all

/-- A state that retains transformed code fields can be paired with its
source-framed counterpart. -/
theorem stateRel_reframe {C F : Type} (s t next : State C F) (related : stateRel s t)
    (frame : next.code = t.code ∧ next.compile = t.compile ∧ next.compileOracle = t.compileOracle) :
    stateRel { next with code := s.code, compile := s.compile, compileOracle := s.compileOracle } next := by
  have code := congrArg (fun state : State C F => state.code) related.1
  have oracle := congrArg (fun state : State C F => state.compileOracle) related.1
  obtain ⟨hcode, hcompile, horacle⟩ := frame
  constructor
  · cases next
    simp_all
  · simpa [hcompile] using related.2

/-- The non-install cases of primitive simulation follow from code-domain
preservation. The installation case of the source theorem remains separate. -/
theorem doAppSimulation_nonInstall {C F : Type} (s t : State C F)
    (related : stateRel s t) (op : ClosLang.Op) (args : List BvlSem.Value)
    (notInstall : op ≠ .install) :
    match doApp op args t with
    | .err error => doApp op args s = .err error
    | .val (value, next) => ∃ sourceNext, stateRel sourceNext next ∧
        doApp op args s = .val (value, sourceNext) := by
  have domains := stateRel_codeDomain s t related
  have unframe := stateRel_unframe s t related
  cases run : doApp op args t with
  | err error =>
    have errorRun := doApp_withCodeErr op args t error s.code s.compile s.compileOracle
      run notInstall (Or.inl (by intro key present; rwa [domains]))
    simpa [unframe] using errorRun
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have frame := doApp_code op args t next value notInstall run
    have successRun := doApp_withCode op args t next value s.code s.compile s.compileOracle
      run notInstall (by intro key present; rwa [domains] at present)
    exact ⟨_, stateRel_reframe s t next related frame, by simpa [unframe] using successRun⟩

/-- The transformed oracle retains exactly the original entry labels. -/
theorem tickRemoved_program_labels (program : List (Nat × Nat × Bvl.Exp)) :
    (program.map (fun (name, arity, body) => (name, arity, removeTicksSing body))).map Prod.fst =
      program.map Prod.fst := by
  simp [List.map_map, Function.comp_def]

/-- A mapped program is disjoint from mapped code exactly when the original
program is disjoint from the original code. -/
theorem tickRemoved_program_disjoint (code : Spt (Nat × Bvl.Exp))
    (program : List (Nat × Nat × Bvl.Exp)) :
    (∀ entry ∈ program.map (fun (name, arity, body) => (name, arity, removeTicksSing body)),
      sptLookup entry.1 (sptMap (fun (arity, body) => (arity, removeTicksSing body)) code) = none) ↔
    (∀ entry ∈ program, sptLookup entry.1 code = none) := by
  simp only [List.mem_map, sptLookup_sptMap, Option.map_eq_none_iff]
  constructor
  · intro h entry mem
    exact h (entry.1, entry.2.1, removeTicksSing entry.2.2) ⟨entry, mem, rfl⟩
  · intro h entry ⟨original, mem, equal⟩
    subst entry
    exact h original mem

/-- Installing mapped program entries yields the mapped union of the source
code and installed program. -/
theorem tickRemoved_code_union (code : Spt (Nat × Bvl.Exp))
    (program : List (Nat × Nat × Bvl.Exp)) :
    sptUnion (sptMap (fun (arity, body) => (arity, removeTicksSing body)) code)
      (sptFromAList (program.map fun (name, arity, body) => (name, arity, removeTicksSing body))) =
    sptMap (fun (arity, body) => (arity, removeTicksSing body)) (sptUnion code (sptFromAList program)) := by
  rw [sptMap_sptUnion, sptMap_sptFromAList]

end Flapjack.Compiler.Backend.BvlInline.Proofs
