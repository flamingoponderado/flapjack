import Flapjack.Compiler.Backend.BvlInline.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyCode

/-! Primitive simulation for the BVL tick-removal relation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps
open Flapjack.SemanticPrimitivesHOL

namespace SimulationCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end SimulationCarrier

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

/-- Installation simulation under the tick-removal state relation. -/
theorem doInstallSimulation {C F : Type} (s t : State C F) (related : stateRel s t)
    (args : List BvlSem.Value) :
    match doInstall (R := BvlSem.Value) args t with
    | .err error => doInstall (R := BvlSem.Value) args s = .err error
    | .val (value, next) => ∃ sourceNext, stateRel sourceNext next ∧
        doInstall (R := BvlSem.Value) args s = .val (value, sourceNext) := by
  classical
  cases args with
  | nil => simp [doInstall]
  | cons first rest =>
    cases rest with
    | nil => simp [doInstall]
    | cons second rest =>
      cases rest with
      | cons third rest => simp [doInstall]
      | nil =>
        cases bytesEq : valueToBytes first with
        | none => simp [doInstall, bytesEq]
        | some bytes =>
          cases wordsEq : valueToWords second with
          | none => simp [doInstall, bytesEq, wordsEq]
          | some words =>
            have fields := related.1
            have compilerEq := related.2
            rw [fields]
            clear fields related
            simp only [doInstall, bytesEq, wordsEq, compilerEq, tickRemoved_program_disjoint,
              tickRemoved_program_labels]
            clear compilerEq
            cases programs : (s.compileOracle 0).2 with
            | nil =>
              cases compiled : t.compile (s.compileOracle 0).1 [] with
              | none => simp [compiled]
              | some output => rcases output with ⟨bs, ws, cfg⟩; simp [compiled]
            | cons entry tail =>
              rcases entry with ⟨name, arity, body⟩
              simp only [List.map_cons]
              by_cases valid : (∀ entry ∈ (name, arity, body) :: tail, sptLookup entry.1 s.code = none) ∧
                  (((name, arity, body) :: tail).map Prod.fst).Nodup
              · simp only [List.map_cons] at valid
                simp only [valid]
                rcases valid with ⟨disjoint, nodup⟩
                simp only [List.mem_cons, forall_eq_or_imp] at disjoint
                rcases disjoint with ⟨headFree, tailFree⟩
                cases compiled : t.compile (s.compileOracle 0).1
                    ((name, arity, removeTicksSing body) :: tail.map (fun (n, a, b) => (n, a, removeTicksSing b))) with
                | none => simp_all
                | some output =>
                  rcases output with ⟨bs, ws, cfg⟩
                  by_cases same : bytes = bs ∧ words = ws ∧ (s.compileOracle 1).1 = cfg
                  · simp_all
                    rw [if_pos tailFree, if_pos tailFree]
                    simp [stateRel, ← tickRemoved_code_union]
                  · simp_all
                    rw [if_pos tailFree, if_pos tailFree]
                    have notSame : ¬(bytes = bs ∧ words = ws ∧ (s.compileOracle 1).1 = cfg) := by aesop
                    rw [if_neg notSame, if_neg notSame]
              · simp only [List.map_cons] at valid
                simp only [valid, if_false]

/-- Primitive application is simulated by tick removal, including installation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "do_app_lemma" 30
  (fmap_as_finite_support := [refs])]
theorem doAppLemma {C F : Type} (s t : Flapjack.Compiler.Backend.BvlSem.State C F) (related : stateRel s t)
    (op : ClosLang.Op) (args : List BvlSem.Value) :
    match doApp op args.reverse t with
    | .err error => doApp op args.reverse s = .err error
    | .val (value, next) => ∃ sourceNext, stateRel sourceNext next ∧
        doApp op args.reverse s = .val (value, sourceNext) := by
  by_cases install : op = .install
  · subst op
    simpa [doApp] using doInstallSimulation s t related args.reverse
  · exact doAppSimulation_nonInstall s t related op args.reverse install

end Flapjack.Compiler.Backend.BvlInline.Proofs
