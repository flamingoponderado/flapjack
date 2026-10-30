import Flapjack.Compiler.Backend.BvlInline.Proofs.MappedState
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyCode
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyRuntimeFrame

/-! Primitive simulation for arity-preserving BVL code maps. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps
open Flapjack.SemanticPrimitivesHOL

/-- Non-install primitives preserve a generic mapped-state relation. This is
Flapjack proof infrastructure, not a standalone HOL declaration. -/
theorem mappedDoApp_nonInstall {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (s t : State C F) (related : mappedStateRel transform s t)
    (op : ClosLang.Op) (args : List BvlSem.Value) (notInstall : op ≠ .install) :
    match doApp op args t with
    | .err error => doApp op args s = .err error
    | .val (value, next) => ∃ sourceNext, mappedStateRel transform sourceNext next ∧
        doApp op args s = .val (value, sourceNext) := by
  have domains := mappedStateRel_codeDomain transform s t related
  have unframe := mappedStateRel_unframe transform s t related
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
    exact ⟨_, mappedStateRel_reframe transform s t next related frame, by simpa [unframe] using successRun⟩

/-- Installation is simulated by an arity-preserving body map, in both its
success and error branches. This is Flapjack proof infrastructure. -/
theorem mappedDoInstall {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (s t : State C F) (related : mappedStateRel transform s t) (args : List BvlSem.Value) :
    match doInstall (R := BvlSem.Value) args s with
    | .err error => doInstall (R := BvlSem.Value) args t = .err error
    | .val (value, next) => ∃ targetNext, mappedStateRel transform next targetNext ∧
        doInstall (R := BvlSem.Value) args t = .val (value, targetNext) := by
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
            simp only [doInstall, bytesEq, wordsEq, compilerEq, mappedProgram_disjoint,
              mappedProgram_labels]
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
                    ((name, arity, transform arity body) :: tail.map (fun (n, a, b) => (n, a, transform a b))) with
                | none => simp_all
                | some output =>
                  rcases output with ⟨bs, ws, cfg⟩
                  by_cases same : bytes = bs ∧ words = ws ∧ (s.compileOracle 1).1 = cfg
                  · simp_all
                    rw [if_pos tailFree, if_pos tailFree]
                    simp [mappedStateRel, ← mappedProgram_codeUnion]
                  · simp_all
                    rw [if_pos tailFree, if_pos tailFree]
                    have notSame : ¬(bytes = bs ∧ words = ws ∧ (s.compileOracle 1).1 = cfg) := by aesop
                    rw [if_neg notSame, if_neg notSame]
              · simp only [List.map_cons] at valid
                simp only [valid, if_false]

/-- Every primitive application is simulated from the source to the mapped
state, including dynamic installation and all error outcomes. This is generic
proof infrastructure for source passes using an arity-preserving body map. -/
theorem mappedDoApp {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (s t : State C F) (related : mappedStateRel transform s t)
    (op : ClosLang.Op) (args : List BvlSem.Value) :
    match doApp op args s with
    | .err error => doApp op args t = .err error
    | .val (value, next) => ∃ targetNext, mappedStateRel transform next targetNext ∧
        doApp op args t = .val (value, targetNext) := by
  by_cases install : op = .install
  · subst op
    simpa [doApp] using mappedDoInstall transform s t related args
  · have frame : runtimeFrame s t = t := by
      have fields := related.1
      cases s
      cases t
      simp_all [runtimeFrame]
    have domains := mappedStateRel_codeDomain transform s t related
    cases run : doApp op args s with
    | err error =>
      have swapped := doAppRerrSwap op args s error t
        ⟨run, install, by intro key present; rwa [domains] at present⟩
      simpa [frame] using swapped
    | val pair =>
      obtain ⟨value, next⟩ := pair
      have code := doApp_code op args s next value install run
      have swapped := doAppRvalSwap op args s next value t
        ⟨run, install, by intro key present; rwa [domains]⟩
      have preserved : mappedStateRel transform next (runtimeFrame next t) := by
        rcases code with ⟨code, compiler, oracle⟩
        have fields := related.1
        have compileRel := related.2
        cases s
        cases t
        cases next
        simp_all [mappedStateRel, runtimeFrame]
      exact ⟨runtimeFrame next t, preserved, by simpa [frame] using swapped⟩

end Flapjack.Compiler.Backend.BvlInline.Proofs
