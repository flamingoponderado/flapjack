import Flapjack.Compiler.Backend.FlatPattern.Proofs.MatchSimulation
import Flapjack.Compiler.Backend.FlatPattern.Proofs.RecursiveClosures

/-! Expression cases for the flat pattern compiler's forward simulation.
The evaluator and proof-side relations remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Literal expressions preserve the state and value relation. -/
theorem compile_lit_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra) (literal : Lit) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.lit trace literal) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  simp [FlatSem.evaluate] at sourceEval
  rcases sourceEval with ⟨rfl, rfl⟩
  refine ⟨target, .val [.litv literal], ?_, states, .values ?_⟩
  · simp [compileExp, FlatSem.evaluate]
  · exact .cons ((valueRel_lit literal _).2 rfl) .nil

/-- Variables are looked up at related names within the compiler's bound. -/
theorem compile_var_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra) (name : VarN) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.varLocal trace name) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  have nameBound : decNameToNum name < n := by simpa [compileExp] using bound
  have lookupRel := envRel_lookup n sourceEnv targetEnv name envs nameBound
  rw [holALookup_mlString, holALookup_mlString] at lookupRel
  cases sourceLookup : sourceEnv.v.lookup name with
  | none =>
    simp [FlatSem.evaluate, sourceLookup] at sourceEval
    rcases sourceEval with ⟨_, result⟩
    exact (safe result.symm).elim
  | some value =>
    cases targetLookup : targetEnv.v.lookup name with
    | none => simp [sourceLookup, targetLookup, optionRel] at lookupRel
    | some value' =>
      have values : ValueRel value value' := by simpa [sourceLookup, targetLookup, optionRel] using lookupRel
      simp [FlatSem.evaluate, sourceLookup] at sourceEval
      rcases sourceEval with ⟨rfl, rfl⟩
      refine ⟨target, .val [value'], ?_, states, .values (.cons values .nil)⟩
      simp [compileExp, FlatSem.evaluate, targetLookup]

/-- Functions compile their bodies inside related closures. -/
theorem compile_fn_simulation {C F : Type} (cfg stateCfg : Config) (trace : VarN)
    (name : VarN) (body : FlatLang.Exp) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.fn trace name body) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  have bodyBound : (compileExp cfg body).1 < n := by
    cases h : compileExp cfg body with
    | mk i rest => cases rest with | mk flag compiled => simpa [compileExp, h] using bound
  simp [FlatSem.evaluate] at sourceEval
  rcases sourceEval with ⟨rfl, rfl⟩
  have closureRel : ValueRel (.closure sourceEnv name body) (.closure targetEnv name (compileDec cfg body)) :=
    .closure envs bodyBound
  refine ⟨target, .val [.closure targetEnv name (compileDec cfg body)], ?_, states, .values (.cons closureRel .nil)⟩
  cases h : compileExp cfg body with
  | mk i rest => cases rest with | mk flag compiled => simp [compileExp, compileDec, FlatSem.evaluate, h]

/-- Raising a value returned by the operand raises that value. -/
theorem evaluate_raise_value {C F : Type} (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [body] = (next, .val [value])) :
    FlatSem.evaluate env state [.raise trace body] = (next, .err (.raise value)) := by
  simp [FlatSem.evaluate, run]

/-- Errors while evaluating a raise operand propagate unchanged. -/
theorem evaluate_raise_error {C F : Type} (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [body] = (next, .err error)) :
    FlatSem.evaluate env state [.raise trace body] = (next, .err error) := by
  simp [FlatSem.evaluate, run]

/-- Raising a related operand preserves the forward simulation. -/
theorem compile_raise_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (body : FlatLang.Exp) (bodyIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg body) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.raise trace body) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  cases compiled : compileExp cfg body with
  | mk bodyBound rest =>
    cases rest with
    | mk flag compiledBody =>
      have smaller : bodyBound < n := by simpa [compileExp, compiled] using bound
      cases bodyRun : FlatSem.evaluate sourceEnv source [body] with
      | mk sourceNext bodyResult =>
        have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
          intro bad
          subst bodyResult
          have outer := evaluate_raise_error trace body sourceEnv source sourceNext (.abort .typeError) bodyRun
          rw [sourceEval] at outer
          exact safe (congrArg Prod.snd outer)
        obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ :=
          bodyIH sourceEnv targetEnv source target sourceNext bodyResult n bodyRun envs states (by simpa [compiled] using smaller) bodySafe
        cases related with
        | error errorsRel =>
          rename_i leftError rightError
          have sourceOuter := evaluate_raise_error trace body sourceEnv source sourceNext leftError bodyRun
          have targetOuter := evaluate_raise_error trace compiledBody targetEnv target targetNext rightError (by simpa [compiled] using targetRun)
          have equal := sourceEval.symm.trans sourceOuter
          cases equal
          exact ⟨targetNext, .err rightError, by simpa [compileExp, compiled] using targetOuter, nextStates, .error errorsRel⟩
        | values valuesRel =>
          rename_i sourceValues targetValues
          obtain ⟨value, valueEq⟩ := singletonSuccess body sourceEnv source sourceNext sourceValues bodyRun
          subst sourceValues
          cases valuesRel with
          | cons valueRel tailRel =>
            cases tailRel
            rename_i value'
            have sourceOuter := evaluate_raise_value trace body sourceEnv source sourceNext value bodyRun
            have targetOuter := evaluate_raise_value trace compiledBody targetEnv target targetNext value' (by simpa [compiled] using targetRun)
            have equal := sourceEval.symm.trans sourceOuter
            cases equal
            exact ⟨targetNext, .err (.raise value'), by simpa [compileExp, compiled] using targetOuter,
              nextStates, .error (.raise valueRel)⟩

/-- Related values select the same conditional branch whenever the source
value is a valid Boolean. -/
theorem doIf_related {α : Type} (value value' : FlatSem.Value) (yes no branch : α)
    (related : ValueRel value value') (selected : FlatSem.doIf value yes no = some branch) :
    FlatSem.doIf value' yes no = some branch := by
  cases value with
  | conv stamp fields =>
    cases stamp with
    | none => simp [FlatSem.doIf] at selected
    | some stamp =>
      obtain ⟨tag, typeId⟩ := stamp
      cases typeId with
      | none => simp [FlatSem.doIf] at selected
      | some typeId =>
        cases fields with
        | cons first rest => simp [FlatSem.doIf] at selected
        | nil =>
          obtain ⟨fields', rfl, relatedFields⟩ := (valueRel_conv (some (tag, some typeId)) [] value').1 related
          cases relatedFields
          exact selected
  | litv _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ => simp [FlatSem.doIf] at selected

/-- Mapping both branches maps the conditional's selected branch. -/
theorem doIf_map {α β : Type} (f : α → β) (value : FlatSem.Value) (yes no : α) :
    FlatSem.doIf value (f yes) (f no) = (FlatSem.doIf value yes no).map f := by
  cases value with
  | conv stamp fields =>
    cases stamp with
    | none => rfl
    | some stamp =>
      obtain ⟨tag, typeId⟩ := stamp
      cases typeId <;> cases fields <;> simp [FlatSem.doIf]
      all_goals split <;> simp_all
  | litv _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ => rfl

/-- A successful Boolean condition evaluates its selected branch. -/
theorem evaluate_if_selected {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no branch : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [condition] = (next, .val [value]))
    (selected : FlatSem.doIf value yes no = some branch) :
    FlatSem.evaluate env state [.if_ trace condition yes no] =
      FlatSem.evaluate env { next with clock := min state.clock next.clock } [branch] := by
  simp only [FlatSem.evaluate, run, FlatSem.fixClock]
  split <;> simp_all

/-- An invalid Boolean condition produces a type error. -/
theorem evaluate_if_bad {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [condition] = (next, .val [value]))
    (selected : FlatSem.doIf value yes no = none) :
    FlatSem.evaluate env state [.if_ trace condition yes no] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp only [FlatSem.evaluate, run, FlatSem.fixClock]
  split <;> simp_all

/-- A condition error propagates through the conditional. -/
theorem evaluate_if_error {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [condition] = (next, .err error)) :
    FlatSem.evaluate env state [.if_ trace condition yes no] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- A conditional satisfies forward simulation when its condition and both
branches do. -/
theorem compile_if_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (condition yes no : FlatLang.Exp)
    (conditionIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg condition)
    (yesIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg yes)
    (noIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg no) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.if_ trace condition yes no) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  cases c : compileExp cfg condition with
  | mk ci crest =>
    cases crest with
    | mk cf ce =>
      cases y : compileExp cfg yes with
      | mk yi yrest =>
        cases yrest with
        | mk yf ye =>
          cases z : compileExp cfg no with
          | mk zi zrest =>
            cases zrest with
            | mk zf ze =>
              have bounds : ci < n ∧ yi < n ∧ zi < n := by
                simp [compileExp, c, y, z] at bound
                omega
              cases conditionRun : FlatSem.evaluate sourceEnv source [condition] with
              | mk sourceNext conditionResult =>
                have conditionSafe : conditionResult ≠ .err (.abort .typeError) := by
                  intro bad
                  subst conditionResult
                  have outer := evaluate_if_error trace condition yes no sourceEnv source sourceNext (.abort .typeError) conditionRun
                  rw [sourceEval] at outer
                  exact safe (congrArg Prod.snd outer)
                obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := conditionIH
                  sourceEnv targetEnv source target sourceNext conditionResult n conditionRun envs states (by simpa [c] using bounds.1) conditionSafe
                cases related with
                | error errorsRel =>
                  rename_i leftError rightError
                  have sourceOuter := evaluate_if_error trace condition yes no sourceEnv source sourceNext leftError conditionRun
                  have targetOuter := evaluate_if_error trace ce ye ze targetEnv target targetNext rightError (by simpa [c] using targetRun)
                  have equal := sourceEval.symm.trans sourceOuter
                  cases equal
                  exact ⟨_, _, by simpa [compileExp, c, y, z, evaluate_smartIf] using targetOuter,
                    stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
                | values valuesRel =>
                  rename_i sourceValues targetValues
                  obtain ⟨value, valueEq⟩ := singletonSuccess condition sourceEnv source sourceNext sourceValues conditionRun
                  subst sourceValues
                  cases valuesRel with
                  | cons valueRel tailRel =>
                    cases tailRel
                    rename_i value'
                    let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
                    let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
                    have fixedStates := stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
                    cases selected : FlatSem.doIf value yes no with
                    | none =>
                      have bad := evaluate_if_bad trace condition yes no sourceEnv source sourceNext value conditionRun selected
                      rw [sourceEval] at bad
                      exact (safe (congrArg Prod.snd bad)).elim
                    | some branch =>
                      have same := doIf_related value value' yes no branch valueRel selected
                      have sourceOuter := evaluate_if_selected trace condition yes no branch sourceEnv source sourceNext value conditionRun selected
                      have sourceBranch := sourceOuter.symm.trans sourceEval
                      have choice := FlatSem.doIf_selected value yes no branch selected
                      rcases choice with choice | choice
                      · subst branch
                        have targetSelected : FlatSem.doIf value' ye ze = some ye := by
                          have mapped := doIf_map (fun expression => (compileExp cfg expression).2.2) value' yes no
                          simpa [same, y, z] using mapped
                        have targetOuter := evaluate_if_selected trace ce ye ze ye targetEnv target targetNext value'
                          (by simpa [c] using targetRun) targetSelected
                        obtain ⟨targetFinal, output, branchRun, finalRel, resultRel⟩ := yesIH
                          sourceEnv targetEnv sourceFixed targetFixed sourceFinal sourceResult n sourceBranch envs fixedStates
                          (by simpa [y] using bounds.2.1) safe
                        refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
                        simpa [compileExp, c, y, z, evaluate_smartIf, targetOuter] using branchRun
                      · subst branch
                        have targetSelected : FlatSem.doIf value' ye ze = some ze := by
                          have mapped := doIf_map (fun expression => (compileExp cfg expression).2.2) value' yes no
                          simpa [same, y, z] using mapped
                        have targetOuter := evaluate_if_selected trace ce ye ze ze targetEnv target targetNext value'
                          (by simpa [c] using targetRun) targetSelected
                        obtain ⟨targetFinal, output, branchRun, finalRel, resultRel⟩ := noIH
                          sourceEnv targetEnv sourceFixed targetFixed sourceFinal sourceResult n sourceBranch envs fixedStates
                          (by simpa [z] using bounds.2.2) safe
                        refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
                        simpa [compileExp, c, y, z, evaluate_smartIf, targetOuter] using branchRun

/-- A successful let initializer extends the environment when a name is present. -/
theorem evaluate_let_value {C F : Type} (trace : BackendCommon.Tra) (name : Option VarN)
    (first body : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [first] = (next, .val [value])) :
    FlatSem.evaluate env state [.let_ trace name first body] =
      FlatSem.evaluate { env with v := match name with | none => env.v | some name => (name, value) :: env.v }
        { next with clock := min state.clock next.clock } [body] := by
  cases name <;> simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- An error in a let initializer is propagated regardless of its binder. -/
theorem evaluate_let_error_any {C F : Type} (trace : BackendCommon.Tra) (name : Option VarN)
    (first body : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [first] = (next, .err error)) :
    FlatSem.evaluate env state [.let_ trace name first body] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- Let expressions satisfy forward simulation when their initializer and
body satisfy their induction hypotheses. -/
theorem compile_let_simulation {C F : Type} (cfg stateCfg : Config) (trace : BackendCommon.Tra)
    (name : Option VarN) (first body : FlatLang.Exp)
    (firstIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg first)
    (bodyIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg body) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.let_ trace name first body) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  cases c : compileExp cfg first with
  | mk ci crest =>
    cases crest with
    | mk cf ce =>
      cases b : compileExp cfg body with
      | mk bi brest =>
        cases brest with
        | mk bf be =>
          have bounds : ci < n ∧ bi < n := by
            simp [compileExp, c, b] at bound
            omega
          cases firstRun : FlatSem.evaluate sourceEnv source [first] with
          | mk sourceNext firstResult =>
            have firstSafe : firstResult ≠ .err (.abort .typeError) := by
              intro bad
              subst firstResult
              have outer := evaluate_let_error_any trace name first body sourceEnv source sourceNext (.abort .typeError) firstRun
              rw [sourceEval] at outer
              exact safe (congrArg Prod.snd outer)
            obtain ⟨targetNext, targetResult, targetRun, nextStates, related⟩ := firstIH
              sourceEnv targetEnv source target sourceNext firstResult n firstRun envs states (by simpa [c] using bounds.1) firstSafe
            cases related with
            | error errorsRel =>
              rename_i leftError rightError
              have sourceOuter := evaluate_let_error_any trace name first body sourceEnv source sourceNext leftError firstRun
              have targetOuter := evaluate_let_error_any trace name ce be targetEnv target targetNext rightError (by simpa [c] using targetRun)
              have equal := sourceEval.symm.trans sourceOuter
              cases equal
              exact ⟨_, _, by simpa [compileExp, c, b] using targetOuter,
                stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates, .error errorsRel⟩
            | values valuesRel =>
              rename_i sourceValues targetValues
              obtain ⟨value, valueEq⟩ := singletonSuccess first sourceEnv source sourceNext sourceValues firstRun
              subst sourceValues
              cases valuesRel with
              | cons valueRel tailRel =>
                cases tailRel
                rename_i value'
                let sourceFixed := { sourceNext with clock := min source.clock sourceNext.clock }
                let targetFixed := { targetNext with clock := min target.clock targetNext.clock }
                have fixedStates := stateRel_fixClock stateCfg source sourceNext target targetNext states nextStates
                cases name with
                | none =>
                  have sourceOuter := evaluate_let_value trace none first body sourceEnv source sourceNext value firstRun
                  have targetOuter := evaluate_let_value trace none ce be targetEnv target targetNext value' (by simpa [c] using targetRun)
                  obtain ⟨targetFinal, output, bodyRun, finalRel, resultRel⟩ := bodyIH
                    sourceEnv targetEnv sourceFixed targetFixed sourceFinal sourceResult n (by simpa using sourceOuter.symm.trans sourceEval)
                    envs fixedStates (by simpa [b] using bounds.2) safe
                  refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
                  simpa [compileExp, c, b, targetOuter] using bodyRun
                | some name =>
                  have sourceOuter := evaluate_let_value trace (some name) first body sourceEnv source sourceNext value firstRun
                  have targetOuter := evaluate_let_value trace (some name) ce be targetEnv target targetNext value' (by simpa [c] using targetRun)
                  have extended := envRel_cons n sourceEnv targetEnv name value value' envs valueRel
                  obtain ⟨targetFinal, output, bodyRun, finalRel, resultRel⟩ := bodyIH
                    { sourceEnv with v := (name, value) :: sourceEnv.v }
                    { targetEnv with v := (name, value') :: targetEnv.v } sourceFixed targetFixed sourceFinal sourceResult n
                    (by simpa using sourceOuter.symm.trans sourceEval) extended fixedStates (by simpa [b] using bounds.2) safe
                  refine ⟨targetFinal, output, ?_, finalRel, resultRel⟩
                  simpa [compileExp, c, b, targetOuter] using bodyRun

/-- Recursive function compilation maps bodies in source order. -/
theorem compileFuns_rows (cfg : Config) (funs : List (VarN × VarN × FlatLang.Exp)) :
    (compileFuns cfg funs).2.2 = compiledRecFuns cfg funs := by
  induction funs with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, arg, body⟩ := entry
    cases first : compileExp cfg body with
    | mk bound result =>
      cases result with
      | mk flag compiled =>
        cases tail : compileFuns cfg rest with
        | mk tailBound result =>
          cases result with
          | mk tailFlag compiledTail =>
            simpa [compileFuns, compiledRecFuns, compileDec, first, tail] using ih

/-- Every recursive function body is bounded by the bundle's maximum. -/
theorem compileFuns_member_bound (cfg : Config) (funs : List (VarN × VarN × FlatLang.Exp))
    (entry : VarN × VarN × FlatLang.Exp) (member : entry ∈ funs) :
    (compileExp cfg entry.2.2).1 ≤ (compileFuns cfg funs).1 := by
  induction funs with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨name, arg, body⟩ := first
    cases head : compileExp cfg body with
    | mk headBound result =>
      cases result with
      | mk flag compiled =>
        cases tail : compileFuns cfg rest with
        | mk tailBound result =>
          cases result with
          | mk tailFlag compiledTail =>
            simp only [List.mem_cons] at member
            rcases member with equal | later
            · subst entry
              simp [compileFuns, head, tail]
              omega
            · have bound := ih later
              simp only [tail] at bound
              simp only [compileFuns, head, tail]
              omega

/-- Recursive binding preserves the forward simulation under the body's
induction hypothesis; function body bounds provide the closure relation. -/
theorem compile_letrec_simulation {C F : Type} (cfg stateCfg : Config) (trace : VarN)
    (funs : List (VarN × VarN × FlatLang.Exp)) (body : FlatLang.Exp)
    (bodyIH : ExpressionSimulation (C := C) (F := F) cfg stateCfg body) :
    ExpressionSimulation (C := C) (F := F) cfg stateCfg (.letrec trace funs body) := by
  intro sourceEnv targetEnv source target sourceFinal sourceResult n sourceEval envs states bound safe
  cases f : compileFuns cfg funs with
  | mk fi frest =>
    cases frest with
    | mk ff fs =>
      cases b : compileExp cfg body with
      | mk bi brest =>
        cases brest with
        | mk bf be =>
          have bounds : fi < n ∧ bi < n := by simp [compileExp, f, b] at bound; omega
          have fsEq : fs = compiledRecFuns cfg funs := by simpa [f] using compileFuns_rows cfg funs
          have funBounds : ∀ entry ∈ funs, (compileExp cfg entry.2.2).1 < n := by
            intro entry member
            have h := compileFuns_member_bound cfg funs entry member
            simp only [f] at h
            omega
          by_cases distinct : (funs.map Prod.fst).Nodup
          · have targetDistinct : (fs.map Prod.fst).Nodup := by simpa [fsEq, compiledRecFuns_names] using distinct
            have relatedEnvs := envRel_buildRec n sourceEnv targetEnv cfg funs envs funBounds
            have sourceBody : FlatSem.evaluate { sourceEnv with v := FlatSem.buildRecEnv funs sourceEnv sourceEnv.v }
                source [body] = (sourceFinal, sourceResult) := by simpa [FlatSem.evaluate, distinct] using sourceEval
            obtain ⟨targetFinal, targetResult, bodyRun, finalRel, resultRel⟩ := bodyIH
              { sourceEnv with v := FlatSem.buildRecEnv funs sourceEnv sourceEnv.v }
              { targetEnv with v := FlatSem.buildRecEnv (compiledRecFuns cfg funs) targetEnv targetEnv.v }
              source target sourceFinal sourceResult n sourceBody relatedEnvs states (by simpa [b] using bounds.2) safe
            refine ⟨targetFinal, targetResult, ?_, finalRel, resultRel⟩
            simpa [compileExp, f, b, FlatSem.evaluate, fsEq, compiledRecFuns_names, distinct] using bodyRun
          · have bad : sourceResult = .err (.abort .typeError) := by
              simpa [FlatSem.evaluate, distinct] using congrArg Prod.snd sourceEval.symm
            exact (safe bad).elim

end Flapjack.Compiler.Backend.FlatPattern
