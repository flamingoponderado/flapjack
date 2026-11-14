module

public import Flapjack.Compiler.Backend.BviInline.Proofs.CompileSimulation
public import Flapjack.Compiler.Backend.BviInline.Proofs.CodeLabels

@[expose] public section

/-! State and code relations for BVI tick removal. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem

namespace TickPrimitiveCarrier
/-- The BVI reference-map representation has a canonical roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end TickPrimitiveCarrier

/-- Remove ticks from each body while preserving arbitrary labels and arities. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "clean_prog_def"]
def cleanProg {Label Arity : Type} (program : List (Label × Arity × Bvi.Exp)) : List (Label × Arity × Bvi.Exp) :=
  program.map fun (name, arity, body) => (name, arity, removeTicksSource body)

/-- Empty and cons programs reduce by applying tick removal to each body. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "clean_prog_CONS"]
theorem cleanProgCons {A B C D : Type} (entry : C × D × Bvi.Exp)
    (rest : List (C × D × Bvi.Exp)) :
    cleanProg ([] : List (A × B × Bvi.Exp)) = [] ∧
      cleanProg (entry :: rest) = (entry.1, entry.2.1, removeTicksSource entry.2.2) :: cleanProg rest := by
  cases entry with
  | mk name pair => cases pair; exact ⟨rfl, rfl⟩

/-- Tick cleanup preserves labels and commutes with sparse-tree conversion. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "clean_prog_simps"]
theorem cleanProgSimps {Arity : Type} (program : List (Nat × Arity × Bvi.Exp)) :
    (cleanProg program).map Prod.fst = program.map Prod.fst ∧
      sptMap (fun entry => (entry.1, removeTicksSource entry.2)) (sptFromAList program) =
        sptFromAList (cleanProg program) := by
  refine ⟨Proofs.removeTicksProg_mapFst program, ?_⟩
  rw [sptMap_sptFromAList]
  rfl

/-- Adapt a compiler callback to remove ticks from each incoming code segment. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_ticks_cc_def"]
def removeTicksCc {Cfg Label Arity Result : Type}
    (compiler : Cfg → List (Label × Arity × Bvi.Exp) → Result) :
    Cfg → List (Label × Arity × Bvi.Exp) → Result :=
  fun config program => compiler config (cleanProg program)

/-- Remove ticks from the code component of an oracle entry. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_ticks_co_def"]
def removeTicksCo {Cfg Label Arity : Type}
    (entry : Cfg × List (Label × Arity × Bvi.Exp)) :
    Cfg × List (Label × Arity × Bvi.Exp) :=
  (entry.1, cleanProg entry.2)

/-- The source and target state relation for tick cleanup. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_state_rel_def"
  (fmap_as_finite_support := [refs])]
def RemoveStateRel {C F : Type} (source target : BviState C F) : Prop :=
  target.refs = source.refs ∧ target.clock = source.clock ∧ target.global = source.global ∧
  target.ffi = source.ffi ∧
  target.code = sptMap (fun entry => (entry.1, removeTicksSource entry.2)) source.code ∧
  target.compileOracle = (removeTicksCo ∘ source.compileOracle) ∧ source.compile = removeTicksCc target.compile

/-- Flapjack infrastructure: equal clock replacement preserves tick-cleanup
state relatedness. -/
theorem removeStateRel_with_clock {C F : Type} (source target : BviState C F)
    (states : RemoveStateRel source target) (clock : Nat) :
    RemoveStateRel { source with clock := clock } { target with clock := clock } := by
  exact ⟨states.1, rfl, states.2.2⟩

/-- Flapjack infrastructure: equal clock decrements preserve tick-cleanup
state relatedness. -/
theorem removeStateRel_decClock {C F : Type} (source target : BviState C F)
    (states : RemoveStateRel source target) (ticks : Nat) :
    RemoveStateRel (BviSem.decClock ticks source) (BviSem.decClock ticks target) := by
  simpa [BviSem.decClock, states.2.1] using removeStateRel_with_clock source target states (source.clock - ticks)

/-- Matching code lookup preserves arguments and removes ticks from the selected callee. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_state_rel_find_code_eq"
  (fmap_as_finite_support := [refs])]
theorem findCode_removeStateRel {C F : Type} (source target : BviState C F)
    (states : RemoveStateRel source target) (destination : Option Nat) (args : List Value) :
    findCode destination args target.code =
      (findCode destination args source.code).map (fun (values, body) => (values, removeTicksSource body)) := by
  rw [states.2.2.2.2.1]
  cases destination with
  | some name =>
    simp only [findCode, sptLookup_sptMap]
    cases lookup : sptLookup name source.code with
    | none => rfl
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      simp only [Option.map_some]
      split <;> rfl
  | none =>
    simp only [findCode]
    by_cases empty : args.isEmpty = true
    · simp [empty]
    · simp only [empty, Bool.false_eq_true, ↓reduceIte]
      cases last : Flapjack.holLast args with
      | codePtr name =>
        simp only [sptLookup_sptMap]
        cases lookup : sptLookup name source.code with
        | none => rfl
        | some entry =>
          obtain ⟨arity, body⟩ := entry
          simp only [Option.map_some]
          split <;> rfl
      | _ => rfl

/-- Flapjack infrastructure: a non-install primitive preserves the tick
cleanup relation and transfers its result, including errors. -/
theorem removeStateRel_doApp_nonInstall {C F : Type} (source target : BviState C F)
    (states : RemoveStateRel source target) (op : ClosLang.Op) (args : List Value)
    (notInstall : op ≠ .install) :
    match BviSem.doApp op args source with
    | .err error => BviSem.doApp op args target = .err error
    | .val (value, next) => ∃ targetNext, BviSem.doApp op args target = .val (value, targetNext) ∧
        RemoveStateRel next targetNext := by
  have frameEq : BviSem.runtimeFrame source target = target := by
    rcases states with ⟨refs, clock, global, ffi, _⟩
    cases source
    cases target
    simp_all [BviSem.runtimeFrame]
  have domains : sptDomain source.code = sptDomain target.code := by
    rw [states.2.2.2.2.1, sptDomain_sptMap]
  have framed := BviSem.doAppFallback_frame op args source target notInstall domains
  have sourceEq : BviSem.doApp op args source = BviSem.doAppFallback op args source := by
    cases op <;> simp_all [BviSem.doApp]
  have targetEq : BviSem.doApp op args target = BviSem.doAppFallback op args target := by
    cases op <;> simp_all [BviSem.doApp]
  rw [sourceEq, targetEq]
  cases run : BviSem.doAppFallback op args source with
  | err error => simpa [run, frameEq] using framed
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have fields := BviSem.doAppFallback_compiler_fields op args source next value run
    obtain ⟨compiler, oracle, code⟩ := fields
    have nextRel : RemoveStateRel next (BviSem.runtimeFrame next target) := by
      simpa [RemoveStateRel, BviSem.runtimeFrame, compiler, oracle, code] using states.2.2.2.2
    exact ⟨BviSem.runtimeFrame next target, by simpa [run, frameEq] using framed, nextRel⟩

/-- Flapjack infrastructure: installation results have the same value and
always use a type error across arbitrary error-payload types. This allows the
generic HOL theorem to reuse the evaluator-specific installation proof. -/
private theorem doInstall_retype {C F R S : Type} (args : List Value) (state : BviState C F) :
    BviSem.doInstall (R := R) args state =
      (match BviSem.doInstall (R := S) args state with
       | .val pair => .val pair
       | .err _ => .err (.abort .typeError)) := by
  unfold BviSem.doInstall
  repeat' split
  all_goals simp_all
  all_goals split at * <;> simp_all

/-- Flapjack infrastructure: successful dynamic installation also preserves
tick-cleanup state relatedness. -/
theorem removeStateRel_doInstall_success {C F : Type} (source sourceNext target : BviState C F)
    (args : List Value) (value : Value) (states : RemoveStateRel source target)
    (run : BviSem.doInstall (R := ExnOrRet) args source = .val (value, sourceNext)) :
    ∃ targetNext, BviSem.doInstall (R := ExnOrRet) args target = .val (value, targetNext) ∧
      RemoveStateRel sourceNext targetNext := by
  obtain ⟨v1, v2, len1, len2, bytes, data, config, key, arity, body, rest, configNext,
    argsEq, decode1, decode2, lenEq1, lenEq2, oracle0, absent, unique, callback, oracle1, valueEq, stateEq⟩ :=
    BviTailrec.doInstall_success_inv args source sourceNext value run
  let code := (key, arity, body) :: rest
  let cleaned := cleanProg code
  have domains : sptDomain source.code = sptDomain target.code := by
    rw [states.2.2.2.2.1, sptDomain_sptMap]
  have targetAbsent : ∀ entry ∈ cleaned, sptLookup entry.1 target.code = none := by
    intro entry member
    have memberNames : entry.1 ∈ code.map Prod.fst := by
      have h : entry.1 ∈ cleaned.map Prod.fst := List.mem_map_of_mem member
      simpa [cleaned, cleanProg, List.map_map, Function.comp_def] using h
    obtain ⟨original, originalMem, same⟩ := List.mem_map.mp memberNames
    have no := absent original (by simpa [code] using originalMem)
    cases found : sptLookup entry.1 target.code with
    | none => rfl
    | some result =>
      have present : sptDomain target.code entry.1 := (sptMem_iff_lookup _ _).2 ⟨result, found⟩
      rw [← domains] at present
      have absentSource : sptLookup entry.1 source.code = none := by simpa [same] using no
      simp [sptDomain, absentSource] at present
  have targetUnique : (cleaned.map Prod.fst).Nodup := by simpa [cleaned, cleanProg, List.map_map, Function.comp_def, code] using unique
  have targetOracle0 : target.compileOracle 0 = (config, cleaned) := by
    rw [states.2.2.2.2.2.1]
    simp [removeTicksCo, oracle0, cleaned, code]
  have targetCallback : target.compile config cleaned = some (bytes, data, configNext) := by
    rw [states.2.2.2.2.2.2] at callback
    simpa [removeTicksCc, cleaned, code] using callback
  have targetOracle1 : (target.compileOracle 1).1 = configNext := by
    rw [states.2.2.2.2.2.1]
    simpa [removeTicksCo] using oracle1
  have head : cleaned = (key, arity, removeTicksSource body) :: cleanProg rest := rfl
  have targetRun : BviSem.doInstall (R := ExnOrRet) args target =
      .val (.codePtr key, { target with
        code := sptUnion target.code (sptFromAList cleaned)
        compileOracle := fun n => target.compileOracle (n + 1) }) := by
    have targetUniqueHead : (((key, arity, removeTicksSource body) :: cleanProg rest).map Prod.fst).Nodup := by
      rw [← head]
      exact targetUnique
    cases target
    simp_all [BviSem.doInstall]
    exact targetAbsent.2
  refine ⟨{ target with
    code := sptUnion target.code (sptFromAList cleaned)
    compileOracle := fun n => target.compileOracle (n + 1) }, ?_, ?_⟩
  · simpa [valueEq] using targetRun
  · rw [stateEq]
    rcases states with ⟨refs, clock, global, ffi, codeRel, oracleRel, compilerRel⟩
    refine ⟨refs, clock, global, ffi, ?_, ?_, compilerRel⟩
    · simp [code, cleaned, codeRel, sptMap_sptUnion, (cleanProgSimps code).2]
    · funext n
      exact congrFun oracleRel (n + 1)

/-- Flapjack infrastructure: if installing cleaned code succeeds, the
corresponding installation before tick cleanup succeeds as well. -/
theorem removeStateRel_doInstall_success_reverse {C F : Type} (source target targetNext : BviState C F)
    (args : List Value) (value : Value) (states : RemoveStateRel source target)
    (run : BviSem.doInstall (R := ExnOrRet) args target = .val (value, targetNext)) :
    ∃ sourceValue sourceNext, BviSem.doInstall (R := ExnOrRet) args source = .val (sourceValue, sourceNext) := by
  obtain ⟨v1, v2, len1, len2, bytes, data, config, key, arity, body, rest, configNext,
    argsEq, decode1, decode2, lenEq1, lenEq2, targetOracle0, absent, unique, callback, targetOracle1, _, _⟩ :=
    BviTailrec.doInstall_success_inv args target targetNext value run
  cases oracle0 : source.compileOracle 0 with
  | mk sourceConfig sourceCode =>
    have targetOracle : target.compileOracle 0 = (sourceConfig, cleanProg sourceCode) := by
      rw [states.2.2.2.2.2.1]
      simp [removeTicksCo, oracle0]
    rw [targetOracle] at targetOracle0
    have configs : sourceConfig = config := (Prod.mk.inj targetOracle0).1
    have codes : cleanProg sourceCode = (key, arity, body) :: rest := (Prod.mk.inj targetOracle0).2
    subst sourceConfig
    cases sourceCode with
    | nil => simp [cleanProg] at codes
    | cons entry tail =>
      obtain ⟨sourceKey, sourceArity, sourceBody⟩ := entry
      have codeEq : cleanProg ((sourceKey, sourceArity, sourceBody) :: tail) =
          (sourceKey, sourceArity, removeTicksSource sourceBody) :: cleanProg tail := rfl
      rw [codeEq] at codes
      have heads := (List.cons.inj codes).1
      have tails := (List.cons.inj codes).2
      have keyEq : sourceKey = key := congrArg Prod.fst heads
      subst sourceKey
      have sourceUnique : (((key, sourceArity, sourceBody) :: tail).map Prod.fst).Nodup := by
        have names : (cleanProg ((key, sourceArity, sourceBody) :: tail)).map Prod.fst =
            ((key, sourceArity, sourceBody) :: tail).map Prod.fst :=
          Proofs.removeTicksProg_mapFst ((key, sourceArity, sourceBody) :: tail)
        rw [codeEq] at names
        rw [heads, tails] at names
        rw [← names]
        exact unique
      have domains : sptDomain source.code = sptDomain target.code := by
        rw [states.2.2.2.2.1, sptDomain_sptMap]
      have sourceAbsent : ∀ entry ∈ ((key, sourceArity, sourceBody) :: tail), sptLookup entry.1 source.code = none := by
        intro entry member
        have memberNames : entry.1 ∈ ((key, arity, body) :: rest).map Prod.fst := by
          have h : entry.1 ∈ (((key, sourceArity, sourceBody) :: tail).map Prod.fst) := List.mem_map_of_mem member
          rw [← (show (cleanProg ((key, sourceArity, sourceBody) :: tail)).map Prod.fst =
            ((key, sourceArity, sourceBody) :: tail).map Prod.fst from
            Proofs.removeTicksProg_mapFst ((key, sourceArity, sourceBody) :: tail)), codeEq, heads, tails] at h
          exact h
        obtain ⟨other, otherMem, same⟩ := List.mem_map.mp memberNames
        have no := absent other otherMem
        cases found : sptLookup entry.1 source.code with
        | none => rfl
        | some result =>
          have present : sptDomain source.code entry.1 := (sptMem_iff_lookup _ _).2 ⟨result, found⟩
          rw [domains] at present
          have absentTarget : sptLookup entry.1 target.code = none := by simpa [same] using no
          simp [sptDomain, absentTarget] at present
      have sourceCallback : source.compile config ((key, sourceArity, sourceBody) :: tail) =
          some (bytes, data, configNext) := by
        rw [states.2.2.2.2.2.2]
        simpa [removeTicksCc, codeEq, heads, tails] using callback
      have sourceOracle1 : (source.compileOracle 1).1 = configNext := by
        rw [states.2.2.2.2.2.1] at targetOracle1
        simpa [removeTicksCo] using targetOracle1
      refine ⟨.codePtr key, { source with
        code := sptUnion source.code (sptFromAList ((key, sourceArity, sourceBody) :: tail))
        compileOracle := fun n => source.compileOracle (n + 1) }, ?_⟩
      cases source
      simp_all [BviSem.doInstall]
      exact sourceAbsent.2

/-- Flapjack infrastructure: failed installation is unchanged by tick
cleanup, including the type-error case. -/
theorem removeStateRel_doInstall_error {C F : Type} (source target : BviState C F)
    (args : List Value) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (states : RemoveStateRel source target)
    (run : BviSem.doInstall (R := ExnOrRet) args source = .err error) :
    BviSem.doInstall (R := ExnOrRet) args target = .err error := by
  have errorEq : error = .abort .typeError := BviTailrec.doApp_install_error args source error (by
    simpa only [BviSem.doApp] using run)
  cases targetRun : BviSem.doInstall (R := ExnOrRet) args target with
  | err targetError =>
    have targetEq : targetError = .abort .typeError := BviTailrec.doApp_install_error args target targetError (by
      simpa only [BviSem.doApp] using targetRun)
    simp [errorEq, targetEq]
  | val pair =>
    obtain ⟨targetValue, targetNext⟩ := pair
    obtain ⟨sourceValue, sourceNext, sourceRun⟩ :=
      removeStateRel_doInstall_success_reverse source target targetNext args targetValue states targetRun
    rw [run] at sourceRun
    contradiction

/-- Installation preserves the tick-cleanup relation, with independent
success-branch error payload types. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_state_rel_do_install"
  (fmap_as_finite_support := [refs])]
theorem removeStateRel_doInstall {C F A B : Type} (args : List Value)
    (source target : BviState C F) (states : RemoveStateRel source target) :
    match BviSem.doInstall (R := A) args source with
    | .val (value, next) => ∃ targetNext,
        BviSem.doInstall (R := B) args target = .val (value, targetNext) ∧ RemoveStateRel next targetNext
    | .err error => BviSem.doInstall (R := A) args target = .err error := by
  cases sourceRun : BviSem.doInstall (R := ExnOrRet) args source with
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have sourceGeneric : BviSem.doInstall (R := A) args source = .val (value, next) := by
      rw [doInstall_retype (S := ExnOrRet), sourceRun]
    simp only [sourceGeneric]
    obtain ⟨targetNext, targetFixed, relation⟩ :=
      removeStateRel_doInstall_success source next target args value states sourceRun
    refine ⟨targetNext, ?_, relation⟩
    rw [doInstall_retype (R := B) (S := ExnOrRet), targetFixed]
  | err error =>
    have errorEq : error = .abort .typeError := BviTailrec.doApp_install_error args source error (by
      simpa only [BviSem.doApp] using sourceRun)
    subst error
    have sourceGeneric : BviSem.doInstall (R := A) args source = .err (.abort .typeError) := by
      rw [doInstall_retype (S := ExnOrRet), sourceRun]
    simp only [sourceGeneric]
    have targetFixed := removeStateRel_doInstall_error source target args (.abort .typeError) states sourceRun
    rw [doInstall_retype (R := A) (S := ExnOrRet), targetFixed]

/-- Every primitive operation transfers through the tick-cleanup relation,
preserving both successful results and errors. The dispatcher inherits the
real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "remove_state_rel_do_app"
  (fmap_as_finite_support := [refs])]
theorem removeStateRel_doApp {C F : Type} (op : ClosLang.Op) (args : List Value)
    (source target : BviState C F) (states : RemoveStateRel source target) :
    match BviSem.doApp op args source with
    | .err error => BviSem.doApp op args target = .err error
    | .val (value, next) => ∃ targetNext, BviSem.doApp op args target = .val (value, targetNext) ∧
        RemoveStateRel next targetNext := by
  by_cases install : op = .install
  · subst op
    have transfer := removeStateRel_doInstall (A := ExnOrRet) (B := ExnOrRet) args source target states
    cases run : BviSem.doInstall (R := ExnOrRet) args source with
    | err error => simpa only [BviSem.doApp, run] using transfer
    | val pair =>
      obtain ⟨value, next⟩ := pair
      simpa only [BviSem.doApp, run] using transfer
  · exact removeStateRel_doApp_nonInstall source target states op args install

/-- Flapjack infrastructure: primitive simulation also works from the
cleaned state back to the original state, with the same value or error. -/
theorem removeStateRel_doApp_reverse {C F : Type} (source target : BviState C F)
    (states : RemoveStateRel source target) (op : ClosLang.Op) (args : List Value) :
    match BviSem.doApp op args target with
    | .err error => BviSem.doApp op args source = .err error
    | .val (value, next) => ∃ sourceNext, BviSem.doApp op args source = .val (value, sourceNext) ∧
        RemoveStateRel sourceNext next := by
  have forward := removeStateRel_doApp op args source target states
  cases sourceRun : BviSem.doApp op args source with
  | err error =>
    rw [sourceRun] at forward
    rw [forward]
  | val pair =>
    obtain ⟨value, next⟩ := pair
    rw [sourceRun] at forward
    obtain ⟨targetNext, targetRun, nextRel⟩ := forward
    rw [targetRun]
    exact ⟨next, rfl, nextRel⟩

end Flapjack.Compiler.Backend.BviInline
