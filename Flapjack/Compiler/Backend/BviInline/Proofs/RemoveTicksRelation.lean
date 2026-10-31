import Flapjack.Compiler.Backend.BviInline.Proofs.CompileSimulation

/-! State and code relations for BVI tick removal. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem

/-- Flapjack infrastructure: remove ticks from every labeled code entry. -/
def cleanProg (program : List (Nat × Nat × Bvi.Exp)) : List (Nat × Nat × Bvi.Exp) :=
  program.map fun (name, arity, body) => (name, arity, removeTicksSource body)

/-- Flapjack infrastructure: tick cleanup preserves program labels. -/
theorem cleanProg_names (program : List (Nat × Nat × Bvi.Exp)) :
    (cleanProg program).map Prod.fst = program.map Prod.fst := by
  induction program with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, arity, body⟩ := entry
    simp [cleanProg, ← ih]

/-- Flapjack infrastructure: tree conversion and association-list conversion
commute with tick cleanup, including malformed sparse-tree shapes. -/
theorem cleanProg_fromAList (program : List (Nat × Nat × Bvi.Exp)) :
    sptMap (fun entry => (entry.1, removeTicksSource entry.2)) (sptFromAList program) =
      sptFromAList (cleanProg program) := by
  rw [sptMap_sptFromAList]
  rfl

/-- Flapjack infrastructure: adapt the callback to remove ticks from each
incoming code segment. -/
def removeTicksCc {C : Type} (compiler : BviSem.Compiler C) : BviSem.Compiler C :=
  fun config program => compiler config (cleanProg program)

/-- Flapjack infrastructure: remove ticks from each oracle code segment. -/
def removeTicksCo {C : Type} (oracle : BviSem.CompileOracle C) : BviSem.CompileOracle C :=
  fun index => ((oracle index).1, cleanProg (oracle index).2)

/-- Flapjack infrastructure: state relation for tick cleanup. This remains
untagged pending source evaluator and state-carrier review. -/
def RemoveStateRel {C F : Type} (source target : BviState C F) : Prop :=
  target.refs = source.refs ∧ target.clock = source.clock ∧ target.global = source.global ∧
  target.ffi = source.ffi ∧
  target.code = sptMap (fun entry => (entry.1, removeTicksSource entry.2)) source.code ∧
  target.compileOracle = removeTicksCo source.compileOracle ∧ source.compile = removeTicksCc target.compile

/-- Flapjack infrastructure: equal clock replacement preserves tick-cleanup
state relatedness. -/
theorem removeStateRel_with_clock {C F : Type} (source target : BviState C F)
    (states : RemoveStateRel source target) (clock : Nat) :
    RemoveStateRel { source with clock := clock } { target with clock := clock } := by
  exact ⟨states.1, rfl, states.2.2⟩

/-- Flapjack infrastructure: matching code lookup preserves arguments and
removes ticks from the selected callee. -/
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

/-- Flapjack infrastructure: cleaned programs start in tick-related states
when their oracle and compiler callbacks are adapted in the same way. -/
theorem removeStateRel_initial {C F : Type} (program : List (Nat × Nat × Bvi.Exp))
    (oracle : BviSem.CompileOracle C) (compiler : BviSem.Compiler C)
    (ffi : HolFfiState F) (clock : Nat) :
    RemoveStateRel (initialState ffi (sptFromAList program) oracle (removeTicksCc compiler) clock)
      (initialState ffi (sptFromAList (cleanProg program)) (removeTicksCo oracle) compiler clock) := by
  exact ⟨rfl, rfl, rfl, rfl, (cleanProg_fromAList program).symm, rfl, rfl⟩

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
      simpa [cleaned, cleanProg_names] using h
    obtain ⟨original, originalMem, same⟩ := List.mem_map.mp memberNames
    have no := absent original (by simpa [code] using originalMem)
    cases found : sptLookup entry.1 target.code with
    | none => rfl
    | some result =>
      have present : sptDomain target.code entry.1 := (sptMem_iff_lookup _ _).2 ⟨result, found⟩
      rw [← domains] at present
      have absentSource : sptLookup entry.1 source.code = none := by simpa [same] using no
      simp [sptDomain, absentSource] at present
  have targetUnique : (cleaned.map Prod.fst).Nodup := by simpa [cleaned, cleanProg_names, code] using unique
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
    · simp [code, cleaned, codeRel, sptMap_sptUnion, cleanProg_fromAList]
    · funext n
      exact congrFun oracleRel (n + 1)

end Flapjack.Compiler.Backend.BviInline
