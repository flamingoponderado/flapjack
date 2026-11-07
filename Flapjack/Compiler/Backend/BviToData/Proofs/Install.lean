import Flapjack.Compiler.Backend.BviToData.Proofs.State
import Flapjack.Compiler.Backend.BviToData.Proofs.Conversions
import Flapjack.Compiler.Backend.BviToData.Proofs.OpFrame
import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.Semantics.DataSem.Apply
import Flapjack.Misc.Sptree.Map
import Flapjack.Misc.Sptree.Wf

/-! Installation cases for the BVI-to-data simulation. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- The data code entry corresponding to one BVI function. This is
Flapjack infrastructure for the installation proof. -/
noncomputable def compileCodeEntry (entry : Nat × Bvi.Exp) : Nat × DataLang.Prog :=
  (entry.1, compileExp entry.1 entry.2)

/-- Related code trees have corresponding lookups, including missing keys. -/
theorem codeRel_lookup (source : Spt (Nat × Bvi.Exp)) (target : Spt (Nat × DataLang.Prog))
    (related : codeRel source target) (key : Nat) :
    sptLookup key target = (sptLookup key source).map compileCodeEntry := by
  cases found : sptLookup key source with
  | none =>
    have domain := congrFun related.2.2.1 key
    simp [sptDomain, found] at domain
    cases targetFound : sptLookup key target <;> simp_all
  | some entry =>
    obtain ⟨argc, body⟩ := entry
    simpa [found, compileCodeEntry] using related.2.2.2 key body argc found

/-- Matching lookups and well-formed trees establish the code relation. -/
theorem codeRel_of_lookup (source : Spt (Nat × Bvi.Exp)) (target : Spt (Nat × DataLang.Prog))
    (sourceWf : sptWf source = true) (targetWf : sptWf target = true)
    (lookup : ∀ key, sptLookup key target = (sptLookup key source).map compileCodeEntry) :
    codeRel source target := by
  refine ⟨sourceWf, targetWf, ?_, ?_⟩
  · funext key
    simp [sptDomain, lookup]
  · intro key body argc found
    simp [lookup, found, compileCodeEntry]

/-- Compiling all entries of a well-formed BVI code tree produces related
code. -/
theorem codeRel_map (source : Spt (Nat × Bvi.Exp)) (wellFormed : sptWf source = true) :
    codeRel source (sptMap compileCodeEntry source) := by
  apply codeRel_of_lookup source (sptMap compileCodeEntry source) wellFormed
  · simpa [sptWfMap] using wellFormed
  · intro key
    exact sptLookup_sptMap compileCodeEntry source key

/-- Union preserves related code trees, including colliding labels: both
sides give priority to their first tree. -/
theorem codeRel_union (sourceA sourceB : Spt (Nat × Bvi.Exp)) (targetA targetB : Spt (Nat × DataLang.Prog))
    (first : codeRel sourceA targetA) (second : codeRel sourceB targetB) :
    codeRel (sptUnion sourceA sourceB) (sptUnion targetA targetB) := by
  apply codeRel_of_lookup _ _ (sptWfUnion _ _ ⟨first.1, second.1⟩)
    (sptWfUnion _ _ ⟨first.2.1, second.2.1⟩)
  intro key
  rw [sptLookup_sptUnion, sptLookup_sptUnion, codeRel_lookup sourceA targetA first key,
    codeRel_lookup sourceB targetB second key]
  cases sptLookup key sourceA <;> rfl

/-- Building the newly installed code from a source program and its compiled
counterpart produces related trees. -/
theorem codeRel_compileProg (program : List (Nat × Nat × Bvi.Exp)) :
    codeRel (sptFromAList program) (sptFromAList (compileProg program)) := by
  have mapped := codeRel_map (sptFromAList program) (sptWfFromAList program)
  have same : sptMap compileCodeEntry (sptFromAList program) = sptFromAList (compileProg program) := by
    rw [sptMap_sptFromAList]
    congr 1
  rw [← same]
  exact mapped

/-- The program produced by the executed bounded traversal forms a related
code tree, including for duplicate labels. -/
theorem codeRel_compileProgBounded (fuel : Nat) (program : List (Nat × Nat × Bvi.Exp))
    (compiled : List (Nat × Nat × DataLang.Prog))
    (run : (program.mapM fun (name, argc, body) => do
      pure (name, argc, ← compileExpBounded fuel argc body)) = some compiled) :
    codeRel (sptFromAList program) (sptFromAList compiled) := by
  have agreement := compileProgBounded_agrees fuel program
  rw [run] at agreement
  cases agreement
  exact codeRel_compileProg program

/-- Installing corresponding program lists and advancing both compiler
oracles preserves the BVI-to-data state relation. -/
theorem stateRel_install {C F : Type} (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (program : List (Nat × Nat × Bvi.Exp)) :
    stateRel
      { source with
        code := sptUnion source.code (sptFromAList program)
        compileOracle := fun n => source.compileOracle (n + 1) }
      { target with
        code := sptUnion target.code (sptFromAList (compileProg program))
        compileOracle := fun n => target.compileOracle (n + 1) } := by
  rcases related with ⟨clock, code, oracle, compiler, refs, ffi, global⟩
  refine ⟨clock, codeRel_union _ _ _ _ code (codeRel_compileProg program), ?_, compiler, refs, ffi, global⟩
  funext n
  exact congrFun oracle (n + 1)

/-- Installation can fail only with a type error in the current BVI
evaluator. -/
theorem install_error_is_typeError {C F : Type} (args : List BvlSem.Value)
    (state : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.doApp .install args state = .err error) : error = .abort .typeError := by
  simp only [BviSem.doApp, BviSem.doInstall] at run
  repeat' (split at run <;> try simp_all)

/-- A successful BVI installation can be performed by the data dispatcher,
returning the same code label and preserving the state relation. This is
untagged while the evaluator correspondence is under review. -/
theorem doApp_install {C F : Type} (args : List DataSem.Value)
    (source : BviSem.BviState C F) (target : DataSem.State C F)
    (related : stateRel source target) (result : BvlSem.Value) (next : BviSem.BviState C F)
    (run : BviSem.doApp .install (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value, DataSem.doApp .install args target = .val (value, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      targetNext.locals = target.locals ∧ targetNext.stack = target.stack ∧
      targetNext.handler = target.handler ∧ targetNext.clock = target.clock := by
  cases args with
  | nil => simp [BviSem.doApp, BviSem.doInstall] at run
  | cons a rest =>
    cases rest with
    | nil => simp [BviSem.doApp, BviSem.doInstall] at run
    | cons b rest =>
      cases rest with
      | nil => simp [BviSem.doApp, BviSem.doInstall] at run
      | cons c rest =>
        cases rest with
        | nil => simp [BviSem.doApp, BviSem.doInstall] at run
        | cons d rest =>
          cases rest with
          | cons e rest => simp [BviSem.doApp, BviSem.doInstall] at run
          | nil =>
            cases c <;> cases d <;> simp [dataToBviValue, BviSem.doApp, BviSem.doInstall,
              valueToBytes_projection, valueToWords_projection] at run
            case number.number len1 len2 =>
              cases bytesRun : DataSem.valueToBytes a with
              | none => simp [bytesRun] at run
              | some bytes =>
                cases dataRun : DataSem.valueToWords b with
                | none => simp [bytesRun, dataRun] at run
                | some data =>
                  simp [bytesRun, dataRun] at run
                  split at run
                  · simp at run
                  · rename_i lengths
                    cases oracleRun : source.compileOracle 0 with
                    | mk cfg programs =>
                      have targetOracle : target.compileOracle 0 = (cfg, compileProg programs) := by
                        rw [related.2.2.1]
                        simp [oracleRun]
                      have compileEq : target.compile cfg (compileProg programs) = source.compile cfg programs := by
                        rw [related.2.2.2.1]
                      simp [oracleRun] at run
                      split at run
                      · rename_i valid
                        cases programs with
                        | nil => simp at run
                        | cons first programs =>
                          obtain ⟨label, argc, body⟩ := first
                          cases compiled : source.compile cfg ((label, argc, body) :: programs) with
                          | none => simp [compiled] at run
                          | some output =>
                            obtain ⟨outBytes, outData, outConfig⟩ := output
                            simp [compiled] at run
                            split at run
                            · rename_i agrees
                              simp at run
                              obtain ⟨rfl, rfl⟩ := run
                              obtain ⟨rfl, rfl, oracleCfg⟩ := agrees
                              have lenEq : len1 = (bytes.length : Int) ∧ len2 = (data.length : Int) := by
                                simpa using lengths
                              have oracleEq : (target.compileOracle 1).1 = (source.compileOracle 1).1 := by
                                rw [related.2.2.1]
                              have targetCompiled : target.compile cfg (compileProg ((label, argc, body) :: programs)) =
                                  some (bytes, data, outConfig) := compileEq.trans compiled
                              simp only [compileProg, List.map_cons, compilePart] at targetCompiled
                              rcases lenEq with ⟨rfl, rfl⟩
                              refine ⟨{ target with
                                stackMax := none
                                stackFrameSizes := .ln
                                safeForSpace := false
                                code := sptUnion target.code (sptFromAList (compileProg ((label, argc, body) :: programs)))
                                compileOracle := fun n => target.compileOracle (n + 1) },
                                .codePtr label, ?_, by simp [dataToBviValue], ?_, rfl, rfl, rfl, rfl⟩
                              · simp [DataSem.doApp, DataSem.doInstall, bytesRun, dataRun, targetOracle,
                                  targetCompiled, oracleEq, oracleCfg, compileProg, compilePart]
                              · simpa [stateRel] using stateRel_install source target related ((label, argc, body) :: programs)
                            · simp at run
                      · simp at run

/-- A successful compiled installation establishes the continuing expression
invariant. The installation-specific frame permits its stack-frame metadata
reset while preserving the stack and handler used by `correctOutcome`. -/
theorem evaluate_iAssign_install_outcome {C F : Type}
    (target : DataSem.State C F) (source next : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (result : BvlSem.Value)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (fresh : ∀ key, dest ≤ key → sptLookup key target.locals = none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp .install (args.map dataToBviValue) source = .val (result, next)) :
    ∃ targetNext value,
      DataSem.evaluate (iAssign dest .install operands live corr) target = (none, targetNext) ∧
      result = dataToBviValue value ∧ stateRel next targetNext ∧
      sptLookup dest targetNext.locals = some value ∧
      correctOutcome (.val [result]) target targetNext dest (dest + 1) corr live [dest] env false none none := by
  classical
  let roots := operands ++ live ++ corr
  let cut := sptMkWf (sptInter target.locals (namesOfList roots))
  let prepared := { target with locals := cut }
  have cutRel : stateRel source prepared := by simpa [prepared, stateRel] using related
  have rootsPresent := roots_present target operands live corr env args vars livePresent read
  have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
    cutEnv_namesOfList roots target.locals rootsPresent
  obtain ⟨applied, value, app, projected, finalRel, localsFrame, stackFrame, handlerFrame, clockFrame⟩ :=
    doApp_install args source prepared cutRel result next run
  let targetNext := DataSem.setVar dest value (DataSem.installSfs .install applied)
  have execution : DataSem.evaluate (iAssign dest .install operands live corr) target = (none, targetNext) := by
    have cutEnv' : DataSem.cutEnv (namesOfList (operands ++ (live ++ corr))) target.locals = some cut := by
      simpa [roots, List.append_assoc] using cutEnv
    have app' := app
    simp only [prepared] at app'
    simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.evaluate, read,
      DataSem.cutStateOpt, DataSem.cutState, cutEnv', app', targetNext]
  have finalRel' : stateRel next targetNext := by
    simpa [targetNext, stateRel, DataSem.setVar, DataSem.installSfs] using finalRel
  have locals : targetNext.locals = sptInsert dest value cut := by
    simp [targetNext, DataSem.setVar, DataSem.installSfs, localsFrame, prepared]
  have stack : targetNext.stack = target.stack := by
    simpa [targetNext, DataSem.setVar, DataSem.installSfs, prepared] using stackFrame
  have handler : targetNext.handler = target.handler := by
    simpa [targetNext, DataSem.setVar, DataSem.installSfs, prepared] using handlerFrame
  have destRead : sptLookup dest targetNext.locals = some value := by simp [locals, sptLookup_sptInsert_same]
  have lookupOther : ∀ key, key ≠ dest → sptLookup key targetNext.locals =
      if key ∈ operands ++ live ++ corr then sptLookup key target.locals else none := by
    intro key different
    rw [locals, sptLookup_sptInsert_ne dest key value cut different]
    exact lookup_cut_namesOfList roots target.locals key
  have keeps : ∀ key ∈ operands ++ live ++ corr, key ≠ dest →
      sptLookup key targetNext.locals = sptLookup key target.locals := by
    intro key member different
    rw [lookupOther key different, ite_eq_left member]
  have varsNew : DataProps.varCorr env corr (sptMap dataToBviValue targetNext.locals) := by
    apply varCorr_of_lookup_eq dataToBviValue target.locals targetNext.locals corr env vars
    intro key member
    have root : key ∈ operands ++ live ++ corr := by simp [member]
    have different : key ≠ dest := by
      intro equal
      subst key
      exact rootsPresent dest root (fresh dest (Nat.le_refl dest))
    exact keeps key root different
  refine ⟨targetNext, value, execution, projected, finalRel', destRead, ?_⟩
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, varsNew, ?_, ?_, stack.symm, handler.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ dest := by omega
    rw [lookupOther key different]
    simp [fresh key (by omega)]
  · intro key dataValue lookup
    by_cases equal : key = dest
    · omega
    · have oldLookup : sptLookup key target.locals = some dataValue := by
        rw [lookupOther key equal] at lookup
        split at lookup <;> simp_all
      by_contra bound
      have absent := fresh key (by omega)
      rw [oldLookup] at absent
      contradiction
  · intro key dataValue lookup needed
    have different : key ≠ dest := by
      intro equal
      subst key
      have absent := fresh dest (Nat.le_refl dest)
      rw [lookup] at absent
      contradiction
    have root : key ∈ operands ++ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    rw [keeps key root different]
    exact lookup
  · intro available
    by_cases h : target.handler < target.stack.length
    · simp only [DataSem.jumpExc, stack, handler, ite_eq_left h] at available ⊢
      cases frame : target.stack.drop (target.stack.length - (target.handler + 1)) with
      | nil => simp [frame] at available
      | cons head rest => cases head <;> simp_all
    · simp [DataSem.jumpExc, h] at available
  · constructor
    · simp [DataSem.getVar, sptLookup_sptMap, destRead, projected]
    · constructor

end Flapjack.Compiler.Backend.BviToData
