import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationDecode
import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Compiler.Backend.ClosKnown.Proofs.OracleMonotonic
import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateOracle
import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateOracleDisjoint
import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownSubspt
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Simulation

/-! Installation prerequisites for the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Simulation.Install
open ClosSem ClosProps Relations Relations.StateRelation BackendProps
open Flapjack.SemanticPrimitivesHOL

/-- A non-type-error installation and related arguments have identical
decoded byte and word payloads on the target side. This is Flapjack proof
infrastructure for the installation case. -/
theorem relatedInstallPayload {C F : Type} (c : Config) (g : Spt ValApprox)
    (sourceValues targetValues : List ClosSem.Value) (s s1 : State C F)
    (result : Result (List ClosLang.Exp) ClosSem.Value)
    (related : List.Forall₂ (ValueRel c g) sourceValues targetValues)
    (run : doInstall sourceValues s = (result, s1)) (noType : result ≠ .err (.abort .typeError)) :
    ∃ sourceBytes sourceWords targetBytes targetWords bytes words,
      sourceValues = [sourceBytes, sourceWords] ∧ targetValues = [targetBytes, targetWords] ∧
      valueToBytes sourceBytes = some bytes ∧ valueToBytes targetBytes = some bytes ∧
      valueToWords sourceWords = some words ∧ valueToWords targetWords = some words := by
  obtain ⟨sourceBytes, sourceWords, bytes, words, _, _, _, _, shape, bytesRun, wordsRun, _⟩ :=
    doInstall_nonType_parts sourceValues s s1 result run noType
  subst sourceValues
  cases related with
  | cons first tail =>
    cases tail with
    | cons second tail =>
      cases tail
      rename_i targetBytes targetWords
      have bytesSame := valueRelImpValueToBytes c g sourceBytes targetBytes first
      have wordsSame := valueRelImpValueToWords c g sourceWords targetWords second
      exact ⟨sourceBytes, sourceWords, targetBytes, targetWords, bytes, words,
        rfl, rfl, bytesRun, bytesSame.trans bytesRun, wordsRun, wordsSame.trans wordsRun⟩

/-- Each target compiler-oracle entry is obtained by running the known pass
on the source entry, preserving the empty auxiliary-code component. This is
Flapjack proof infrastructure for installation. -/
theorem relatedOracleEntry {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (n : Nat)
    (related : StateRel c g s t) :
    ∃ tree config program eas next,
      s.compileOracle n = ((tree, config), program, []) ∧
      knownListTotal (resetInlineFactor c) program [] tree = (eas, next) ∧
      t.compileOracle n = (config, eas.map Prod.fst, []) := by
  obtain ⟨auxEmpty, _, _, _, _, _, _, _, _, _, oracle⟩ := related
  cases entry : s.compileOracle n with
  | mk config program =>
    rcases config with ⟨tree, config⟩
    rcases program with ⟨program, auxiliary⟩
    have aux : auxiliary = [] := by simpa [entry] using auxEmpty n
    subst auxiliary
    cases known : knownListTotal (resetInlineFactor c) program [] tree with
    | mk eas next =>
      refine ⟨tree, config, program, eas, next, rfl, known, ?_⟩
      rw [oracle]
      simp [stateCo, entry, compileInc, known]

/-- A successful source callback yields the identical code and data from the
target callback and threads exactly the known pass's next approximation tree.
This is Flapjack proof infrastructure for installation. -/
theorem relatedCompilerCallback {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (related : StateRel c g s t)
    (tree : Spt ValApprox) (config : C) (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))
    (bytes : List (BitVec 8)) (words : List (BitVec 64)) (nextTree : Spt ValApprox) (nextConfig : C)
    (run : s.compile (tree, config) program = some (bytes, words, (nextTree, nextConfig))) :
    t.compile config (compileInc c tree program).2 = some (bytes, words, nextConfig) ∧
      (compileInc c tree program).1 = nextTree := by
  have compiler := related.2.2.2.2.2.2.2.2.2.1
  rw [compiler] at run
  unfold stateCc at run
  cases compiled : compileInc c tree program with
  | mk computedTree computedProgram =>
    simp only [compiled] at run ⊢
    cases callback : t.compile config computedProgram with
    | none => simp [callback] at run
    | some output =>
      rcases output with ⟨code, data, configNext⟩
      simp [callback] at run
      rcases run with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩

/-- Shifting both compiler oracles and setting equal clocks preserves the
state relation after enlarging its approximation tree. This is Flapjack proof
infrastructure for the installation transition. -/
theorem relatedShiftedStates {C F : Type} (c : Config) (g next : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (shift clock : Nat)
    (related : StateRel c g s t) (sub : sptSubspt g next) :
    StateRel c next { s with clock := clock, compileOracle := Flapjack.holShiftSeq shift s.compileOracle }
      { t with clock := clock, compileOracle := Flapjack.holShiftSeq shift t.compileOracle } := by
  have widened := stateRelSubspt c g s t next ⟨related, sub⟩
  obtain ⟨aux, free, codeS, codeT, _, ffi, maxApp, globals, refs, compiler, oracle⟩ := widened
  refine ⟨?_, ?_, codeS, codeT, rfl, ffi, maxApp, globals, refs, compiler, ?_⟩
  · intro n; exact aux (n + shift)
  · intro n; exact free (n + shift)
  · rw [oracle]
    funext n
    rfl

/-- A non-type-error installation produces related shifted states and either
the same timeout or the source and optimized oracle programs. This is Flapjack
proof infrastructure for the optimizer installation case. -/
theorem relatedInstallNonType {C F : Type} (c : Config)
    (s : State (Spt ValApprox × C) F) (t : State C F)
    (sourceValues targetValues : List ClosSem.Value)
    (result : Result (List ClosLang.Exp) ClosSem.Value)
    (s1 : State (Spt ValApprox × C) F)
    (state : StateRel c (nextG s) s t)
    (mono : OracleMonotonic.oracleGapproxSubspt s.compileOracle)
    (values : List.Forall₂ (ValueRel c (nextG s)) sourceValues targetValues)
    (run : doInstall sourceValues s = (result, s1)) (noType : result ≠ .err (.abort .typeError)) :
    ∃ targetResult t1 program eas tree next,
      doInstall targetValues t = (targetResult, t1) ∧
      knownListTotal (resetInlineFactor c) program [] tree = (eas, next) ∧
      program = (s.compileOracle 0).2.1 ∧ tree = nextG s ∧
      (result = .err (.abort .timeoutError) ∧ targetResult = .err (.abort .timeoutError) ∨
        result = .val program ∧ targetResult = .val (eas.map Prod.fst)) ∧
      nextG s1 = next ∧ StateRel c (nextG s1) s1 t1 := by
  obtain ⟨sourceBytes, sourceWords, targetBytes, targetWords, bytes, words,
    sourceShape, targetShape, sourceBytesRun, targetBytesRun, sourceWordsRun, targetWordsRun⟩ :=
    relatedInstallPayload c (nextG s) sourceValues targetValues s s1 result values run noType
  obtain ⟨sb, sw, bytes', words', configPair, program', auxiliary, nextPair,
    shape, bytesEq, wordsEq, sourceOracle, callback, _, _, nextOracle, programNonempty, finalState, finalResult⟩ :=
    doInstall_nonType_parts sourceValues s s1 result run noType
  rw [sourceShape] at shape
  simp only [List.cons.injEq, and_true] at shape
  obtain ⟨rfl, rfl⟩ := shape
  rw [sourceBytesRun] at bytesEq
  rw [sourceWordsRun] at wordsEq
  cases bytesEq
  cases wordsEq
  obtain ⟨tree, config, program, eas, next, entry, known, targetOracle⟩ := relatedOracleEntry c (nextG s) s t 0 state
  rw [entry] at sourceOracle
  simp only [Prod.mk.injEq] at sourceOracle
  obtain ⟨rfl, rfl, rfl⟩ := sourceOracle
  have compiled := relatedCompilerCallback c (nextG s) s t state tree config (program, []) bytes words nextPair.1 nextPair.2 callback
  have callbackTarget : t.compile config (eas.map Prod.fst, []) = some (bytes, words, nextPair.2) := by
    simpa [compileInc, known] using compiled.1
  have nextTree : next = nextPair.1 := by simpa [compileInc, known] using compiled.2
  have targetNext : (Flapjack.holShiftSeq 1 t.compileOracle 0).1 = nextPair.2 := by
    have p := congrArg Prod.snd nextOracle
    simpa [Flapjack.holShiftSeq, state.2.2.2.2.2.2.2.2.2.2, stateCo] using p
  have targetNonempty : eas.map Prod.fst ≠ [] := by
    intro empty
    have len := knownListTotal_length (resetInlineFactor c) program [] tree
    rw [known] at len
    have : eas = [] := List.map_eq_nil_iff.mp empty
    subst eas
    simp at len
    exact programNonempty (List.eq_nil_of_length_eq_zero (by omega))
  let t1 := { t with compileOracle := Flapjack.holShiftSeq 1 t.compileOracle, clock := t.clock - 1 }
  have targetRun : doInstall targetValues t =
      (if t.clock = 0 then .err (.abort .timeoutError) else .val (eas.map Prod.fst), t1) := by
    rw [targetShape]
    by_cases zero : t.clock = 0 <;>
      simp [doInstall, targetBytesRun, targetWordsRun, targetOracle, callbackTarget, targetNext,
        targetNonempty, t1, HolFiniteMapExact.updateListEq, zero]
  have auxEmpty : s.code.updateListEq ([] : List (Nat × Nat × ClosLang.Exp)) = s.code := by
    simp [HolFiniteMapExact.updateListEq]
  rw [auxEmpty] at finalState
  have sub : sptSubspt (nextG s) (nextG s1) := by
    rw [finalState]
    simpa [nextG, Flapjack.holShiftSeq] using mono 0
  have clockEq : s.clock = t.clock := state.2.2.2.2.1
  have relatedFinal : StateRel c (nextG s1) s1 t1 := by
    rw [finalState] at sub ⊢
    simpa [t1, ← clockEq] using relatedShiftedStates c (nextG s) _ s t 1 (s.clock - 1) state sub
  have nextEq : nextG s1 = next := by
    rw [finalState]
    have p := congrArg Prod.fst nextOracle
    simpa [nextG, Flapjack.holShiftSeq, ← nextTree] using p
  have programEq : program = (s.compileOracle 0).2.1 := by simp [entry]
  have treeEq : tree = nextG s := by simp [nextG, entry]
  refine ⟨_, t1, program, eas, tree, next, targetRun, known, programEq, treeEq, ?_, nextEq, relatedFinal⟩
  rw [clockEq] at finalResult
  by_cases zero : t.clock = 0 <;> simp [zero] at finalResult ⊢ <;> simp [finalResult]

/-- Successful installation supplies the syntax, safety, free-variable and
oracle conditions needed to evaluate the installed program. This is Flapjack
proof infrastructure for the installation induction hypothesis. -/
theorem installedProgramPreconditions {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (values : List ClosSem.Value)
    (program : List ClosLang.Exp) (s1 : State (Spt ValApprox × C) F)
    (state : StateRel c g s t) (safe : StateGlobalSafety.ssgcFree s)
    (oracleSyntax : OracleMonotonic.coEveryFnVarsNone s.compileOracle)
    (oracleSafe : StateRelation.Oracle.oracleStateSgcFree s.compileOracle)
    (disjoint : StateOracleDisjoint.stateOracleMglobalsDisjoint s)
    (mono : OracleMonotonic.oracleGapproxSubspt s.compileOracle)
    (run : doInstall values s = (.val program, s1)) :
    StateGlobalSafety.ssgcFree s1 ∧ (∀ e ∈ program, esgcFree e) ∧
      program ≠ [] ∧ everyFnVarsNone program ∧ fvMax 0 program ∧
      UniqueGlobalsPort.mglobalsDisjoint s1.globals program ∧
      StateOracleDisjoint.stateOracleMglobalsDisjoint s1 ∧
      OracleMonotonic.coEveryFnVarsNone s1.compileOracle ∧
      StateRelation.Oracle.oracleStateSgcFree s1.compileOracle ∧
      OracleMonotonic.oracleGapproxSubspt s1.compileOracle := by
  have installed := doInstallSsgc values s program s1 ⟨run, safe⟩
  have programEntry : (s.compileOracle 0).2.1 = program := by
    have entry := installed.2.2.2.2.1
    simpa [firstNExps] using entry
  have fnSyntax : everyFnVarsNone program := by
    rw [← programEntry]
    exact (oracleSyntax 0 _ _ rfl).1
  have free : fvMax 0 program := by
    rw [← programEntry]
    exact state.2.1 0
  have sameGlobals : s1.globals = s.globals := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, _⟩ :=
      doInstall_nonType_parts values s s1 (.val program) run (by simp)
    rw [final]
  have programDisjoint : UniqueGlobalsPort.mglobalsDisjoint s1.globals program := by
    rw [sameGlobals, ← programEntry]
    exact disjoint 0
  have oracleDisjoint : StateOracleDisjoint.stateOracleMglobalsDisjoint s1 := by
    intro n
    rw [sameGlobals, installed.2.2.2.1]
    exact disjoint (n + 1)
  refine ⟨installed.1, installed.2.1, installed.2.2.1, fnSyntax, free,
    programDisjoint, oracleDisjoint, ?_, ?_, ?_⟩
  · rw [installed.2.2.2.1]
    exact OracleMonotonic.coEveryFnVarsNoneShift s.compileOracle oracleSyntax 1
  · rw [installed.2.2.2.1]
    exact StateRelation.Oracle.oracleStateSgcFreeShift s.compileOracle oracleSafe 1
  · rw [installed.2.2.2.1]
    exact OracleMonotonic.oracleGapproxSubsptShift s.compileOracle mono 1

/-- If all oracle writes are unique, the first oracle program remains unique
against the shifted oracle after installation. This is Flapjack proof
infrastructure for the installed-program induction hypothesis. -/
theorem firstOracleProgramUnique {A B : Type}
    (co : Nat → A × List ClosLang.Exp × B)
    (unique : UniqueGlobalsPort.uniqueSetGlobals [] co) :
    UniqueGlobalsPort.uniqueSetGlobals (co 0).2.1 (Flapjack.holShiftSeq 1 co) := by
  intro n key
  have bound := unique (n + 1) key
  rw [firstNExpsShiftSeq co n 1] at bound
  simpa [firstNExps, elistGlobals_append] using bound

/-- A successfully installed program has unique writes relative to the
remaining oracle whenever the original oracle had unique writes. This is
Flapjack proof infrastructure for the installation induction hypothesis. -/
theorem installedProgramUnique {C F : Type} (s : State C F) (values : List ClosSem.Value)
    (program : List ClosLang.Exp) (s1 : State C F)
    (safe : StateGlobalSafety.ssgcFree s)
    (unique : UniqueGlobalsPort.uniqueSetGlobals [] s.compileOracle)
    (run : doInstall values s = (.val program, s1)) :
    UniqueGlobalsPort.uniqueSetGlobals program s1.compileOracle := by
  have installed := doInstallSsgc values s program s1 ⟨run, safe⟩
  have programEntry : (s.compileOracle 0).2.1 = program := by
    have entry := installed.2.2.2.2.1
    simpa [firstNExps] using entry
  rw [← programEntry, installed.2.2.2.1]
  exact firstOracleProgramUnique s.compileOracle unique

/-- The installed state's global values satisfy the approximation produced by
optimizing the installed program. This is Flapjack proof infrastructure for
the installation induction hypothesis. -/
theorem installedProgramGlobalsApprox {C F : Type} (c : Config) (tree next : Spt ValApprox)
    (s : State C F) (values : List ClosSem.Value) (program : List ClosLang.Exp)
    (s1 : State C F) (eas : List (ClosLang.Exp × ValApprox))
    (safe : StateGlobalSafety.ssgcFree s)
    (globals : stateGlobalsApprox s tree)
    (disjoint : StateOracleDisjoint.stateOracleMglobalsDisjoint s)
    (known : knownListTotal c program [] tree = (eas, next))
    (run : doInstall values s = (.val program, s1)) : stateGlobalsApprox s1 next := by
  have installed := doInstallSsgc values s program s1 ⟨run, safe⟩
  have programEntry : (s.compileOracle 0).2.1 = program := by
    have entry := installed.2.2.2.2.1
    simpa [firstNExps] using entry
  have programDisjoint : UniqueGlobalsPort.mglobalsDisjoint s.globals program := by
    rw [← programEntry]
    exact disjoint 0
  have after := ApproxEvaluate.stateGlobalsApproxKnownDisjoint c program [] tree eas next s
    ⟨known, programDisjoint, globals⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, _⟩ :=
    doInstall_nonType_parts values s s1 (.val program) run (by simp)
  simpa [final, stateGlobalsApprox] using after

/-- Processing the installed program preserves approximation disjointness
against the shifted oracle. This is Flapjack proof infrastructure for the
installation induction hypothesis. -/
theorem installedOracleDisjoint {C F : Type} (c : Config) (tree next : Spt ValApprox)
    (s : State C F) (values : List ClosSem.Value) (program : List ClosLang.Exp)
    (s1 : State C F) (eas : List (ClosLang.Exp × ValApprox))
    (safe : StateGlobalSafety.ssgcFree s)
    (unique : UniqueGlobalsPort.uniqueSetGlobals [] s.compileOracle)
    (oracle : OracleGlobals.oracleGapproxDisjoint tree s.compileOracle)
    (known : knownListTotal c program [] tree = (eas, next))
    (run : doInstall values s = (.val program, s1)) :
    OracleGlobals.oracleGapproxDisjoint next s1.compileOracle := by
  have installed := doInstallSsgc values s program s1 ⟨run, safe⟩
  have programEntry : (s.compileOracle 0).2.1 = program := by
    have entry := installed.2.2.2.2.1
    simpa [firstNExps] using entry
  rw [installed.2.2.2.1]
  apply OracleGlobals.oracleGapproxDisjointInstall c s.compileOracle tree eas next
  exact ⟨by simpa [programEntry] using known, unique, oracle⟩

/-- Successful installation preserves the stateful compiler-oracle
invariant. This is Flapjack proof infrastructure for the installation
induction hypothesis. -/
theorem installedStateOracle {C F : Type} (c : Config)
    (s : State (Spt ValApprox × C) F) (values : List ClosSem.Value)
    (program : List ClosLang.Exp) (s1 : State (Spt ValApprox × C) F)
    (safe : StateGlobalSafety.ssgcFree s)
    (oracle : isStateOracle (compileInc c) s.compileOracle)
    (run : doInstall values s = (.val program, s1)) :
    isStateOracle (compileInc c) s1.compileOracle := by
  have installed := doInstallSsgc values s program s1 ⟨run, safe⟩
  rw [installed.2.2.2.1]
  intro n
  simpa [Flapjack.holShiftSeq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using oracle (n + 1)

/-- Optimizing the first oracle program retains its incoming approximation
tree when oracle writes are unique and disjoint from that tree. This is
Flapjack proof infrastructure for the installation induction hypothesis. -/
theorem firstOracleKnownSubspt {A B : Type} (c : Config)
    (co : Nat → A × List ClosLang.Exp × B) (tree next : Spt ValApprox)
    (eas : List (ClosLang.Exp × ValApprox))
    (known : knownListTotal c (co 0).2.1 [] tree = (eas, next))
    (safe : ∀ e ∈ (co 0).2.1, esgcFree e) (treeSafe : globalsApproxSgcFree tree)
    (unique : UniqueGlobalsPort.uniqueSetGlobals [] co)
    (oracle : OracleGlobals.oracleGapproxDisjoint tree co) : sptSubspt tree next := by
  have writes : ∀ i, elistGlobals (co 0).2.1 i ≤ 1 := by
    intro i
    have bound := unique 1 i
    simpa [UniqueGlobalsPort.uniqueSetGlobals, firstNExps] using bound
  have distinct : ∀ i, KnownSubspt.domainBag tree i + elistGlobals (co 0).2.1 i ≤ 1 := by
    intro i
    by_cases member : sptMem i tree
    · have zero : elistGlobals (co 0).2.1 i = 0 := by
        by_contra nonzero
        exact (Set.disjoint_left.mp (oracle 0)) member nonzero
      simp [KnownSubspt.domainBag, member, zero]
    · simpa [KnownSubspt.domainBag, member] using writes i
  exact (KnownSubspt.knownSubspt c (co 0).2.1 [] tree eas next
    ⟨known, safe, by simp, treeSafe, distinct⟩).2

/-- A successful installation can invoke the original installed-program
induction hypothesis and produces a related target evaluation. This is
Flapjack proof infrastructure for the enclosing operation case. -/
theorem installedProgramSimulation {C F : Type} (c : Config)
    (s : State (Spt ValApprox × C) F) (t : State C F)
    (sourceValues targetValues : List ClosSem.Value) (program : List ClosLang.Exp)
    (s1 final : State (Spt ValApprox × C) F)
    (res : Result (List ClosSem.Value) ClosSem.Value)
    (state : StateRel c (nextG s) s t)
    (safe : StateGlobalSafety.ssgcFree s)
    (oracleSyntax : OracleMonotonic.coEveryFnVarsNone s.compileOracle)
    (oracleSafe : StateRelation.Oracle.oracleStateSgcFree s.compileOracle)
    (disjoint : StateOracleDisjoint.stateOracleMglobalsDisjoint s)
    (mono : OracleMonotonic.oracleGapproxSubspt s.compileOracle)
    (unique : UniqueGlobalsPort.uniqueSetGlobals [] s.compileOracle)
    (globals : stateGlobalsApprox s (nextG s))
    (oracleDisjoint : OracleGlobals.oracleGapproxDisjoint (nextG s) s.compileOracle)
    (oracleState : isStateOracle (compileInc c) s.compileOracle)
    (values : List.Forall₂ (ValueRel c (nextG s)) sourceValues targetValues)
    (install : doInstall sourceValues s = (.val program, s1))
    (ih : KnownSimulationAt program [] s1)
    (run : evaluate program [] s1 = (res, final)) (noType : res ≠ .err (.abort .typeError)) :
    ∃ targetProgram t1 targetResult targetFinal,
      doInstall targetValues t = (.val targetProgram, t1) ∧
      evaluate targetProgram [] t1 = (targetResult, targetFinal) ∧
      Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (ValueRel c (nextG final)))
        (ValueRel c (nextG final)) res targetResult ∧
      StateRel c (nextG final) final targetFinal ∧ stateGlobalsApprox final (nextG final) ∧
      isStateOracle (compileInc c) final.compileOracle ∧
      OracleGlobals.oracleGapproxDisjoint (nextG final) final.compileOracle := by
  obtain ⟨targetInstall, t1, sourceProgram, eas, tree, next, targetRun, known,
    programEq, treeEq, outcome, nextEq, relatedState⟩ :=
    relatedInstallNonType c s t sourceValues targetValues (.val program) s1 state mono values install (by simp)
  rcases outcome with ⟨impossible, _⟩ | ⟨same, rfl⟩
  · cases impossible
  · cases same
    subst tree
    have pre := installedProgramPreconditions c (nextG s) s t sourceValues program s1
      state safe oracleSyntax oracleSafe disjoint mono install
    have uniqueNext := installedProgramUnique s sourceValues program s1 safe unique install
    have globalsNext := installedProgramGlobalsApprox (resetInlineFactor c) (nextG s) next s
      sourceValues program s1 eas safe globals disjoint known install
    have disjointNext := installedOracleDisjoint (resetInlineFactor c) (nextG s) next s
      sourceValues program s1 eas safe unique oracleDisjoint known install
    have oracleNext := installedStateOracle c s sourceValues program s1 safe oracleState install
    have treeSafe : globalsApproxSgcFree (nextG s) := by
      simpa [nextG, StateRelation.Oracle.oracleStateSgcFree] using oracleSafe 0
    have sub : sptSubspt (nextG s) next := by
      apply firstOracleKnownSubspt (resetInlineFactor c) s.compileOracle (nextG s) next eas
      · simpa [programEq] using known
      · simpa [programEq] using pre.2.1
      · exact treeSafe
      · exact unique
      · exact oracleDisjoint
    have refl : sptSubspt next (nextG s1) := by
      rw [nextEq]
      intro k member
      exact ⟨member, rfl⟩
    have stateReset : StateRel (resetInlineFactor c) (nextG s1) s1 t1 := by
      simpa [resetInlineFactor, stateRelUpdateInlineFactor] using relatedState
    have oracleReset : isStateOracle (compileInc (resetInlineFactor c)) s1.compileOracle := by
      simpa [resetInlineFactor, compileIncUpdateInlineFactor] using oracleNext
    have nextGlobals : stateGlobalsApprox s1 (nextG s1) := by simpa [nextEq] using globalsNext
    have nextDisjoint : OracleGlobals.oracleGapproxDisjoint (nextG s1) s1.compileOracle := by
      simpa [nextEq] using disjointNext
    have step := ih res final [] [] [] [] t1 (resetInlineFactor c) (nextG s) next [] eas
      ⟨run, known, stateReset, pre.2.2.2.1, pre.2.2.2.2.2.2.2.1, pre.2.2.2.2.2.1,
        nextDisjoint, pre.2.2.2.2.2.2.1, pre.2.1, pre.1, by simp, .nil,
        pre.2.2.2.2.2.2.2.2.1, treeSafe, by simp, nextGlobals, sub, refl,
        pre.2.2.2.2.2.2.2.2.2, by simpa using pre.2.2.2.2.1, .nil, uniqueNext,
        oracleReset, rfl, noType⟩
    obtain ⟨targetResult, targetFinal, evalTarget, resultRel, finalState, finalGlobals, finalOracle, finalDisjoint⟩ := step
    refine ⟨eas.map Prod.fst, t1, targetResult, targetFinal, targetRun, ?_, ?_, ?_, finalGlobals, ?_, finalDisjoint⟩
    · simpa using evalTarget
    · simpa [resetInlineFactor, valueRelUpdateInlineFactor] using resultRel
    · simpa [resetInlineFactor, stateRelUpdateInlineFactor] using finalState
    · simpa [resetInlineFactor, compileIncUpdateInlineFactor] using finalOracle

end Flapjack.Compiler.Backend.ClosKnown.Simulation.Install
