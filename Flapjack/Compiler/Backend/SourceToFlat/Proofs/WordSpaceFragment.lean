import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordFragment
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.FragmentSpace
import Flapjack.Compiler.Backend.BviToData.Proofs.Simulation
import Flapjack.Compiler.Backend.BviToData.Proofs.Program
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallFragment

/-! Connecting allocation-capable data fragments to configured word output. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

/-- The actual emitted word body has an ordinary simulation outcome or the
permitted allocation failure, for all closure-optimizer settings. The candidate
data-to-word relation and uncovered instructions remain open, so this is not
whole-program correctness. -/
theorem configuredSpaceFragmentFunction_simulation {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (codeLabel arity l1 l2 : Nat) (body : DataLang.Prog)
    (sourceState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 sourceState targetState none locs)
    (sourceCode : sourceState.code = sptFromAList (BviToData.compileProg bviCode))
    (sourceLookup : sptLookup codeLabel sourceState.code = some (arity, body))
    (fragment : VerifiedWithSpace body)
    (safe : (DataSem.evaluate body sourceState).1 ≠ some (.err (.abort .typeError))) :
    ∃ code wordBody,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      (fragmentOutcomesAt64 word l1 l2 body wordBody sourceState targetState locs ∨
        ∃ final, WordSemStateFiniteExact.evaluate wordBody targetState = (some .notEnoughSpace, final) ∧
          BackendProps.optionLe final.stackMax (DataSem.evaluate body sourceState).2.stackMax ∧
          final.ffi.ioEvents <+: (DataSem.evaluate body sourceState).2.ffi.ioEvents ∧
          (word.gcKind ≠ .none → (DataSem.evaluate body sourceState).2.safeForSpace = false)) := by
  obtain ⟨code, wordRun, codeRel⟩ := compileCakeToWord64ConfiguredFuel_codeRel_allSettings fuel source nextSource
    closure nextClosure bvlConfig nextBvlConfig word declarations bviCode names run
  let wordBody := (compileControl64 word codeLabel 2 body).1
  have outputLookup : sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) := by
    exact codeRel.2.2 codeLabel arity body (by simpa [sourceCode] using sourceLookup)
  have targetLookup : sptLookup codeLabel targetState.code = some (arity + 1, wordBody) :=
    related.2.2.2.2.1.2.2 codeLabel arity body sourceLookup
  refine ⟨code, wordBody, wordRun, outputLookup, targetLookup, ?_⟩
  have simulation := verifiedWithSpace64 word codeLabel l1 l2 body fragment 2 sourceState targetState locs related safe
  simpa [wordBody, outcomesWithSpace64, outOfSpace64, fragmentOutcomesAt64,
    outcomes64, continues64, returns64, timesOut64, raises64] using simulation

/-- An entry of the BVI code emitted by the configured frontend is present in
the data code map with its compiled body. Label uniqueness follows from the
actual frontend run, including all closure-optimizer settings. -/
theorem configuredBvi_data_lookup (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (declarations : List AstHOL.Dec)
    (bviCode : List (Nat × Nat × Bvi.Exp)) (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (codeLabel arity : Nat) (body : Bvi.Exp) (member : (codeLabel, arity, body) ∈ bviCode) :
    sptLookup codeLabel (sptFromAList (BviToData.compileProg bviCode)) =
      some (arity, BviToData.compileExp arity body) := by
  have distinct : ((BviToData.compileProg bviCode).map Prod.fst).Nodup := by
    rw [bviToData_labels]
    exact (configured_bvi_labels fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
      declarations bviCode names run).1
  have dataMember : (codeLabel, arity, BviToData.compileExp arity body) ∈ BviToData.compileProg bviCode := by
    apply List.mem_map.mpr
    exact ⟨(codeLabel, arity, body), member, rfl⟩
  rw [sptLookup_sptFromAList]
  apply sptAListLookup_eq_of_mem_unique _ _ _ dataMember
  intro other otherMember
  have eq : (codeLabel, other) = (codeLabel, arity, BviToData.compileExp arity body) :=
    List.inj_on_of_nodup_map distinct otherMember dataMember rfl
  exact congrArg Prod.snd eq

/-- The word body emitted for an actual frontend BVI function simulates its
compiled data body, including allocation failure. The verified-fragment,
candidate-state-relation and source-safety conditions remain explicit; this
is Flapjack pipeline infrastructure, not full compiler correctness. -/
theorem configuredBviSpaceFragment_simulation {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (codeLabel arity l1 l2 : Nat) (body : Bvi.Exp) (member : (codeLabel, arity, body) ∈ bviCode)
    (sourceState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 sourceState targetState none locs)
    (sourceCode : sourceState.code = sptFromAList (BviToData.compileProg bviCode))
    (fragment : VerifiedWithSpace (BviToData.compileExp arity body))
    (safe : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).1 ≠
      some (.err (.abort .typeError))) :
    ∃ code wordBody,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      (fragmentOutcomesAt64 word l1 l2 (BviToData.compileExp arity body) wordBody sourceState targetState locs ∨
        ∃ final, WordSemStateFiniteExact.evaluate wordBody targetState = (some .notEnoughSpace, final) ∧
          BackendProps.optionLe final.stackMax (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.stackMax ∧
          final.ffi.ioEvents <+: (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.ffi.ioEvents ∧
          (word.gcKind ≠ .none → (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.safeForSpace = false)) := by
  have lookup : sptLookup codeLabel sourceState.code = some (arity, BviToData.compileExp arity body) := by
    rw [sourceCode]
    exact configuredBvi_data_lookup fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
      declarations bviCode names run codeLabel arity body member
  exact configuredSpaceFragmentFunction_simulation fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
    word declarations bviCode names run codeLabel arity l1 l2 (BviToData.compileExp arity body)
    sourceState targetState locs related sourceCode lookup fragment safe

/-- Successful and exceptional BVI results paired with the corresponding
actual word outcome, or the permitted target allocation failure. This is
Lean-side composition infrastructure, not a HOL result relation. -/
def bviWordOutcomes64 {C F : Type} (conf : DataToWord.Config) (l1 l2 : Nat)
    (result : BviSem.BviResult) (body : DataLang.Prog) (wordBody : WordLangProgHOL (BitVec 64))
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat)) : Prop :=
  (∃ values words source' target', values.length = words.length ∧
    (result = .val (values.map BviToData.dataToBviValue) ∨
      result = .err (.raise (.ret (values.map BviToData.dataToBviValue)))) ∧
    DataSem.evaluate body source = (some (.val values), source') ∧
    WordSemStateFiniteExact.evaluate wordBody target = (some (.result (.loc l1 l2) words), target') ∧
    stateRel64 conf l1 l2 source' target' (some (values.zip words)) locs) ∨
  (∃ source' target', result = .err (.abort .timeoutError) ∧
    DataSem.evaluate body source = (some (.err (.abort .timeoutError)), source') ∧
    WordSemStateFiniteExact.evaluate wordBody target = (some .timeOut, target') ∧
    target'.ffi = source'.ffi ∧ BackendProps.optionLe target'.stackMax source'.stackMax) ∨
  (∃ value word source' target' a b r1 r2 remaining,
    result = .err (.raise (.exn (BviToData.dataToBviValue value))) ∧
    DataSem.evaluate body source = (some (.err (.raise value)), source') ∧
    WordSemStateFiniteExact.evaluate wordBody target = (some (.exception (.loc a b) word), target') ∧
    (∃ jumpState, WordSemStateFiniteExact.jumpExc target = some (jumpState, a, b)) ∧
    target'.ffi = source'.ffi ∧ BackendProps.optionLe target'.stackMax source'.stackMax ∧
    wordSemLastN (source'.stack.length + 1) locs = (r1, r2) :: remaining ∧
    ∀ dest, stateRel64 conf r1 r2 (DataSem.setVar dest value source')
      (WordSemStateFiniteExact.setVar (DataToWord.adjustVar dest) word target') none remaining) ∨
  (∃ final, WordSemStateFiniteExact.evaluate wordBody target = (some .notEnoughSpace, final) ∧
    BackendProps.optionLe final.stackMax (DataSem.evaluate body source).2.stackMax ∧
    final.ffi.ioEvents <+: (DataSem.evaluate body source).2.ffi.ioEvents ∧
    (conf.gcKind ≠ .none → (DataSem.evaluate body source).2.safeForSpace = false))

/-- Compose the BVI result projection with the word fragment outcomes. The
continuing-data branch is impossible because the BVI simulation produced a
finished data result. -/
theorem bviWordOutcomes64_of_data {C F : Type} (conf : DataToWord.Config) (l1 l2 : Nat)
    (result : BviSem.BviResult) (body : DataLang.Prog) (wordBody : WordLangProgHOL (BitVec 64))
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (dataResult : Flapjack.SemanticPrimitivesHOL.Result (List DataSem.Value) DataSem.Value)
    (dataFinal : DataSem.State C F)
    (dataRun : DataSem.evaluate body source = (some dataResult, dataFinal))
    (projection : ¬ BviToData.isReturn result → BviToData.dataToBviResult dataResult = result)
    (returns : BviToData.isReturn result → ∃ values, dataResult = .val values ∧
      result = .err (.raise (.ret (values.map BviToData.dataToBviValue))))
    (wordOutcome : fragmentOutcomesAt64 conf l1 l2 body wordBody source target locs ∨
      ∃ final, WordSemStateFiniteExact.evaluate wordBody target = (some .notEnoughSpace, final) ∧
        BackendProps.optionLe final.stackMax (DataSem.evaluate body source).2.stackMax ∧
        final.ffi.ioEvents <+: (DataSem.evaluate body source).2.ffi.ioEvents ∧
        (conf.gcKind ≠ .none → (DataSem.evaluate body source).2.safeForSpace = false)) :
    bviWordOutcomes64 conf l1 l2 result body wordBody source target locs := by
  rcases wordOutcome with ordinary | outOfSpace
  · rcases ordinary with continued | returned | timeout | raised
    · obtain ⟨s, t, sourceRun, _⟩ := continued
      rw [dataRun] at sourceRun
      cases sourceRun
    · obtain ⟨values, words, s, t, length, sourceRun, targetRun, related⟩ := returned
      have same : dataResult = .val values := by
        have eq := dataRun.symm.trans sourceRun
        exact Option.some.inj (congrArg Prod.fst eq)
      have resultEq : result = .val (values.map BviToData.dataToBviValue) ∨
          result = .err (.raise (.ret (values.map BviToData.dataToBviValue))) := by
        by_cases isRet : BviToData.isReturn result
        · obtain ⟨vs, valEq, retEq⟩ := returns isRet
          rw [same] at valEq
          cases valEq
          exact Or.inr retEq
        · exact Or.inl (by simpa [same, BviToData.dataToBviResult] using (projection isRet).symm)
      exact Or.inl ⟨values, words, s, t, length, resultEq, sourceRun, targetRun, related⟩
    · obtain ⟨s, t, sourceRun, targetRun, ffiEq, bound⟩ := timeout
      have same : dataResult = .err (.abort .timeoutError) := by
        have eq := dataRun.symm.trans sourceRun
        exact Option.some.inj (congrArg Prod.fst eq)
      have notRet : ¬ BviToData.isReturn result := by
        intro isRet
        obtain ⟨vs, valEq, _⟩ := returns isRet
        rw [same] at valEq
        cases valEq
      have resultEq : result = .err (.abort .timeoutError) := by
        simpa [same, BviToData.dataToBviResult] using (projection notRet).symm
      exact Or.inr (Or.inl ⟨s, t, resultEq, sourceRun, targetRun, ffiEq, bound⟩)
    · obtain ⟨value, word, s, t, a, b, r1, r2, remaining, sourceRun, targetRun, jump, ffiEq, bound, stack, related⟩ := raised
      have same : dataResult = .err (.raise value) := by
        have eq := dataRun.symm.trans sourceRun
        exact Option.some.inj (congrArg Prod.fst eq)
      have notRet : ¬ BviToData.isReturn result := by
        intro isRet
        obtain ⟨vs, valEq, _⟩ := returns isRet
        rw [same] at valEq
        cases valEq
      have resultEq : result = .err (.raise (.exn (BviToData.dataToBviValue value))) := by
        simpa [same, BviToData.dataToBviResult] using (projection notRet).symm
      exact Or.inr (Or.inr (Or.inl ⟨value, word, s, t, a, b, r1, r2, remaining,
        resultEq, sourceRun, targetRun, jump, ffiEq, bound, stack, related⟩))
  · exact Or.inr (Or.inr (Or.inr outOfSpace))

/-- Word execution preserves the final BVI FFI state for ordinary outcomes;
on allocation failure its event trace is a prefix of the BVI trace. This is
Flapjack composition infrastructure for the two candidate state relations. -/
theorem bviWordOutcomes64_ffi {C F : Type} (conf : DataToWord.Config) (l1 l2 : Nat)
    (result : BviSem.BviResult) (body : DataLang.Prog) (wordBody : WordLangProgHOL (BitVec 64))
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat))
    (bviFinal : BviSem.BviState C F)
    (dataFfi : (DataSem.evaluate body source).2.ffi = bviFinal.ffi)
    (outcome : bviWordOutcomes64 conf l1 l2 result body wordBody source target locs) :
    ∃ wordResult targetFinal, WordSemStateFiniteExact.evaluate wordBody target = (some wordResult, targetFinal) ∧
      ((wordResult ≠ .notEnoughSpace ∧ targetFinal.ffi = bviFinal.ffi) ∨
        (wordResult = .notEnoughSpace ∧ targetFinal.ffi.ioEvents <+: bviFinal.ffi.ioEvents)) := by
  rcases outcome with returned | timeout | raised | outOfSpace
  · obtain ⟨values, words, s, t, length, resultEq, sourceRun, targetRun, related⟩ := returned
    have sourceFfi : s.ffi = bviFinal.ffi := by simpa [sourceRun] using dataFfi
    exact ⟨_, t, targetRun, Or.inl ⟨by simp, related.1.trans sourceFfi⟩⟩
  · obtain ⟨s, t, resultEq, sourceRun, targetRun, ffiEq, bound⟩ := timeout
    have sourceFfi : s.ffi = bviFinal.ffi := by simpa [sourceRun] using dataFfi
    exact ⟨_, t, targetRun, Or.inl ⟨by simp, ffiEq.trans sourceFfi⟩⟩
  · obtain ⟨value, word, s, t, a, b, r1, r2, remaining, resultEq, sourceRun, targetRun, jump, ffiEq, bound, stack, related⟩ := raised
    have sourceFfi : s.ffi = bviFinal.ffi := by simpa [sourceRun] using dataFfi
    exact ⟨_, t, targetRun, Or.inl ⟨by simp, ffiEq.trans sourceFfi⟩⟩
  · obtain ⟨t, targetRun, bound, events, unsafeProof⟩ := outOfSpace
    exact ⟨_, t, targetRun, Or.inr ⟨rfl, by simpa [dataFfi] using events⟩⟩

/-- A non-type-error BVI evaluation corresponds to the emitted word body's
return, timeout, exception, or allocation-failure outcome. This connects the
two existing Lean-side pass proofs; their candidate relations, exception
premise, verified fragment, and cross-language reviews remain explicit. -/
theorem configuredBviSpaceFragment_fromBvi {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (codeLabel arity l1 l2 : Nat) (body : Bvi.Exp) (member : (codeLabel, arity, body) ∈ bviCode)
    (env : List BvlSem.Value) (envLength : env.length = arity)
    (bviState nextBvi : BviSem.BviState C F) (bviResult : BviSem.BviResult)
    (bviRun : BviSem.evaluate [body] env bviState = (bviResult, nextBvi))
    (bviSafe : bviResult ≠ .err (.abort .typeError))
    (sourceState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (vars : DataProps.varCorr env (List.range env.length) (sptMap BviToData.dataToBviValue sourceState.locals))
    (fresh : ∀ k, env.length ≤ k → sptLookup k sourceState.locals = none)
    (bviRelated : BviToData.stateRel bviState sourceState)
    (exceptionJump : BviToData.isException bviResult → DataSem.jumpExc sourceState ≠ none)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 sourceState targetState none locs)
    (sourceCode : sourceState.code = sptFromAList (BviToData.compileProg bviCode))
    (fragment : VerifiedWithSpace (BviToData.compileExp arity body)) :
    ∃ code wordBody dataResult final dataNames next ls localsSize stackMax safe peak,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      DataSem.evaluate (BviToData.compileExp arity body) sourceState =
        (some dataResult, { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak }) ∧
      BviToData.stateRel nextBvi { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safe, peakHeapLength := peak } ∧
      BviToData.correctOutcome bviResult sourceState final env.length next (List.range env.length)
        [] dataNames env true (some dataResult) ls ∧
      bviWordOutcomes64 word l1 l2 bviResult (BviToData.compileExp arity body) wordBody sourceState targetState locs ∧
      ∃ wordResult targetFinal, WordSemStateFiniteExact.evaluate wordBody targetState = (some wordResult, targetFinal) ∧
        ((wordResult ≠ .notEnoughSpace ∧ targetFinal.ffi = nextBvi.ffi) ∨
          (wordResult = .notEnoughSpace ∧ targetFinal.ffi.ioEvents <+: nextBvi.ffi.ioEvents)) := by
  have safe : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).1 ≠
      some (.err (.abort .typeError)) := by
    simpa [envLength] using BviToData.compileExp_notType body env bviState nextBvi bviResult
      sourceState bviRun bviSafe vars fresh bviRelated exceptionJump
  obtain ⟨code, wordBody, wordRun, outputLookup, targetLookup, wordOutcome⟩ :=
    configuredBviSpaceFragment_simulation fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
    word declarations bviCode names run codeLabel arity l1 l2 body member sourceState targetState
    locs related sourceCode fragment safe
  obtain ⟨dataResult, final, dataNames, next, ls, localsSize, stackMax, safeFlag, peak,
    dataRun, _, finalRel, outcome⟩ :=
    BviToData.compileExp_of_simulation body env bviState nextBvi bviResult sourceState
      (BviToData.simulationFor_all [body] env bviState) bviRun bviSafe vars fresh bviRelated exceptionJump
  have actualDataRun : DataSem.evaluate (BviToData.compileExp arity body) sourceState =
      (some dataResult, { final with localsSize := localsSize, stackMax := stackMax, safeForSpace := safeFlag, peakHeapLength := peak }) := by
    simpa [envLength] using dataRun
  have bviWord := bviWordOutcomes64_of_data word l1 l2 bviResult (BviToData.compileExp arity body)
    wordBody sourceState targetState locs dataResult _ actualDataRun outcome.1 outcome.2.1 wordOutcome
  have dataFfi : (DataSem.evaluate (BviToData.compileExp arity body) sourceState).2.ffi = nextBvi.ffi := by
    rw [actualDataRun]
    exact finalRel.2.2.2.2.2.1.symm
  have observations := bviWordOutcomes64_ffi word l1 l2 bviResult (BviToData.compileExp arity body)
    wordBody sourceState targetState locs nextBvi dataFfi bviWord
  exact ⟨code, wordBody, dataResult, final, dataNames, next, ls, localsSize, stackMax, safeFlag, peak,
    wordRun, outputLookup, targetLookup, actualDataRun, finalRel, outcome, bviWord, observations⟩

/-- The actual word entry call simulates a non-type-error BVI entry call when
the data code table belongs to the recursive call fragment. The code table is
the one emitted by the configured compiler, and recursive and mutually
recursive calls are covered by the clock induction. This Lean-side result
still assumes the candidate state relations and does not cover allocation
instructions or establish whole-program HOL correspondence. -/
theorem configuredBviCallFragment_entry {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (names : Spt Basis.Pure.MlString.MlString)
    (bviCompile : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (wordCompile : compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
      some (nextSource, nextClosure, nextBvlConfig, wordCode, names))
    (start secn label l1 l2 : Nat) (bviState nextBvi : BviSem.BviState C F)
    (result : BviSem.BviResult)
    (bviRun : BviSem.evaluate [.call 0 (some start) [] none] [] bviState = (result, nextBvi))
    (notType : result ≠ .err (.abort .typeError))
    (dataState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (bviRelated : BviToData.stateRel bviState dataState)
    (empty : sptIsEmpty dataState.locals = true)
    (jump : ∀ x, result = .err (.raise x) → DataSem.jumpExc dataState ≠ none)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 dataState targetState none locs)
    (sourceCode : dataState.code = sptFromAList (BviToData.compileProg bviCode))
    (targetCode : targetState.code = sptFromAList wordCode)
    (closed : CallFragmentCode (sptFromAList (BviToData.compileProg bviCode))) :
    ∃ dataResult dataFinal,
      DataToWord.Proofs.Gc.codeRel64 word (sptFromAList (BviToData.compileProg bviCode))
        targetState.code ∧
      DataSem.evaluate (.call none (some start) [] none) dataState = (some dataResult, dataFinal) ∧
      BviToData.stateRel nextBvi dataFinal ∧ BviToData.dataToBviResult dataResult = result ∧
      bviWordOutcomes64 word l1 l2 result (.call none (some start) [] none)
        (.call none (some start) [0] none) dataState targetState locs ∧
      ∃ wordResult targetFinal,
        WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) targetState = (some wordResult, targetFinal) ∧
        wordResult ≠ .notEnoughSpace ∧ targetFinal.ffi = nextBvi.ffi := by
  obtain ⟨actualCode, actualRun, codeRel⟩ :=
    compileCakeToWord64ConfiguredFuel_codeRel_allSettings fuel source nextSource closure nextClosure
      bvlConfig nextBvlConfig word declarations bviCode names bviCompile
  have codeEq : actualCode = wordCode := by
    have eq := Option.some.inj (actualRun.symm.trans wordCompile)
    exact congrArg (fun x => x.2.2.2.1) eq
  subst actualCode
  obtain ⟨dataResult, dataFinal, dataRun, finalRel, projection⟩ :=
    BviToData.compilePart_evaluate start bviState nextBvi dataState result bviRun notType bviRelated empty jump
  have dataSafe : (DataSem.evaluate (.call none (some start) [] none) dataState).1 ≠
      some (.err (.abort .typeError)) := by
    have resultSafe : dataResult ≠ .err (.abort .typeError) := by
      intro eq
      subst dataResult
      exact notType (by simpa [BviToData.dataToBviResult] using projection.symm)
    simpa [dataRun] using resultSafe
  have entryFragment : CallFragment (.call none (some start) [] none) :=
    CallFragment.call none (some start) [] none (by simp)
  have closedState : CallFragmentCode dataState.code := by simpa only [sourceCode] using closed
  have simulation := callFragment64 word _ entryFragment secn label l1 l2 dataState targetState locs closedState related dataSafe
  have entryCompile : (compileControl64 word secn label (.call none (some start) [] none)).1 =
      .call none (some start) [0] none := rfl
  have ordinary : fragmentOutcomesAt64 word l1 l2 (.call none (some start) [] none)
      (.call none (some start) [0] none) dataState targetState locs := by
    simpa only [fragmentOutcomesAt64, outcomes64, continues64, returns64, timesOut64, raises64, entryCompile] using simulation
  have noSpace : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) targetState).1 ≠
      some .notEnoughSpace := by
    rcases ordinary with continued | returned | timeout | raised
    · obtain ⟨_, _, _, targetRun, _⟩ := continued
      simp [targetRun]
    · obtain ⟨_, _, _, _, _, _, targetRun, _⟩ := returned
      simp [targetRun]
    · obtain ⟨_, _, _, targetRun, _, _⟩ := timeout
      simp [targetRun]
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, targetRun, _⟩ := raised
      simp [targetRun]
  have noReturn := BviToData.entryCall_notReturn start bviState nextBvi result bviRun
  have bviWord := bviWordOutcomes64_of_data word l1 l2 result (.call none (some start) [] none)
    (.call none (some start) [0] none) dataState targetState locs dataResult dataFinal dataRun
    (fun _ => projection) (fun impossible => False.elim (noReturn impossible)) (Or.inl ordinary)
  have dataFfi : (DataSem.evaluate (.call none (some start) [] none) dataState).2.ffi = nextBvi.ffi := by
    rw [dataRun]
    exact finalRel.2.2.2.2.2.1.symm
  have observations := bviWordOutcomes64_ffi word l1 l2 result (.call none (some start) [] none)
    (.call none (some start) [0] none) dataState targetState locs nextBvi dataFfi bviWord
  obtain ⟨wordResult, targetFinal, wordRun, ffiCase⟩ := observations
  have notOutOfSpace : wordResult ≠ .notEnoughSpace := by
    intro eq
    subst wordResult
    apply noSpace
    simp [wordRun]
  have ffiEq : targetFinal.ffi = nextBvi.ffi := by
    rcases ffiCase with normal | failure
    · exact normal.2
    · exact False.elim (notOutOfSpace failure.1)
  exact ⟨dataResult, dataFinal, by simpa only [targetCode] using codeRel,
    dataRun, finalRel, projection, bviWord, wordResult, targetFinal, wordRun, notOutOfSpace, ffiEq⟩

end Flapjack.Compiler.Backend.SourceToFlat
