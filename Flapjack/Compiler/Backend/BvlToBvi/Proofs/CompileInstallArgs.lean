import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileAllocGlobal

/-! Operand preparation for BVL-to-BVI code installation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Any successful BVL installation has exactly two operands that decode to
the source byte and word sequences. -/
theorem install_operand_shape {C F R : Type} (args : List Value) (state next : BvlSem.State C F)
    (result : Value) (run : BvlSem.doInstall (R := R) args state = .val (result, next)) :
    ∃ byteValue wordValue bytes words, args = [byteValue, wordValue] ∧
      BvlSem.valueToBytes byteValue = some bytes ∧ BvlSem.valueToWords wordValue = some words := by
  cases args with
  | nil => simp [BvlSem.doInstall] at run
  | cons byteValue rest =>
    cases rest with
    | nil => simp [BvlSem.doInstall] at run
    | cons wordValue rest =>
      cases rest with
      | cons extra tail => simp [BvlSem.doInstall] at run
      | nil =>
        cases bytesRun : BvlSem.valueToBytes byteValue with
        | none => simp [BvlSem.doInstall, bytesRun] at run
        | some bytes =>
          cases wordsRun : BvlSem.valueToWords wordValue with
          | none => simp [BvlSem.doInstall, bytesRun, wordsRun] at run
          | some words => exact ⟨byteValue, wordValue, bytes, words, rfl, bytesRun, wordsRun⟩

/-- A successful source installation identifies its oracle program, callback
result, name guards, and the shifted oracle configuration. -/
theorem install_success_shape {C F R : Type} (byteValue wordValue : Value)
    (state next : BvlSem.State C F) (result : Value)
    (run : BvlSem.doInstall (R := R) [byteValue, wordValue] state = .val (result, next)) :
    ∃ (bytes : List (BitVec 8)) (words : List (BitVec 64)) (config nextConfig : C)
      (key arity : Nat) (body : Bvl.Exp) (rest : List (Nat × Nat × Bvl.Exp)),
      BvlSem.valueToBytes byteValue = some bytes ∧ BvlSem.valueToWords wordValue = some words ∧
      state.compileOracle 0 = (config, (key, arity, body) :: rest) ∧
      (∀ entry ∈ (key, arity, body) :: rest, sptLookup entry.1 state.code = none) ∧
      (((key, arity, body) :: rest).map Prod.fst).Nodup ∧
      state.compile config ((key, arity, body) :: rest) = some (bytes, words, nextConfig) ∧
      (state.compileOracle 1).1 = nextConfig ∧ result = .codePtr key ∧
      next = { state with
        code := sptUnion state.code (sptFromAList ((key, arity, body) :: rest))
        compileOracle := fun n => state.compileOracle (n + 1) } := by
  unfold BvlSem.doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals aesop

/-- Successfully decoded installation buffers remain unchanged by reference
relocation. -/
theorem valueToBytes_adjust_some (relocate : Nat → Nat) (value : Value) (bytes : List (BitVec 8))
    (decoded : BvlSem.valueToBytes value = some bytes) :
    BvlSem.valueToBytes (adjustBv relocate value) = some bytes := by
  have original := (BvlSem.valueToBytes_eq_some value bytes).1 decoded
  apply (BvlSem.valueToBytes_eq_some _ _).2
  simpa [original, List.map_map, Function.comp_def, adjustBv] using valueToList_adjust relocate value

/-- Successfully decoded installation words remain unchanged by reference
relocation. -/
theorem valueToWords_adjust_some (relocate : Nat → Nat) (value : Value) (words : List (BitVec 64))
    (decoded : BvlSem.valueToWords value = some words) :
    BvlSem.valueToWords (adjustBv relocate value) = some words := by
  have original := (BvlSem.valueToWords_eq_some value words).1 decoded
  apply (BvlSem.valueToWords_eq_some _ _).2
  simpa [original, List.map_map, Function.comp_def, adjustBv] using valueToList_adjust relocate value

/-- The generated length call works at any environment position. -/
theorem evaluate_listLength_at {C F : Type} (value : Value) (values : List Value) (index : Nat)
    (env : List Value) (state : BviSem.BviState C F)
    (varLookup : env[index]? = some value)
    (code : sptLookup listLengthLocation state.code = some listLengthCode)
    (decode : BvlSem.valueToList value = some values) :
    ∃ clock, BviSem.evaluate [.call 0 (some listLengthLocation)
      [.var index, .op (.intOp (.const 0)) []] none] env (BviProps.incClock clock state) =
      (.val [.number (Int.ofNat values.length)], state) := by
  obtain ⟨clock, stub⟩ := evaluate_listLength_decoded value values 0 state code decode
  refine ⟨clock + 1, ?_⟩
  let start := BviProps.incClock (clock + 1) state
  have varRun : BviSem.evaluate [.var index] env start = (.val [value], start) := by simp [BviSem.evaluate, varLookup]
  have zeroRun : BviSem.evaluate [.op (.intOp (.const 0)) []] env start = (.val [.number 0], start) := by
    apply evaluate_smallConst
    decide
  have argsRun := evaluate_pair (.var index) (.op (.intOp (.const 0)) []) env start value (.number 0) varRun zeroRun
  change BviSem.evaluate [.call 0 (some listLengthLocation) [.var index, .op (.intOp (.const 0)) []] none] env start = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  have startCode : sptLookup listLengthLocation start.code = some listLengthCode := by simpa [start, BviProps.incClock] using code
  have nonzero : start.clock ≠ 0 := by simp [start, BviProps.incClock]
  have clocks : BviSem.decClock 1 start = BviProps.incClock clock state := by simp [start, BviSem.decClock, BviProps.incClock]
  simp only [BvlSem.findCode, startCode, listLengthCode, List.length_cons, List.length_nil, ite_true,
    Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
  simp [listLengthCode] at stub
  simp [clocks, stub]

/-- The installation body calculates both lengths before passing the original
buffers and their lengths to the target installation primitive. Untagged
pending BVI evaluator and dispatcher correspondence review. -/
theorem evaluate_installBody {C F : Type} (byteValue wordValue : Value)
    (bytes : List (BitVec 8)) (words : List (BitVec 64)) (env : List Value)
    (state final : BviSem.BviState C F) (result : Value)
    (bytesDecode : BvlSem.valueToBytes byteValue = some bytes)
    (wordsDecode : BvlSem.valueToWords wordValue = some words)
    (code : sptLookup listLengthLocation state.code = some listLengthCode)
    (application : BviSem.doApp .install [byteValue, wordValue, .number bytes.length, .number words.length] state =
      .val (result, final)) :
    ∃ clock, BviSem.evaluate [.op .install
      [.call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none,
        .call 0 (some listLengthLocation) [.var 1, .op (.intOp (.const 0)) []] none,
        .var 0, .var 1]] (wordValue :: byteValue :: env) (BviProps.incClock clock state) =
      (.val [result], final) := by
  let input := wordValue :: byteValue :: env
  let wordLength : Bvi.Exp := .call 0 (some listLengthLocation) [.var 0, .op (.intOp (.const 0)) []] none
  let byteLength : Bvi.Exp := .call 0 (some listLengthLocation) [.var 1, .op (.intOp (.const 0)) []] none
  have wordList := (BvlSem.valueToWords_eq_some _ _).1 wordsDecode
  have byteList := (BvlSem.valueToBytes_eq_some _ _).1 bytesDecode
  obtain ⟨wordClock, wordRun⟩ := evaluate_listLength_at wordValue (words.map Value.word64) 0 input state (by simp [input]) code wordList
  obtain ⟨byteClock, byteRun⟩ := evaluate_listLength_at byteValue (bytes.map (fun b => .number b.toNat)) 1 input state (by simp [input]) code byteList
  have wordResult : BviSem.evaluate [wordLength] input (BviProps.incClock wordClock state) =
      (.val [.number words.length], state) := by simpa [wordLength] using wordRun
  have byteResult : BviSem.evaluate [byteLength] input (BviProps.incClock byteClock state) =
      (.val [.number bytes.length], state) := by simpa [byteLength] using byteRun
  let start := BviProps.incClock (byteClock + wordClock) state
  let middle := BviProps.incClock byteClock state
  have shifted := BviProps.evaluate_inv_clock [wordLength] input (BviProps.incClock wordClock state) state
    (.val [.number words.length]) byteClock wordResult (by simp)
  rw [BviProps.incClock_add] at shifted
  have wordShifted : BviSem.evaluate [wordLength] input start = (.val [.number words.length], middle) := by
    simpa [start, middle] using shifted
  have byteMiddle : BviSem.evaluate [byteLength] input middle = (.val [.number bytes.length], state) := by
    simpa [middle] using byteResult
  have vars : BviSem.evaluate [.var 0, .var 1] input state = (.val [wordValue, byteValue], state) := by
    apply evaluate_readOnly
    simp [input, BviSem.evaluate]
  have rest := evaluate_cons_threaded byteLength [.var 0, .var 1] input middle state state
    (.number bytes.length) [wordValue, byteValue] byteMiddle vars
  have all := evaluate_cons_threaded wordLength [byteLength, .var 0, .var 1] input start middle state
    (.number words.length) [.number bytes.length, wordValue, byteValue] wordShifted rest
  refine ⟨byteClock + wordClock, ?_⟩
  change BviSem.evaluate [.op .install [wordLength, byteLength, .var 0, .var 1]] input start = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, all]
  simp [application]

/-- The source callback's successful incremental compilation determines the
corresponding target callback and oracle entries. -/
theorem install_callback_transfer {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (counter nextCounter : Nat) (config nextConfig : C)
    (program : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Nat × Bvi.Exp))
    (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (related : stateRel relocate source target)
    (oracle : source.compileOracle 0 = ((counter, config), program))
    (compiledEq : compileIncSource counter program = (nextCounter, compiled))
    (callback : source.compile (counter, config) program = some (bytes, words, (nextCounter, nextConfig)))
    (nextOracle : (source.compileOracle 1).1 = (nextCounter, nextConfig)) :
    target.compileOracle 0 = (config, compiled) ∧
      target.compile config compiled = some (bytes, words, nextConfig) ∧
      (target.compileOracle 1).1 = nextConfig := by
  have oracleRel := related.2.2.2.2.1
  have callbackRel := related.2.2.2.2.2.1
  constructor
  · rw [oracleRel]
    simp [BackendProps.stateCo, oracle, compiledEq]
  constructor
  · rw [callbackRel] at callback
    simp [BackendProps.stateCc, compiledEq] at callback
    cases targetRun : target.compile config compiled with
    | none => simp [targetRun] at callback
    | some output =>
      rcases output with ⟨outBytes, outWords, outConfig⟩
      simp [targetRun] at callback
      rcases callback with ⟨rfl, rfl, rfl⟩
      rfl
  · rw [oracleRel]
    simpa [BackendProps.stateCo] using congrArg Prod.snd nextOracle

/-- Once the target code-name guards and callback are established, the BVI
installation primitive installs that exact compiled program and advances its
oracle. Untagged pending BVI dispatcher correspondence review. -/
theorem doInstall_target {C F : Type} (byteValue wordValue : Value)
    (bytes : List (BitVec 8)) (words : List (BitVec 64)) (state : BviSem.BviState C F)
    (config nextConfig : C) (key arity : Nat) (body : Bvi.Exp) (rest : List (Nat × Nat × Bvi.Exp))
    (bytesDecode : BvlSem.valueToBytes byteValue = some bytes)
    (wordsDecode : BvlSem.valueToWords wordValue = some words)
    (oracle : state.compileOracle 0 = (config, (key, arity, body) :: rest))
    (available : ∀ entry ∈ (key, arity, body) :: rest, sptLookup entry.1 state.code = none)
    (distinct : (((key, arity, body) :: rest).map Prod.fst).Nodup)
    (callback : state.compile config ((key, arity, body) :: rest) = some (bytes, words, nextConfig))
    (nextOracle : (state.compileOracle 1).1 = nextConfig) :
    BviSem.doApp .install [byteValue, wordValue, .number bytes.length, .number words.length] state =
      .val (.codePtr key, { state with
        code := sptUnion state.code (sptFromAList ((key, arity, body) :: rest))
        compileOracle := fun n => state.compileOracle (n + 1) }) := by
  simp [BviSem.doApp, BviSem.doInstall, bytesDecode, wordsDecode, oracle, callback, nextOracle]
  simpa [and_assoc] using And.intro available distinct

/-- Incremental compilation emits the first source function's translated
entry before its auxiliary code and the remaining functions. -/
theorem compileIncSource_head (counter key arity : Nat) (body : Bvl.Exp)
    (rest : List (Nat × Nat × Bvl.Exp)) :
    ∃ targetBody targetRest,
      (compileIncSource counter ((key, arity, body) :: rest)).2 =
        (bvlNumStubs + bvlToBviNamespaces * key, arity, targetBody) :: targetRest := by
  rcases first : compileSingSource counter body with ⟨converted, aux, next⟩
  rcases remaining : compileProgramsSource next rest with ⟨other, final⟩
  refine ⟨BviLet.compileSing [] 0 converted, appListAppend aux ++ appListAppend other, ?_⟩
  simp only [compileIncSource, compileProgramsSource, compileSingleSource, first, remaining,
    appListAppend_smartAppend]
  simp [appListAppend, appendAux]

/-- Successful installation transfers to the BVI primitive once the compiled
program's disjointness and distinctness guards have been established. The
remaining code-name invariant is deliberately an explicit premise here. -/
theorem install_target_transfer {C F : Type} (relocate : Nat → Nat)
    (source next : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (byteValue wordValue result : Value) (related : stateRel relocate source target)
    (run : BvlSem.doInstall (R := Value) [byteValue, wordValue] source = .val (result, next))
    (available : ∀ entry ∈ (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2,
      sptLookup entry.1 target.code = none)
    (distinct : ((compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2.map Prod.fst).Nodup) :
    ∃ bytes words targetNext,
      BvlSem.valueToBytes byteValue = some bytes ∧ BvlSem.valueToWords wordValue = some words ∧
      BviSem.doApp .install [adjustBv relocate byteValue, adjustBv relocate wordValue,
        .number bytes.length, .number words.length] target = .val (adjustBv relocate result, targetNext) ∧
      targetNext.code = sptUnion target.code (sptFromAList (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2) ∧
      targetNext.compileOracle = (fun n => target.compileOracle (n + 1)) ∧
      targetNext = { target with
        code := sptUnion target.code (sptFromAList (compileIncSource (source.compileOracle 0).1.1 (source.compileOracle 0).2).2)
        compileOracle := fun n => target.compileOracle (n + 1) } := by
  obtain ⟨bytes, words, ⟨counter, config⟩, ⟨nextCounter, nextConfig⟩, key, arity, body, rest,
    bytesDecode, wordsDecode, oracle, _, _, callback, nextOracle, resultEq, _⟩ :=
      install_success_shape byteValue wordValue source next result run
  rcases compiledEq : compileIncSource counter ((key, arity, body) :: rest) with ⟨actualCounter, compiled⟩
  have counterEq : actualCounter = nextCounter := by
    have sourceCallback := callback
    rw [related.2.2.2.2.2.1] at sourceCallback
    simp [BackendProps.stateCc, compiledEq] at sourceCallback
    cases targetRun : target.compile config compiled with
    | none => simp [targetRun] at sourceCallback
    | some output =>
      rcases output with ⟨outBytes, outWords, outConfig⟩
      simp [targetRun] at sourceCallback
      exact sourceCallback.2.2.1
  subst actualCounter
  obtain ⟨targetOracle, targetCallback, targetNextOracle⟩ :=
    install_callback_transfer relocate source target counter nextCounter config nextConfig
      ((key, arity, body) :: rest) compiled bytes words related oracle compiledEq callback nextOracle
  obtain ⟨targetBody, targetRest, headEq⟩ := compileIncSource_head counter key arity body rest
  rw [compiledEq] at headEq
  change compiled = _ at headEq
  subst compiled
  have targetAvailable : ∀ entry ∈ (bvlNumStubs + bvlToBviNamespaces * key, arity, targetBody) :: targetRest,
      sptLookup entry.1 target.code = none := by simpa [oracle, compiledEq] using available
  have targetDistinct : (((bvlNumStubs + bvlToBviNamespaces * key, arity, targetBody) :: targetRest).map Prod.fst).Nodup := by
    simpa [oracle, compiledEq] using distinct
  have targetRun := doInstall_target (adjustBv relocate byteValue) (adjustBv relocate wordValue) bytes words target
    config nextConfig (bvlNumStubs + bvlToBviNamespaces * key) arity targetBody targetRest
    (valueToBytes_adjust_some relocate byteValue bytes bytesDecode)
    (valueToWords_adjust_some relocate wordValue words wordsDecode)
    targetOracle targetAvailable targetDistinct targetCallback targetNextOracle
  refine ⟨bytes, words, { target with
    code := sptUnion target.code (sptFromAList ((bvlNumStubs + bvlToBviNamespaces * key, arity, targetBody) :: targetRest))
    compileOracle := fun n => target.compileOracle (n + 1) }, bytesDecode, wordsDecode, ?_, ?_, rfl, ?_⟩
  · simpa [resultEq, adjustBv] using targetRun
  · simp [oracle, compiledEq]
  · simp [oracle, compiledEq]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
