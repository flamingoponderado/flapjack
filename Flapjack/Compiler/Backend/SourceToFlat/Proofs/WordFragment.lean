import Flapjack.Compiler.Backend.SourceToFlat.Proofs.WordLabels
import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.FragmentCompiler

/-! Linking verified data-language fragments to configured compiler output. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

/-- The covered source and target outcomes for an explicitly supplied word
body. This lets the driver theorem refer directly to the emitted code entry. -/
def fragmentOutcomesAt64 {C F : Type} (conf : DataToWord.Config) (l1 l2 : Nat)
    (body : DataLang.Prog) (wordBody : WordLangProgHOL (BitVec 64))
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F) (locs : List (Nat × Nat)) : Prop :=
  (∃ source' target', DataSem.evaluate body source = (none, source') ∧
    WordSemStateFiniteExact.evaluate wordBody target = (none, target') ∧
    stateRel64 conf l1 l2 source' target' none locs) ∨
  (∃ values words source' target', values.length = words.length ∧
    DataSem.evaluate body source = (some (.val values), source') ∧
    WordSemStateFiniteExact.evaluate wordBody target = (some (.result (.loc l1 l2) words), target') ∧
    stateRel64 conf l1 l2 source' target' (some (values.zip words)) locs) ∨
  (∃ source' target', DataSem.evaluate body source = (some (.err (.abort .timeoutError)), source') ∧
    WordSemStateFiniteExact.evaluate wordBody target = (some .timeOut, target') ∧
    target'.ffi = source'.ffi ∧ BackendProps.optionLe target'.stackMax source'.stackMax) ∨
  (∃ value word source' target' a b r1 r2 remaining,
    DataSem.evaluate body source = (some (.err (.raise value)), source') ∧
    WordSemStateFiniteExact.evaluate wordBody target = (some (.exception (.loc a b) word), target') ∧
    target'.ffi = source'.ffi ∧ BackendProps.optionLe target'.stackMax source'.stackMax ∧
    wordSemLastN (source'.stack.length + 1) locs = (r1, r2) :: remaining ∧
    ∀ dest, stateRel64 conf r1 r2 (DataSem.setVar dest value source')
      (WordSemStateFiniteExact.setVar (DataToWord.adjustVar dest) word target') none remaining)

/-- The configured function lookup for either setting of multi-argument introduction. -/
theorem compileCakeToWord64ConfiguredFuel_fragmentFunction_noCallKnown (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (calls : closure.doCall = false) (known : closure.knownConf = none)
    (codeLabel arity : Nat) (body : DataLang.Prog)
    (sourceLookup : sptLookup codeLabel (sptFromAList (BviToData.compileProg bviCode)) = some (arity, body))
    (fragment : VerifiedFragment body) :
    ∃ code wordBody nextLabel,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      fragmentCompile64 word codeLabel 2 body = some (wordBody, nextLabel) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) := by
  obtain ⟨code, wordRun, codeRel⟩ := compileCakeToWord64ConfiguredFuel_codeRel_noCallKnown fuel source nextSource
    closure nextClosure bvlConfig nextBvlConfig word declarations bviCode names run calls known
  refine ⟨code, (compileControl64 word codeLabel 2 body).1, (compileControl64 word codeLabel 2 body).2,
    wordRun, ?_, codeRel.2.2 codeLabel arity body sourceLookup⟩
  simpa using fragmentCompile64_agrees word codeLabel body fragment 2

/-- The BVI-member lookup for either setting of multi-argument introduction. -/
theorem compileCakeToWord64ConfiguredFuel_bviFragment_noCallKnown (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (calls : closure.doCall = false) (known : closure.knownConf = none)
    (codeLabel arity : Nat) (body : Bvi.Exp) (member : (codeLabel, arity, body) ∈ bviCode)
    (fragment : VerifiedFragment (BviToData.compileExp arity body)) :
    ∃ code wordBody nextLabel,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      fragmentCompile64 word codeLabel 2 (BviToData.compileExp arity body) = some (wordBody, nextLabel) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) := by
  have distinct : ((BviToData.compileProg bviCode).map Prod.fst).Nodup := by
    rw [bviToData_labels]
    exact (configured_bvi_labels_noCallKnown fuel source nextSource closure nextClosure bvlConfig nextBvlConfig
      declarations bviCode names run calls known).1
  have dataMember : (codeLabel, arity, BviToData.compileExp arity body) ∈ BviToData.compileProg bviCode := by
    apply List.mem_map.mpr
    exact ⟨(codeLabel, arity, body), member, rfl⟩
  have sourceLookup : sptLookup codeLabel (sptFromAList (BviToData.compileProg bviCode)) =
      some (arity, BviToData.compileExp arity body) := by
    rw [sptLookup_sptFromAList]
    apply sptAListLookup_eq_of_mem_unique _ _ _ dataMember
    intro other otherMember
    have eq : (codeLabel, other) = (codeLabel, arity, BviToData.compileExp arity body) :=
      List.inj_on_of_nodup_map distinct otherMember dataMember rfl
    exact congrArg Prod.snd eq
  exact compileCakeToWord64ConfiguredFuel_fragmentFunction_noCallKnown fuel source nextSource closure nextClosure
    bvlConfig nextBvlConfig word declarations bviCode names run calls known codeLabel arity
    (BviToData.compileExp arity body) sourceLookup fragment

/-- The emitted-body simulation for either setting of multi-argument introduction. -/
theorem configuredFragmentFunction_simulation_noCallKnown {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (calls : closure.doCall = false) (known : closure.knownConf = none)
    (codeLabel arity l1 l2 : Nat) (body : DataLang.Prog)
    (sourceState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 sourceState targetState none locs)
    (sourceCode : sourceState.code = sptFromAList (BviToData.compileProg bviCode))
    (sourceLookup : sptLookup codeLabel sourceState.code = some (arity, body))
    (fragment : VerifiedFragment body)
    (safe : (DataSem.evaluate body sourceState).1 ≠ some (.err (.abort .typeError))) :
    ∃ code wordBody nextLabel,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      fragmentCompile64 word codeLabel 2 body = some (wordBody, nextLabel) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      fragmentOutcomesAt64 word l1 l2 body wordBody sourceState targetState locs := by
  obtain ⟨code, wordBody, nextLabel, wordRun, compilerEq, outputLookup⟩ :=
    compileCakeToWord64ConfiguredFuel_fragmentFunction_noCallKnown fuel source nextSource closure nextClosure
      bvlConfig nextBvlConfig word declarations bviCode names run calls known codeLabel arity body
      (by simpa [sourceCode] using sourceLookup) fragment
  have targetLookup := related.2.2.2.2.1.2.2 codeLabel arity body sourceLookup
  have agreement := fragmentCompile64_agrees word codeLabel body fragment 2
  rw [compilerEq] at agreement
  have same := Option.some.inj agreement
  have bodyEq : wordBody = (compileControl64 word codeLabel 2 body).1 := by
    exact congrArg Prod.fst same
  refine ⟨code, wordBody, nextLabel, wordRun, compilerEq, outputLookup, ?_, ?_⟩
  · simpa [bodyEq] using targetLookup
  · have simulation := verifiedFragment64 word codeLabel l1 l2 body fragment 2 sourceState targetState locs related safe
    simpa [fragmentOutcomesAt64, outcomes64, continues64, returns64, timesOut64, raises64, bodyEq] using simulation

/-- A function in the configured BVI-to-data output whose body lies in the
verified fragment is installed in the actual word output with the same body as
the independent source-shaped fragment traversal. This is pipeline
infrastructure, not a port of HOL's complete compiler-correctness theorem. -/
theorem compileCakeToWord64ConfiguredFuel_fragmentFunction_mti (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (_enabled : closure.doMti = true) (calls : closure.doCall = false) (known : closure.knownConf = none)
    (codeLabel arity : Nat) (body : DataLang.Prog)
    (sourceLookup : sptLookup codeLabel (sptFromAList (BviToData.compileProg bviCode)) = some (arity, body))
    (fragment : VerifiedFragment body) :
    ∃ code wordBody nextLabel,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      fragmentCompile64 word codeLabel 2 body = some (wordBody, nextLabel) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) := by
  exact compileCakeToWord64ConfiguredFuel_fragmentFunction_noCallKnown fuel source nextSource closure nextClosure
    bvlConfig nextBvlConfig word declarations bviCode names run calls known codeLabel arity body sourceLookup fragment

/-- A labeled function occurring in the executed BVI output is installed in
the actual word output when its BVI-to-data body belongs to the verified
fragment. Distinctness is derived from the configured frontend run. -/
theorem compileCakeToWord64ConfiguredFuel_bviFragment_mti (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (_enabled : closure.doMti = true) (calls : closure.doCall = false) (known : closure.knownConf = none)
    (codeLabel arity : Nat) (body : Bvi.Exp) (member : (codeLabel, arity, body) ∈ bviCode)
    (fragment : VerifiedFragment (BviToData.compileExp arity body)) :
    ∃ code wordBody nextLabel,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      fragmentCompile64 word codeLabel 2 (BviToData.compileExp arity body) = some (wordBody, nextLabel) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) := by
  exact compileCakeToWord64ConfiguredFuel_bviFragment_noCallKnown fuel source nextSource closure nextClosure
    bvlConfig nextBvlConfig word declarations bviCode names run calls known codeLabel arity body member fragment

/-- Whenever related machine states use the configured output tables, the
installed function body satisfies the established fragment simulation. The
state relation and exclusion of source type errors are explicit prerequisites;
this does not establish whole-program correctness. -/
theorem configuredFragmentFunction_simulation_mti {C F : Type} (fuel : Nat)
    (source nextSource : Config) (closure nextClosure : ClosToBvl.Config)
    (bvlConfig nextBvlConfig : BvlToBvi.Config) (word : DataToWord.Config)
    (declarations : List AstHOL.Dec) (bviCode : List (Nat × Nat × Bvi.Exp))
    (names : Spt Basis.Pure.MlString.MlString)
    (run : compileCakeToBviConfiguredFuel fuel source closure bvlConfig declarations =
      some (nextSource, nextClosure, nextBvlConfig, bviCode, names))
    (_enabled : closure.doMti = true) (calls : closure.doCall = false) (known : closure.knownConf = none)
    (codeLabel arity l1 l2 : Nat) (body : DataLang.Prog)
    (sourceState : DataSem.State C F) (targetState : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 word l1 l2 sourceState targetState none locs)
    (sourceCode : sourceState.code = sptFromAList (BviToData.compileProg bviCode))
    (sourceLookup : sptLookup codeLabel sourceState.code = some (arity, body))
    (fragment : VerifiedFragment body)
    (safe : (DataSem.evaluate body sourceState).1 ≠ some (.err (.abort .typeError))) :
    ∃ code wordBody nextLabel,
      compileCakeToWord64ConfiguredFuel fuel source closure bvlConfig word declarations =
        some (nextSource, nextClosure, nextBvlConfig, code, names) ∧
      fragmentCompile64 word codeLabel 2 body = some (wordBody, nextLabel) ∧
      sptLookup codeLabel (sptFromAList code) = some (arity + 1, wordBody) ∧
      sptLookup codeLabel targetState.code = some (arity + 1, wordBody) ∧
      fragmentOutcomesAt64 word l1 l2 body wordBody sourceState targetState locs := by
  exact configuredFragmentFunction_simulation_noCallKnown fuel source nextSource closure nextClosure
    bvlConfig nextBvlConfig word declarations bviCode names run calls known codeLabel arity l1 l2 body
    sourceState targetState locs related sourceCode sourceLookup fragment safe

end Flapjack.Compiler.Backend.SourceToFlat
