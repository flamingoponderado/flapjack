import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Install
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Compiled chains used to execute an installed expression list. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Target code for a nonempty sequence: each intermediate result is discarded
and the next zero-argument code entry is called. -/
def bvlChain (start : Nat) : List Bvl.Exp → List (Nat × Nat × Bvl.Exp)
  | [] => []
  | [body] => [(start, 0, body)]
  | body :: next :: rest =>
      (start, 0, .let [body] (.call 0 (some (start + 1)) [])) :: bvlChain (start + 1) (next :: rest)

/-- Compiling source chain entries yields exactly the target chain of the
individually compiled expressions. The list must be nonempty because the
source chain builder emits a dummy entry for the empty list. -/
theorem compile_chain_entries (maxApp start : Nat) (expressions : List ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) (nonempty : expressions ≠ []) :
    let compiled := (compileExpsHOL maxApp expressions aux).1
    let chainSource := chainExps start expressions
    let chainTargets := (compileExpsHOL maxApp (chainSource.map (fun (_, _, exp) => exp)) aux).1
    (chainSource.zip chainTargets).map (fun ((loc, arity, _), body) => (loc + numStubs maxApp, arity, body)) =
      bvlChain (start + numStubs maxApp) compiled := by
  induction expressions generalizing start aux with
  | nil => contradiction
  | cons first rest ih =>
    cases rest with
    | nil =>
      cases firstRun : compileExpHOL maxApp first aux with
      | mk target middle =>
        simp [chainExps, compileExps_eq_list, compileExpListHOL, firstRun, bvlChain]
    | cons second tail =>
      cases firstRun : compileExpHOL maxApp first aux with
      | mk target middle =>
        have tailShape := ih (start + 1) middle (by simp)
        cases tailRun : compileExpListHOL maxApp (second :: tail) middle with
        | mk targets finalAux =>
          have targetNonempty : targets ≠ [] := by
            intro empty
            have len := compileExpList_length maxApp (second :: tail) middle
            rw [tailRun, empty] at len
            simp at len
          cases targets with
          | nil => contradiction
          | cons nextTarget remaining =>
            simp only [compileExps_eq_list, tailRun] at tailShape
            simp [chainExps, compileExps_eq_list, compileExpListHOL, compileExpHOL, firstRun,
              tailRun, bvlChain, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at tailShape ⊢
            exact tailShape

/-- When the first expression fails, the chained entry propagates that error
without entering the next code block. -/
theorem evaluate_chain_first_error {C F : Type} (s next : BvlSem.State C F)
    (first : Bvl.Exp) (address : Nat) (error : ErrorResult BvlSem.Value)
    (run : BvlSem.evaluate [first] [] s = (.err error, next)) :
    BvlSem.evaluate [.let [first] (.call 0 (some address) [])] [] s = (.err error, next) := by
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- A successful chain step supplies one clock unit for the generated call,
then continues with the next installed body at the requested extra clock. -/
theorem evaluate_chain_first_success {C F : Type} (s middle final : BvlSem.State C F)
    (first body : Bvl.Exp) (address extra : Nat) (value : BvlSem.Value)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (headRun : BvlSem.evaluate [first] [] s = (.val [value], middle))
    (lookup : sptLookup address middle.code = some (0, body))
    (tailRun : BvlSem.evaluate [body] [] { middle with clock := middle.clock + extra } = (result, final)) :
    BvlSem.evaluate [.let [first] (.call 0 (some address) [])] []
        { s with clock := s.clock + (extra + 1) } = (result, final) := by
  have shifted := BvlProps.evaluate_addClock [first] [] s middle (.val [value]) (extra + 1) headRun (by simp)
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, shifted]
  simpa [BvlSem.evaluate, BvlSem.fixClock, BvlSem.findCode, lookup, BvlSem.decClock] using tailRun

/-- The result of an installed chain keeps only the last successful value and
preserves an error unchanged. -/
def chainResult : Result (List BvlSem.Value) BvlSem.Value → Result (List BvlSem.Value) BvlSem.Value
  | .err error => .err error
  | .val values => .val (values.getLast?.toList)

/-- An installed target chain executes the original nonempty expression list,
returning its last value or the same error and preserving the final state. -/
theorem evaluate_bvlChain {C F : Type} (expressions : List Bvl.Exp) (start : Nat)
    (s final : BvlSem.State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (nonempty : expressions ≠ []) (installed : codeInstalled (bvlChain start expressions) s.code)
    (run : BvlSem.evaluate expressions [] s = (result, final)) :
    ∃ body extra, (start, 0, body) ∈ bvlChain start expressions ∧
      BvlSem.evaluate [body] [] { s with clock := s.clock + extra } = (chainResult result, final) := by
  induction expressions generalizing start s final result with
  | nil => contradiction
  | cons first rest ih =>
    cases rest with
    | nil =>
      refine ⟨first, 0, by simp [bvlChain], ?_⟩
      cases result with
      | err error => simpa [chainResult] using run
      | val values =>
        have length := BvlSem.evaluate_length [first] [] s final values run
        cases values with
        | nil => simp at length
        | cons value tail =>
          cases tail with
          | cons other tail => simp at length
          | nil => simpa [chainResult] using run
    | cons second tail =>
      cases headRun : BvlSem.evaluate [first] [] s with
      | mk headResult middle =>
        have decomposed := run
        rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, headRun] at decomposed
        cases headResult with
        | err error =>
          simp at decomposed
          rcases decomposed with ⟨rfl, rfl⟩
          exact ⟨.let [first] (.call 0 (some (start + 1)) []), 0, by simp [bvlChain],
            by simpa [chainResult] using evaluate_chain_first_error s middle first (start + 1) error headRun⟩
        | val values =>
          have length := BvlSem.evaluate_length [first] [] s middle values headRun
          cases values with
          | nil => simp at length
          | cons value remaining =>
            cases remaining with
            | cons other remaining => simp at length
            | nil =>
              cases tailRun : BvlSem.evaluate (second :: tail) [] middle with
              | mk tailResult last =>
                simp only at decomposed
                rw [tailRun] at decomposed
                have growth : sptSubspt s.code middle.code :=
                  BvlProps.evaluateMono [first] [] s (.val [value]) middle headRun
                have tailInstalled : codeInstalled (bvlChain (start + 1) (second :: tail)) middle.code := by
                  apply codeInstalled_subspt (code2 := middle.code) ?_ growth
                  intro entry member
                  apply installed entry
                  simp only [bvlChain, List.mem_cons]
                  exact Or.inr member
                obtain ⟨body, extra, member, chainRun⟩ := ih (start + 1) middle last tailResult (by simp) tailInstalled tailRun
                have lookup : sptLookup (start + 1) middle.code = some (0, body) := tailInstalled _ member
                have chained := evaluate_chain_first_success s middle last first body (start + 1) extra value
                  (chainResult tailResult) headRun lookup chainRun
                have resultEq : chainResult result = chainResult tailResult ∧ final = last := by
                  cases tailResult with
                  | err error =>
                    simp at decomposed
                    rcases decomposed with ⟨rfl, rfl⟩
                    simp [chainResult]
                  | val tailValues =>
                    have tailLength := BvlSem.evaluate_length (second :: tail) [] middle last tailValues tailRun
                    cases tailValues with
                    | nil => simp at tailLength
                    | cons next more =>
                      simp at decomposed
                      rcases decomposed with ⟨rfl, rfl⟩
                      simp [chainResult]
                obtain ⟨resultEq, rfl⟩ := resultEq
                refine ⟨.let [first] (.call 0 (some (start + 1)) []), extra + 1, by simp [bvlChain], ?_⟩
                simpa [resultEq] using chained

/-- Installing an incremental program installs the target chain of its
compiled, name-extracted expression list. -/
theorem compileInc_bvlChain_installed (maxApp start : Nat) (expressions real : List ClosLang.Exp)
    (auxiliary : List (Nat × Nat × ClosLang.Exp)) (compiled : List Bvl.Exp)
    (finalAux : List (Nat × Nat × Bvl.Exp)) (code : Spt (Nat × Bvl.Exp))
    (extract : extractName expressions = (start, real)) (nonempty : real ≠ [])
    (compile : compileExpsHOL maxApp real [] = (compiled, finalAux))
    (installed : codeInstalled (compileInc maxApp (expressions, auxiliary)) code) :
    codeInstalled (bvlChain (start + numStubs maxApp) compiled) code := by
  let chainSource := chainExps start real
  let chainExps := chainSource.map (fun (_, _, exp) => exp)
  let extraExps := auxiliary.map (fun (_, _, exp) => exp)
  cases chainRun : compileExpsHOL maxApp chainExps [] with
  | mk chainTargets chainAux =>
    cases extraRun : compileExpsHOL maxApp extraExps chainAux with
    | mk extraTargets outputAux =>
      have whole : compileExpsHOL maxApp (chainExps ++ extraExps) [] =
          (chainTargets ++ extraTargets, outputAux) := by
        simp [compileExps_append, chainRun, extraRun]
      have lengths : chainSource.length = chainTargets.length := by
        have h := compileExps_length maxApp chainExps [] chainTargets chainAux chainRun
        simpa [chainExps] using h.symm
      have shape := compile_chain_entries maxApp start real [] nonempty
      have chainRun' : compileExpsHOL maxApp ((Flapjack.Compiler.Backend.ClosToBvl.chainExps start real).map (fun (_, _, exp) => exp)) [] =
          (chainTargets, chainAux) := by
        simpa [chainExps, chainSource] using chainRun
      simp only [compile, chainRun'] at shape
      have shape' : (chainSource.zip chainTargets).map
          (fun ((loc, arity, _), body) => (loc + numStubs maxApp, arity, body)) =
            bvlChain (start + numStubs maxApp) compiled := by
        simpa [chainSource] using shape
      have installed' : codeInstalled
          (((chainSource ++ auxiliary).zip (chainTargets ++ extraTargets)).map
            (fun ((loc, arity, _), body) => (loc + numStubs maxApp, arity, body)) ++ outputAux) code := by
        have h : (chainSource ++ auxiliary).map (fun (_, _, exp) => exp) = chainExps ++ extraExps := by
          simp [chainExps, extraExps]
        simpa [compileInc, extractNameSource_eq_extractName, extract, compileProgExpsHOL, chainSource, h, whole] using installed
      rw [List.zip_append lengths, List.map_append, shape'] at installed'
      intro entry member
      apply installed' entry
      simp [member]

/-- Evaluating the compiled extracted body is reproduced by the actual
installed incremental main entry, with enough extra clock for the chain calls. -/
theorem evaluate_compileInc_chain {C F : Type} (maxApp start : Nat)
    (expressions real : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (compiled : List Bvl.Exp) (aux : List (Nat × Nat × Bvl.Exp))
    (s final : BvlSem.State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (extract : extractName expressions = (start, real)) (nonempty : real ≠ [])
    (compile : compileExpsHOL maxApp real [] = (compiled, aux))
    (installed : codeInstalled (compileInc maxApp (expressions, auxiliary)) s.code)
    (run : BvlSem.evaluate compiled [] s = (result, final)) :
    ∃ body tail extra,
      compileInc maxApp (expressions, auxiliary) = (start + numStubs maxApp, 0, body) :: tail ∧
      BvlSem.evaluate [body] [] { s with clock := s.clock + extra } = (chainResult result, final) := by
  have compiledNonempty : compiled ≠ [] := by
    intro empty
    have len := compileExps_length maxApp real [] compiled aux compile
    rw [empty] at len
    have realEmpty : real = [] := List.length_eq_zero_iff.mp len.symm
    exact nonempty realEmpty
  have chainInstalled := compileInc_bvlChain_installed maxApp start expressions real auxiliary compiled aux s.code
    extract nonempty compile installed
  obtain ⟨chainBody, extra, chainMember, chainRun⟩ :=
    evaluate_bvlChain compiled (start + numStubs maxApp) s final result compiledNonempty chainInstalled run
  obtain ⟨mainStart, mainBody, tail, extracted, program⟩ := compileInc_head maxApp (expressions, auxiliary)
  have startEq : mainStart = start := by
    simpa [extract] using extracted.symm
  subst mainStart
  simp [extract] at program
  have mainMember : (start + numStubs maxApp, 0, mainBody) ∈ compileInc maxApp (expressions, auxiliary) := by
    rw [program]
    simp
  have mainLookup := installed _ mainMember
  have chainLookup := chainInstalled _ chainMember
  have same : mainBody = chainBody := by
    have equal := mainLookup.symm.trans chainLookup
    simpa using equal
  subst mainBody
  exact ⟨chainBody, tail, extra, program, chainRun⟩

/-- Name extraction either keeps the compiled expression list or removes
one leading, side-effect-free integer marker. -/
theorem extractName_compiled_shape (maxApp start : Nat) (expressions real : List ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) (extract : extractName expressions = (start, real)) :
    (compileExpsHOL maxApp expressions aux).1 = (compileExpsHOL maxApp real aux).1 ∨
      (compileExpsHOL maxApp expressions aux).1 =
        .op (.intOp (.const (Int.ofNat start))) [] :: (compileExpsHOL maxApp real aux).1 := by
  unfold extractName at extract
  split at extract
  · rename_i trace n rest
    split at extract
    · cases extract
      exact Or.inl rfl
    · cases extract
      right
      cases h : compileExpListHOL maxApp real aux with
      | mk result finalAux =>
        simp [compileExps_eq_list, compileExpListHOL, compileExpHOL, compileOp, h]
  · cases extract
    exact Or.inl rfl

/-- The optional compiled name marker leaves state unchanged and does not
affect the final value or error of a nonempty extracted program. -/
theorem evaluate_extractName_compiled {C F : Type} (maxApp start : Nat)
    (expressions real : List ClosLang.Exp) (compiled originalAux : List Bvl.Exp)
    (auxiliary : List (Nat × Nat × Bvl.Exp)) (s final : BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (extract : extractName expressions = (start, real)) (nonempty : expressions ≠ [])
    (originalCompile : compileExpsHOL maxApp expressions [] = (compiled, auxiliary))
    (realCompile : (compileExpsHOL maxApp real []).1 = originalAux)
    (run : BvlSem.evaluate compiled [] s = (result, final)) :
    ∃ realResult, BvlSem.evaluate originalAux [] s = (realResult, final) ∧
      chainResult result = chainResult realResult := by
  have realNonempty := extractName_nonempty expressions start real extract nonempty
  have compiledNonempty : originalAux ≠ [] := by
    cases realRun : compileExpsHOL maxApp real [] with
    | mk target aux =>
      have length := compileExps_length maxApp real [] target aux realRun
      have equal : target = originalAux := by simpa [realRun] using realCompile
      intro empty
      rw [equal, empty] at length
      exact realNonempty (List.length_eq_zero_iff.mp length.symm)
  have shape := extractName_compiled_shape maxApp start expressions real [] extract
  simp only [originalCompile, realCompile] at shape
  cases shape with
  | inl same =>
    subst compiled
    exact ⟨result, run, rfl⟩
  | inr marked =>
    subst compiled
    cases originalAux with
    | nil => contradiction
    | cons first rest =>
      have markerRun : BvlSem.evaluate [.op (.intOp (.const (Int.ofNat start))) []] [] s =
          (.val [.number (Int.ofNat start)], s) := by
        simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp]
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, markerRun] at run
      cases realRun : BvlSem.evaluate (first :: rest) [] s with
      | mk realResult realFinal =>
        rw [realRun] at run
        cases realResult with
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨.err error, rfl, rfl⟩
        | val values =>
          have len := BvlSem.evaluate_length (first :: rest) [] s realFinal values realRun
          cases values with
          | nil => simp at len
          | cons value tail =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            exact ⟨.val (value :: tail), rfl, by simp [chainResult]⟩

/-- Evaluation of the original compiled nonempty program is reproduced by
the actual installed incremental main entry, up to its final result projection. -/
theorem evaluate_original_compileInc_chain {C F : Type} (maxApp : Nat)
    (expressions : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (compiled : List Bvl.Exp) (aux : List (Nat × Nat × Bvl.Exp))
    (s final : BvlSem.State C F) (result : Result (List BvlSem.Value) BvlSem.Value)
    (nonempty : expressions ≠ []) (compile : compileExpsHOL maxApp expressions [] = (compiled, aux))
    (installed : codeInstalled (compileInc maxApp (expressions, auxiliary)) s.code)
    (run : BvlSem.evaluate compiled [] s = (result, final)) :
    ∃ start body tail extra,
      (extractName expressions).1 = start ∧
      compileInc maxApp (expressions, auxiliary) = (start + numStubs maxApp, 0, body) :: tail ∧
      BvlSem.evaluate [body] [] { s with clock := s.clock + extra } = (chainResult result, final) := by
  cases extract : extractName expressions with
  | mk start real =>
    cases realCompile : compileExpsHOL maxApp real [] with
    | mk realTargets realAux =>
      obtain ⟨realResult, realRun, resultEq⟩ := evaluate_extractName_compiled maxApp start expressions real
        compiled realTargets aux s final result extract nonempty compile (by simp [realCompile]) run
      have realNonempty := extractName_nonempty expressions start real extract nonempty
      obtain ⟨body, tail, extra, program, chainRun⟩ := evaluate_compileInc_chain maxApp start expressions real
        auxiliary realTargets realAux s final realResult extract realNonempty realCompile installed realRun
      refine ⟨start, body, tail, extra, ?_, program, ?_⟩
      · rfl
      · simpa [resultEq] using chainRun

/-- After installation, the target main entry resolves and reproduces the
last value or error of the original compiled source expression list. -/
theorem install_evaluate_compiled_main {C F : Type} (s : ClosSem.State C F) (t final : BvlSem.State C F)
    (config : C) (expressions : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (compiled : List Bvl.Exp) (aux : List (Nat × Nat × Bvl.Exp))
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary)) (nonempty : expressions ≠ [])
    (compile : compileExpsHOL s.maxApp expressions [] = (compiled, aux))
    (oracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle)
    (run : BvlSem.evaluate compiled [] { t with
      code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
      compileOracle := fun n => t.compileOracle (n + 1) } = (result, final)) :
    ∃ start body tail extra,
      (extractName expressions).1 = start ∧
      compileInc s.maxApp (expressions, auxiliary) = (start + numStubs s.maxApp, 0, body) :: tail ∧
      let targetNext := { t with
        code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
        compileOracle := fun n => t.compileOracle (n + 1) }
      BvlSem.findCode none [.codePtr (start + numStubs s.maxApp)] targetNext.code = some ([], body) ∧
      BvlSem.evaluate [body] [] { targetNext with clock := targetNext.clock + extra } = (chainResult result, final) := by
  obtain ⟨headEq, _, nodup, fresh⟩ := compileOracleInv_head s.maxApp s.code s.compile s.compileOracle
    t.code t.compile t.compileOracle oracle
  have targetHead : t.compileOracle 0 = (config, compileInc s.maxApp (expressions, auxiliary)) := by
    simpa [sourceHead, BackendProps.pureCo] using headEq
  have distinct : ((compileInc s.maxApp (expressions, auxiliary)).map Prod.fst).Nodup := by
    simpa [targetHead] using nodup
  have targetFresh : ∀ entry ∈ compileInc s.maxApp (expressions, auxiliary), sptLookup entry.1 t.code = none := by
    simpa [targetHead] using fresh
  have installed := install_codeInstalled t.code (compileInc s.maxApp (expressions, auxiliary)) distinct targetFresh
  obtain ⟨start, body, tail, extra, extracted, program, chainRun⟩ :=
    evaluate_original_compileInc_chain s.maxApp expressions auxiliary compiled aux _ final result nonempty compile installed run
  have member : (start + numStubs s.maxApp, 0, body) ∈ compileInc s.maxApp (expressions, auxiliary) := by
    rw [program]
    simp
  have lookup := installed _ member
  refine ⟨start, body, tail, extra, extracted, program, ?_, chainRun⟩
  simp [BvlSem.findCode, Flapjack.holLast, lookup]

private instance : Nonempty ClosSem.Value := ⟨ClosSem.unitValue⟩

/-- Related nonempty lists have related last values. -/
theorem forall₂_last_related {α β : Type} [Nonempty α] {R : α → β → Prop}
    {source : List α} {target : List β} (related : List.Forall₂ R source target)
    (nonempty : source ≠ []) :
    ∃ value, target.getLast? = some value ∧ R (Flapjack.holLast source) value := by
  induction related with
  | nil => contradiction
  | @cons a b as bs head tail ih =>
    cases tail with
    | nil => exact ⟨b, by simp, by simpa [Flapjack.holLast] using head⟩
    | @cons a' b' as' bs' head' tail' =>
      obtain ⟨value, last, valueRel⟩ := ih (by simp)
      exact ⟨value, by simpa using last, by simpa [Flapjack.holLast] using valueRel⟩

/-- Relating the lists returned by the installed program also relates the
single value returned by the source installation and the target chain. -/
theorem install_resultRel (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (source : Result (List ClosSem.Value) ClosSem.Value) (target : Result (List BvlSem.Value) BvlSem.Value)
    (related : resultRel (List.Forall₂ (vRel maxApp f refs code)) (vRel maxApp f refs code) source target)
    (nonempty : ∀ values, source = .val values → values ≠ []) :
    resultRel (List.Forall₂ (vRel maxApp f refs code)) (vRel maxApp f refs code)
      (match source with | .err error => .err error | .val values => .val [Flapjack.holLast values])
      (chainResult target) := by
  cases source with
  | err sourceError =>
    cases target with
    | val values => simp [resultRel] at related
    | err targetError => simpa [resultRel, chainResult] using related
  | val sourceValues =>
    cases target with
    | err error => simp [resultRel] at related
    | val targetValues =>
      have valuesRel : List.Forall₂ (vRel maxApp f refs code) sourceValues targetValues := by
        simpa [resultRel] using related
      obtain ⟨last, targetLast, valueRel⟩ := forall₂_last_related valuesRel (nonempty sourceValues rfl)
      simp [resultRel, chainResult, targetLast, valueRel]

/-- A successful source installation and its program evaluation are simulated
by the installed target entry under a predecessor-clock body hypothesis. -/
theorem install_success_body_simulation {C F : Type}
    (s installedSource finalSource : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (sourceValues : List ClosSem.Value) (targetValues : List BvlSem.Value)
    (expressions : List ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value) (clockBound : Nat)
    (installRun : ClosSem.doInstall sourceValues s = (.val expressions, installedSource))
    (bodyRun : ClosSem.evaluate expressions [] installedSource = (result, finalSource))
    (noType : result ≠ .err (.abort .typeError)) (callerBound : s.clock ≤ clockBound)
    (valuesRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceValues targetValues)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound expressions) :
    ∃ auxiliary start mainBody extra targetResult targetFinal fFinal,
      let targetNext := { t with
        code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
        compileOracle := fun n => t.compileOracle (n + 1) }
      BvlSem.doInstall (R := BvlSem.Value) targetValues t = .val (.codePtr (start + numStubs s.maxApp), targetNext) ∧
      BvlSem.findCode none [.codePtr (start + numStubs s.maxApp)] targetNext.code = some ([], mainBody) ∧
      BvlSem.evaluate [mainBody] [] { targetNext with clock := installedSource.clock + extra } =
        (chainResult targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (vRel s.maxApp fFinal targetFinal.refs targetFinal.code))
        (vRel s.maxApp fFinal targetFinal.refs targetFinal.code)
        (match result with | .err error => .err error | .val values => .val [Flapjack.holLast values])
        (chainResult targetResult) ∧
      stateRel fFinal finalSource targetFinal ∧ relocationSubmap f fFinal ∧
      unmappedRefsSubmap t.refs targetFinal.refs f fFinal ∧ codeAnnotations finalSource ∧
      finalSource.clock = targetFinal.clock := by
  have successClock := ClosSem.doInstall_success_clock sourceValues s installedSource expressions installRun
  obtain ⟨sourceBytes, sourceWords, bytes, words, config, installedExpressions, auxiliary, nextConfig,
    valuesEq, bytesRun, wordsRun, sourceHead, compiledBytes, sourceNext, nonempty, _, _, nextEq, resultEq⟩ :=
      install_source_inv s installedSource sourceValues (.val expressions) installRun (by simp)
  have expressionsEq : expressions = installedExpressions := by
    simpa [Nat.ne_of_gt successClock.1] using resultEq
  subst installedExpressions
  have oracle := states.2.2.2.2.2.2.2.2.2.2.2.1
  have installedStates := install_stateRel s t f config expressions auxiliary sourceHead states
  have installedAnnotations := install_codeAnnotations s t config expressions auxiliary sourceHead annotations oracle
  have mainAnnotations := oracle.2.2.2.2 0
  have locations : ClosProps.everyFnLocationSome expressions := by simpa [sourceHead] using mainAnnotations.1
  have vars : ClosProps.everyFnVarsSome expressions := by simpa [sourceHead] using mainAnnotations.2.1
  let targetNext := { t with
    code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
    compileOracle := fun n => t.compileOracle (n + 1) }
  have states' : stateRel f installedSource targetNext := by simpa [nextEq, targetNext] using installedStates
  have annotations' : codeAnnotations installedSource := by simpa [nextEq, codeAnnotations] using installedAnnotations
  have smaller : installedSource.clock < clockBound := by omega
  cases compile : compileExpsHOL installedSource.maxApp expressions [] with
  | mk compiled aux =>
    have maxApp : installedSource.maxApp = s.maxApp := by simp [nextEq]
    have originalCompile : compileExpsHOL s.maxApp expressions [] = (compiled, aux) := by simpa [maxApp] using compile
    have codeInstalled' : codeInstalled aux targetNext.code := by
      simpa [targetNext] using install_original_aux_installed s t config expressions auxiliary compiled aux
        sourceHead nonempty originalCompile oracle
    have post := bodyIH installedSource finalSource targetNext [] [] f [] aux compiled result smaller bodyRun noType compile
      locations annotations' vars codeInstalled' (by simp [envRel]) states'
    obtain ⟨bodyExtra, targetResult, targetFinal, fFinal, targetRun, resultRelated, finalStates,
      map, refs, finalAnnotations, finalClock⟩ := post
    have shiftedOracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle
        { t with clock := installedSource.clock + bodyExtra }.code
        { t with clock := installedSource.clock + bodyExtra }.compile
        { t with clock := installedSource.clock + bodyExtra }.compileOracle := by simpa using oracle
    have run' : BvlSem.evaluate compiled [] { { t with clock := installedSource.clock + bodyExtra } with
        code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
        compileOracle := fun n => t.compileOracle (n + 1) } = (targetResult, targetFinal) := by
      simpa [targetNext] using targetRun
    obtain ⟨start, mainBody, tail, chainExtra, extracted, program, mainFound, chainRun⟩ :=
      install_evaluate_compiled_main s { t with clock := installedSource.clock + bodyExtra } targetFinal
        config expressions auxiliary compiled aux targetResult sourceHead nonempty originalCompile shiftedOracle run'
    have sourceValuesNonempty : ∀ values, result = .val values → values ≠ [] := by
      intro values resultEq empty
      have len := (ClosSem.evaluate_length (C := C) (F := F)).1 expressions [] installedSource finalSource values
        (by simpa [resultEq] using bodyRun)
      rw [empty] at len
      exact nonempty (List.length_eq_zero_iff.mp len.symm)
    have projected := install_resultRel s.maxApp fFinal targetFinal.refs targetFinal.code result targetResult
      (by simpa [maxApp] using resultRelated) sourceValuesNonempty
    have projected' : resultRel (List.Forall₂ (vRel s.maxApp fFinal targetFinal.refs targetFinal.code))
        (vRel s.maxApp fFinal targetFinal.refs targetFinal.code)
        (match result with | .err error => .err error | .val values => .val [Flapjack.holLast values])
        (chainResult targetResult) := by
      cases result <;> simpa using projected
    subst sourceValues
    cases valuesRel with
    | cons bytesRel tailRel =>
      cases tailRel with
      | cons wordsRel tailRel =>
        cases tailRel
        obtain ⟨start', body', tail', extracted', program', targetInstall⟩ :=
          install_target_run s t f sourceBytes sourceWords _ _ bytes words config nextConfig expressions auxiliary
            bytesRel wordsRel bytesRun wordsRun sourceHead sourceNext compiledBytes oracle
        have startEq : start' = start := extracted'.symm.trans extracted
        subst start'
        refine ⟨auxiliary, start, mainBody, bodyExtra + chainExtra, targetResult, targetFinal, fFinal,
          ?_, ?_, ?_, projected', finalStates, map, ?_, finalAnnotations, finalClock⟩
        · simpa [targetNext, extracted] using targetInstall
        · simpa [targetNext] using mainFound
        · simpa [targetNext, Nat.add_assoc] using chainRun
        · simpa [targetNext] using refs

end Flapjack.Compiler.Backend.ClosToBvl
