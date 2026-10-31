import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Install
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Compiled chains used to execute an installed expression list. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

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
        simpa [compileInc, extract, compileProgExpsHOL, chainSource, h, whole] using installed
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

end Flapjack.Compiler.Backend.ClosToBvl
