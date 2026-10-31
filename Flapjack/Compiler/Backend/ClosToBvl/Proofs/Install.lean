import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockList
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WordRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions
import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply

/-! Value decoding needed by the dynamic-installation simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- A source byte list and a related target value decode to identical bytes. -/
theorem install_valueToBytes_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (source : ClosSem.Value) (target : BvlSem.Value) (bytes : List (BitVec 8))
    (related : vRel maxApp f refs code source target)
    (decoded : ClosSem.valueToBytes source = some bytes) :
    BvlSem.valueToBytes target = some bytes := by
  have sourceList := (ClosSem.valueToBytes_eq_some source bytes).1 decoded
  obtain ⟨values, targetList, valuesRel⟩ := decodedList_related source target _ related sourceList
  have valuesEq : values = bytes.map (fun b => BvlSem.Value.number b.toNat) := by
    clear decoded sourceList targetList related
    induction bytes generalizing values with
    | nil => cases valuesRel; rfl
    | cons byte rest ih =>
      cases valuesRel with
      | cons head tail =>
        have first := vRel_number_inv head
        have remaining := ih _ tail
        simp [first, remaining]
  apply (BvlSem.valueToBytes_eq_some target bytes).2
  simpa [valuesEq] using targetList

/-- A source word list and a related target value decode to identical words. -/
theorem install_valueToWords_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (source : ClosSem.Value) (target : BvlSem.Value) (words : List (BitVec 64))
    (related : vRel maxApp f refs code source target)
    (decoded : ClosSem.valueToWords source = some words) :
    BvlSem.valueToWords target = some words := by
  have sourceList := (ClosSem.valueToWords_eq_some source words).1 decoded
  obtain ⟨values, targetList, valuesRel⟩ := decodedList_related source target _ related sourceList
  have valuesEq : values = words.map BvlSem.Value.word64 := by
    clear decoded sourceList targetList related
    induction words generalizing values with
    | nil => cases valuesRel; rfl
    | cons word rest ih =>
      cases valuesRel with
      | cons head tail =>
        have first := vRel_word64_inv head
        have remaining := ih _ tail
        simp [first, remaining]
  apply (BvlSem.valueToWords_eq_some target words).2
  simpa [valuesEq] using targetList

/-- Compiling a program whose first entry has arity zero preserves its first
location, shifted past the generated closure-call stubs. -/
theorem compileProgExps_head_zero (maxApp start : Nat) (expression : ClosLang.Exp)
    (rest : List (Nat × Nat × ClosLang.Exp)) :
    ∃ body tail, compileProgExpsHOL maxApp ((start, 0, expression) :: rest) =
      (start + numStubs maxApp, 0, body) :: tail := by
  cases first : compileExpHOL maxApp expression [] with
  | mk body aux =>
    cases remaining : compileExpListHOL maxApp (rest.map (fun (_, _, exp) => exp)) aux with
    | mk bodies finalAux =>
      refine ⟨body, (rest.zip bodies).map (fun ((loc, args, _), exp) => (loc + numStubs maxApp, args, exp)) ++ finalAux, ?_⟩
      simp [compileProgExpsHOL, compileExps_eq_list, compileExpListHOL, first, remaining]

/-- Every incremental compilation has a zero-arity entry for the extracted
main location, even when the expression list is empty. -/
theorem compileInc_head (maxApp : Nat) (program : ClosSem.Program) :
    ∃ start body tail, (extractName program.1).1 = start ∧
      compileInc maxApp program = (start + numStubs maxApp, 0, body) :: tail := by
  cases extract : extractName program.1 with
  | mk start expressions =>
    have chain : ∃ expression rest, chainExps start expressions ++ program.2 =
        (start, 0, expression) :: rest := by
      cases expressions with
      | nil => simp [chainExps]
      | cons first remaining =>
        cases remaining with
        | nil => simp [chainExps]
        | cons second tail => simp [chainExps]
    obtain ⟨expression, rest, chainEq⟩ := chain
    obtain ⟨body, tail, compiled⟩ := compileProgExps_head_zero maxApp start expression rest
    refine ⟨start, body, tail, ?_, ?_⟩
    · rfl
    · simpa [compileInc, extract, chainEq] using compiled

/-- A source compiler result accepted by the installation oracle is also
accepted by the target installer, with the incremental main entry returned. -/
theorem install_target_run {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (sourceBytes sourceWords : ClosSem.Value)
    (targetBytes targetWords : BvlSem.Value) (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (config nextConfig : C) (expressions : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (bytesRel : vRel s.maxApp f t.refs t.code sourceBytes targetBytes)
    (wordsRel : vRel s.maxApp f t.refs t.code sourceWords targetWords)
    (bytesDecoded : ClosSem.valueToBytes sourceBytes = some bytes)
    (wordsDecoded : ClosSem.valueToWords sourceWords = some words)
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary))
    (sourceNext : (s.compileOracle 1).1 = nextConfig)
    (compiled : s.compile config (expressions, auxiliary) = some (bytes, words, nextConfig))
    (oracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle) :
    ∃ start body tail,
      (extractName expressions).1 = start ∧
      compileInc s.maxApp (expressions, auxiliary) = (start + numStubs s.maxApp, 0, body) :: tail ∧
      BvlSem.doInstall (R := BvlSem.Value) [targetBytes, targetWords] t =
        .val (.codePtr (start + numStubs s.maxApp), { t with
          code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
          compileOracle := fun n => t.compileOracle (n + 1) }) := by
  obtain ⟨start, body, tail, extracted, program⟩ := compileInc_head s.maxApp (expressions, auxiliary)
  have targetBytesDecoded := install_valueToBytes_related sourceBytes targetBytes bytes bytesRel bytesDecoded
  have targetWordsDecoded := install_valueToWords_related sourceWords targetWords words wordsRel wordsDecoded
  obtain ⟨headEq, compileEq, nodup, fresh⟩ := compileOracleInv_head s.maxApp s.code s.compile s.compileOracle
    t.code t.compile t.compileOracle oracle
  have targetHead : t.compileOracle 0 = (config, compileInc s.maxApp (expressions, auxiliary)) := by
    simpa [sourceHead, BackendProps.pureCo] using headEq
  have targetCompile : t.compile config (compileInc s.maxApp (expressions, auxiliary)) = some (bytes, words, nextConfig) := by
    simpa [compileEq] using compiled
  have targetNext : (t.compileOracle 1).1 = nextConfig := by
    have oracleEq := oracle.2.1
    have atOne := congrFun oracleEq 1
    simpa [BackendProps.pureCo, sourceNext] using congrArg Prod.fst atOne
  have fresh' : ∀ entry ∈ compileInc s.maxApp (expressions, auxiliary), sptLookup entry.1 t.code = none := by
    simpa only [targetHead] using fresh
  have nodup' : ((compileInc s.maxApp (expressions, auxiliary)).map Prod.fst).Nodup := by
    simpa only [targetHead] using nodup
  rw [program] at fresh' nodup' targetCompile
  refine ⟨start, body, tail, extracted, program, ?_⟩
  simp [BvlSem.doInstall, targetBytesDecoded, targetWordsDecoded, targetHead, program, targetCompile, targetNext]
  simpa [and_assoc] using And.intro fresh' nodup'

/-- A source installation that avoids a type error has valid decoded inputs,
a matching oracle compilation and the precise code/oracle/clock update.
The result may still be a timeout, which happens after that update. -/
theorem install_source_inv {C F : Type} (s next : ClosSem.State C F)
    (values : List ClosSem.Value) (result : Result (List ClosLang.Exp) ClosSem.Value)
    (run : ClosSem.doInstall values s = (result, next))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ sourceBytes sourceWords bytes words config expressions auxiliary nextConfig,
      values = [sourceBytes, sourceWords] ∧
      ClosSem.valueToBytes sourceBytes = some bytes ∧ ClosSem.valueToWords sourceWords = some words ∧
      s.compileOracle 0 = (config, expressions, auxiliary) ∧
      s.compile config (expressions, auxiliary) = some (bytes, words, nextConfig) ∧
      (s.compileOracle 1).1 = nextConfig ∧ expressions ≠ [] ∧
      (∀ index ∈ auxiliary.map Prod.fst, s.code.lookup index = none) ∧
      (auxiliary.map Prod.fst).Nodup ∧
      next = { s with
        code := s.code.updateListEq auxiliary
        compileOracle := Flapjack.holShiftSeq 1 s.compileOracle
        clock := s.clock - 1 } ∧
      result = if s.clock = 0 then .err (.abort .timeoutError) else .val expressions := by
  classical
  cases values with
  | nil =>
    simp [ClosSem.doInstall] at run
    exact False.elim (noType run.1.symm)
  | cons sourceBytes rest =>
    cases rest with
    | nil =>
      simp [ClosSem.doInstall] at run
      exact False.elim (noType run.1.symm)
    | cons sourceWords rest =>
      cases rest with
      | cons extra rest =>
        simp [ClosSem.doInstall] at run
        exact False.elim (noType run.1.symm)
      | nil =>
        cases bytesRun : ClosSem.valueToBytes sourceBytes with
        | none =>
          simp [ClosSem.doInstall, bytesRun] at run
          exact False.elim (noType run.1.symm)
        | some bytes =>
          cases wordsRun : ClosSem.valueToWords sourceWords with
          | none =>
            simp [ClosSem.doInstall, bytesRun, wordsRun] at run
            exact False.elim (noType run.1.symm)
          | some words =>
            cases oracleRun : s.compileOracle 0 with
            | mk config program =>
              cases program with
              | mk expressions auxiliary =>
                by_cases valid : (∀ index ∈ auxiliary.map Prod.fst, s.code.lookup index = none) ∧
                    (auxiliary.map Prod.fst).Nodup
                · cases compileRun : s.compile config (expressions, auxiliary) with
                  | none =>
                    simp only [ClosSem.doInstall, bytesRun, wordsRun, oracleRun] at run
                    rw [if_pos valid, compileRun] at run
                    simp only [Prod.mk.injEq] at run
                    exact False.elim (noType run.1.symm)
                  | some output =>
                    obtain ⟨compiledBytes, compiledWords, nextConfig⟩ := output
                    by_cases agrees : bytes = compiledBytes ∧ words = compiledWords ∧
                        (Flapjack.holShiftSeq 1 s.compileOracle 0).1 = nextConfig ∧ expressions ≠ []
                    · have step := run
                      simp only [ClosSem.doInstall, bytesRun, wordsRun, oracleRun] at step
                      rw [if_pos valid, compileRun] at step
                      dsimp only at step
                      rw [if_pos agrees] at step
                      have nextEq : next = { s with
                          code := s.code.updateListEq auxiliary
                          compileOracle := Flapjack.holShiftSeq 1 s.compileOracle
                          clock := s.clock - 1 } := by
                        by_cases clock : s.clock = 0
                        · rw [if_pos clock] at step
                          exact (congrArg Prod.snd step).symm
                        · rw [if_neg clock] at step
                          exact (congrArg Prod.snd step).symm
                      have resultEq : result = if s.clock = 0 then .err (.abort .timeoutError) else .val expressions := by
                        by_cases clock : s.clock = 0
                        · rw [if_pos clock] at step ⊢
                          exact (congrArg Prod.fst step).symm
                        · rw [if_neg clock] at step ⊢
                          exact (congrArg Prod.fst step).symm
                      refine ⟨sourceBytes, sourceWords, bytes, words, config, expressions, auxiliary, nextConfig,
                        rfl, bytesRun, wordsRun, rfl, ?_, ?_, agrees.2.2.2, valid.1, valid.2, nextEq, resultEq⟩
                      · simpa [agrees.1, agrees.2.1] using compileRun
                      · simpa [Flapjack.holShiftSeq] using agrees.2.2.1
                    · simp only [ClosSem.doInstall, bytesRun, wordsRun, oracleRun] at run
                      rw [if_pos valid, compileRun] at run
                      dsimp only at run
                      rw [if_neg agrees] at run
                      simp only [Prod.mk.injEq] at run
                      exact False.elim (noType run.1.symm)
                · simp only [ClosSem.doInstall, bytesRun, wordsRun, oracleRun] at run
                  rw [if_neg valid] at run
                  simp only [Prod.mk.injEq] at run
                  exact False.elim (noType run.1.symm)

/-- Every non-type-error source installation has a matching successful target
installation. Source timeout still installs code and shifts the oracle. -/
theorem install_dispatch {C F : Type} (s next : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (values : List ClosSem.Value) (targets : List BvlSem.Value)
    (result : Result (List ClosLang.Exp) ClosSem.Value)
    (run : ClosSem.doInstall values s = (result, next))
    (noType : result ≠ .err (.abort .typeError))
    (related : List.Forall₂ (vRel s.maxApp f t.refs t.code) values targets)
    (oracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle) :
    ∃ expressions auxiliary start body tail,
      result = (if s.clock = 0 then .err (.abort .timeoutError) else .val expressions) ∧
      next = { s with
        code := s.code.updateListEq auxiliary
        compileOracle := Flapjack.holShiftSeq 1 s.compileOracle
        clock := s.clock - 1 } ∧
      expressions ≠ [] ∧ (extractName expressions).1 = start ∧
      compileInc s.maxApp (expressions, auxiliary) = (start + numStubs s.maxApp, 0, body) :: tail ∧
      BvlSem.doInstall (R := BvlSem.Value) targets t =
        .val (.codePtr (start + numStubs s.maxApp), { t with
          code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
          compileOracle := fun n => t.compileOracle (n + 1) }) := by
  obtain ⟨sourceBytes, sourceWords, bytes, words, config, expressions, auxiliary, nextConfig,
    valuesEq, bytesRun, wordsRun, sourceHead, compiled, sourceNext, nonempty, _, _, nextEq, resultEq⟩ :=
      install_source_inv s next values result run noType
  subst values
  cases related with
  | cons bytesRel tail =>
    cases tail with
    | cons wordsRel tail =>
      cases tail
      obtain ⟨start, body, tail, extracted, program, targetRun⟩ :=
        install_target_run s t f sourceBytes sourceWords _ _ bytes words config nextConfig expressions auxiliary
          bytesRel wordsRel bytesRun wordsRun sourceHead sourceNext compiled oracle
      exact ⟨expressions, auxiliary, start, body, tail, resultEq, nextEq, nonempty, extracted, program, targetRun⟩

/-- Each indexed output expression comes from compiling the corresponding
source singleton, and its auxiliary output is installed whenever the final
accumulator is installed. This supports the new-code part of installation. -/
theorem compileExps_index_installed (maxApp : Nat) (expressions : List ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (code : Spt (Nat × Bvl.Exp)) (index : Nat) (source : ClosLang.Exp) (target : Bvl.Exp)
    (run : compileExpsHOL maxApp expressions aux = (compiled, finalAux))
    (sourceAt : expressions[index]? = some source) (targetAt : compiled[index]? = some target)
    (installed : codeInstalled finalAux code) :
    ∃ auxBefore auxAfter, compileExpsHOL maxApp [source] auxBefore = ([target], auxAfter) ∧
      codeInstalled auxAfter code := by
  induction expressions generalizing aux finalAux compiled index with
  | nil => simp at sourceAt
  | cons first rest ih =>
    cases firstRun : compileExpHOL maxApp first aux with
    | mk firstTarget middleAux =>
      cases restRun : compileExpListHOL maxApp rest middleAux with
      | mk restTargets lastAux =>
        have whole : compileExpsHOL maxApp (first :: rest) aux = (firstTarget :: restTargets, lastAux) := by
          simp [compileExps_eq_list, compileExpListHOL, firstRun, restRun]
        have equal := run.symm.trans whole
        cases equal
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceAt targetAt
          subst source
          subst target
          have tailRun : compileExpsHOL maxApp rest middleAux = (restTargets, finalAux) := by
            simpa [compileExps_eq_list] using restRun
          have firstInstalled := compileExps_codeInstalled maxApp rest middleAux finalAux restTargets code tailRun installed
          exact ⟨aux, middleAux, by simp [compileExps_eq_list, compileExpListHOL, firstRun], firstInstalled⟩
        | succ index =>
          simp only [List.getElem?_cons_succ] at sourceAt targetAt
          have tailRun : compileExpsHOL maxApp rest middleAux = (restTargets, finalAux) := by
            simpa [compileExps_eq_list] using restRun
          exact ih middleAux finalAux restTargets index tailRun sourceAt targetAt installed

/-- If a compiled program is installed, each source entry resolves at its
shifted target label and the auxiliary code for that entry is installed. -/
theorem compileProgExps_entry_installed (maxApp : Nat) (program : List (Nat × Nat × ClosLang.Exp))
    (code : Spt (Nat × Bvl.Exp)) (name arity : Nat) (source : ClosLang.Exp)
    (installed : codeInstalled (compileProgExpsHOL maxApp program) code)
    (member : (name, arity, source) ∈ program) :
    ∃ auxBefore target auxAfter,
      compileExpsHOL maxApp [source] auxBefore = ([target], auxAfter) ∧
      sptLookup (name + numStubs maxApp) code = some (arity, target) ∧ codeInstalled auxAfter code := by
  cases compiledRun : compileExpsHOL maxApp (program.map (fun (_, _, exp) => exp)) [] with
  | mk targets finalAux =>
    let entries := (program.zip targets).map (fun ((loc, args, _), exp) => (loc + numStubs maxApp, args, exp))
    have allInstalled : codeInstalled (entries ++ finalAux) code := by
      simpa [compileProgExpsHOL, compiledRun, entries] using installed
    have finalInstalled : codeInstalled finalAux code := by
      intro entry inAux
      exact allInstalled entry (List.mem_append_right entries inAux)
    obtain ⟨index, indexBound, sourceEq⟩ := List.mem_iff_getElem.mp member
    have targetLength : targets.length = program.length := by
      simpa using compileExps_length maxApp (program.map (fun (_, _, exp) => exp)) [] targets finalAux compiledRun
    have targetBound : index < targets.length := by omega
    let target := targets[index]
    have sourceAt : (program.map (fun (_, _, exp) => exp))[index]? = some source := by
      simp [List.getElem?_map, List.getElem?_eq_getElem indexBound, sourceEq]
    have targetAt : targets[index]? = some target := List.getElem?_eq_getElem targetBound
    obtain ⟨auxBefore, auxAfter, singleton, auxInstalled⟩ :=
      compileExps_index_installed maxApp (program.map (fun (_, _, exp) => exp)) [] finalAux targets
        code index source target compiledRun sourceAt targetAt finalInstalled
    have zipBound : index < (program.zip targets).length := by simp [List.length_zip]; omega
    have zipped : ((name, arity, source), target) ∈ program.zip targets := by
      apply List.mem_iff_getElem.mpr
      refine ⟨index, zipBound, ?_⟩
      simp [List.getElem_zip, sourceEq, target]
    have outputMember : (name + numStubs maxApp, arity, target) ∈ entries ++ finalAux := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨((name, arity, source), target), zipped, rfl⟩
    exact ⟨auxBefore, target, auxAfter, singleton, allInstalled _ outputMember, auxInstalled⟩

private theorem install_assoc_lookup {α : Type} (entries : List (Nat × α)) (key : Nat) (value : α)
    (distinct : (entries.map Prod.fst).Nodup) (member : (key, value) ∈ entries) :
    sptAListLookup key entries = some value := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    obtain ⟨other, payload⟩ := entry
    simp only [List.map_cons, List.nodup_cons] at distinct
    simp only [List.mem_cons] at member
    cases member with
    | inl same =>
      cases same
      simp [sptAListLookup]
    | inr inRest =>
      have different : key ≠ other := by
        intro equal
        subst other
        apply distinct.1
        exact List.mem_map.mpr ⟨(key, value), inRest, rfl⟩
      simp [sptAListLookup, different, ih distinct.2 inRest]

/-- Fresh, distinct target entries are all installed in the union of the old
code and the tree built from those entries. -/
theorem install_codeInstalled (code : Spt (Nat × Bvl.Exp)) (entries : List (Nat × Nat × Bvl.Exp))
    (distinct : (entries.map Prod.fst).Nodup)
    (fresh : ∀ entry ∈ entries, sptLookup entry.1 code = none) :
    codeInstalled entries (sptUnion code (sptFromAList entries)) := by
  intro entry member
  obtain ⟨key, arity, body⟩ := entry
  rw [sptLookup_sptUnion, fresh (key, arity, body) member, sptLookup_sptFromAList]
  exact install_assoc_lookup entries key (arity, body) distinct member

/-- Every auxiliary source entry in the next oracle program has a compiled
entry and installed auxiliary code after the target installation. -/
theorem install_auxiliary_entry {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (config : C) (expressions : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (name arity : Nat) (source : ClosLang.Exp)
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary))
    (member : (name, arity, source) ∈ auxiliary)
    (oracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle) :
    ∃ auxBefore target auxAfter,
      compileExpsHOL s.maxApp [source] auxBefore = ([target], auxAfter) ∧
      sptLookup (name + numStubs s.maxApp)
        (sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))) = some (arity, target) ∧
      codeInstalled auxAfter (sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))) := by
  obtain ⟨headEq, _, nodup, fresh⟩ := compileOracleInv_head s.maxApp s.code s.compile s.compileOracle
    t.code t.compile t.compileOracle oracle
  have targetHead : t.compileOracle 0 = (config, compileInc s.maxApp (expressions, auxiliary)) := by
    simpa [sourceHead, BackendProps.pureCo] using headEq
  have distinct : ((compileInc s.maxApp (expressions, auxiliary)).map Prod.fst).Nodup := by
    simpa [targetHead] using nodup
  have targetFresh : ∀ entry ∈ compileInc s.maxApp (expressions, auxiliary), sptLookup entry.1 t.code = none := by
    simpa [targetHead] using fresh
  have installed := install_codeInstalled t.code (compileInc s.maxApp (expressions, auxiliary)) distinct targetFresh
  cases extract : extractName expressions with
  | mk start body =>
    have installed' : codeInstalled (compileProgExpsHOL s.maxApp (chainExps start body ++ auxiliary))
        (sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))) := by
      simpa [compileInc, extract] using installed
    exact compileProgExps_entry_installed s.maxApp (chainExps start body ++ auxiliary) _ name arity source installed'
      (List.mem_append_right _ member)

end Flapjack.Compiler.Backend.ClosToBvl
