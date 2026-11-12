module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.BlockList
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WordRelation
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshTargetRefs
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InstalledCode.Original
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Apply

@[expose] public section

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

/-- Every source chain begins with a zero-arity entry. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_exps_cons"]
theorem chainExps_cons (n : Nat) (expressions : List ClosLang.Exp) :
    ∃ k1 k2 other, chainExps n expressions = (k1, 0, k2) :: other := by
  cases expressions with
  | nil => simp [chainExps]
  | cons first rest => cases rest <;> simp [chainExps]

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
    · simpa [compileInc, extractNameSource_eq_extractName, extract, chainEq] using compiled

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

/-- Fresh, distinct target entries are all installed in the union of the old
code and the tree built from those entries. This Flapjack-specific composition
reuses the HOL association-list and disjoint-union theorems at installation sites. -/
theorem install_codeInstalled (code : Spt (Nat × Bvl.Exp)) (entries : List (Nat × Nat × Bvl.Exp))
    (distinct : (entries.map Prod.fst).Nodup)
    (fresh : ∀ entry ∈ entries, sptLookup entry.1 code = none) :
    codeInstalled entries (sptUnion code (sptFromAList entries)) := by
  apply codeInstalled_union entries (sptFromAList entries) code
  constructor
  · exact codeInstalled_fromAList_strong entries entries ⟨distinct, List.infix_refl entries⟩
  · intro key ⟨member, present⟩
    obtain ⟨entry, entryMember, entryKey⟩ := List.mem_map.mp member
    obtain ⟨value, lookup⟩ := (sptMem_iff_lookup _ _).1 present
    have absent := fresh entry entryMember
    rw [entryKey, lookup] at absent
    contradiction

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
      simpa [compileInc, extractNameSource_eq_extractName, extract] using installed
    exact compileProgExps_entry_installed s.maxApp (chainExps start body ++ auxiliary) _ name arity source installed'
      (List.mem_append_right _ member)

/-- A source lookup after installation either names one of the installed
entries or was already present in the source code. -/
theorem install_source_lookup (s : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (entries : List (Nat × Nat × ClosLang.Exp)) (name arity : Nat) (body : ClosLang.Exp)
    (found : (s.updateListEq entries).lookup name = some (arity, body)) :
    (name, arity, body) ∈ entries ∨ s.lookup name = some (arity, body) := by
  rw [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_eq_FUPDATE_LIST] at found
  have split := flookupFupdateList_mem_or_base s.lookup entries name (arity, body) found
  cases split with
  | inl fromEntries =>
    obtain ⟨entry, member, keyEq, valueEq⟩ := fromEntries
    cases entry with
    | mk key value =>
      dsimp only at keyEq valueEq
      subst key
      subst value
      exact Or.inl member
  | inr fromBase => exact Or.inr fromBase

/-- The source-code correspondence is preserved by installing the next
oracle program, both for existing and newly added entries. -/
theorem install_code_relation {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (config : C) (expressions : List ClosLang.Exp)
    (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary))
    (states : stateRel f s t) :
    ∀ name arity body, (s.code.updateListEq auxiliary).lookup name = some (arity, body) →
      ∃ auxBefore target auxAfter,
        compileExpsHOL s.maxApp [body] auxBefore = ([target], auxAfter) ∧
        sptLookup (name + numStubs s.maxApp)
          (sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))) = some (arity, target) ∧
        codeInstalled auxAfter (sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, oracle, oldCode⟩ := states
  intro name arity body found
  cases install_source_lookup s.code auxiliary name arity body found with
  | inl newEntry =>
    exact install_auxiliary_entry s t config expressions auxiliary name arity body sourceHead newEntry oracle
  | inr oldEntry =>
    obtain ⟨auxBefore, target, auxAfter, compiled, lookup, installed⟩ := oldCode name arity body oldEntry
    have growth := sptSubsptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
    refine ⟨auxBefore, target, auxAfter, compiled, ?_, codeInstalled_subspt installed growth⟩
    exact (sptSubsptLookup _ _).1 growth _ _ lookup

/-- Installing an oracle program preserves the candidate source/target state
relation, including old values, newly compiled code and the shifted oracle. -/
theorem install_stateRel {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (config : C) (expressions : List ClosLang.Exp)
    (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary))
    (states : stateRel f s t) :
    stateRel f { s with
      code := s.code.updateListEq auxiliary
      compileOracle := Flapjack.holShiftSeq 1 s.compileOracle
      clock := s.clock - 1 } { t with
      code := sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))
      compileOracle := fun n => t.compileOracle (n + 1) } := by
  have codeRel := install_code_relation s t f config expressions auxiliary sourceHead states
  obtain ⟨ffi, globals, table, injective, notFrozen, sourceDomain, targetDomain, cells,
    generic, partialCode, force, oracle, oldCode⟩ := states
  let added := sptFromAList (compileInc s.maxApp (expressions, auxiliary))
  have growth : sptSubspt t.code (sptUnion t.code added) := sptSubsptUnion _ _
  have valuesGrow : ∀ a b, vRel s.maxApp f t.refs t.code a b → vRel s.maxApp f t.refs (sptUnion t.code added) a b := by
    intro a b related
    exact vRel_subspt f t.refs ⟨related, growth⟩
  have shift := compileOracleInv_shift s.maxApp s.code (s.code.updateListEq auxiliary)
    s.compile s.compileOracle t.code t.compile t.compileOracle oracle
  have oracleHead : t.compileOracle 0 = (config, compileInc s.maxApp (expressions, auxiliary)) := by
    have invHead := (compileOracleInv_head s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle oracle).1
    simpa [sourceHead, BackendProps.pureCo] using invHead
  refine ⟨ffi, ?_, table, injective, notFrozen, sourceDomain, targetDomain, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply globals.imp
    intro source target related
    cases source <;> cases target <;> simp only [optionValueRel] at related ⊢
    exact valuesGrow _ _ related
  · intro index source found
    obtain ⟨target, ptr, mapped, targetLookup, cellRel⟩ := cells index source found
    exact ⟨target, ptr, mapped, targetLookup, refRel_mono valuesGrow source target cellRel⟩
  · intro n bound
    exact (sptSubsptLookup _ _).1 growth _ _ (generic n bound)
  · intro total n bound
    exact (sptSubsptLookup _ _).1 growth _ _ (partialCode total n bound)
  · exact (sptSubsptLookup _ _).1 growth _ _ force
  · change compileOracleInv s.maxApp (s.code.updateListEq auxiliary) s.compile
      (fun n => s.compileOracle (n + 1))
      (sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))) t.compile
      (fun n => t.compileOracle (n + 1))
    simpa [added, oracleHead] using shift
  · exact codeRel

/-- Installing the oracle's auxiliary entries preserves the required location
and captured-variable annotations on all source code. -/
theorem install_codeAnnotations {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (config : C) (expressions : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary))
    (annotations : codeAnnotations s)
    (oracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle) :
    codeAnnotations { s with code := s.code.updateListEq auxiliary } := by
  have oracleAnnotations := oracle.2.2.2.2 0 config expressions auxiliary sourceHead
  have newLocations : ∀ entry ∈ auxiliary, ClosProps.everyFnLocationSome [entry.2.2] := by
    exact oracleAnnotations.2.2.1
  have newVars : ∀ entry ∈ auxiliary, ClosProps.everyFnVarsSome [entry.2.2] := by
    exact oracleAnnotations.2.2.2
  constructor
  · intro name arity body found
    cases install_source_lookup s.code auxiliary name arity body found with
    | inl member => exact newLocations (name, arity, body) member
    | inr old => exact annotations.1 name arity body old
  · intro name arity body found
    cases install_source_lookup s.code auxiliary name arity body found with
    | inl member => exact newVars (name, arity, body) member
    | inr old => exact annotations.2 name arity body old

/-- The next installation's compiled main entry can be called indirectly
with no arguments in the extended target code. -/
theorem install_main_findCode {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (config : C) (expressions : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary))
    (oracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle) :
    ∃ start body tail,
      (extractName expressions).1 = start ∧
      compileInc s.maxApp (expressions, auxiliary) = (start + numStubs s.maxApp, 0, body) :: tail ∧
      BvlSem.findCode none [.codePtr (start + numStubs s.maxApp)]
        (sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))) = some ([], body) := by
  obtain ⟨start, body, tail, extracted, program⟩ := compileInc_head s.maxApp (expressions, auxiliary)
  obtain ⟨headEq, _, nodup, fresh⟩ := compileOracleInv_head s.maxApp s.code s.compile s.compileOracle
    t.code t.compile t.compileOracle oracle
  have targetHead : t.compileOracle 0 = (config, compileInc s.maxApp (expressions, auxiliary)) := by
    simpa [sourceHead, BackendProps.pureCo] using headEq
  have distinct : ((compileInc s.maxApp (expressions, auxiliary)).map Prod.fst).Nodup := by
    simpa [targetHead] using nodup
  have targetFresh : ∀ entry ∈ compileInc s.maxApp (expressions, auxiliary), sptLookup entry.1 t.code = none := by
    simpa [targetHead] using fresh
  have installed := install_codeInstalled t.code (compileInc s.maxApp (expressions, auxiliary)) distinct targetFresh
  have member : (start + numStubs s.maxApp, 0, body) ∈ compileInc s.maxApp (expressions, auxiliary) := by
    rw [program]
    simp
  have lookup := installed (start + numStubs s.maxApp, 0, body) member
  refine ⟨start, body, tail, extracted, program, ?_⟩
  simp [BvlSem.findCode, Flapjack.holLast, lookup]

/-- After the installation primitive succeeds and returns a resolvable main
entry, the generated target expression either times out or enters that entry. -/
theorem evaluate_install_target_call {C F : Type}
    (s middle next : BvlSem.State C F) (env : List BvlSem.Value)
    (args : List Bvl.Exp) (values : List BvlSem.Value) (address : Nat) (body : Bvl.Exp)
    (argsRun : BvlSem.evaluate args env s = (.val values, middle))
    (installed : BvlSem.doInstall (R := BvlSem.Value) values.reverse middle = .val (.codePtr address, next))
    (mainFound : BvlSem.findCode none [.codePtr address] next.code = some ([], body)) :
    BvlSem.evaluate [.call 0 none [.op .install args]] env s =
      if next.clock = 0 then (.err (.abort .timeoutError), { next with clock := 0 })
      else BvlSem.evaluate [body] [] (BvlSem.decClock 1 next) := by
  have opRun : BvlSem.evaluate [.op .install args] env s = (.val [.codePtr address], next) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun]
    simp [BvlSem.doApp, installed]
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, opRun]
  simp [mainFound]

/-- Adding chain calls changes the generated
expressions but leaves the compiler's auxiliary-code accumulator unchanged. -/
theorem compileExps_chain_aux (maxApp : Nat) (expressions : List ClosLang.Exp)
    (start : Nat) (aux : List (Nat × Nat × Bvl.Exp)) :
    (compileExpsHOL maxApp ((chainExps start expressions).map (fun (_, _, exp) => exp)) aux).2 =
      (compileExpsHOL maxApp expressions aux).2 := by
  induction expressions generalizing start aux with
  | nil => simp [chainExps, compileExps_eq_list, compileExpListHOL, compileExpHOL]
  | cons first rest ih =>
    cases rest with
    | nil => simp [chainExps]
    | cons second tail =>
      cases firstRun : compileExpHOL maxApp first aux with
      | mk target middle =>
        have tailEq := ih (start + 1) middle
        simp only [compileExps_eq_list] at tailEq ⊢
        simpa [chainExps, compileExpListHOL, compileExpHOL, firstRun] using tailEq

/-- Compiling a nonempty chain and its original expressions produces the same
final auxiliary accumulator from the same initial accumulator. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_chain_exps_cons"]
theorem compileExps_chainExps_cons (maxApp start : Nat) (first : ClosLang.Exp)
    (rest : List ClosLang.Exp) (initial : List (Nat × Nat × Bvl.Exp))
    (newExps : List Bvl.Exp) (aux : List (Nat × Nat × Bvl.Exp))
    (compiled : List Bvl.Exp) (originalAux : List (Nat × Nat × Bvl.Exp))
    (premises : compileExpsHOL maxApp ((chainExps start (first :: rest)).map (fun (_, _, exp) => exp)) initial =
        (newExps, aux) ∧
      compileExpsHOL maxApp (first :: rest) initial = (compiled, originalAux)) :
    originalAux = aux := by
  have same := compileExps_chain_aux maxApp (first :: rest) start initial
  simpa only [premises.1, premises.2] using same.symm

/-- Removing an entry-name marker does not change generated auxiliary code. -/
theorem extractName_aux (maxApp : Nat) (expressions : List ClosLang.Exp)
    (start : Nat) (real : List ClosLang.Exp) (aux : List (Nat × Nat × Bvl.Exp))
    (extract : extractName expressions = (start, real)) :
    (compileExpsHOL maxApp expressions aux).2 = (compileExpsHOL maxApp real aux).2 := by
  unfold extractName at extract
  split at extract
  · rename_i trace n rest
    split at extract
    · cases extract
      rfl
    · cases extract
      simp [compileExps_eq_list, compileExpListHOL, compileExpHOL]
  · cases extract
    rfl

/-- Extracting an entry name from a nonempty program retains a nonempty body. -/
theorem extractName_nonempty (expressions : List ClosLang.Exp) (start : Nat)
    (real : List ClosLang.Exp) (extract : extractName expressions = (start, real))
    (nonempty : expressions ≠ []) : real ≠ [] := by
  unfold extractName at extract
  split at extract
  · rename_i trace n rest
    split at extract
    · cases extract
      exact nonempty
    · rename_i notEmpty
      cases extract
      cases real <;> simp_all
  · cases extract
    exact nonempty

/-- Name extraction and chaining preserve the original auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_same_aux"]
theorem compileExps_same_aux (maxApp start : Nat) (real expressions : List ClosLang.Exp)
    (newExps compiled : List Bvl.Exp) (aux originalAux : List (Nat × Nat × Bvl.Exp))
    (premises : compileExpsHOL maxApp ((chainExps start real).map (fun (_, _, exp) => exp)) [] = (newExps, aux) ∧
      extractName expressions = (start, real) ∧
      compileExpsHOL maxApp expressions [] = (compiled, originalAux)) : originalAux = aux := by
  obtain ⟨chainRun, extract, originalRun⟩ := premises
  have same := compileExps_chain_aux maxApp real start []
  have extractSame := extractName_aux maxApp expressions start real [] extract
  simp only [chainRun, originalRun] at same extractSame
  exact extractSame.trans same.symm

/-- Compiling concatenated expression lists threads the same auxiliary state
as compiling each list in sequence. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_APPEND"]
theorem compileExps_append (maxApp : Nat) (left right : List ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) :
    compileExpsHOL maxApp (left ++ right) aux =
      let (first, middle) := compileExpsHOL maxApp left aux
      let (second, finalAux) := compileExpsHOL maxApp right middle
      (first ++ second, finalAux) := by
  simp only [compileExps_eq_list]
  induction left generalizing aux with
  | nil => simp [compileExpListHOL]
  | cons first rest ih =>
    cases firstRun : compileExpHOL maxApp first aux with
    | mk target middle =>
      cases restRun : compileExpListHOL maxApp rest middle with
      | mk compiled lastAux =>
        cases rightRun : compileExpListHOL maxApp right lastAux with
        | mk other finalAux =>
          have step := ih middle
          simp [restRun, rightRun] at step
          simp [compileExpListHOL, firstRun, step, restRun, rightRun]

/-- Auxiliary code from the original program occurs in the compilation of
the extracted chain followed by additional expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_twice_IS_SUBLIST"]
theorem compileExps_twice_isSublist (expressions real additional : List ClosLang.Exp)
    (start maxApp : Nat) (newExps compiled : List Bvl.Exp)
    (aux originalAux : List (Nat × Nat × Bvl.Exp))
    (premises : extractName expressions = (start, real) ∧
      compileExpsHOL maxApp ((chainExps start real).map (fun (_, _, exp) => exp) ++ additional) [] =
        (newExps, aux) ∧
      compileExpsHOL maxApp expressions [] = (compiled, originalAux)) :
    originalAux <:+: aux := by
  obtain ⟨extract, whole, originalRun⟩ := premises
  cases chainRun : compileExpsHOL maxApp ((chainExps start real).map (fun (_, _, exp) => exp)) [] with
  | mk chainTargets chainAux =>
    cases extraRun : compileExpsHOL maxApp additional chainAux with
    | mk extraTargets finalAux =>
      have pairEq : (chainTargets ++ extraTargets, finalAux) = (newExps, aux) := by
        simpa [compileExps_append, chainRun, extraRun] using whole
      cases pairEq
      have same := compileExps_same_aux maxApp start real expressions chainTargets compiled chainAux originalAux
        ⟨chainRun, extract, originalRun⟩
      have suffix := compileExps_acc maxApp additional chainAux
      rw [extraRun] at suffix
      obtain ⟨_, added, finalEq⟩ := suffix
      have included : chainAux <:+ aux := ⟨added, finalEq.symm⟩
      simpa [same] using included.isInfix

/-- Installing the incremental program also installs its original auxiliary code. -/
theorem compileInc_original_aux_installed (maxApp : Nat) (expressions : List ClosLang.Exp)
    (auxiliary : List (Nat × Nat × ClosLang.Exp)) (compiled : List Bvl.Exp)
    (originalAux : List (Nat × Nat × Bvl.Exp)) (code : Spt (Nat × Bvl.Exp))
    (originalRun : compileExpsHOL maxApp expressions [] = (compiled, originalAux))
    (installed : codeInstalled (compileInc maxApp (expressions, auxiliary)) code) :
    codeInstalled originalAux code := by
  cases extract : extractName expressions with
  | mk start real =>
    cases whole : compileExpsHOL maxApp
        ((chainExps start real).map (fun (_, _, exp) => exp) ++
          auxiliary.map (fun (_, _, exp) => exp)) [] with
    | mk targets finalAux =>
      have included := compileExps_twice_isSublist expressions real
        (auxiliary.map (fun (_, _, exp) => exp)) start maxApp targets compiled finalAux originalAux
        ⟨extract, whole, originalRun⟩
      have installed' : codeInstalled
          ((((chainExps start real ++ auxiliary).zip targets).map
            (fun ((loc, args, _), exp) => (loc + numStubs maxApp, args, exp))) ++ finalAux) code := by
        simpa [compileInc, extractNameSource_eq_extractName, extract, compileProgExpsHOL,
          List.map_append, whole] using installed
      intro entry member
      exact installed' entry (List.mem_append_right _ (included.sublist.subset member))

/-- After target installation, the original main program's auxiliary code is installed. -/
theorem install_original_aux_installed {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (config : C) (expressions : List ClosLang.Exp) (auxiliary : List (Nat × Nat × ClosLang.Exp))
    (compiled : List Bvl.Exp) (originalAux : List (Nat × Nat × Bvl.Exp))
    (sourceHead : s.compileOracle 0 = (config, expressions, auxiliary))
    (originalRun : compileExpsHOL s.maxApp expressions [] = (compiled, originalAux))
    (oracle : compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle) :
    codeInstalled originalAux (sptUnion t.code (sptFromAList (compileInc s.maxApp (expressions, auxiliary)))) := by
  obtain ⟨headEq, _, nodup, fresh⟩ := compileOracleInv_head s.maxApp s.code s.compile s.compileOracle
    t.code t.compile t.compileOracle oracle
  have targetHead : t.compileOracle 0 = (config, compileInc s.maxApp (expressions, auxiliary)) := by
    simpa [sourceHead, BackendProps.pureCo] using headEq
  have distinct : ((compileInc s.maxApp (expressions, auxiliary)).map Prod.fst).Nodup := by
    simpa [targetHead] using nodup
  have targetFresh : ∀ entry ∈ compileInc s.maxApp (expressions, auxiliary), sptLookup entry.1 t.code = none := by
    simpa [targetHead] using fresh
  have installed := install_codeInstalled t.code (compileInc s.maxApp (expressions, auxiliary)) distinct targetFresh
  exact compileInc_original_aux_installed s.maxApp expressions auxiliary compiled originalAux _ originalRun installed

end Flapjack.Compiler.Backend.ClosToBvl
