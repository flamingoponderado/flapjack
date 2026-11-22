module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.SemanticsDraft
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelInit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Limits
public import Flapjack.Compiler.Backend.WordToWord.Proofs.Syntactic
public import Flapjack.Compiler.Backend.Semantics.DataProps.SemanticsZeroLimits
public import Flapjack.Compiler.Backend.Semantics.DataProps.StackMaxLimit
public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateLimitsSwap
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMaxClock
public import Flapjack.Compiler.Backend.DataToWord.Proofs.OptionLe

@[expose] public section

/-! `compile_semantics` (`data_to_wordProofScript.sml` lines 1785-1915) from the
statement of `compile_correct`, and drafts of `compile_semantics_lemma`,
`compile_semantics_precise_lemma`, `compile_semantics_precise` and
`compile_semantics` taking the not-yet-ported `Assign` case of
`data_compile_correct` as their only extra hypothesis. Flapjack proof
infrastructure, not HOL ports: once `assign_thm` lands, discharging
`assignCase` gives the tagged theorems. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.SemanticsDraft
open Flapjack Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The heap length of `init_store_ok` encodes its limit exactly: the arithmetic step of
HOL's `compile_semantics` proof. -/
theorem heapArith {width : Nat} [NeZero width] (c : Config) (good : goodDimindex width)
    (limit : Nat) (le : limit ≤ maxHeapLimit width c) :
    limit * (wordSemBytesInWord : BitVec width).toNat < 2 ^ width ∧
    (wordSemBytesInWord * BitVec.ofNat width limit : BitVec width).toNat / (width / 8) = limit := by
  have hmax : limit * 2 ^ (wordShiftAmount width + 1) ≤ 2 ^ width := by
    have := le.trans (Nat.min_le_right _ _)
    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mp this
  rcases good with rfl | rfl
  · simp only [wordShiftAmount, if_true] at hmax
    have h : limit * 4 < 2 ^ 32 := by omega
    refine ⟨by simpa [wordSemBytesInWord] using h, ?_⟩
    simp [wordSemBytesInWord, BitVec.toNat_mul]
    omega
  · simp only [wordShiftAmount, show (64 : Nat) ≠ 32 by decide, if_false] at hmax
    have h : limit * 8 < 2 ^ 64 := by omega
    refine ⟨by simpa [wordSemBytesInWord] using h, ?_⟩
    simp [wordSemBytesInWord, BitVec.toNat_mul]
    omega

/-- The initial `state_rel_ext` established in HOL's `compile_semantics` proof, via
`state_rel_init`. -/
theorem stateRelExt_init {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (c : Config)
    (prog : List (Nat × Nat × DataLang.Prog)) (x1 : Spt (Nat × WordLangProgHOL (BitVec width)))
    (co : DataSem.CompileOracle C)
    (tcc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (tco : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (tt : Bool) (kk aa : Nat) (coo : Compiler.Encoders.Asm.AsmConfigExact width)
    (hhandler : t.handler = 0) (hgc : t.gcFun = WordGcFunctions.wordGcFun c)
    (init : initStoreOk c t.store t.memory t.mdomain t.codeBuffer t.dataBuffer)
    (good : goodDimindex width) (hloc : sptLookup 0 t.locals = some (.loc 1 0))
    (hstack : t.stack = []) (conf : confOk width c) (hdep : t.termdep = 0)
    (hcode : codeRel c (sptFromAList prog) x1)
    (htco : tco = Prod.map id (List.map (compilePart c)) ∘ co)
    (stubs : ∀ n, ∀ entry ∈ (co n).2, dataNumStubs ≤ entry.1)
    (hext : WordToWord.codeRelExt x1 t.code) (hdom : sptDomain x1 = sptDomain t.code)
    (hbe : t.be = c.be) (hmax : t.stackMax = some 1) (hlsize : t.localsSize = some 0)
    (horacle : t.compileOracle =
      Prod.map id (List.map (fun p => WordToWord.fullCompileSingle tt kk aa coo (p, none))) ∘ tco)
    (htcc : tcc = fun conf progs =>
      t.compile conf (progs.map (fun p => WordToWord.fullCompileSingle tt kk aa coo (p, none)))) :
    stateRelExt c 1 0
      (DataSem.initialState t.ffi (sptFromAList prog) co
        (fun cfg => Option.map (Prod.map id (Prod.map (List.map upperW2w) id)) ∘ tcc cfg ∘
          List.map (compilePart c))
        true (getLimits c t) t.stackSize t.clock) t := by
  have init' := init
  obtain ⟨limit, curr, limitLe, -, -, -, -, -, -, -, -, heapLen, codeBuf, codeBufEnd, bitBuf,
    bitBufEnd, codeEmpty, dataEmpty, -, -⟩ := init
  obtain ⟨arith, heapDiv⟩ := heapArith c good limit limitLe
  have heapLimit : (getLimits c t).heapLimit = limit := by
    rw [getLimits_heap_of_lookup c t _ heapLen, heapDiv]
  let t2 : WordSemStateFiniteExact width C F :=
    { t with code := x1, termdep := 2, compileOracle := tco, compile := tcc }
  refine ⟨t2, t.code, ?_, hdom, by simp [t2], ⟨tt, kk, aa, coo, horacle, htcc⟩, ?_, ?_⟩
  · refine stateRel_init t2 t.ffi c (sptFromAList prog) _ co 1 0 (getLimits c t)
      ⟨rfl, hhandler, hgc, hcode, ?_, good, hloc, hstack, hmax, hlsize, rfl, rfl, hbe.symm,
        by simp [getLimits], by rw [heapLimit]; exact arith, ?_, rfl, rfl, conf, ?_⟩
    · refine ⟨codeEmpty, dataEmpty, codeBuf, codeBufEnd, bitBuf, bitBufEnd, ?_, ?_, stubs⟩
      · funext cfg program
        show Option.map _ (tcc cfg (program.map (compilePart c))) =
          Option.map _ (tcc cfg (program.map (compilePart c)))
        rcases tcc cfg (program.map (compilePart c)) with _ | ⟨bytes, words, next⟩ <;> rfl
      · show tco = _
        rw [htco]
        funext n
        rfl
    · rw [heapLimit, holFapply_of_lookup heapLen]
    · exact init'
  · intro n v hv
    obtain ⟨t', k', a', c', col, h⟩ := hext n v.1 v.2 hv.symm
    exact ⟨t', k', a', c', col, h.symm⟩
  · change t = { t with termdep := 0 }
    cases t
    simp only at hdep
    subst hdep
    rfl

/-- `compile_semantics` from the statement of `compile_correct`. -/
theorem compileSemantics_of_compileCorrect {width : Nat} [NeZero width] {C F : Type}
    (compileCorrect : CompileCorrectStmt width C F)
    (t : WordSemStateFiniteExact width C F) (c : Config)
    (prog : List (Nat × Nat × DataLang.Prog)) (x1 : Spt (Nat × WordLangProgHOL (BitVec width)))
    (cc : DataSem.Compiler C)
    (tcc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (tco : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (co : DataSem.CompileOracle C)
    (tt : Bool) (kk aa : Nat) (coo : Compiler.Encoders.Asm.AsmConfigExact width)
    (fs : Spt Nat) (start : Nat)
    (h : t.handler = 0 ∧ t.gcFun = WordGcFunctions.wordGcFun c ∧
      initStoreOk c t.store t.memory t.mdomain t.codeBuffer t.dataBuffer ∧
      goodDimindex width ∧ sptLookup 0 t.locals = some (.loc 1 0) ∧ t.stack = [] ∧
      confOk width c ∧ t.termdep = 0 ∧ codeRel c (sptFromAList prog) x1 ∧
      cc = (fun cfg => Option.map (Prod.map id (Prod.map (List.map upperW2w) id)) ∘ tcc cfg ∘
        List.map (compilePart c)) ∧
      tco = Prod.map id (List.map (compilePart c)) ∘ co ∧
      (∀ n, ∀ entry ∈ (co n).2, dataNumStubs ≤ entry.1) ∧
      WordToWord.codeRelExt x1 t.code ∧ sptDomain x1 = sptDomain t.code ∧ t.be = c.be ∧
      t.stackMax = some 1 ∧ t.localsSize = some 0 ∧ t.stackLimit ≠ 0 ∧
      t.compileOracle =
        Prod.map id (List.map (fun p => WordToWord.fullCompileSingle tt kk aa coo (p, none))) ∘ tco ∧
      tcc = (fun conf progs =>
        t.compile conf (progs.map (fun p => WordToWord.fullCompileSingle tt kk aa coo (p, none)))) ∧
      fs = t.stackSize ∧
      HolBehaviour.fail ≠
        DataSem.semantics t.ffi (sptFromAList prog) co cc DataProps.zeroLimits fs start) :
    (DataSem.dataLangSafeForSpace t.ffi (sptFromAList prog) (getLimits c t) fs start ∧
        c.gcKind ≠ .none →
      WordSemStateFiniteExact.wordLangSafeForSpace t start) ∧
    (open Classical in
    SemanticsPropsHOL.extendWithResourceLimitPrimeHOL
      (decide (DataSem.dataLangSafeForSpace t.ffi (sptFromAList prog) (getLimits c t) fs start ∧
        c.gcKind ≠ .none))
      (fun b => b = DataSem.semantics t.ffi (sptFromAList prog) co cc DataProps.zeroLimits fs start)
      (WordSemStateFiniteExact.semantics t start)) := by
  classical
  obtain ⟨hhandler, hgc, init, good, hloc, hstack, conf, hdep, hcode, hcc, htco, stubs, hext,
    hdom, hbe, hmax, hlsize, hlimit, horacle, htcc, hfs, notFail⟩ := h
  subst hcc hfs
  have related := stateRelExt_init t c prog x1 co tcc tco tt kk aa coo hhandler hgc init good hloc
    hstack conf hdep hcode htco stubs hext hdom hbe hmax hlsize horacle htcc
  have semEq : ∀ (cc' : DataSem.Compiler C),
      DataSem.semantics t.ffi (sptFromAList prog) co cc' (getLimits c t) t.stackSize start =
      DataSem.semantics t.ffi (sptFromAList prog) co cc' DataProps.zeroLimits t.stackSize start := by
    intro cc'
    rw [DataProps.semantics_zero_limits _ _ _ _ (getLimits c t),
      DataProps.semantics_zero_limits _ _ _ _ DataProps.zeroLimits t.stackSize]
  have notFail' := notFail
  rw [← semEq] at notFail'
  have sim := entrySim_of_compileCorrect compileCorrect c t.ffi _ co _ (getLimits c t) start t
    related
  refine ⟨?_, ?_⟩
  · rintro ⟨safe, -⟩ k res t' run
    have hk := safe k
    rcases unitRun : DataSem.evaluate (.call none (some start) [] none)
        (DataSem.initialState t.ffi (sptFromAList prog)
          (@holArb (DataSem.CompileOracle Unit) ⟨fun _ => ((), [])⟩)
          (@holArb (DataSem.Compiler Unit) ⟨fun _ _ => none⟩) true (getLimits c t) t.stackSize k)
      with ⟨r, s⟩
    rw [unitRun] at hk
    obtain ⟨s1, actualRun, diff⟩ := DataProps.evaluate_cc_co_only_diff _ _ r s
      (DataSem.initialState t.ffi (sptFromAList prog) co _ true (getLimits c t) t.stackSize k)
      ⟨unitRun, hk, by simp [DataProps.ccCoOnlyDiff, DataSem.initialState]⟩
    have notType := dataNotTypeError t.ffi _ co _ (getLimits c t) _ start (Ne.symm notFail') k
    rw [dataEntry, actualRun] at notType
    obtain ⟨ck, t1, res1, wordRun, maxLe, -⟩ := sim k r s1 actualRun notType
    have grows := WordSemStateFiniteExact.evaluate_stack_max_only_grows _ {t with clock := k} res t'
      ck res1 t1 ⟨run, wordRun⟩
    have dataBound := DataProps.evaluate_stackMax_le_stackLimit _ _ r s
      ⟨unitRun, hk, by simp [DataSem.initialState, BackendProps.optionLe, getLimits]; omega⟩
    have dataLimit := DataProps.evaluate_stack_limit _ _ r s unitRun
    have wordLimit := WordSemStateFiniteExact.evaluate_stack_limit _ _ res t' run
    have chain := BackendProps.optionLe_trans _ _ _ ⟨grows, BackendProps.optionLe_trans _ _ _
      ⟨maxLe, by rw [← diff.2.2.2.1]; exact dataBound⟩⟩
    rw [dataLimit] at chain
    obtain ⟨m, hm, hle⟩ := (optionLe_SOME _ _).mp chain
    exact ⟨m, hm, by rw [wordLimit]; simpa [DataSem.initialState, getLimits] using hle⟩
  · by_cases precise : DataSem.dataLangSafeForSpace t.ffi (sptFromAList prog) (getLimits c t)
        t.stackSize start ∧ c.gcKind ≠ .none
    · simp only [SemanticsPropsHOL.extendWithResourceLimitPrimeHOL, decide_eq_true precise, if_true]
      rw [← semEq]
      exact semanticsEqOfEntrySim c t.ffi _ co _ (getLimits c t) _ start t sim (Ne.symm notFail')
        precise.2 (safeAtEveryClock t.ffi _ co _ _ _ start precise.1)
    · simp only [SemanticsPropsHOL.extendWithResourceLimitPrimeHOL, decide_eq_false precise,
        Bool.false_eq_true, if_false]
      rw [← semEq]
      exact semanticsOfEntrySim c t.ffi _ co _ (getLimits c t) _ start t sim (Ne.symm notFail')

/-- `compile_semantics_lemma`, modulo the `Assign` case of `data_compile_correct`. -/
theorem compileSemanticsLemma_of_assign {width : Nat} [NeZero width] {C F : Type}
    (assignCase : ∀ (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
      (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) (.assign dest op names live) s)
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
    (prog : List (Nat × Nat × DataLang.Prog)) (co : DataSem.CompileOracle C)
    (cc : DataSem.Compiler C) (lims : DataSem.Limits) (t : WordSemStateFiniteExact width C F)
    (fs : Spt Nat) (start : Nat)
    (h : stateRelExt conf 1 0
        (DataSem.initialState ffi (sptFromAList prog) co cc true lims t.stackSize t.clock) t ∧
      fs = t.stackSize ∧
      DataSem.semantics ffi (sptFromAList prog) co cc lims fs start ≠ .fail) :
    SemanticsPropsHOL.extendWithResourceLimitHOL
      (fun b => b = DataSem.semantics ffi (sptFromAList prog) co cc lims fs start)
      (WordSemStateFiniteExact.semantics t start) :=
  compileSemanticsLemma_of_compileCorrect (compileCorrectStmt_of_assign assignCase) conf ffi prog co cc lims t fs start h

/-- `compile_semantics_precise_lemma`, modulo the `Assign` case of `data_compile_correct`. -/
theorem compileSemanticsPreciseLemma_of_assign {width : Nat} [NeZero width] {C F : Type}
    (assignCase : ∀ (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
      (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) (.assign dest op names live) s)
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
    (prog : List (Nat × Nat × DataLang.Prog)) (co : DataSem.CompileOracle C)
    (cc : DataSem.Compiler C) (lims : DataSem.Limits) (t : WordSemStateFiniteExact width C F)
    (fs : Spt Nat) (start : Nat)
    (h : stateRelExt conf 1 0
        (DataSem.initialState ffi (sptFromAList prog) co cc true lims t.stackSize t.clock) t ∧
      fs = t.stackSize ∧
      DataSem.dataLangSafeForSpace ffi (sptFromAList prog) lims fs start ∧
      conf.gcKind ≠ .none ∧
      DataSem.semantics ffi (sptFromAList prog) co cc lims fs start ≠ .fail) :
    SemanticsPropsHOL.extendWithResourceLimitPrimeHOL true
      (fun b => b = DataSem.semantics ffi (sptFromAList prog) co cc lims fs start)
      (WordSemStateFiniteExact.semantics t start) :=
  compileSemanticsPreciseLemma_of_compileCorrect (compileCorrectStmt_of_assign assignCase) conf ffi prog co cc lims t fs start h

/-- `compile_semantics_precise`, modulo the `Assign` case of `data_compile_correct`. -/
theorem compileSemanticsPrecise_of_assign {width : Nat} [NeZero width] {C F : Type}
    (assignCase : ∀ (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
      (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) (.assign dest op names live) s)
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ffi : HolFfiState F)
    (prog : List (Nat × Nat × DataLang.Prog)) (co : DataSem.CompileOracle C)
    (cc : DataSem.Compiler C) (lims : DataSem.Limits) (t : WordSemStateFiniteExact width C F)
    (fs : Spt Nat) (start : Nat)
    (h : stateRelExt conf 1 0
        (DataSem.initialState ffi (sptFromAList prog) co cc true lims t.stackSize t.clock) t ∧
      fs = t.stackSize ∧ conf.gcKind ≠ .none ∧
      DataSem.semantics ffi (sptFromAList prog) co cc lims fs start ≠ .fail ∧
      DataSem.dataLangSafeForSpace ffi (sptFromAList prog) lims fs start) :
    WordSemStateFiniteExact.semantics t start =
      DataSem.semantics ffi (sptFromAList prog) co cc lims fs start :=
  compileSemanticsPrecise_of_compileCorrect (compileCorrectStmt_of_assign assignCase) conf ffi prog co cc lims t fs start h

/-- `compile_semantics`, modulo the `Assign` case of `data_compile_correct`. -/
theorem compileSemantics_of_assign {width : Nat} [NeZero width] {C F : Type}
    (assignCase : ∀ (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
      (s : Flapjack.Compiler.Backend.DataSem.State C F),
      dataCompileCorrectInduction (width := width) (.assign dest op names live) s)
    (t : WordSemStateFiniteExact width C F) (c : Config)
    (prog : List (Nat × Nat × DataLang.Prog)) (x1 : Spt (Nat × WordLangProgHOL (BitVec width)))
    (cc : DataSem.Compiler C)
    (tcc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (tco : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (co : DataSem.CompileOracle C)
    (tt : Bool) (kk aa : Nat) (coo : Compiler.Encoders.Asm.AsmConfigExact width)
    (fs : Spt Nat) (start : Nat)
    (h : t.handler = 0 ∧ t.gcFun = WordGcFunctions.wordGcFun c ∧
      initStoreOk c t.store t.memory t.mdomain t.codeBuffer t.dataBuffer ∧
      goodDimindex width ∧ sptLookup 0 t.locals = some (.loc 1 0) ∧ t.stack = [] ∧
      confOk width c ∧ t.termdep = 0 ∧ codeRel c (sptFromAList prog) x1 ∧
      cc = (fun cfg => Option.map (Prod.map id (Prod.map (List.map upperW2w) id)) ∘ tcc cfg ∘
        List.map (compilePart c)) ∧
      tco = Prod.map id (List.map (compilePart c)) ∘ co ∧
      (∀ n, ∀ entry ∈ (co n).2, dataNumStubs ≤ entry.1) ∧
      WordToWord.codeRelExt x1 t.code ∧ sptDomain x1 = sptDomain t.code ∧ t.be = c.be ∧
      t.stackMax = some 1 ∧ t.localsSize = some 0 ∧ t.stackLimit ≠ 0 ∧
      t.compileOracle =
        Prod.map id (List.map (fun p => WordToWord.fullCompileSingle tt kk aa coo (p, none))) ∘ tco ∧
      tcc = (fun conf progs =>
        t.compile conf (progs.map (fun p => WordToWord.fullCompileSingle tt kk aa coo (p, none)))) ∧
      fs = t.stackSize ∧
      HolBehaviour.fail ≠
        DataSem.semantics t.ffi (sptFromAList prog) co cc DataProps.zeroLimits fs start) :
    (DataSem.dataLangSafeForSpace t.ffi (sptFromAList prog) (getLimits c t) fs start ∧
        c.gcKind ≠ .none →
      WordSemStateFiniteExact.wordLangSafeForSpace t start) ∧
    (open Classical in
    SemanticsPropsHOL.extendWithResourceLimitPrimeHOL
      (decide (DataSem.dataLangSafeForSpace t.ffi (sptFromAList prog) (getLimits c t) fs start ∧
        c.gcKind ≠ .none))
      (fun b => b = DataSem.semantics t.ffi (sptFromAList prog) co cc DataProps.zeroLimits fs start)
      (WordSemStateFiniteExact.semantics t start)) :=
  compileSemantics_of_compileCorrect (compileCorrectStmt_of_assign assignCase) t c prog x1 cc tcc tco co tt kk aa coo fs start h

end Flapjack.Compiler.Backend.DataToWord.Proofs.SemanticsDraft
