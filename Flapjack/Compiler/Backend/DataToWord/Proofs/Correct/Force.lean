module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ForceLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.GetVarLoc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.ThunkBits
public import Flapjack.Compiler.Backend.DataToWord.Proofs.WordTest
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Thunk
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StateRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutEnvsOdd

@[expose] public section

/-! The `Force` case of the data-to-word evaluator simulation
(`data_to_wordProofScript.sml` lines 391-742). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum

/-- The thunk header is encodable under the memory relation's size bounds. -/
theorem encodeHeader_thunk_isSome {width : Nat} [NeZero width] (conf : Config)
    (good : goodDimindex width) (lenPos : conf.lenSize ≠ 0) (lenBound : conf.lenSize + 7 < width) :
    ∃ h, encodeHeader (width := width) conf 14 1 = some h := by
  have p1 : 2 ^ 6 ≤ 2 ^ (width - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have p3 : 2 ^ 1 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
  have cond : 14 < 2 ^ (width - conf.lenSize - 2) ∧ 14 < 2 ^ width / 16 ∧ 1 < 2 ^ (width - 4) ∧
      1 < 2 ^ conf.lenSize := by
    rcases good with rfl | rfl
    all_goals exact ⟨by omega, by decide, by decide, by omega⟩
  simp only [encodeHeader, if_pos cond]
  exact ⟨_, rfl⟩

/-- The source side of a forced reference: a successful thunk inspection
identifies a clear reference pointer to a thunk cell. -/
theorem destThunk_isThunk {thunk : DataSem.Value} {refs : Spt (BvlSem.Ref DataSem.Value)}
    {mode : AstHOL.ThunkMode} {f : DataSem.Value}
    (h : DataSem.destThunk thunk refs = .isThunk mode f) :
    ∃ p, thunk = .refPtr false p ∧ sptLookup p refs = some (.thunk mode f) := by
  unfold DataSem.destThunk at h
  split at h
  · rename_i bit p
    split at h
    · cases h
    · rename_i mode' body found
      cases bit
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨p, rfl, found⟩
      · simp at h
    · cases h
  · cases h


/-- Finishing a forced evaluated value returned to the caller. -/
theorem forceFinish_none {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (prog : WordLangProgHOL (BitVec width)) (f : DataSem.Value) (w : WordLocW width)
    (related : stateRel conf l1 l2 source target none locs)
    (root : memoryRel conf target.be (holThe source.tstamps) source.refs source.space target.store
      target.memory target.mdomain ((f, w) :: stateRoots source target))
    (wordRun : WordSemStateFiniteExact.evaluate prog target =
      (some (.result (.loc l1 l2) [w]), WordSemStateFiniteExact.flushState false target)) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate prog target = (res1, target1) ∧
      optionLe target1.stackMax (DataSem.flushState false source).stackMax ∧
      (res1 = some .notEnoughSpace →
        target1.ffi.ioEvents.IsPrefix (DataSem.flushState false source).ffi.ioEvents ∧
        (conf.gcKind ≠ .none → (DataSem.flushState false source).safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        ∃ words, words.length = [f].length ∧
          stateRel conf l1 l2 (DataSem.flushState false source) target1 (some ([f].zip words)) locs ∧
          res1 = some (.result (.loc l1 l2) words)) := by
  refine ⟨_, _, wordRun, ?_, by simp, fun _ => ⟨[w], rfl, ?_, rfl⟩⟩
  · simpa [WordSemStateFiniteExact.flushState, DataSem.flushState] using
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · simpa using stateRel_flush_single conf l1 l2 source target locs f w related root

/-- Finishing a forced evaluated value stored in a destination variable. -/
theorem forceFinish_some {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target t3 : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (prog : WordLangProgHOL (BitVec width)) (f : DataSem.Value) (w : WordLocW width)
    (dest : Nat) (names : NumSet) (env : Spt DataSem.Value)
    (related : stateRel conf l1 l2 source t3 none locs)
    (cut : DataSem.cutEnv names source.locals = some env)
    (root : memoryRel conf t3.be (holThe source.tstamps) source.refs source.space t3.store
      t3.memory t3.mdomain ((f, w) :: stateRoots source t3))
    (wordRun : WordSemStateFiniteExact.evaluate prog target =
      (none, WordSemStateFiniteExact.setVar (adjustVar dest) w t3)) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate prog target = (res1, target1) ∧
      optionLe target1.stackMax (DataSem.setVar dest f { source with locals := env }).stackMax ∧
      (res1 = some .notEnoughSpace →
        target1.ffi.ioEvents.IsPrefix (DataSem.setVar dest f { source with locals := env }).ffi.ioEvents ∧
        (conf.gcKind ≠ .none →
          (DataSem.setVar dest f { source with locals := env }).safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest f { source with locals := env }) target1 none locs ∧
          res1 = none) := by
  refine ⟨_, _, wordRun, ?_, by simp, fun _ => ⟨?_, rfl⟩⟩
  · simpa [WordSemStateFiniteExact.setVar, DataSem.setVar] using
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact stateRel_cutEnv_setVar conf l1 l2 source t3 locs names env dest f w related cut root

/-- The `Force` case of `data_compile_correct` under the evaluator induction
hypotheses for the forcing calls. Flapjack-specific case infrastructure for the
tagged `dataCompileCorrect_force`. -/
theorem dataCompileCorrect_forceGen {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (ret : Option (Nat × NumSet))
    (loc src : Nat)
    (ihRet : ∀ thunk mode v args1 prog ss dest names env s1,
      DataSem.getVar src source.locals = some thunk ∧
      DataSem.destThunk thunk source.refs = .isThunk mode v ∧ mode = .notEvaluated ∧
      DataSem.findCode (some loc) [thunk, v] source.code source.stackFrameSizes =
        some (args1, prog, ss) ∧
      ret = some (dest, names) ∧ DataSem.cutEnv names source.locals = some env ∧
      s1 = DataSem.callEnv args1 ss (DataSem.pushEnv env false (DataSem.decClock source)) ∧
      source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog s1)
    (ihTail : ∀ thunk mode v args1 prog ss,
      DataSem.getVar src source.locals = some thunk ∧
      DataSem.destThunk thunk source.refs = .isThunk mode v ∧ mode = .notEvaluated ∧
      DataSem.findCode (some loc) [thunk, v] source.code source.stackFrameSizes =
        some (args1, prog, ss) ∧
      ret = none ∧ source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog
        (DataSem.callEnv args1 ss (DataSem.decClock source))) :
    dataCompileCorrectInduction (width := width) (.force ret loc src) source := by
  intro conf n l l1 l2 res source1 target locs run notTypeError related depth
  have compiled : compileControl (width := width) conf n l (.force ret loc src) =
      forceThunk conf n l ret loc src := by
    have h := compileControl_option (width := width) conf n l (.force ret loc src)
    simp [compileControl?] at h
    exact h.symm
  cases hsrc : DataSem.getVar src source.locals with
  | none =>
    exfalso; apply notTypeError
    simpa [DataSem.evaluate, hsrc] using (congrArg Prod.fst run).symm
  | some thunk =>
  cases hdt : DataSem.destThunk thunk source.refs with
  | badRef =>
    exfalso; apply notTypeError
    simpa [DataSem.evaluate, hsrc, hdt] using (congrArg Prod.fst run).symm
  | notThunk =>
    exfalso; apply notTypeError
    simpa [DataSem.evaluate, hsrc, hdt] using (congrArg Prod.fst run).symm
  | isThunk mode f =>
  obtain ⟨p, rfl, hp⟩ := destThunk_isThunk hdt
  obtain ⟨w, hw⟩ := stateRel_getVar conf l1 l2 source target none locs src _ related hsrc
  have hmem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have memRoot : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
      target.store target.memory target.mdomain ((.refPtr false p, w) :: stateRoots source target) :=
    memoryRel_lookup conf target.be _ source.refs source.space target.store target.memory
      target.mdomain source.locals target.locals _ src _ w
      ⟨by simpa [stateRoots, List.append_assoc] using hmem, hsrc, hw⟩
  have good : goodDimindex width := related.2.2.2.2.2.2.1
  obtain ⟨heap, limit, a, sp, sp1, gens, hstore, _, _, _⟩ := hmem
  obtain ⟨hdr, hhdr⟩ := encodeHeader_thunk_isSome (width := width) conf good hstore.2.2.2.1
    hstore.2.2.2.2.1
  have hzero : sptLookup 0 target.locals = some (.loc l1 l2) := related.2.2.2.2.2.2.2.2.2.2.1 rfl
  have shift : shiftLength conf < width := related.2.2.2.2.2.2.2.1
  have dataEvalNone : mode = .evaluated → ret = none →
      res = some (.val [f]) ∧ source1 = DataSem.flushState false source := by
    rintro rfl rfl
    simpa [DataSem.evaluate, hsrc, hdt] using run.symm
  have dataEvalSome : ∀ dest names, mode = .evaluated → ret = some (dest, names) →
      ∃ env, DataSem.cutEnv names source.locals = some env ∧ res = none ∧
        source1 = DataSem.setVar dest f { source with locals := env } := by
    rintro dest names rfl rfl
    cases hcut : DataSem.cutEnv names source.locals with
    | none =>
      exfalso; apply notTypeError
      simpa [DataSem.evaluate, hsrc, hdt, hcut] using (congrArg Prod.fst run).symm
    | some env =>
      exact ⟨env, rfl, by simpa [DataSem.evaluate, hsrc, hdt, hcut] using run.symm⟩
  have hv : sptLookup (adjustVar src) target.locals = some w := hw
  have shapes : (wordSemWordCmp (width := width) .test w (.word (BitVec.ofNat width 1)) = some true ∧
      ((∃ a b, w = .loc a b) ∨ ∃ x : BitVec width, w = .word x ∧ x.getLsbD 0 = false)) ∨
      ∃ x : BitVec width, w = .word x ∧ x.getLsbD 0 = true := by
    cases w with
    | loc a b =>
      have b0 : b = 0 := stateRel_getVar_refPtr_loc conf l1 l2 source target none locs src false p a b
        ⟨related, hsrc, hw⟩
      subst b0
      exact Or.inl ⟨by simp [wordSemWordCmp], Or.inl ⟨a, 0, rfl⟩⟩
    | word x =>
      by_cases bit0 : x.getLsbD 0 = true
      · exact Or.inr ⟨x, rfl, bit0⟩
      · refine Or.inl ⟨?_, Or.inr ⟨x, rfl, by simpa using bit0⟩⟩
        have h := (StackAlloc.word_and_one_eq_0_iff x).mpr bit0
        simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL]
        exact h
  rcases shapes with ⟨cmp, shape⟩ | ⟨x, rfl, bit0⟩
  · -- the inlined outcomes: the forced value is the variable's own word
    obtain ⟨hmode, mem'⟩ := memoryRel_thunkInlined conf target.be _ source.refs source.space
      target.store target.memory target.mdomain false p w _ mode f ⟨memRoot, shape, hp, good⟩
    cases ret with
    | none =>
      obtain ⟨rfl, rfl⟩ := dataEvalNone hmode rfl
      have wordRun : WordSemStateFiniteExact.evaluate (compileControl conf n l (.force none loc src)).1 target =
          (some (.result (.loc l1 l2) [w]), WordSemStateFiniteExact.flushState false target) := by
        rw [compiled]
        simp [forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar, hv,
          WordSemStateFiniteExact.getVarImm, cmp, WordSemStateFiniteExact.getVars, hzero]
      obtain ⟨t1, r1, a, b, c, d⟩ := forceFinish_none conf l1 l2 source target locs _ f w related mem' wordRun
      exact ⟨t1, r1, a, b, c, d⟩
    | some pair =>
      obtain ⟨dest, names⟩ := pair
      obtain ⟨env, cut, rfl, rfl⟩ := dataEvalSome dest names hmode rfl
      have wordRun : WordSemStateFiniteExact.evaluate
          (compileControl conf n l (.force (some (dest, names)) loc src)).1 target =
          (none, WordSemStateFiniteExact.setVar (adjustVar dest) w target) := by
        rw [compiled]
        simp [forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar, hv,
          WordSemStateFiniteExact.getVarImm, cmp, WordSemStateFiniteExact.wordExp]
      obtain ⟨t1, r1, a, b, c, d⟩ := forceFinish_some conf l1 l2 source target target locs _ f w dest names
        env related cut mem' wordRun
      exact ⟨t1, r1, a, b, c, d⟩
  · have cmpF : wordSemWordCmp (width := width) .test (.word x) (.word (BitVec.ofNat width 1)) =
        some false := by
      have h : ¬ (x &&& 1 = 0) := fun h => ((StackAlloc.word_and_one_eq_0_iff x).mp h) bit0
      simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL]
      exact h
    have hv' : sptLookup (adjustVar src) target.locals = some (.word x) := hv
    have andOne : (AndOp.and x (BitVec.ofNat width 1) == 0#width) = false := by
      have h : ¬ (x &&& 1 = 0) := fun h => ((StackAlloc.word_and_one_eq_0_iff x).mp h) bit0
      exact beq_eq_false_iff_ne.mpr h
    have src1 : adjustVar src ≠ 1 := by simp only [adjustVar]; omega
    have src3 : adjustVar src ≠ 3 := by simp only [adjustVar]; omega
    have src5 : adjustVar src ≠ 5 := by simp only [adjustVar]; omega
    rcases memoryRel_thunkImp conf target.be _ source.refs source.space target.store target.memory
        target.mdomain false p (.word x) _ mode f ⟨memRoot, hp, good⟩ with
      ⟨_, hmode, inl⟩ | ⟨x', address, header, hx', _, b3, b2, b4, _, hga, hmemA, hdomA, hdomB, _,
        hb5, mem2⟩
    · -- an inlined pointer: the header is not a thunk header
      obtain ⟨mem', address, header, hga, hmemA, hdomA, ne24, ne56⟩ := inl x ⟨rfl, bit0⟩
      have addrExp := getRealAddr_lemma conf (adjustVar src) target x address ⟨shift, good, hw, hga⟩
      have hand : AndOp.and header (AndOp.and (60#width) (BitVec.allOnes width)) = header &&& 60#width := by
        show header &&& (60#width &&& BitVec.allOnes width) = _
        rw [BitVec.and_allOnes]
      have ne56' : (header &&& 60#width == 56#width) = false := beq_eq_false_iff_ne.mpr ne56
      have ne24' : (header &&& 60#width == 24#width) = false := beq_eq_false_iff_ne.mpr ne24
      cases ret with
      | none =>
        obtain ⟨rfl, rfl⟩ := dataEvalNone hmode rfl
        have wordRun : WordSemStateFiniteExact.evaluate
            (compileControl conf n l (.force none loc src)).1 target =
            (some (.result (.loc l1 l2) [.word x]), WordSemStateFiniteExact.flushState false target) := by
          rw [compiled]
          simp [forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
            hv', WordSemStateFiniteExact.getVarImm, andOne, wordListSeq, addrExp, sptLookup_sptInsert_same,
            theWords, wordOpHOL, wordOp,
            WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad, hdomA, hmemA,
            WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock, wordSemWordCmp,
            Compiler.Encoders.Asm.wordCmpHOL, hand, ne56', ne24', WordSemStateFiniteExact.getVars, hzero,
            sptLookup_sptInsert_ne, src1, src3, WordSemStateFiniteExact.flushState]
        obtain ⟨t1, r1, a, b, c, d⟩ :=
          forceFinish_none conf l1 l2 source target locs _ f _ related mem' wordRun
        exact ⟨t1, r1, a, b, c, d⟩
      | some pair =>
        obtain ⟨dest, names⟩ := pair
        obtain ⟨env, cut, rfl, rfl⟩ := dataEvalSome dest names hmode rfl
        let t3 := WordSemStateFiniteExact.setVar 3 (.word (header &&& 60#width))
          (WordSemStateFiniteExact.setVar 1 (.word address) target)
        have rel3 : stateRel conf l1 l2 source t3 none locs := by
          rw [stateRel_setVar_odd _ _ _ _ _ _ _ 3 _ (by decide),
            stateRel_setVar_odd _ _ _ _ _ _ _ 1 _ (by decide)]
          exact related
        have root3 : memoryRel conf t3.be (holThe source.tstamps) source.refs source.space t3.store
            t3.memory t3.mdomain ((f, .word x) :: stateRoots source t3) := by
          rw [stateRoots_setVar_odd _ _ 3 _ (by decide), stateRoots_setVar_odd _ _ 1 _ (by decide)]
          exact mem'
        have wordRun : WordSemStateFiniteExact.evaluate
            (compileControl conf n l (.force (some (dest, names)) loc src)).1 target =
            (none, WordSemStateFiniteExact.setVar (adjustVar dest) (.word x) t3) := by
          rw [compiled]
          simp [t3, forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
            hv', WordSemStateFiniteExact.getVarImm, andOne, wordListSeq, addrExp, sptLookup_sptInsert_same,
            theWords, wordOpHOL, wordOp,
            WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad, hdomA, hmemA,
            WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock, wordSemWordCmp,
            Compiler.Encoders.Asm.wordCmpHOL, hand, ne56', ne24', sptLookup_sptInsert_ne, src1, src3]
        obtain ⟨t1, r1, a, b, c, d⟩ := forceFinish_some conf l1 l2 source target t3 locs _ f _ dest
          names env rel3 cut root3 wordRun
        exact ⟨t1, r1, a, b, c, d⟩
    · -- a thunk block
      simp only [WordLocW.word.injEq] at hx'
      subst hx'
      have addrExp := getRealAddr_lemma conf (adjustVar src) target x address ⟨shift, good, hw, hga⟩
      cases mode with
      | evaluated =>
        have b5 : header.getLsbD 5 = true := hb5.mpr rfl
        have eq56 : (header &&& 60#width == 56#width) = true := by
          have h := (wordTestLemma1 header good).mpr ⟨b2, b3, b4, b5⟩
          rw [BitVec.and_comm] at h
          exact beq_iff_eq.mpr h
        have hand : AndOp.and header (AndOp.and (60#width) (BitVec.allOnes width)) = header &&& 60#width := by
          show header &&& (60#width &&& BitVec.allOnes width) = _
          rw [BitVec.and_allOnes]
        have mem' : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
            target.store target.memory target.mdomain
            ((f, target.memory (address + wordSemBytesInWord)) :: stateRoots source target) := by
          apply memoryRel_rearrange _ _ _ _ _ _ _ _ _ _ ?_ mem2
          intro pair member
          simp only [List.mem_cons] at member ⊢
          tauto
        cases ret with
        | none =>
          obtain ⟨rfl, rfl⟩ := dataEvalNone rfl rfl
          have wordRun : WordSemStateFiniteExact.evaluate
              (compileControl conf n l (.force none loc src)).1 target =
              (some (.result (.loc l1 l2) [target.memory (address + wordSemBytesInWord)]),
                WordSemStateFiniteExact.flushState false target) := by
            rw [compiled]
            simp [forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
              hv', WordSemStateFiniteExact.getVarImm, andOne, wordListSeq, addrExp, sptLookup_sptInsert_same,
            theWords, wordOpHOL, wordOp,
              WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad, hdomA, hmemA, hdomB,
              WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock, wordSemWordCmp,
              Compiler.Encoders.Asm.wordCmpHOL, hand, eq56, WordSemStateFiniteExact.getVars, hzero,
              sptLookup_sptInsert_ne, WordSemStateFiniteExact.flushState]
          obtain ⟨t1, r1, a, b, c, d⟩ :=
            forceFinish_none conf l1 l2 source target locs _ f _ related mem' wordRun
          exact ⟨t1, r1, a, b, c, d⟩
        | some pair =>
          obtain ⟨dest, names⟩ := pair
          obtain ⟨env, cut, rfl, rfl⟩ := dataEvalSome dest names rfl rfl
          let t3 := WordSemStateFiniteExact.setVar 3 (.word (header &&& 60#width))
            (WordSemStateFiniteExact.setVar 1 (.word address) target)
          have rel3 : stateRel conf l1 l2 source t3 none locs := by
            rw [stateRel_setVar_odd _ _ _ _ _ _ _ 3 _ (by decide),
              stateRel_setVar_odd _ _ _ _ _ _ _ 1 _ (by decide)]
            exact related
          have root3 : memoryRel conf t3.be (holThe source.tstamps) source.refs source.space t3.store
              t3.memory t3.mdomain
              ((f, target.memory (address + wordSemBytesInWord)) :: stateRoots source t3) := by
            rw [stateRoots_setVar_odd _ _ 3 _ (by decide), stateRoots_setVar_odd _ _ 1 _ (by decide)]
            exact mem'
          have wordRun : WordSemStateFiniteExact.evaluate
              (compileControl conf n l (.force (some (dest, names)) loc src)).1 target =
              (none, WordSemStateFiniteExact.setVar (adjustVar dest)
                (target.memory (address + wordSemBytesInWord)) t3) := by
            rw [compiled]
            simp [t3, forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
              hv', WordSemStateFiniteExact.getVarImm, andOne, wordListSeq, addrExp, sptLookup_sptInsert_same,
            theWords, wordOpHOL, wordOp,
              WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.memLoad, hdomA, hmemA, hdomB,
              WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock, wordSemWordCmp,
              Compiler.Encoders.Asm.wordCmpHOL, hand, eq56, sptLookup_sptInsert_ne]
          obtain ⟨t1, r1, a, b, c, d⟩ := forceFinish_some conf l1 l2 source target t3 locs _ f _ dest
            names env rel3 cut root3 wordRun
          exact ⟨t1, r1, a, b, c, d⟩
      | notEvaluated =>
        have b5 : header.getLsbD 5 = false := by
          cases h : header.getLsbD 5 with
          | false => rfl
          | true => exact absurd (hb5.mp h) (by simp)
        have hand : AndOp.and header (AndOp.and (60#width) (BitVec.allOnes width)) = header &&& 60#width := by
          show header &&& (60#width &&& BitVec.allOnes width) = _
          rw [BitVec.and_allOnes]
        have h24 : header &&& 60#width = 24#width := by
          have h := (wordTestLemma2 header good).mpr ⟨b2, b3, b4, b5⟩
          rw [BitVec.and_comm] at h
          exact h
        have ne2456 : (24#width == 56#width) = false := by
          apply beq_eq_false_iff_ne.mpr
          intro h
          have h' := congrArg BitVec.toNat h
          rcases good with rfl | rfl <;> simp at h'
        have hclock : target.clock = source.clock := related.2.1
        have hffi : target.ffi = source.ffi := related.1
        have hsize : target.stackSize = source.stackFrameSizes :=
          related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have bound : optionLe target.stackMax source.stackMax :=
          related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have stackLen : source.stack.length = locs.length := by
          have h1 := related.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
          have h2 := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
          omega
        cases hfind : DataSem.findCode (some loc) [.refPtr false p, f] source.code
            source.stackFrameSizes with
        | none =>
          exfalso; apply notTypeError
          cases ret with
          | none => simpa [DataSem.evaluate, hsrc, hdt, hfind] using (congrArg Prod.fst run).symm
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            simpa [DataSem.evaluate, hsrc, hdt, hfind] using (congrArg Prod.fst run).symm
        | some found =>
        obtain ⟨args1, body, ss⟩ := found
        have codeFacts : sptLookup loc source.code = some (2, body) ∧ args1 = [.refPtr false p, f] ∧
            ss = sptLookup loc source.stackFrameSizes := by
          unfold DataSem.findCode at hfind
          cases hc : sptLookup loc source.code with
          | none => simp [hc] at hfind
          | some entry =>
            obtain ⟨arity, prog⟩ := entry
            by_cases ha : 2 = arity
            · subst ha
              simp [hc] at hfind
              obtain ⟨rfl, rfl, rfl⟩ := hfind
              exact ⟨rfl, rfl, rfl⟩
            · simp [hc, ha] at hfind
        obtain ⟨hcode, rfl, rfl⟩ := codeFacts
        have tcode := related.2.2.2.2.1.2.2 loc 2 body hcode
        let w' := target.memory (address + wordSemBytesInWord)
        let t3 := WordSemStateFiniteExact.setVar 3 (.word (header &&& 60#width))
          (WordSemStateFiniteExact.setVar 1 (.word address) target)
        let t5 := WordSemStateFiniteExact.setVar 5 w' t3
        have roots5 : stateRoots source t5 = stateRoots source target := by
          rw [stateRoots_setVar_odd _ _ 5 _ (by decide), stateRoots_setVar_odd _ _ 3 _ (by decide),
            stateRoots_setVar_odd _ _ 1 _ (by decide)]
        have rel5 : stateRel conf l1 l2 source t5 none locs := by
          rw [stateRel_setVar_odd _ _ _ _ _ _ _ 5 _ (by decide),
            stateRel_setVar_odd _ _ _ _ _ _ _ 3 _ (by decide),
            stateRel_setVar_odd _ _ _ _ _ _ _ 1 _ (by decide)]
          exact related
        have relRoots : stateRel conf l1 l2 source t5
            (some ([.refPtr false p, f].zip [.word x, w'])) locs := by
          apply stateRel_withRoots conf l1 l2 source t5 locs _ rel5
          rw [roots5]
          apply memoryRel_rearrange _ _ _ _ _ _ _ _ _ _ ?_ mem2
          intro pair member
          simp only [List.zip_cons_cons, List.zip_nil_right, List.cons_append, List.nil_append,
            List.mem_cons] at member ⊢
          tauto
        have zero5 : sptLookup 0 t5.locals = some (.loc l1 l2) := by
          simp [t5, t3, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, hzero]
        have locs5 : mkLoc (width := width) (WordSemStateFiniteExact.jumpExc t5) =
              mkLoc (width := width) (WordSemStateFiniteExact.jumpExc target) ∧
            (WordSemStateFiniteExact.jumpExc t5 = none ↔ WordSemStateFiniteExact.jumpExc target = none) := by
          have a5 := jumpExc_setVar t3 5 w'
          have a3 := jumpExc_setVar (WordSemStateFiniteExact.setVar 1 (.word address) target) 3
            (.word (header &&& 60#width))
          have a1 := jumpExc_setVar target 1 (.word address)
          exact ⟨a5.1.trans (a3.1.trans a1.1), a5.2.trans (a3.2.trans a1.2)⟩
        have t5clock : t5.clock = source.clock := hclock
        cases ret with
        | none =>
          have wordFind : wordSemFindCode (some loc) [.loc l1 l2, .word x, w'] t5.code t5.stackSize =
              some ([.loc l1 l2, .word x, w'], (compileControl conf loc 2 body).1,
                sptLookup loc source.stackFrameSizes) := by
            simp [wordSemFindCode, t5, t3, WordSemStateFiniteExact.setVar, tcode, hsize]
          by_cases zero : source.clock = 0
          · have sourceEq : res = some (.err (.abort .timeoutError)) ∧
                source1 = { source with stack := [], locals := .ln } := by
              simpa [DataSem.evaluate, hsrc, hdt, hfind, zero] using run.symm
            obtain ⟨rfl, rfl⟩ := sourceEq
            refine ⟨WordSemStateFiniteExact.flushState true t5, some .timeOut, ?_, ?_, by simp, ?_⟩
            · rw [compiled]
              simp [forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
                hv', WordSemStateFiniteExact.getVarImm, andOne, wordListSeq, addrExp,
                sptLookup_sptInsert_same, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.wordExp,
                WordSemStateFiniteExact.memLoad, hdomA, hmemA, hdomB, WordSemStateFiniteExact.setVar,
                WordSemStateFiniteExact.fixClock, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
                hand, h24, ne2456, WordSemStateFiniteExact.getVars, hzero, sptLookup_sptInsert_ne,
                src1, src3, src5, wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode, tcode, hsize,
                hclock, zero, t5, t3, w']
            · simpa [WordSemStateFiniteExact.flushState, t5, t3, WordSemStateFiniteExact.setVar] using bound
            · intro _
              simpa [WordSemStateFiniteExact.flushState, t5, t3, WordSemStateFiniteExact.setVar] using hffi
          · cases hcall : DataSem.evaluate body
                (DataSem.callEnv [.refPtr false p, f] (sptLookup loc source.stackFrameSizes)
                  (DataSem.decClock source)) with
            | mk r mid =>
            cases r with
            | none =>
              exfalso; apply notTypeError
              simpa [DataSem.evaluate, hsrc, hdt, hfind, zero, hcall] using (congrArg Prod.fst run).symm
            | some r =>
            have sourceEq : res = some r ∧ source1 = mid := by
              simpa [DataSem.evaluate, hsrc, hdt, hfind, zero, hcall] using run.symm
            obtain ⟨rfl, rfl⟩ := sourceEq
            have calleeRel := stateRel_callEnv_values conf l1 l2 l1 l2 source t5 locs
              [.refPtr false p, f] [.word x, w'] (sptLookup loc source.stackFrameSizes) rfl relRoots
            have depth' : (WordSemStateFiniteExact.callEnv [.loc l1 l2, .word x, w']
                (sptLookup loc source.stackFrameSizes) (WordSemStateFiniteExact.decClock t5)).termdep > 1 := by
              simpa [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, t5, t3,
                WordSemStateFiniteExact.setVar] using depth
            obtain ⟨t1, res1, wordRun, stackBound, space, result⟩ :=
              ihTail (.refPtr false p) .notEvaluated f [.refPtr false p, f] body
                (sptLookup loc source.stackFrameSizes) ⟨hsrc, hdt, rfl, hfind, rfl, zero⟩
                conf loc 2 l1 l2 (some r) source1 _ locs hcall notTypeError calleeRel depth'
            have locFacts := jumpExc_callEnv_decClock t5 [.loc l1 l2, .word x, w']
              (sptLookup loc source.stackFrameSizes)
            have notBadRet : wordSemBadFunReturn res1 = false := by
              cases res1 with
              | none =>
                have h := result (by simp)
                rcases r with values | (value | (_ | _ | _))
                all_goals simp at h
              | some w =>
                cases w with
                | «break» _ =>
                  have h := result (by simp)
                  rcases r with values | (value | (_ | _ | _))
                  all_goals simp at h
                | «continue» _ =>
                  have h := result (by simp)
                  rcases r with values | (value | (_ | _ | _))
                  all_goals simp at h
                | _ => rfl
            have tzero : t5.clock ≠ 0 := by rw [t5clock]; exact zero
            refine ⟨t1, res1, ?_, stackBound, space, ?_⟩
            · have pre : WordSemStateFiniteExact.evaluate (compileControl conf n l (.force none loc src)).1 target =
                  WordSemStateFiniteExact.evaluate (.call none (some loc) [0, adjustVar src, 5] none) t5 := by
                rw [compiled]
                simp [forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
                  hv', WordSemStateFiniteExact.getVarImm, andOne, wordListSeq, addrExp,
                  sptLookup_sptInsert_same, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.memLoad, hdomA, hmemA, hdomB, WordSemStateFiniteExact.setVar,
                  WordSemStateFiniteExact.fixClock, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
                  hand, h24, ne2456, t5, t3, w', sptLookup_sptInsert_ne]
              rw [pre]
              have reads : WordSemStateFiniteExact.getVars [0, adjustVar src, 5] t5 =
                  some [.loc l1 l2, .word x, w'] := by
                simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, t5, t3,
                  WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
                  src1, src3, src5, hzero, hv']
              simp [WordSemStateFiniteExact.evaluate, reads, wordSemBadDestArgs, wordSemAddRetLoc,
                wordFind, tzero, wordRun, notBadRet]
            · intro hs
              have h := result hs
              rcases r with values | (value | e)
              · exact h
              · obtain ⟨hf, w, l5, l6, rest, hres, hjump⟩ := h
                refine ⟨hf, w, l5, l6, rest, ?_, ?_⟩
                · rw [hres, locFacts.1, locs5.1]
                · intro present
                  exact hjump (fun empty => present (locs5.2.mp (locFacts.2.mp empty)))
              · cases e <;> exact h
        | some pair =>
          obtain ⟨dest, names⟩ := pair
          cases hcut : DataSem.cutEnv names source.locals with
          | none =>
            exfalso; apply notTypeError
            simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut] using (congrArg Prod.fst run).symm
          | some env =>
          obtain ⟨wordCut, wordCutRun⟩ :=
            cutEnv_imp_wordCutEnv conf l1 l2 source target locs names env ⟨related, hcut⟩
          obtain ⟨first, second, cutsRun, _⟩ :=
            cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut wordCutRun
          have cuts5 : wordSemCutEnvs (adjustSets names) t5.locals = some (first, second) := by
            simp only [t5, t3, WordSemStateFiniteExact.setVar]
            rw [cutEnvs_adjustSets_insertOdd names _ 5 _ (by decide),
              cutEnvs_adjustSets_insertOdd names _ 3 _ (by decide),
              cutEnvs_adjustSets_insertOdd names _ 1 _ (by decide)]
            exact cutsRun
          have calleeRel := stateRel_callEnv_push conf l1 l2 n l source t5 locs [.refPtr false p, f]
            [.word x, w'] (sptLookup loc source.stackFrameSizes) names env (first, second)
            ⟨relRoots, rfl, zero5, hcut, cuts5⟩
          have reads : WordSemStateFiniteExact.getVars [adjustVar src, 5] t5 = some [.word x, w'] := by
            simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, t5, t3,
              WordSemStateFiniteExact.setVar, sptLookup_sptInsert_ne, sptLookup_sptInsert_same,
              src1, src3, src5, hv']
          have wordFind : wordSemFindCode (some loc)
              (wordSemAddRetLoc (some ([adjustVar dest], adjustSets names, (.skip : WordLangProgHOL (BitVec width)), n, l))
                [.word x, w']) t5.code t5.stackSize =
              some ([.loc n l, .word x, w'], (compileControl conf loc 2 body).1,
                sptLookup loc source.stackFrameSizes) := by
            simp [wordSemFindCode, wordSemAddRetLoc, t5, t3, WordSemStateFiniteExact.setVar, tcode, hsize]
          have nonEmpty : ¬ sptDomainEmpty (adjustSets names).1 := by
            intro empty
            exact empty 0 (by simp [adjustSets, sptMem, sptDomain, sptLookup])
          have guard : ¬ (sptDomainEmpty (adjustSets names).1 ∨ ¬ [adjustVar dest].Nodup) := by
            simp [nonEmpty]
          have pre : WordSemStateFiniteExact.evaluate
              (compileControl conf n l (.force (some (dest, names)) loc src)).1 target =
              WordSemStateFiniteExact.evaluate (.call (some ([adjustVar dest], adjustSets names, .skip, n, l))
                (some loc) [adjustVar src, 5] none) t5 := by
            rw [compiled]
            simp [forceThunk, hhdr, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
              hv', WordSemStateFiniteExact.getVarImm, andOne, wordListSeq, addrExp,
              sptLookup_sptInsert_same, theWords, wordOpHOL, wordOp, WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.memLoad, hdomA, hmemA, hdomB, WordSemStateFiniteExact.setVar,
              WordSemStateFiniteExact.fixClock, wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL,
              hand, h24, ne2456, t5, t3, w', sptLookup_sptInsert_ne]
          by_cases zero : source.clock = 0
          · have sourceEq : res = some (.err (.abort .timeoutError)) ∧
                source1 = { DataSem.callEnv [.refPtr false p, f] (sptLookup loc source.stackFrameSizes)
                  (DataSem.pushEnv env false (DataSem.decClock source)) with stack := [], locals := .ln } := by
              simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut, zero] using run.symm
            obtain ⟨rfl, rfl⟩ := sourceEq
            have tz : t5.clock = 0 := by rw [t5clock]; exact zero
            have timeoutEq := Flapjack.WordAlloc.evaluate_call_ret_timeout t5 [adjustVar dest]
              (adjustSets names) .skip n l (some loc) [adjustVar src, 5] none [.word x, w']
              [.loc n l, .word x, w'] (compileControl conf loc 2 body).1
              (sptLookup loc source.stackFrameSizes) (first, second) reads (by simp [wordSemBadDestArgs])
              wordFind guard cuts5 tz
            have calleeBound := calleeRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            refine ⟨_, some .timeOut, by rw [pre, timeoutEq], ?_, by simp, ?_⟩
            · simpa [WordSemStateFiniteExact.flushState, ← callEnv_pushEnv_stackMax] using calleeBound
            · intro _
              simpa [WordSemStateFiniteExact.flushState, DataSem.callEnv, DataSem.pushEnv,
                DataSem.decClock, t5, t3, WordSemStateFiniteExact.setVar] using hffi
          · have tzero : t5.clock ≠ 0 := by rw [t5clock]; exact zero
            cases hcall : DataSem.evaluate body
                (DataSem.callEnv [.refPtr false p, f] (sptLookup loc source.stackFrameSizes)
                  (DataSem.pushEnv env false (DataSem.decClock source))) with
            | mk r mid =>
            have dataFix : DataSem.fixClock
                (DataSem.callEnv [.refPtr false p, f] (sptLookup loc source.stackFrameSizes)
                  (DataSem.pushEnv env false (DataSem.decClock source)))
                (DataSem.evaluate body
                  (DataSem.callEnv [.refPtr false p, f] (sptLookup loc source.stackFrameSizes)
                    (DataSem.pushEnv env false (DataSem.decClock source)))) = (r, mid) := by
              rw [DataSem.fixClockEvaluate, hcall]
            cases r with
            | none =>
              exfalso; apply notTypeError
              simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut, zero, dataFix] using
                (congrArg Prod.fst run).symm
            | some r =>
            have notTE : some r ≠ some (Result.err (ErrorResult.abort Abort.typeError) :
                Result (List DataSem.Value) DataSem.Value) := by
              intro h
              cases h
              apply notTypeError
              simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut, zero, dataFix] using
                (congrArg Prod.fst run).symm
            have depth' : (WordSemStateFiniteExact.callEnv [.loc n l, .word x, w']
                (sptLookup loc source.stackFrameSizes) (WordSemStateFiniteExact.pushEnv (first, second)
                  none (WordSemStateFiniteExact.decClock t5))).termdep > 1 := by
              simpa [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
                WordSemStateFiniteExact.decClock, t5, t3, WordSemStateFiniteExact.setVar] using depth
            obtain ⟨t1, res1, wordRun, stackBound, space, result⟩ :=
              ihRet (.refPtr false p) .notEvaluated f [.refPtr false p, f] body
                (sptLookup loc source.stackFrameSizes) dest names env _
                ⟨hsrc, hdt, rfl, hfind, rfl, hcut, rfl, zero⟩ conf loc 2 n l (some r) mid _
                ((l1, l2) :: locs) hcall notTE calleeRel depth'
            have callEq := Flapjack.WordAlloc.evaluate_call_ret_eq t5 [adjustVar dest] (adjustSets names)
              .skip n l (some loc) [adjustVar src, 5] none [.word x, w'] [.loc n l, .word x, w']
              (compileControl conf loc 2 body).1 (sptLookup loc source.stackFrameSizes) (first, second)
              reads (by simp [wordSemBadDestArgs]) wordFind guard cuts5 tzero
            have sourceAfter : ∀ values, r = .val values →
                ∃ value, values = [value] ∧ ∃ next, DataSem.popEnv mid = some next ∧ res = none ∧
                  source1 = DataSem.setVar dest value next := by
              intro values hr
              subst hr
              match values, run with
              | [value], run =>
                cases hpop : DataSem.popEnv mid with
                | none =>
                  exfalso; apply notTypeError
                  simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut, zero, dataFix, hpop] using
                    (congrArg Prod.fst run).symm
                | some next =>
                  have h : res = none ∧ source1 = DataSem.setVar dest value next := by
                    simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut, zero, dataFix, hpop] using run.symm
                  exact ⟨value, rfl, next, rfl, h⟩
              | [], run =>
                exfalso; apply notTypeError
                simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut, zero, dataFix] using
                  (congrArg Prod.fst run).symm
              | _ :: _ :: _, run =>
                exfalso; apply notTypeError
                simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut, zero, dataFix] using
                  (congrArg Prod.fst run).symm
            have sourceErr : ∀ e, r = .err e → res = some (.err e) ∧ source1 = mid := by
              intro e hr
              subst hr
              simpa [DataSem.evaluate, hsrc, hdt, hfind, hcut, zero, dataFix] using run.symm
            have locFacts := jumpExc_callEnv_pushEnv_none t5 [.loc n l, .word x, w']
              (sptLookup loc source.stackFrameSizes) (first, second)
            by_cases nes : res1 = some .notEnoughSpace
            · subst nes
              have spaceFacts := space rfl
              have after : optionLe mid.stackMax source1.stackMax ∧
                  mid.ffi.ioEvents <+: source1.ffi.ioEvents ∧
                  (source1.safeForSpace = true → mid.safeForSpace = true) := by
                cases r with
                | val values =>
                  obtain ⟨value, _, next, pop, _, rfl⟩ := sourceAfter values rfl
                  have pc := DataSem.popEnv_const mid next pop
                  have hsafe : next.safeForSpace = mid.safeForSpace := by
                    unfold DataSem.popEnv at pop
                    split at pop <;> simp at pop <;> subst pop <;> rfl
                  refine ⟨?_, ?_, ?_⟩
                  · simp [DataSem.setVar, pc.2.2, optionLe_refl]
                  · simp [DataSem.setVar, pc.1]
                  · simp [DataSem.setVar, hsafe]
                | err e =>
                  obtain ⟨_, rfl⟩ := sourceErr e rfl
                  exact ⟨optionLe_refl _, List.prefix_refl _, id⟩
              refine ⟨t1, some .notEnoughSpace, ?_, optionLe_trans stackBound after.1, ?_, by simp⟩
              · rw [pre, callEq, wordRun]
                simp [Flapjack.WordAlloc.callRetTail]
              · intro _
                refine ⟨spaceFacts.1.trans after.2.1, fun gc => ?_⟩
                cases hs : source1.safeForSpace with
                | false => rfl
                | true =>
                  have midSafe := after.2.2 hs
                  rw [spaceFacts.2 gc] at midSafe
                  exact absurd midSafe (by simp)
            · have h := result nes
              cases r with
              | val values =>
                obtain ⟨value, rfl, next, pop, rfl, rfl⟩ := sourceAfter values rfl
                obtain ⟨ws, lens, calleeRet, rfl⟩ := h
                obtain ⟨t2, tpop, dom, rel2, smax⟩ := callReturnValues conf l1 l2 n l locs [dest]
                  (List.nodup_singleton dest) [value] mid next t5 t1 ws _ [.loc n l, .word x, w']
                  (sptLookup loc source.stackFrameSizes) (first, second) none wordRun calleeRet lens rfl pop
                have pc := DataSem.popEnv_const mid next pop
                have relSet : stateRel conf l1 l2 (DataSem.setVar dest value next)
                    (WordSemStateFiniteExact.setVars [adjustVar dest] ws t2) none locs := by
                  have h := stateRel_sourceLocals_congr conf l1 l2 _ _ none locs
                    (sptInsert dest value next.locals) (fun key => by
                      change sptLookup key (sptInsert dest value next.locals) =
                        sptLookup key (sptUnion (sptInsert dest value (sptFromAList [])) next.locals)
                      by_cases same : key = dest
                      · subst key
                        rw [sptLookup_sptUnion]
                        simp [sptLookup_sptInsert_same]
                      · rw [sptLookup_sptUnion, sptLookup_sptInsert_ne dest key value _ same,
                          sptLookup_sptInsert_ne dest key value _ same]
                        simp [sptFromAList]) rel2
                  exact h
                refine ⟨WordSemStateFiniteExact.setVars [adjustVar dest] ws t2, none, ?_, ?_, by simp,
                  fun _ => ⟨relSet, rfl⟩⟩
                · have lenW : ws.length = [adjustVar dest].length := by simpa using lens
                  rw [pre, callEq, wordRun]
                  simp [Flapjack.WordAlloc.callRetTail, lenW, tpop, dom, WordSemStateFiniteExact.evaluate]
                · simpa [WordSemStateFiniteExact.setVars, DataSem.setVar, smax, pc.2.2] using stackBound
              | err e =>
                obtain ⟨rfl, rfl⟩ := sourceErr e rfl
                cases e with
                | raise v =>
                  obtain ⟨hf, w, l5, l6, rest, rfl, hjump⟩ := h
                  refine ⟨t1, _, ?_, stackBound, space, fun _ => ⟨hf, w, l5, l6, rest, ?_, ?_⟩⟩
                  · rw [pre, callEq, wordRun]
                    simp [Flapjack.WordAlloc.callRetTail]
                  · rw [locFacts.1, locs5.1]
                  · intro present
                    obtain ⟨hl, hrel⟩ := hjump (fun empty => present (locs5.2.mp (locFacts.2.mp empty)))
                    have shorter := evaluate_raise_stackShorter body [.refPtr false p, f]
                      (sptLookup loc source.stackFrameSizes) env source source1 v hcall
                    refine ⟨?_, hrel⟩
                    rw [← wordSemLastN_cons_of_le _ (l1, l2) locs (by omega)]
                    exact hl
                | abort a =>
                  cases a with
                  | typeError => exact absurd rfl notTE
                  | timeoutError =>
                    obtain ⟨rfl, hf⟩ := h
                    refine ⟨t1, _, ?_, stackBound, space, fun _ => ⟨rfl, hf⟩⟩
                    rw [pre, callEq, wordRun]
                    simp [Flapjack.WordAlloc.callRetTail]
                  | ffiError f =>
                    obtain ⟨rfl, hf⟩ := h
                    refine ⟨t1, _, ?_, stackBound, space, fun _ => ⟨rfl, hf⟩⟩
                    rw [pre, callEq, wordRun]
                    simp [Flapjack.WordAlloc.callRetTail]

namespace reviewedDataCompileCorrect_forceMap
/-- Canonical roundtrip for the target state used by this HOL port. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end reviewedDataCompileCorrect_forceMap

/-- The `Force` case retains the complete conclusion of `data_compile_correct`.
Its two hypotheses are the `Force` clause's evaluator induction hypotheses for
the forcing call of an unevaluated thunk, with and without a return
destination. HOL's auxiliary pattern variables for the found code triple and
the return pair are bound here as the corresponding tuple patterns. The word
evaluator inherits the real-model assumption documented in
`docs/SOUNDNESS.md` item 8. The full theorem still requires assembly of all
cases. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "data_compile_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem dataCompileCorrect_force {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 : Nat)
    (res : Option (Result (List Flapjack.Compiler.Backend.DataSem.Value) Flapjack.Compiler.Backend.DataSem.Value)) (source1 : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (ret : Option (Nat × NumSet)) (loc src : Nat)
    (ihRet : ∀ thunk mode v args1 prog ss dest names env s1,
      DataSem.getVar src source.locals = some thunk ∧
      DataSem.destThunk thunk source.refs = .isThunk mode v ∧ mode = .notEvaluated ∧
      DataSem.findCode (some loc) [thunk, v] source.code source.stackFrameSizes =
        some (args1, prog, ss) ∧
      ret = some (dest, names) ∧ DataSem.cutEnv names source.locals = some env ∧
      s1 = DataSem.callEnv args1 ss (DataSem.pushEnv env false (DataSem.decClock source)) ∧
      source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog s1)
    (ihTail : ∀ thunk mode v args1 prog ss,
      DataSem.getVar src source.locals = some thunk ∧
      DataSem.destThunk thunk source.refs = .isThunk mode v ∧ mode = .notEvaluated ∧
      DataSem.findCode (some loc) [thunk, v] source.code source.stackFrameSizes =
        some (args1, prog, ss) ∧
      ret = none ∧ source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog
        (DataSem.callEnv args1 ss (DataSem.decClock source)))
    (run : DataSem.evaluate (.force ret loc src) source = (res, source1))
    (notTypeError : res ≠ some (.err (.abort .typeError)))
    (related : stateRel conf l1 l2 source target none locs)
    (depth : target.termdep > 1) :
    ∃ target1 res1,
      WordSemStateFiniteExact.evaluate (compileControl conf n l (.force ret loc src)).1 target = (res1, target1) ∧
      optionLe target1.stackMax source1.stackMax ∧
      (res1 = some .notEnoughSpace →
        target1.ffi.ioEvents.IsPrefix source1.ffi.ioEvents ∧
        (conf.gcKind ≠ .none → source1.safeForSpace = false)) ∧
      (res1 ≠ some .notEnoughSpace →
        match res with
        | none => stateRel conf l1 l2 source1 target1 none locs ∧ res1 = none
        | some (.val values) =>
            ∃ words, words.length = values.length ∧
              stateRel conf l1 l2 source1 target1 (some (values.zip words)) locs ∧
              res1 = some (.result (.loc l1 l2) words)
        | some (.err (.raise value)) =>
            target1.ffi = source1.ffi ∧
            ∃ word l5 l6 rest,
              res1 = some (.exception (mkLoc (WordSemStateFiniteExact.jumpExc target)) word) ∧
              (WordSemStateFiniteExact.jumpExc target ≠ none →
                wordSemLastN (source1.stack.length + 1) locs = (l5, l6) :: rest ∧
                ∀ i, stateRel conf l5 l6 (DataSem.setVar i value source1)
                  (WordSemStateFiniteExact.setVar (adjustVar i) word target1) none rest)
        | some (.err (.abort (.ffiError event))) =>
            res1 = some (.finalFfi event) ∧ target1.ffi = source1.ffi
        | some (.err (.abort _)) => res1 = some .timeOut ∧ target1.ffi = source1.ffi) := by
  obtain ⟨target1, res1, wordRun, stackBound, space, result⟩ :=
    dataCompileCorrect_forceGen source ret loc src ihRet ihTail conf n l l1 l2 res source1 target locs
      run notTypeError related depth
  refine ⟨target1, res1, wordRun, stackBound, space, fun hs => ?_⟩
  have h := result hs
  cases res with
  | none => exact h
  | some r =>
    cases r with
    | val values => exact h
    | err err =>
      cases err with
      | raise value => exact h
      | abort err => cases err <;> exact h

end Flapjack.Compiler.Backend.DataToWord.Proofs
