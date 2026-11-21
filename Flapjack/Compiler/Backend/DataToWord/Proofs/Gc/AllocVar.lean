module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocFail
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutInsertOne
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocLocals
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackSizeTail
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HasSpace
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SilentFfi
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Heap
@[expose] public section

/-! Variable allocation correctness for both collector and silent-FFI paths. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Evaluation of an assignment followed by a program, factored for this proof;
there is no separate HOL declaration. -/
private theorem evalAssignSeq {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (key : Nat) (expr : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (read : s.wordExp expr = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign key expr) tail) s =
      WordSemStateFiniteExact.evaluate tail (s.setVar key v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Unfold sequential evaluation for this proof; there is no separate HOL declaration. -/
private theorem evalSeqLocal {width : Nat} [NeZero width] {C F : Type}
    (p q : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.evaluate (.seq p q) s =
      match WordSemStateFiniteExact.evaluate p s with
      | (none, s1) => WordSemStateFiniteExact.evaluate q s1
      | (some res, s1) => (some res, s1) := by
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate]
  cases h : WordSemStateFiniteExact.evaluate p s with
  | mk res s1 => cases res <;> rfl

/-- Select a word conditional using established operand and comparison results. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem evalIfLocal {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (cmp : Cmp) (r : Nat)
    (ri : WordRegImm (BitVec width)) (yes no : WordLangProgHOL (BitVec width))
    (v1 v2 : WordLocW width) (b : Bool)
    (hr : s.getVar r = some v1) (hi : s.getVarImm ri = some v2)
    (hc : wordSemWordCmp cmp v1 v2 = some b) :
    WordSemStateFiniteExact.evaluate (.ite cmp r ri yes no) s =
      WordSemStateFiniteExact.evaluate (if b then yes else no) s := by
  rw [WordSemStateFiniteExact.evaluate, hr, hi]
  simp only [hc]
  cases b <;> rfl


/-- Cutting a live set that retains register 1 ignores other odd temporaries.
This is proof infrastructure for variable allocation, with no separate HOL declaration. -/
private theorem cutKeepOdd {α β : Type} (names : Spt α) (env : Spt β)
    (n : Nat) (value : β) (odd : n % 2 = 1) (notOne : n ≠ 1) :
    wordSemCutEnv ((adjustSets names).1, sptInsert 1 () (adjustSets names).2)
      (sptInsert n value env) =
    wordSemCutEnv ((adjustSets names).1, sptInsert 1 () (adjustSets names).2) env := by
  have notZero : ¬ sptMem n (.ls () : NumSet) := by
    intro member
    obtain ⟨v, found⟩ := (sptMem_iff_lookup n (.ls ())).mp member
    cases n <;> simp_all
  have absent : ¬ sptMem n (sptInsert 1 () (adjustSet names)) := by
    intro member
    rcases (sptMem_sptInsert n 1 () (adjustSet names)).mp member with eq | mem
    · exact notOne eq
    · obtain ⟨k, eq, _⟩ := (adjustSet_domain names n).mp mem
      simp [adjustVar] at eq
      omega
  simp only [wordSemCutEnv, wordSemCutEnvs, adjustSets]
  rw [cutNames_insert_notMem (.ls ()) env n value notZero,
    cutNames_insert_notMem (sptInsert 1 () (adjustSet names)) env n value absent]

/-- Evaluation of the allocation-specific silent call retaining register 1.
This factors the original variable-allocation proof and has no separate HOL declaration. -/
private theorem evaluateSilentKeep {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (env : Spt (WordLocW width))
    (enabled : conf.callEmptyFfi = true)
    (related : stateRel conf l1 l2 source target none locs)
    (cut : wordSemCutEnv ((adjustSets names).1, sptInsert 1 () (adjustSets names).2) target.locals = some env) :
    WordSemStateFiniteExact.evaluate
      (silentFfi conf 3 ((adjustSets names).1, sptInsert 1 () (adjustSets names).2)) target =
      (none, { target with locals := env, fpRegs := HolFiniteMapExact.empty,
                           memory := target.memory, ffi := target.ffi }) := by
  obtain ⟨nf, curr, len, hnf, hcurr, hlen⟩ := stateRel_lookupHeap conf l1 l2 source target locs related
  simp [silentFfi, enabled, wordListSeq, WordSemStateFiniteExact.evaluate,
    WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
    WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
    WordSemStateFiniteExact.fixClock, theWords, wordOpHOL, wordOp,
    sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
    hnf, hcurr, hlen, cut, cutKeepOdd,
    readBytearrayWordHOL, readBytearrayGenericHOL, writeBytearrayExact, callFFIHOL_empty_extCall]


namespace AllocVarWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AllocVarWitnesses

/-- Full variable-allocation correctness, including allocation failure and success.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "AllocVar_thm_gen"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocVar_gen {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target result : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (names : NumSet) (cut : Spt DataSem.Value) (w : BitVec width) (limit : Nat)
    (q : Option (WordSemResult width))
    (related : stateRel conf l1 l2 source target none locs)
    (cutEq : DataSem.cutEnv names source.locals = some cut)
    (read : target.getVar 1 = some (.word w))
    (run : WordSemStateFiniteExact.evaluate (allocVar conf limit names) target = (q, result))
    (limitBound : limit < 2 ^ width / 8) :
    (q = some .notEnoughSpace → result.ffi = source.ffi ∧ optionLe result.stackMax source.stackMax ∧
      (conf.gcKind ≠ .none ∧ w.toNat / 4 < limit ∧ DataSem.noThunksInRefs source.refs →
        ∀ (roots dups : List DataSem.Value) (n : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (visited : NumSet),
          roots.Perm (dups ++ sptToList cut ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) ∧
          (∀ v, v ∈ dups → v ∈ sptToList cut ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) ∧
          DataSem.sizeOfValues source.limits roots source.refs .ln = (n, refs, visited) →
            source.limits.heapLimit < n + (w.toNat / 4 + 1))) ∧
    (q ≠ some .notEnoughSpace → w.toNat / 4 < limit ∧
      stateRel conf l1 l2 {source with locals := cut, space := w.toNat / 4 + 1} result none locs ∧
      result.store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      result.code = target.code ∧ result.codeBuffer = target.codeBuffer ∧
      result.dataBuffer = target.dataBuffer ∧ result.compileOracle = target.compileOracle ∧ q = none) := by
  have good : goodDimindex width := related.2.2.2.2.2.2.1
  have heap := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap0, cap, offset, sp0, sp1, gens, heapStore, inv, memBound, spaceBound⟩ := heap
  obtain ⟨_, _, _, _, _, _, _, curr, other, _, _, currEq, _, nextEq, triggerEq, _, heapLenEq, _⟩ := heapStore
  have limitWord : limit < 2 ^ width := by
    have pos : 0 < 2 ^ width := Nat.pow_pos (by decide)
    have divide : 2 ^ width / 8 ≤ 2 ^ width := Nat.div_le_self _ _
    omega
  have widthBig : 2 < width := by rcases good with h | h <;> subst width <;> decide
  have twoPow : 2 < 2 ^ width := by rcases good with h | h <;> subst width <;> norm_num
  have shiftRead : target.wordExp (shiftN .lsr (.var 1) 2) = some (.word (w >>> 2)) := by
    simp [shiftN, WordSemStateFiniteExact.wordExp, read, wordShiftHOL, Nat.mod_eq_of_lt twoPow, widthBig]
  have cmpEq : wordSemWordCmp .lower (.word (w >>> 2)) (.word (BitVec.ofNat width limit)) =
      some (decide (w.toNat / 4 < limit)) := by
    simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt limitWord, Nat.mod_eq_of_lt twoPow]
  simp only [allocVar, wordListSeq] at run
  rw [evalAssignSeq target 1 _ (.word (w >>> 2)) _ shiftRead] at run
  let t1 := target.setVar 1 (.word (w >>> 2))
  have t1read : t1.getVar 1 = some (.word (w >>> 2)) := by
    simp [t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
  change WordSemStateFiniteExact.evaluate (.seq _ _) t1 = (q, result) at run
  rw [evalSeqLocal] at run
  by_cases fits : w.toNat / 4 < limit
  · have compare : wordSemWordCmp .lower (.word (w >>> 2)) (.word (BitVec.ofNat width limit)) = some true := by
      simpa [fits] using cmpEq
    rw [evalIfLocal t1 .lower 1 (.imm (BitVec.ofNat width limit)) _ _ _ _ true t1read (by rfl) compare] at run
    simp only [ite_true] at run
    have requestedBound : (w.toNat / 4 + 1) * (width / 8) < 2 ^ width := by
      rcases good with h | h <;> subst width <;> norm_num at * <;> omega
    have allocWord : ((w >>> (2 : Nat)) + 1) <<< wordShiftAmount width =
        (gcAllocSize (w.toNat / 4 + 1) : BitVec width) := by
      rw [gcAllocSize, if_pos requestedBound]
      rcases good with h | h <;> subst width <;>
        apply BitVec.eq_of_toNat_eq <;>
        simp [wordShiftAmount, BitVec.toNat_shiftLeft,
          BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] <;> omega
    have shiftAmountBound : wordShiftAmount width < width := by
      rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
    have shiftAmountPow : wordShiftAmount width < 2 ^ width := by
      rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
    have wordTwo : (2 : BitVec width).toNat = 2 := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt twoPow]
    have branchRead : t1.wordExp (shiftN .lsl (.op .add [.var 1, .const 1]) (wordShiftAmount width)) =
        some (.word (gcAllocSize (w.toNat / 4 + 1))) := by
      simp [shiftN, WordSemStateFiniteExact.wordExp, t1read, wordOpHOL, wordOp, theWords,
        wordShiftHOL, wordTwo, Nat.mod_eq_of_lt shiftAmountPow, shiftAmountBound,
        - BitVec.shiftLeft_add_distrib, - BitVec.ofNat_eq_ofNat]
      exact allocWord
    let requested : BitVec width := gcAllocSize (w.toNat / 4 + 1)
    let t2 := t1.setVar 1 (.word requested)
    have assignRun : WordSemStateFiniteExact.evaluate
        (.assign 1 (shiftN .lsl (.op .add [.var 1, .const 1]) (wordShiftAmount width))) t1 = (none, t2) := by
      simp [WordSemStateFiniteExact.evaluate, - BitVec.ofNat_eq_ofNat, branchRead, t2, requested, WordSemStateFiniteExact.setVar]
    rw [assignRun] at run
    simp only at run
    let gap := (curr + StackRemove.bytesInWord width * BitVec.ofNat width (offset + sp0)) -
      (curr + StackRemove.bytesInWord width * BitVec.ofNat width offset)
    have gapRead : t2.wordExp (.op .sub [.lookup .triggerGC, .lookup .nextFree]) = some (.word gap) := by
      simp [t2, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.getStore, triggerEq, nextEq, wordOpHOL, wordOp, theWords, gap]
    rw [evalAssignSeq t2 3 _ (.word gap) _ gapRead] at run
    let t3 := t2.setVar 3 (.word gap)
    have t3one : t3.getVar 1 = some (.word requested) := by
      simp [t3, t2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
        sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have t3three : t3.getVar 3 = some (.word gap) := by
      simp [t3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
    have t1rel : stateRel conf l1 l2 source t1 none locs := by
      simpa [t1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using related
    have t2rel : stateRel conf l1 l2 source t2 none locs := by
      simpa [t2, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using t1rel
    have t3rel : stateRel conf l1 l2 source t3 none locs := by
      simpa [t3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using t2rel
    change WordSemStateFiniteExact.evaluate (.ite .lower 3 (.reg 1) _ _) t3 = (q, result) at run
    by_cases collect : gap < requested
    · have compare : wordSemWordCmp .lower (.word gap) (.word requested) = some true := by
        simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, collect]
      rw [evalIfLocal t3 .lower 3 (.reg 1) _ _ _ _ true t3three
        (by simpa [WordSemStateFiniteExact.getVarImm] using t3one) compare] at run
      simp only [ite_true] at run
      cases ffiFlag : conf.callEmptyFfi with
      | false =>
        simp only [silentFfi, ffiFlag, Bool.false_eq_true, if_false] at run
        rw [evalSeqLocal] at run
        simp only [show WordSemStateFiniteExact.evaluate .skip t3 = (none, t3) from by simp [WordSemStateFiniteExact.evaluate]] at run
        rw [evalSeqLocal] at run
        simp only [show WordSemStateFiniteExact.evaluate (.alloc 1 (adjustSets names)) t3 =
          WordSemStateFiniteExact.alloc requested (adjustSets names) t3 from by
            simp only [WordSemStateFiniteExact.evaluate, t3one]] at run
        cases allocRun : WordSemStateFiniteExact.alloc requested (adjustSets names) t3 with
        | mk outcome after =>
          simp only [allocRun] at run
          cases outcome with
          | none =>
            simp only [WordSemStateFiniteExact.evaluate] at run
            have h := allocLemma_gen conf l1 l2 source t3 after locs names cut
              (w.toNat / 4 + 1) none ⟨t3rel, cutEq, by simpa [requested] using allocRun⟩
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨by simp, ?_⟩
            intro _
            exact ⟨fits, (h.2 (by simp)).1, (h.2 (by simp)).2.2.1,
              (h.2 (by simp)).2.2.2.1, (h.2 (by simp)).2.2.2.2.1,
              (h.2 (by simp)).2.2.2.2.2.1, (h.2 (by simp)).2.2.2.2.2.2.1, rfl⟩
          | some outcome =>
            have h := allocLemma_gen conf l1 l2 source t3 after locs names cut
              (w.toNat / 4 + 1) (some outcome) ⟨t3rel, cutEq, by simpa [requested] using allocRun⟩
            obtain ⟨rfl, rfl⟩ := run
            constructor
            · intro isSpace
              have facts := h.1 isSpace
              exact ⟨facts.1, facts.2.1, fun conditions => facts.2.2 ⟨conditions.1, conditions.2.2⟩⟩
            · intro notSpace
              exact ⟨fits, (h.2 notSpace).1, (h.2 notSpace).2.2.1,
                (h.2 notSpace).2.2.2.1, (h.2 notSpace).2.2.2.2.1,
                (h.2 notSpace).2.2.2.2.2.1, (h.2 notSpace).2.2.2.2.2.2.1,
                (h.2 notSpace).2.2.2.2.2.2.2⟩
      | true =>
        obtain ⟨cutWord, cutWordEq⟩ := cutEnv_imp_wordCutEnv conf l1 l2 source target locs names cut ⟨related, cutEq⟩
        have ffiCut : wordSemCutEnv ((adjustSets names).1, sptInsert 1 () (adjustSets names).2) t3.locals =
            some (sptInsert 1 (.word requested) cutWord) := by
          simp only [t3, t2, t1, WordSemStateFiniteExact.setVar, sptInsert_insert_shadow]
          rw [cutKeepOdd names (sptInsert 1 (.word requested) target.locals) 3 _ (by decide) (by decide),
            cutEnvInsertOne names target.locals (.word requested), cutWordEq]
          rfl
        have ffiRun := evaluateSilentKeep conf l1 l2 source t3 locs names _ ffiFlag t3rel ffiCut
        rw [evalSeqLocal, ffiRun] at run
        simp only at run
        let cutTarget : WordSemStateFiniteExact width C F :=
          {target with locals := cutWord, fpRegs := HolFiniteMapExact.empty}
        have cutRelated : stateRel conf l1 l2 {source with locals := cut} cutTarget none locs := by
          have h := stateRel_cutEnv_cutEnv conf l1 l2 source target locs names cut cutWord ⟨related, cutEq, cutWordEq⟩
          exact stateRel_withFpRegs conf l1 l2 _ _ none locs HolFiniteMapExact.empty h
        have recut : DataSem.cutEnv names cut = some cut := cutEnv_idempotent names source.locals cut cutEq
        have ffiState : {t3 with locals := sptInsert 1 (.word requested) cutWord, fpRegs := HolFiniteMapExact.empty, memory := t3.memory, ffi := t3.ffi} =
            {cutTarget with locals := sptInsert 1 (.word requested) cutTarget.locals} := by
          simp [cutTarget, t3, t2, t1, WordSemStateFiniteExact.setVar]
        rw [ffiState, evalSeqLocal] at run
        simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
          sptLookup_sptInsert_same, alloc_locals_insert_one] at run
        cases allocRun : WordSemStateFiniteExact.alloc requested (adjustSets names) cutTarget with
        | mk outcome after =>
          simp only [allocRun] at run
          have h := allocLemma_gen conf l1 l2 {source with locals := cut} cutTarget after locs names cut
            (w.toNat / 4 + 1) outcome ⟨cutRelated, recut, by simpa [requested] using allocRun⟩
          cases outcome with
          | some e =>
            obtain ⟨rfl, rfl⟩ := run
            constructor
            · intro fail
              have facts := h.1 fail
              exact ⟨facts.1, facts.2.1, fun cond => facts.2.2 ⟨cond.1, cond.2.2⟩⟩
            · intro nonfail
              have impossible := (h.2 nonfail).2.2.2.2.2.2.2
              contradiction
          | none =>
            have post := h.2 (by simp)
            let postSource := {source with locals := cut, space := w.toNat / 4 + 1}
            have postRel : stateRel conf l1 l2 postSource after none locs := by
              simpa [postSource] using post.1
            have postCutSource : DataSem.cutEnv names postSource.locals = some cut := by
              simpa [postSource] using recut
            obtain ⟨endCut, endCutEq⟩ := cutEnv_imp_wordCutEnv conf l1 l2 postSource after locs names cut ⟨postRel, postCutSource⟩
            have finalRun := evaluate_silentFfi_three conf l1 l2 postSource after locs names endCut ⟨ffiFlag, postRel, endCutEq⟩
            simp only at run
            rw [finalRun] at run
            obtain ⟨rfl, rfl⟩ := run
            have finalRel := stateRel_cutEnv_cutEnv conf l1 l2 postSource after locs names cut endCut ⟨postRel, postCutSource, endCutEq⟩
            have finalFp := stateRel_withFpRegs conf l1 l2 _ _ none locs HolFiniteMapExact.empty finalRel
            refine ⟨by simp, fun _ => ⟨fits, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩⟩
            · simpa [postSource] using finalFp
            · simpa [cutTarget] using post.2.2.1
            · simpa [cutTarget] using post.2.2.2.1
            · simpa [cutTarget] using post.2.2.2.2.1
            · simpa [cutTarget] using post.2.2.2.2.2.1
            · simpa [cutTarget] using post.2.2.2.2.2.2.1
    · have compare : wordSemWordCmp .lower (.word gap) (.word requested) = some false := by
        simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, collect]
      rw [evalIfLocal t3 .lower 3 (.reg 1) _ _ _ _ false t3three
        (by simpa [WordSemStateFiniteExact.getVarImm] using t3one) compare] at run
      simp [WordSemStateFiniteExact.evaluate] at run
      obtain ⟨rfl, rfl⟩ := run
      have gapLe : requested.toNat ≤ gap.toNat := by
        apply Nat.le_of_not_gt
        intro h
        exact collect (BitVec.lt_def.mpr h)
      have hasSpace : t3.hasSpace (.word requested) = some true := by
        simp only [WordSemStateFiniteExact.hasSpace, WordSemStateFiniteExact.getStore,
          t3, t2, t1, WordSemStateFiniteExact.setVar, nextEq, triggerEq]
        change some (decide (requested.toNat ≤ gap.toNat)) = some true
        simp [gapLe]
      have cutRel := stateRel_cutEnv conf l1 l2 source t3 locs names cut ⟨t3rel, cutEq⟩
      have postRel := hasSpace_stateRel conf l1 l2 {source with locals := cut} t3 locs
        (w.toNat / 4 + 1) ⟨by simpa [requested] using hasSpace, cutRel⟩
      refine ⟨by simp, ?_⟩
      intro _
      refine ⟨fits, postRel, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
        simp [t3, t2, t1, WordSemStateFiniteExact.setVar]
  · have compare : wordSemWordCmp .lower (.word (w >>> 2)) (.word (BitVec.ofNat width limit)) = some false := by
      simpa [fits] using cmpEq
    rw [evalIfLocal t1 .lower 1 (.imm (BitVec.ofNat width limit)) _ _ _ _ false t1read (by rfl) compare] at run
    simp only [Bool.false_eq_true, if_false] at run
    let t2 := t1.setVar 1 (.word (-1))
    have assignRun : WordSemStateFiniteExact.evaluate (.assign 1 (.const (-1))) t1 = (none, t2) := by
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, t2, WordSemStateFiniteExact.setVar]
    rw [assignRun] at run
    simp only at run
    let gap := (curr + StackRemove.bytesInWord width * BitVec.ofNat width (offset + sp0)) -
      (curr + StackRemove.bytesInWord width * BitVec.ofNat width offset)
    have gapRead : t2.wordExp (.op .sub [.lookup .triggerGC, .lookup .nextFree]) = some (.word gap) := by
      simp [t2, t1, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.getStore, triggerEq, nextEq, wordOpHOL, wordOp, theWords, gap]
    rw [evalAssignSeq t2 3 _ (.word gap) _ gapRead] at run
    let t3 := t2.setVar 3 (.word gap)
    have t3one : t3.getVar 1 = some (.word (-1)) := by
      simp [t3, t2, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
        sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
    have t3three : t3.getVar 3 = some (.word gap) := by
      simp [t3, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
    have t1rel : stateRel conf l1 l2 source t1 none locs := by
      simpa [t1, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using related
    have t2rel : stateRel conf l1 l2 source t2 none locs := by
      simpa [t2, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using t1rel
    have t3rel : stateRel conf l1 l2 source t3 none locs := by
      simpa [t3, WordSemStateFiniteExact.setVar, stateRel_insertOdd] using t2rel
    have gapLt : gap < (-1 : BitVec width) := by
      apply BitVec.lt_def.mpr
      by_contra h
      have maxLe : (-1 : BitVec width).toNat ≤ gap.toNat := Nat.le_of_not_gt h
      have zero := (wordMaxLeIffAddOneEqZero gap).mp maxLe
      have gapEq : gap = wordSemBytesInWord * BitVec.ofNat width sp0 := by
        simp [gap, StackRemove.bytesInWord, wordSemBytesInWord, BitVec.ofNat_add,
          BitVec.mul_add]
      rw [gapEq] at zero
      exact bytesInWordAddOneNeZero _ good zero
    have compare : wordSemWordCmp .lower (.word gap) (.word (-1)) = some true := by
      simpa only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq, decide_eq_true_eq] using gapLt
    rw [evalIfLocal t3 .lower 3 (.reg 1) _ _ _ _ true t3three
      (by simpa [WordSemStateFiniteExact.getVarImm] using t3one) compare] at run
    simp only [ite_true] at run
    cases ffiFlag : conf.callEmptyFfi with
    | false =>
      simp only [silentFfi, ffiFlag, Bool.false_eq_true, if_false] at run
      rw [evalSeqLocal] at run
      simp only [show WordSemStateFiniteExact.evaluate .skip t3 = (none, t3) from by simp [WordSemStateFiniteExact.evaluate]] at run
      rw [evalSeqLocal] at run
      simp only [show WordSemStateFiniteExact.evaluate (.alloc 1 (adjustSets names)) t3 =
        WordSemStateFiniteExact.alloc (-1) (adjustSets names) t3 from by
          simp only [WordSemStateFiniteExact.evaluate, t3one]] at run
      cases allocRun : WordSemStateFiniteExact.alloc (-1) (adjustSets names) t3 with
      | mk outcome after =>
        have facts := allocFail conf l1 l2 source t3 after locs names cut outcome ⟨good, t3rel, cutEq, allocRun⟩
        have failFacts := facts.1 facts.2
        simp only [allocRun, facts.2] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨fun _ => ⟨failFacts.1, failFacts.2, by simp [fits]⟩, by simp⟩
    | true =>
      obtain ⟨cutWord, cutWordEq⟩ := cutEnv_imp_wordCutEnv conf l1 l2 source target locs names cut ⟨related, cutEq⟩
      have ffiCut : wordSemCutEnv ((adjustSets names).1, sptInsert 1 () (adjustSets names).2) t3.locals =
          some (sptInsert 1 (.word (-1)) cutWord) := by
        simp only [t3, t2, t1, WordSemStateFiniteExact.setVar, sptInsert_insert_shadow]
        rw [cutKeepOdd names (sptInsert 1 (.word (-1)) target.locals) 3 _ (by decide) (by decide),
          cutEnvInsertOne names target.locals (.word (-1)), cutWordEq]
        rfl
      have ffiRun := evaluateSilentKeep conf l1 l2 source t3 locs names _ ffiFlag t3rel ffiCut
      rw [evalSeqLocal, ffiRun] at run
      simp only at run
      let cutTarget : WordSemStateFiniteExact width C F :=
        {target with locals := cutWord, fpRegs := HolFiniteMapExact.empty}
      have cutRelated : stateRel conf l1 l2 {source with locals := cut} cutTarget none locs := by
        have h := stateRel_cutEnv_cutEnv conf l1 l2 source target locs names cut cutWord ⟨related, cutEq, cutWordEq⟩
        exact stateRel_withFpRegs conf l1 l2 _ _ none locs HolFiniteMapExact.empty h
      have recut : DataSem.cutEnv names cut = some cut := cutEnv_idempotent names source.locals cut cutEq
      have ffiState : {t3 with locals := sptInsert 1 (.word (-1)) cutWord, fpRegs := HolFiniteMapExact.empty, memory := t3.memory, ffi := t3.ffi} =
          {cutTarget with locals := sptInsert 1 (.word (-1)) cutTarget.locals} := by
        simp [cutTarget, t3, t2, t1, WordSemStateFiniteExact.setVar]
      rw [ffiState, evalSeqLocal] at run
      simp only [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar,
        sptLookup_sptInsert_same, alloc_locals_insert_one] at run
      cases allocRun : WordSemStateFiniteExact.alloc (-1) (adjustSets names) cutTarget with
      | mk outcome after =>
        have facts := allocFail conf l1 l2 {source with locals := cut} cutTarget after locs names cut outcome ⟨good, cutRelated, recut, allocRun⟩
        have failFacts := facts.1 facts.2
        simp only [allocRun, facts.2] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨fun _ => ⟨failFacts.1, failFacts.2, by simp [fits]⟩, by simp⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
