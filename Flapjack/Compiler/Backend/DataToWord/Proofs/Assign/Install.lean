module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BignumHalt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.InstallStubs
public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithLocals
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Equal
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GiveUp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemoryLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SmallStateLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CodePointer

@[expose] public section

/-! The `Install` assignment (`data_to_word_assignProofScript.sml`
`assign_Install`, lines 2451-2745) and its prerequisites. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace InstallWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end InstallWitness

/-- The bignum guard preserves the original conditional result. The evaluator
inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_BignumHalt"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateBignumHalt {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (reg : Nat) (w : BitVec width)
    (related : stateRel conf l1 l2 source target none locs)
    (read : target.getVar reg = some (.word w)) :
    ∃ r, WordSemStateFiniteExact.evaluate (bignumHalt reg) target =
      (if w.getLsbD 0 then (some .notEnoughSpace, r) else (none, target)) ∧
      r.ffi = source.ffi ∧ target.ffi = source.ffi := by
  obtain ⟨r, run, rffi, tffi, -⟩ := evaluateBignumHalt2 conf l1 l2 source target locs reg w related read
  exact ⟨r, run, rffi, tffi⟩

/-- A successful primitive whose result state is still space-safe is an
admitted operation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml"
  "do_app_safe_for_space_allowed_op"]
theorem doApp_safeForSpace_allowedOp {C F : Type} (op : ClosLang.Op)
    (xs : List DataSem.Value) (s : DataSem.State C F) (r : DataSem.Value) (s1 : DataSem.State C F)
    (h : DataSem.doApp op xs s = .val (r, s1) ∧ s1.safeForSpace = true) :
    DataSem.allowedOp op xs.length := by
  obtain ⟨run, safe⟩ := h
  by_contra notAllowed
  unfold DataSem.doApp at run
  split at run
  · simp only [DataSem.doInstall] at run
    repeat (first | split at run | simp only [reduceCtorEq] at run)
    all_goals (try cases run)
    all_goals simp_all
  · cases run
  · cases run
  · split at run
    · cases run
    · rename_i space spaceRun
      dsimp only at run
      have flagFalse : (DataSem.doStack op xs (DataSem.doLimSafe space op xs)).safeForSpace = false := by
        rw [DataProps.doStack_doLimSafe_safeForSpace op xs s space spaceRun]
        simp [DataProps.doAppSafe, notAllowed]
      have := DataProps.doAppAux_safeForSpace_of_false op xs _ s1 r run flagFalse
      simp [this] at safe

/-- Invert a successful source installation; local proof infrastructure for
`assign_Install`. -/
private theorem installSource {C F : Type} (values : List DataSem.Value)
    (cut resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp .install values cut = .val (result, resultState)) :
    ∃ hv1 hv2 q1 q2 cfg k entry rest cfg',
      values = [hv1, hv2, .number (Int.ofNat q1.length), .number (Int.ofNat q2.length)] ∧
      DataSem.valueToBytes hv1 = some q1 ∧ DataSem.valueToWords hv2 = some q2 ∧
      cut.compileOracle 0 = (cfg, (k, entry) :: rest) ∧
      cut.compile cfg ((k, entry) :: rest) = some (q1, q2, cfg') ∧
      (cut.compileOracle 1).1 = cfg' ∧
      result = .codePtr k ∧
      resultState = { cut with
        stackMax := none
        stackFrameSizes := .ln
        safeForSpace := false
        code := sptUnion cut.code (sptFromAList ((k, entry) :: rest))
        compileOracle := fun n => cut.compileOracle (n + 1) } := by
  simp only [DataSem.doApp, DataSem.doInstall] at run
  repeat (first | split at run | simp only [reduceCtorEq] at run)
  all_goals (try (cases run))
  rename_i _ v1 v2 len1 len2 _ _ bytes data hb hd hlen _ programs _ _ cfg' label snd tail hc hp heqs
  obtain ⟨rfl, rfl, hcfg⟩ := heqs
  simp only [ne_eq, not_or, not_not] at hlen
  obtain ⟨rfl, rfl⟩ := hlen
  refine ⟨v1, v2, bytes, data, (cut.compileOracle 0).1, label, snd, tail, cfg', rfl, hb, hd, ?_, ?_, hcfg, rfl, ?_⟩
  · rw [← hp]
  · rw [← hp]; exact hc
  · rw [hp]

/-- Set a store entry before a continuation. -/
private theorem installSeqSet {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (v : WordStoreHOL) (exp : WordLangExpHOL (BitVec width))
    (w : WordLocW width) (tail : WordLangProgHOL (BitVec width))
    (ok : v ≠ .handler ∧ v ≠ .bitmapBase) (read : s.wordExp exp = some w) :
    WordSemStateFiniteExact.evaluate (.seq (.set v exp) tail) s =
      WordSemStateFiniteExact.evaluate tail (s.setStore v w) := by
  simp [WordSemStateFiniteExact.evaluate, read, ok.1, ok.2, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setStore]

/-- Cutting to the return-address register keeps that register. -/
private theorem installCutZero {α : Type} (env : Spt α) (x : α) (h : sptLookup 0 env = some x) :
    ∃ cut, wordSemCutEnv (.ls (), .ln) env = some cut ∧ sptLookup 0 cut = some x := by
  have live : LoopSemStateFiniteExact.sptSubsetLive (.ls () : Spt Unit) env := by
    intro key mem
    rw [sptMem_ls] at mem
    subst key
    exact (sptMem_iff_lookup 0 env).mpr ⟨x, h⟩
  have liveLn : LoopSemStateFiniteExact.sptSubsetLive (.ln : Spt Unit) env := by
    intro key mem
    exact absurd mem (sptMem_ln key)
  refine ⟨sptUnion (sptInter env (.ln : Spt Unit)) (sptInter env (.ls () : Spt Unit)),
    by simp [wordSemCutEnv, wordSemCutEnvs, wordSemCutNames, live, liveLn], ?_⟩
  rw [sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases, h]
  simp [sptLookup]

/-- One successful `Install` instruction before a continuation. -/
private theorem installSeqInstall {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (r1 r2 r3 r4 : Nat) (names : WordLangCutsetsHOL)
    (tail : WordLangProgHOL (BitVec width)) (env : Spt (WordLocW width)) (w1 w2 w3 w4 : BitVec width)
    (cfg cfg' : C) (k : Nat) (p : Nat × WordLangProgHOL (BitVec width))
    (tr : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bytes : List (BitVec 8)) (data : List (BitVec width))
    (cb : WordSemBuffer width 8) (db : WordSemBuffer width width)
    (cut : wordSemCutEnv names s.locals = some env)
    (g1 : s.getVar r1 = some (.word w1)) (g2 : s.getVar r2 = some (.word w2))
    (g3 : s.getVar r3 = some (.word w3)) (g4 : s.getVar r4 = some (.word w4))
    (oracle : s.compileOracle 0 = (cfg, (k, p) :: tr))
    (flushC : wordSemBufferFlush s.codeBuffer w1 w2 = some (bytes, cb))
    (flushD : wordSemBufferFlush s.dataBuffer w3 w4 = some (data, db))
    (comp : s.compile cfg ((k, p) :: tr) = some (bytes, data, cfg'))
    (next : (s.compileOracle 1).1 = cfg') :
    WordSemStateFiniteExact.evaluate (.seq (.install r1 r2 r3 r4 names) tail) s =
      WordSemStateFiniteExact.evaluate tail { s with
        codeBuffer := cb
        dataBuffer := db
        code := sptUnion s.code (sptFromAList ((k, p) :: tr))
        locals := sptInsert r1 (.loc k 0) env
        fpRegs := HolFiniteMapExact.empty
        compileOracle := holShiftSeq 1 s.compileOracle
        stackMax := none
        stackSize := .ln } := by
  simp [WordSemStateFiniteExact.evaluate, cut, g1, g2, g3, g4, oracle, flushC, flushD, comp,
    holShiftSeq, next, WordSemStateFiniteExact.fixClock]

/-- The installation stubs copy both buffers, install the compiled code and
return its code pointer; local proof infrastructure for `assign_Install`,
following the HOL proof's uses of `InstallCode_code_thm`,
`InstallData_code_thm` and the evaluation of `Install_code`. -/
private theorem installStubsRun {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (e0 : WordSemStateFiniteExact width C F) (hv1 hv2 : DataSem.Value)
    (q1 : List (BitVec 8)) (q2 : List (BitVec 64)) (a1 a2 : WordLocW width)
    (vars : List (DataSem.Value × WordLocW width)) (sp ts : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (n l k : Nat) (cfg cfg' : C)
    (p : Nat × WordLangProgHOL (BitVec width)) (tr : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (rel : memoryRel conf e0.be ts refs sp e0.store e0.memory e0.mdomain ((hv1, a1) :: (hv2, a2) :: vars))
    (codeIC : sptLookup installCodeLocation e0.code = some (4, installCodeStub conf))
    (codeID : sptLookup installDataLocation e0.code = some (4, installDataStub conf))
    (codeI : sptLookup installLocation e0.code = some (3, installCode conf))
    (bitmap : e0.store.lookup .bitmapBuffer = some (.word e0.dataBuffer.position))
    (codeb : e0.store.lookup .codeBuffer = some (.word e0.codeBuffer.position))
    (cbEmpty : e0.codeBuffer.buffer = []) (dbEmpty : e0.dataBuffer.buffer = [])
    (bytes : DataSem.valueToBytes hv1 = some q1) (words : DataSem.valueToWords hv2 = some q2)
    (space1 : q1.length ≤ e0.codeBuffer.spaceLeft) (space2 : q2.length ≤ e0.dataBuffer.spaceLeft)
    (clock : q1.length + q2.length + 2 ≤ e0.clock)
    (r0 : e0.getVar 0 = some (.loc n l)) (r2 : e0.getVar 2 = some a1) (r4 : e0.getVar 4 = some a2)
    (r6 : e0.getVar 6 = some (.word e0.codeBuffer.position))
    (oracle : e0.compileOracle 0 = (cfg, (k, p) :: tr))
    (comp : e0.compile cfg ((k, p) :: tr) = some (q1, q2.map w2wUpper, cfg'))
    (next : (e0.compileOracle 1).1 = cfg')
    (good : goodDimindex width) :
    ∃ ck, WordSemStateFiniteExact.evaluate (installCodeStub conf) e0 =
      (some (.result (.loc n l) [.loc k 0]),
        { e0 with
          locals := .ln
          localsSize := some 0
          clock := ck
          store := (e0.store.updateEq (.bitmapBuffer, .word (e0.dataBuffer.position +
              wordSemBytesInWord * BitVec.ofNat width q2.length))).updateEq
            (.codeBuffer, .word (e0.codeBuffer.position + BitVec.ofNat width q1.length))
          codeBuffer := ⟨e0.codeBuffer.position + BitVec.ofNat width q1.length,
            [], e0.codeBuffer.spaceLeft - q1.length⟩
          dataBuffer := ⟨e0.dataBuffer.position + wordSemBytesInWord * BitVec.ofNat width q2.length,
            [], e0.dataBuffer.spaceLeft - q2.length⟩
          code := sptUnion e0.code (sptFromAList ((k, p) :: tr))
          fpRegs := HolFiniteMapExact.empty
          compileOracle := holShiftSeq 1 e0.compileOracle
          stackMax := none
          stackSize := .ln }) := by
  obtain ⟨lsz, smx, eqIC⟩ := installCode_correct e0 conf hv1 q1 a1 a2 (.loc n l)
    (.word e0.dataBuffer.position) ((hv2, a2) :: vars) sp refs ts
    ⟨rel, codeIC, codeID, bitmap, bytes, space1, by omega, r0, r2, r4, by simpa [cbEmpty] using r6, good⟩
  let cpos := e0.codeBuffer.position + BitVec.ofNat width (e0.codeBuffer.buffer.length + q1.length)
  let e1 : WordSemStateFiniteExact width C F := { e0 with
    locals := sptFromList2 [.loc n l, .word e0.dataBuffer.position, a2, .word cpos]
    localsSize := lsz
    clock := e0.clock - q1.length - 1
    codeBuffer := { e0.codeBuffer with
      buffer := e0.codeBuffer.buffer ++ q1
      spaceLeft := e0.codeBuffer.spaceLeft - q1.length }
    stackMax := smx }
  have relTl := memoryRel_tl conf e0.be ts refs sp e0.store e0.memory e0.mdomain _ _ rel
  obtain ⟨smx2, lsz2, eqID⟩ := installData_correct e1 conf hv2 q2 (.word cpos) a2 (.loc n l) vars sp refs ts
    ⟨relTl, codeID, codeI, words, space2, by simp [e1]; omega,
      by simp [e1, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      by simp [e1, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup, dbEmpty],
      by simp [e1, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup],
      by simp [e1, WordSemStateFiniteExact.getVar, WordToStackProofs.fromList2Lookup], good⟩
  let dpos := e1.dataBuffer.position + wordSemBytesInWord * BitVec.ofNat width e1.dataBuffer.buffer.length +
    wordSemBytesInWord * BitVec.ofNat width q2.length
  let e2 : WordSemStateFiniteExact width C F := { e1 with
    locals := sptFromList2 [.loc n l, .word dpos, .word cpos]
    clock := e1.clock - q2.length - 1
    dataBuffer := { e1.dataBuffer with
      buffer := e1.dataBuffer.buffer ++ q2.map w2wUpper
      spaceLeft := e1.dataBuffer.spaceLeft - q2.length }
    localsSize := lsz2
    stackMax := smx2 }
  change _ = match WordSemStateFiniteExact.evaluate (installCode conf) e2 with
    | (res, s) => if wordSemBadFunReturn res then (some (WordSemResult.error : WordSemResult width), s) else (res, s) at eqID
  let RR : WordSemStateFiniteExact width C F := { e2 with
    locals := .ln
    localsSize := some 0
    store := (e2.store.updateEq (.bitmapBuffer, .word dpos)).updateEq (.codeBuffer, .word cpos)
    codeBuffer := ⟨cpos, [], e2.codeBuffer.spaceLeft⟩
    dataBuffer := ⟨dpos, [], e2.dataBuffer.spaceLeft⟩
    code := sptUnion e2.code (sptFromAList ((k, p) :: tr))
    fpRegs := HolFiniteMapExact.empty
    compileOracle := holShiftSeq 1 e2.compileOracle
    stackMax := none
    stackSize := .ln }
  have eqI : WordSemStateFiniteExact.evaluate (installCode (width := width) conf) e2 =
      (some (.result (.loc n l) [.loc k 0]), RR) := by
    simp only [installCode, wordListSeq]
    rw [installSeqAssign e2 1 _ (.word e0.dataBuffer.position) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, e2, e1, bitmap])]
    rw [installSeqAssign _ 3 _ (.word e0.codeBuffer.position) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, WordSemStateFiniteExact.setVar,
        e2, e1, codeb])]
    rw [installSeqSet _ .bitmapBuffer (.var 2) (.word dpos) _ ⟨by decide, by decide⟩ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        installLookupInsert, e2, WordToStackProofs.fromList2Lookup])]
    rw [installSeqSet _ .codeBuffer (.var 4) (.word cpos) _ ⟨by decide, by decide⟩ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.setStore, installLookupInsert, e2, WordToStackProofs.fromList2Lookup])]
    let s4 := WordSemStateFiniteExact.setStore .codeBuffer (.word cpos)
      (WordSemStateFiniteExact.setStore .bitmapBuffer (.word dpos)
        (WordSemStateFiniteExact.setVar 3 (.word e0.codeBuffer.position)
          (WordSemStateFiniteExact.setVar 1 (.word e0.dataBuffer.position) e2)))
    change WordSemStateFiniteExact.evaluate _ s4 = _
    obtain ⟨env, cutRun, env0⟩ := installCutZero s4.locals (.loc n l) (by
      simp [s4, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, installLookupInsert, e2,
        WordToStackProofs.fromList2Lookup])
    rw [installSeqInstall s4 3 4 1 2 _ _ env e0.codeBuffer.position cpos e0.dataBuffer.position dpos
      cfg cfg' k p tr q1 (q2.map w2wUpper) ⟨cpos, [], e2.codeBuffer.spaceLeft⟩
      ⟨dpos, [], e2.dataBuffer.spaceLeft⟩ cutRun
      (by simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setStore,
        WordSemStateFiniteExact.setVar, installLookupInsert])
      (by simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setStore,
        WordSemStateFiniteExact.setVar, installLookupInsert, e2, WordToStackProofs.fromList2Lookup])
      (by simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setStore,
        WordSemStateFiniteExact.setVar, installLookupInsert])
      (by simp [s4, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setStore,
        WordSemStateFiniteExact.setVar, installLookupInsert, e2, WordToStackProofs.fromList2Lookup])
      (by simpa [s4, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, e2, e1] using oracle)
      (by simp [s4, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, e2, e1, cpos,
        wordSemBufferFlush, cbEmpty])
      (by simp [s4, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, e2, e1, dpos,
        wordSemBufferFlush, dbEmpty, wordSemBytesInWord])
      (by simpa [s4, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, e2, e1] using comp)
      (by simpa [s4, WordSemStateFiniteExact.setStore, WordSemStateFiniteExact.setVar, e2, e1] using next)]
    simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVars,
      installLookupInsert, env0, WordSemStateFiniteExact.flushState]
    rfl
  rw [eqIC, eqID, eqI]
  refine ⟨RR.clock, ?_⟩
  simp only [wordSemBadFunReturn, Bool.false_eq_true, if_false]
  simp [RR, e2, e1, cpos, dpos, cbEmpty, dbEmpty]

/-- The small length immediate shifted right by two is the length. -/
private theorem installSmallShift {width : Nat} [NeZero width] (good : goodDimindex width) (len : Nat)
    (small : smallInt width (Int.ofNat len)) :
    ((smallnum (Int.ofNat len) : BitVec width) >>> (2 : Nat)).toNat = len := by
  unfold smallnum
  rw [if_neg (by simp)]
  unfold smallInt at small
  rcases good with rfl | rfl <;> simp at small ⊢ <;> omega

/-- A data length that passes the free-space check fits the data buffer. -/
private theorem installDataSpace {width : Nat} [NeZero width] (good : goodDimindex width) (len sl : Nat)
    (small : smallInt width (Int.ofNat len))
    (h : ¬ ((BitVec.ofNat width (width / 8) * BitVec.ofNat width sl) >>> wordShiftAmount width <
      (smallnum (Int.ofNat len) : BitVec width) >>> (2 : Nat))) : len ≤ sl := by
  have shifted := installSmallShift good len small
  rw [BitVec.lt_def, shifted] at h
  rcases good with rfl | rfl <;> simp [wordShiftAmount] at h <;> omega

/-- A code length that passes the free-space check fits the code buffer. -/
private theorem installCodeSpace {width : Nat} [NeZero width] (good : goodDimindex width) (len sl : Nat)
    (small : smallInt width (Int.ofNat len))
    (h : ¬ (BitVec.ofNat width sl < (smallnum (Int.ofNat len) : BitVec width) >>> (2 : Nat))) :
    len ≤ sl := by
  have shifted := installSmallShift good len small
  rw [BitVec.lt_def, shifted] at h
  simp at h
  have := Nat.mod_le sl (2 ^ width)
  omega

/-- Branch on an unsigned comparison of two word registers. -/
private theorem installEvalLower {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (r r' : Nat) (a b : BitVec width)
    (c1 c2 : WordLangProgHOL (BitVec width))
    (ra : s.getVar r = some (.word a)) (rb : s.getVar r' = some (.word b)) :
    WordSemStateFiniteExact.evaluate (.ite .lower r (.reg r') c1 c2) s =
      if a < b then WordSemStateFiniteExact.evaluate c1 s else WordSemStateFiniteExact.evaluate c2 s := by
  simp [WordSemStateFiniteExact.evaluate, ra, rb, WordSemStateFiniteExact.getVarImm,
    wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : a < b <;> simp [h]

/-- Evaluate a returning stub call from its established premises, as in the
HOL proof's direct evaluation of the call. -/
private theorem installDirectCall {width : Nat} [NeZero width] {C F : Type}
    (s returned restored : WordSemStateFiniteExact width C F) (names : WordLangCutsetsHOL)
    (first second : Spt (WordLocW width)) (n l d loc : Nat) (argNames : List Nat)
    (xs : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width)) (res : WordLocW width)
    (args : s.getVars argNames = some xs)
    (code : sptLookup loc s.code = some (xs.length + 1, prog))
    (cut : wordSemCutEnvs names s.locals = some (first, second))
    (live : ¬ sptDomainEmpty names.1) (clock : s.clock ≠ 0)
    (run : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv (.loc n l :: xs) (sptLookup loc s.stackSize)
        (WordSemStateFiniteExact.pushEnv (first, second) none (WordSemStateFiniteExact.decClock s))) =
      (some (.result (.loc n l) [res]), returned))
    (pop : WordSemStateFiniteExact.popEnv returned = some restored)
    (domain : sptDomainEqUnion restored.locals first second) :
    WordSemStateFiniteExact.evaluate
      (.call (some ([d], names, .skip, n, l)) (some loc) argNames none) s =
      (none, WordSemStateFiniteExact.setVars [d] [res] restored) := by
  rw [WordSemStateFiniteExact.evaluate]
  simp only [args, wordSemBadDestArgs, Bool.false_eq_true, if_false, wordSemAddRetLoc,
    wordSemFindCode, code, List.length_cons, live, not_false_eq_true,
    List.nodup_cons, List.mem_nil_iff, cut, clock]
  simp
  rw [WordSemStateFiniteExact.fix_clock_evaluate, run]
  simp only [List.length_cons, List.length_nil, not_true_eq_false, false_or, if_false]
  rw [pop]
  simp [domain, WordSemStateFiniteExact.evaluate]

/-- A sequence whose first command finishes normally without changing the
state continues with the second command. -/
private theorem installSeqSame {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (c1 c2 : WordLangProgHOL (BitVec width))
    (h : WordSemStateFiniteExact.evaluate c1 s = (none, s)) :
    WordSemStateFiniteExact.evaluate (.seq c1 c2) s = WordSemStateFiniteExact.evaluate c2 s := by
  simp [WordSemStateFiniteExact.evaluate, h, WordSemStateFiniteExact.fixClock]

/-- A sequence whose first command stops returns that result. -/
private theorem installSeqStop {width : Nat} [NeZero width] {C F : Type}
    (s s1 : WordSemStateFiniteExact width C F) (c1 c2 : WordLangProgHOL (BitVec width))
    (x : WordSemResult width) (h : WordSemStateFiniteExact.evaluate c1 s = (some x, s1)) :
    ∃ s2, WordSemStateFiniteExact.evaluate (.seq c1 c2) s = (some x, s2) ∧ s2.ffi = s1.ffi := by
  refine ⟨(WordSemStateFiniteExact.fixClock s (some x, s1)).2, ?_, rfl⟩
  simp [WordSemStateFiniteExact.evaluate, h]
  rfl

/-- Installation satisfies the complete HOL assignment simulation. The word
evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_Install"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignInstall_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat)
    (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : op = .install)
    (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values)
    (depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q, r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace →
        stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  subst op
  cases names with
  | none => simp [DataLang.opRequiresNames] at validNames
  | some names =>
    obtain ⟨wordCut, words, cutWord, getWord, lens1, lens2, relCut, relCutWord⟩ :=
      stateRel_cutStateOpt_some conf l1 l2 source target locs args values names cut ⟨related, argsEq, cutEq⟩
    obtain ⟨hv1, hv2, q1, q2, cfg, k, entry, rest, cfg', rfl, bytes, wordsOk, oracle0, compileOk, oracle1,
      rfl, rfl⟩ := installSource values cut resultState result run
    obtain ⟨v1, v2, v3, v4, rfl⟩ : ∃ v1 v2 v3 v4, args = [v1, v2, v3, v4] := by
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩ <;> simp at lens1
      exact ⟨a, b, c, d, rfl⟩
    obtain ⟨w1, w2, w3, w4, rfl⟩ : ∃ w1 w2 w3 w4, words = [w1, w2, w3, w4] := by
      rcases words with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tail⟩⟩⟩⟩⟩ <;> simp at lens2
      exact ⟨a, b, c, d, rfl⟩
    have reads : target.getVar (adjustVar v1) = some w1 ∧ target.getVar (adjustVar v2) = some w2 ∧
        target.getVar (adjustVar v3) = some w3 ∧ target.getVar (adjustVar v4) = some w4 := by
      simp only [List.map, WordSemStateFiniteExact.getVars] at getWord
      revert getWord
      cases h1 : target.getVar (adjustVar v1) <;> cases h2 : target.getVar (adjustVar v2) <;>
        cases h3 : target.getVar (adjustVar v3) <;> cases h4 : target.getVar (adjustVar v4) <;> simp
    let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
      flatStack source.stack target.stack
    let stackVars := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++ envs
    have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
      target.store target.memory target.mdomain target envs [v1, v2, v3, v4] _ [w1, w2, w3, w4] (by
        refine ⟨?_, argsEq, getWord⟩
        simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    simp only [List.zip_cons_cons, List.zip_nil_right, List.cons_append, List.nil_append] at roots
    have good := related.2.2.2.2.2.2.1
    obtain ⟨x3, rfl, x3Bit⟩ := memoryRel_anyNumberImp conf target.be (holThe source.tstamps) source.refs
      source.space target.store target.memory target.mdomain _ w3 _
      ⟨good, memoryRel_tl _ _ _ _ _ _ _ _ _ _ (memoryRel_tl _ _ _ _ _ _ _ _ _ _ roots)⟩
    obtain ⟨x4, rfl, x4Bit⟩ := memoryRel_anyNumberImp conf target.be (holThe source.tstamps) source.refs
      source.space target.store target.memory target.mdomain _ w4 _
      ⟨good, memoryRel_tl _ _ _ _ _ _ _ _ _ _ (memoryRel_tl _ _ _ _ _ _ _ _ _ _
        (memoryRel_tl _ _ _ _ _ _ _ _ _ _ roots))⟩
    simp only [compileAssign, arg4, assignInstall, wordListSeq]
    by_cases b3 : x3.getLsbD 0 = true
    · obtain ⟨r, giveRun, rffi, tffi, -⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
      have h1 : WordSemStateFiniteExact.evaluate (bignumHalt (adjustVar v3)) target =
          (some .notEnoughSpace, r) := by
        unfold bignumHalt
        rw [installEvalTestOne target _ x3 _ _ reads.2.2.1, b3, if_pos rfl]
        exact giveRun
      obtain ⟨s2, run2, ffi2⟩ := installSeqStop _ _ _ _ _ h1
      exact ⟨_, _, run2, fun _ => ⟨by rw [ffi2, rffi, tffi], by simp [optionLe], fun _ => trivial⟩,
        fun h => (h rfl).elim⟩
    have h3 : WordSemStateFiniteExact.evaluate (bignumHalt (adjustVar v3)) target = (none, target) := by
      unfold bignumHalt
      rw [installEvalTestOne target _ x3 _ _ reads.2.2.1, if_neg b3]
      simp [WordSemStateFiniteExact.evaluate]
    rw [installSeqSame _ _ _ h3]
    by_cases b4 : x4.getLsbD 0 = true
    · obtain ⟨r, giveRun, rffi, tffi, -⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
      have h1 : WordSemStateFiniteExact.evaluate (bignumHalt (adjustVar v4)) target =
          (some .notEnoughSpace, r) := by
        unfold bignumHalt
        rw [installEvalTestOne target _ x4 _ _ reads.2.2.2, b4, if_pos rfl]
        exact giveRun
      obtain ⟨s2, run2, ffi2⟩ := installSeqStop _ _ _ _ _ h1
      exact ⟨_, _, run2, fun _ => ⟨by rw [ffi2, rffi, tffi], by simp [optionLe], fun _ => trivial⟩,
        fun h => (h rfl).elim⟩
    have h4 : WordSemStateFiniteExact.evaluate (bignumHalt (adjustVar v4)) target = (none, target) := by
      unfold bignumHalt
      rw [installEvalTestOne target _ x4 _ _ reads.2.2.2, if_neg b4]
      simp [WordSemStateFiniteExact.evaluate]
    rw [installSeqSame _ _ _ h4]
    have small3 : smallInt width (Int.ofNat q1.length) := by simpa [b3] using x3Bit
    have small4 : smallInt width (Int.ofNat q2.length) := by simpa [b4] using x4Bit
    have x3Eq : x3 = smallnum (Int.ofNat q1.length) := WordLocW.word.inj
      (memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs source.space target.store
        target.memory target.mdomain _ _ _ ⟨good, small3,
          memoryRel_tl _ _ _ _ _ _ _ _ _ _ (memoryRel_tl _ _ _ _ _ _ _ _ _ _ roots)⟩)
    have x4Eq : x4 = smallnum (Int.ofNat q2.length) := WordLocW.word.inj
      (memoryRel_numberImp conf target.be (holThe source.tstamps) source.refs source.space target.store
        target.memory target.mdomain _ _ _ ⟨good, small4,
          memoryRel_tl _ _ _ _ _ _ _ _ _ _ (memoryRel_tl _ _ _ _ _ _ _ _ _ _
            (memoryRel_tl _ _ _ _ _ _ _ _ _ _ roots))⟩)
    subst x3Eq x4Eq
    obtain ⟨cbEmpty, dbEmpty, storeCB, storeCBE, storeBB, storeBBE, compileRel, oracleRel, oracleBound⟩ :=
      related.2.2.2.2.2.1
    have odd1 : adjustVar v4 ≠ 1 ∧ adjustVar v4 ≠ 3 ∧ adjustVar v3 ≠ 1 ∧ adjustVar v3 ≠ 3 ∧
        adjustVar v3 ≠ 5 := by simp [adjustVar]; omega
    let dsl := target.dataBuffer.spaceLeft
    let dbytes := BitVec.ofNat width (width / 8) * BitVec.ofNat width dsl
    let t1 := target.setVar 1 (.word target.dataBuffer.position)
    rw [installSeqAssign target 1 _ (.word target.dataBuffer.position) _ (by
      simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, storeBB])]
    rw [installSeqAssign t1 3 _ (.word dbytes) _ (by
      simp [t1, dbytes, dsl, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, storeBBE,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert, theWords,
        wordOpHOL, wordOp])]
    let t3 := t1.setVar 3 (.word dbytes)
    let len2 := (smallnum (Int.ofNat q2.length) : BitVec width) >>> (2 : Nat)
    have r4' := reads.2.2.2
    simp only [WordSemStateFiniteExact.getVar] at r4'
    rw [installSeqAssign t3 5 _ (.word len2) _ (by
      rw [wordExpShiftVar]
      simp [t3, t1, WordSemStateFiniteExact.setVar, installLookupInsert, odd1, r4',
        SemanticPrimitivesProps.shiftLookup, len2])]
    let t5 := t3.setVar 5 (.word len2)
    let dfree := dbytes >>> wordShiftAmount width
    rw [installSeqAssign t5 3 _ (.word dfree) _ (by
      rw [wordExpShiftVar]
      simp [t5, t3, WordSemStateFiniteExact.setVar, installLookupInsert,
        SemanticPrimitivesProps.shiftLookup, dfree])]
    let t6 := t5.setVar 3 (.word dfree)
    have rel6 : stateRel conf l1 l2 source t6 none locs :=
      (stateRel_insertOdd conf l1 l2 source t5 none locs 3 _ rfl).mpr
        ((stateRel_insertOdd conf l1 l2 source t3 none locs 5 _ rfl).mpr
          ((stateRel_insertOdd conf l1 l2 source t1 none locs 3 _ rfl).mpr
            ((stateRel_insertOdd conf l1 l2 source target none locs 1 _ rfl).mpr related)))
    have lowerD := installEvalLower t6 3 5 dfree len2 (giveUp (width := width)) .skip
      (by simp [t6, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert])
      (by simp [t6, t5, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert])
    by_cases dLow : dfree < len2
    · obtain ⟨r, giveRun, rffi, tffi, -⟩ := evaluateGiveUp2 conf l1 l2 source t6 locs rel6
      rw [if_pos dLow, giveRun] at lowerD
      obtain ⟨s2, run2, ffi2⟩ := installSeqStop _ _ _ _ _ lowerD
      exact ⟨_, _, run2, fun _ => ⟨by rw [ffi2, rffi, ← tffi]; rfl, by simp [optionLe], fun _ => trivial⟩,
        fun h => (h rfl).elim⟩
    rw [if_neg dLow] at lowerD
    rw [installSeqSame _ _ _ (by rw [lowerD]; simp [WordSemStateFiniteExact.evaluate]; rfl)]
    have dataSpace : q2.length ≤ target.dataBuffer.spaceLeft :=
      installDataSpace good q2.length dsl small4 dLow
    let csl := target.codeBuffer.spaceLeft
    let t7 := t6.setVar 1 (.word target.codeBuffer.position)
    rw [installSeqAssign t6 1 _ (.word target.codeBuffer.position) _ (by
      simp [t6, t5, t3, t1, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
        WordSemStateFiniteExact.setVar, storeCB])]
    rw [installSeqAssign t7 3 _ (.word (BitVec.ofNat width csl)) _ (by
      simp [t7, t6, t5, t3, t1, csl, WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore,
        storeCBE, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert,
        theWords, wordOpHOL, wordOp])]
    let t8 := t7.setVar 3 (.word (BitVec.ofNat width csl))
    let len1 := (smallnum (Int.ofNat q1.length) : BitVec width) >>> (2 : Nat)
    have r3' := reads.2.2.1
    simp only [WordSemStateFiniteExact.getVar] at r3'
    rw [installSeqAssign t8 5 _ (.word len1) _ (by
      rw [wordExpShiftVar]
      simp [t8, t7, t6, t5, t3, t1, WordSemStateFiniteExact.setVar, installLookupInsert, odd1, r3',
        SemanticPrimitivesProps.shiftLookup, len1])]
    let t9 := t8.setVar 5 (.word len1)
    have rel9 : stateRel conf l1 l2 source t9 none locs :=
      (stateRel_insertOdd conf l1 l2 source t8 none locs 5 _ rfl).mpr
        ((stateRel_insertOdd conf l1 l2 source t7 none locs 3 _ rfl).mpr
          ((stateRel_insertOdd conf l1 l2 source t6 none locs 1 _ rfl).mpr rel6))
    have lowerC := installEvalLower t9 3 5 (BitVec.ofNat width csl) len1 (giveUp (width := width)) .skip
      (by simp [t9, t8, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert])
      (by simp [t9, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, installLookupInsert])
    by_cases cLow : BitVec.ofNat width csl < len1
    · obtain ⟨r, giveRun, rffi, tffi, -⟩ := evaluateGiveUp2 conf l1 l2 source t9 locs rel9
      rw [if_pos cLow, giveRun] at lowerC
      obtain ⟨s2, run2, ffi2⟩ := installSeqStop _ _ _ _ _ lowerC
      exact ⟨_, _, run2, fun _ => ⟨by rw [ffi2, rffi, ← tffi]; rfl, by simp [optionLe], fun _ => trivial⟩,
        fun h => (h rfl).elim⟩
    rw [if_neg cLow] at lowerC
    rw [installSeqSame _ _ _ (by rw [lowerC]; simp [WordSemStateFiniteExact.evaluate]; rfl)]
    have codeSpace : q1.length ≤ target.codeBuffer.spaceLeft :=
      installCodeSpace good q1.length csl small3 cLow
    have codeMembership :
        (installLocation, 3, installCode (width := width) ()) ∈ stubs (width := width) conf ∧
        (installCodeLocation, 4, installCodeStub conf) ∈ stubs (width := width) conf ∧
        (installDataLocation, 4, installDataStub conf) ∈ stubs (width := width) conf := by
      simp [stubs, fixedStubs?, compileConfiguredStub?, compileStub?,
        fromListLocation, fromList1Location, refByteLocation, refArrayLocation,
        replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation,
        divLocation, modLocation, compare1Location, compareLocation, equal1Location,
        equalLocation, longDiv1Location, longDivLocation, memCopyLocation,
        byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation,
        installLocation, installCodeLocation, installDataLocation, dummyLocation,
        appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation,
        unusedLocation, stringCmpLoopLocation, wordNumStubs, stackNumStubs]
    have codeI : sptLookup installLocation target.code = some (3, installCode conf) :=
      related.2.2.2.2.1.2.1 _ codeMembership.1
    have codeIC : sptLookup installCodeLocation target.code = some (4, installCodeStub conf) :=
      related.2.2.2.2.1.2.1 _ codeMembership.2.1
    have codeID : sptLookup installDataLocation target.code = some (4, installDataStub conf) :=
      related.2.2.2.2.1.2.1 _ codeMembership.2.2
    have sourceEq : cut = { source with locals := cut.locals } := by
      rw [cutStateOpt_some_eq names source cut cutEq]
    have oracleSame : cut.compileOracle = source.compileOracle := by rw [sourceEq]
    have compileSame : cut.compile = source.compile := by rw [sourceEq]
    let progs := (k, entry) :: rest
    have targetOracle0 : target.compileOracle 0 = (cfg, progs.map (compilePart (width := width) conf)) := by
      simp only [oracleRel, ← oracleSame, oracle0, progs]
    have targetNext : (target.compileOracle 1).1 = cfg' := by
      simp only [oracleRel, ← oracleSame]
      rw [← oracle1]
    have targetCompile : target.compile cfg (progs.map (compilePart (width := width) conf)) =
        some (q1, q2.map w2wUpper, cfg') := by
      have h := compileOk
      rw [compileSame, compileRel] at h
      simp only at h
      cases hc : target.compile cfg (progs.map (compilePart (width := width) conf)) with
      | none => rw [hc] at h; simp at h
      | some triple =>
        obtain ⟨b, ws, c'⟩ := triple
        rw [hc] at h
        simp at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [w2wUpper_upperW2w ws good]
    obtain ⟨cutFirst, cutSecond, cutPair, cutUnion⟩ :=
      cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut cutWord
    let t10 := t9
    let initial := { t10 with clock := wordSemMustTerminateLimit width, termdep := t10.termdep - 1 }
    let cpos := target.codeBuffer.position
    let e0 := WordSemStateFiniteExact.callEnv [.loc n l, w1, w2, .word cpos]
      (sptLookup installCodeLocation target.stackSize)
      (WordSemStateFiniteExact.pushEnv (cutFirst, cutSecond) none (WordSemStateFiniteExact.decClock initial))
    have limitBig : 2 * 2 ^ width + 1 ≤ wordSemMustTerminateLimit width := by
      unfold wordSemMustTerminateLimit
      dsimp only
      have pos : 1 ≤ 2 ^ width * 2 ^ width := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      refine Nat.le_trans ?_ (Nat.le_add_right _ _)
      refine Nat.le_trans ?_ (Nat.le_add_right _ _)
      exact Nat.add_le_add_left pos _
    have len1Small : q1.length < 2 ^ width := by
      unfold smallInt at small3
      simp only [Int.ofNat_eq_natCast] at small3
      have : 2 ^ width / 8 ≤ 2 ^ width := Nat.div_le_self _ _
      omega
    have len2Small : q2.length < 2 ^ width := by
      unfold smallInt at small4
      simp only [Int.ofNat_eq_natCast] at small4
      have : 2 ^ width / 8 ≤ 2 ^ width := Nat.div_le_self _ _
      omega
    obtain ⟨ck, stubRun⟩ := installStubsRun conf e0 hv1 hv2 q1 q2 w1 w2
      ((.number (Int.ofNat q1.length), .word (smallnum (Int.ofNat q1.length))) ::
        (.number (Int.ofNat q2.length), .word (smallnum (Int.ofNat q2.length))) :: stackVars)
      source.space (holThe source.tstamps) source.refs n l k cfg cfg'
      (compilePart (width := width) conf (k, entry)).2 (rest.map (compilePart (width := width) conf))
      roots
      codeIC codeID codeI
      storeBB storeCB cbEmpty
      dbEmpty bytes wordsOk codeSpace
      dataSpace
      (by
        show q1.length + q2.length + 2 ≤ wordSemMustTerminateLimit width - 1
        omega)
      (by simp [e0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
            WordToStackProofs.fromList2Lookup])
      (by simp [e0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
            WordToStackProofs.fromList2Lookup])
      (by simp [e0, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
            WordToStackProofs.fromList2Lookup])
      (by simp [e0, cpos, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
            WordToStackProofs.fromList2Lookup]; rfl)
      targetOracle0
      targetCompile
      targetNext good
    sorry

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
