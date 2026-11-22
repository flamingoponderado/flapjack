module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BignumHalt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.InstallStubs
public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithLocals

@[expose] public section

/-! The `Install` assignment (`data_to_word_assignProofScript.sml`
`assign_Install`, lines 2451-2745) and its prerequisites. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
