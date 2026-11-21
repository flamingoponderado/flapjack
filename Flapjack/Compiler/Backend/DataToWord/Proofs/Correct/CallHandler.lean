module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallReturn

@[expose] public section

/-! The returning branch with an exception handler of the `Call` case of the
data-to-word evaluator simulation (`data_to_wordProofScript.sml` lines
1038-1152). Flapjack-specific case infrastructure for `data_compile_correct`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The returning branch with a handler of `data_compile_correct`'s `Call`
case, under the evaluator induction hypotheses for the callee and handler. -/
theorem dataCompileCorrect_callHandler {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (dest : Option Nat) (args : List Nat)
    (ns : List Nat) (names : NumSet) (hn : Nat) (hprog : Flapjack.Compiler.Backend.DataLang.Prog)
    (ihHandler : ∀ xs args1 prog ss env s1 s2 x,
      DataSem.getVars args source.locals = some xs ∧
      DataSem.findCode dest xs source.code source.stackFrameSizes = some (args1, prog, ss) ∧
      ns.Nodup ∧ DataSem.cutEnv names source.locals = some env ∧
      s1 = DataSem.callEnv args1 ss (DataSem.pushEnv env true (DataSem.decClock source)) ∧
      source.clock ≠ 0 ∧ DataSem.evaluate prog s1 = (some (.err (.raise x)), s2) →
      dataCompileCorrectInduction (width := width) hprog (DataSem.setVar hn x s2))
    (ih : ∀ xs args1 prog ss env s1,
      DataSem.getVars args source.locals = some xs ∧
      DataSem.findCode dest xs source.code source.stackFrameSizes = some (args1, prog, ss) ∧
      ns.Nodup ∧ DataSem.cutEnv names source.locals = some env ∧
      s1 = DataSem.callEnv args1 ss (DataSem.pushEnv env true (DataSem.decClock source)) ∧
      source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog s1) :
    dataCompileCorrectInduction (width := width)
      (.call (some (ns, names)) dest args (some (hn, hprog))) source := by
  intro conf n l l1 l2 res source1 target locs run notTypeError related depth
  let q1 := (compileControl (width := width) conf n (l + 2) hprog).1
  let hsome : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat) :=
    some (adjustVar hn, q1, n, l + 1)
  have compiled : (compileControl (width := width) conf n l
      (.call (some (ns, names)) dest args (some (hn, hprog)))).1 =
      .call (some (ns.map adjustVar, adjustSets names, .skip, n, l)) dest (args.map adjustVar) hsome := by
    have h := compileControl_option (width := width) conf n l
      (.call (some (ns, names)) dest args (some (hn, hprog)))
    simp [compileControl?, compileControl_option] at h
    rw [← h]
  have hclock : target.clock = source.clock := related.2.1
  have hffi : target.ffi = source.ffi := related.1
  have hsize : target.stackSize = source.stackFrameSizes :=
    related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have stackLen : source.stack.length = locs.length := by
    have h1 := related.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
    have h2 := related.2.2.2.2.2.2.2.2.2.2.2.2.2.1.length_eq
    omega
  cases hxs : DataSem.getVars args source.locals with
  | none =>
    exfalso; apply notTypeError
    simpa [DataSem.evaluate, hxs] using (congrArg Prod.fst run).symm
  | some xs =>
  cases hfind : DataSem.findCode dest xs source.code source.stackFrameSizes with
  | none =>
    exfalso; apply notTypeError
    simpa [DataSem.evaluate, hxs, hfind] using (congrArg Prod.fst run).symm
  | some found =>
  obtain ⟨args1, body, ss⟩ := found
  by_cases hnodup : ns.Nodup
  swap
  · exfalso; apply notTypeError
    simpa [DataSem.evaluate, hxs, hfind, hnodup] using (congrArg Prod.fst run).symm
  cases hcut : DataSem.cutEnv names source.locals with
  | none =>
    exfalso; apply notTypeError
    simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut] using (congrArg Prod.fst run).symm
  | some env =>
  obtain ⟨words, wordRead, _⟩ := stateRel_getVars conf l1 l2 source target locs args xs related hxs
  obtain ⟨wordCut, wordCutRun⟩ :=
    cutEnv_imp_wordCutEnv conf l1 l2 source target locs names env ⟨related, hcut⟩
  obtain ⟨first, second, cutsRun, _⟩ := cutEnv_imp_cutEnvs (adjustSets names) target.locals wordCut wordCutRun
  obtain ⟨args1', n1, n2, wordFind, calleeRel⟩ :=
    findCode_handler conf l1 l2 n l source target locs args xs words dest source.stackFrameSizes
      args1 body hn n q1 ss names env (first, second) ⟨related, hxs, wordRead, hfind, hcut, cutsRun⟩
  rw [← hsize] at wordFind
  have notBad := badDestArgs_adjust dest args xs hxs (dataFindCode dest xs args1 _ _ body ss hfind)
  have nonEmpty : ¬ sptDomainEmpty (adjustSets names).1 := by
    intro empty
    exact empty 0 (by simp [adjustSets, sptMem, sptDomain, sptLookup])
  have adjNodup : (ns.map adjustVar).Nodup :=
    hnodup.map (fun a b h => by simp only [adjustVar] at h; omega)
  by_cases zero : source.clock = 0
  · have sourceEq : res = some (.err (.abort .timeoutError)) ∧
        source1 = { DataSem.callEnv args1 ss (DataSem.pushEnv env true (DataSem.decClock source)) with
          stack := [], locals := .ln } := by
      simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := sourceEq
    have calleeBound : optionLe
        (WordSemStateFiniteExact.callEnv args1' ss (WordSemStateFiniteExact.pushEnv (first, second) hsome
          (WordSemStateFiniteExact.decClock target))).stackMax
        (DataSem.callEnv args1 ss (DataSem.pushEnv env true (DataSem.decClock source))).stackMax :=
      calleeRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    let timeoutState : WordSemStateFiniteExact width C F :=
      { target with
        stack := []
        stackMax := (WordSemStateFiniteExact.callEnv args1' ss
          (WordSemStateFiniteExact.pushEnv (first, second) hsome target)).stackMax }
    refine ⟨WordSemStateFiniteExact.flushState true timeoutState, some .timeOut, ?_, ?_, by simp, ?_⟩
    · simp [compiled, WordSemStateFiniteExact.evaluate, wordRead, notBad, wordSemAddRetLoc,
        wordFind, hclock, zero, nonEmpty, adjNodup, cutsRun, timeoutState]
    · simpa [WordSemStateFiniteExact.flushState, ← callEnv_pushEnv_stackMax] using calleeBound
    · intro _
      simpa [WordSemStateFiniteExact.flushState, DataSem.callEnv, DataSem.pushEnv,
        DataSem.decClock] using hffi
  · have tzero : target.clock ≠ 0 := by rw [hclock]; exact zero
    cases hcall : DataSem.evaluate body
        (DataSem.callEnv args1 ss (DataSem.pushEnv env true (DataSem.decClock source))) with
    | mk r mid =>
    have dataFix : DataSem.fixClock
        (DataSem.callEnv args1 ss (DataSem.pushEnv env true (DataSem.decClock source)))
        (DataSem.evaluate body
          (DataSem.callEnv args1 ss (DataSem.pushEnv env true (DataSem.decClock source)))) =
        (r, mid) := by
      rw [DataSem.fixClockEvaluate, hcall]
    cases r with
    | none =>
      exfalso; apply notTypeError
      simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix] using (congrArg Prod.fst run).symm
    | some r =>
    have notTE : some r ≠ some (Result.err (ErrorResult.abort Abort.typeError) :
        Result (List DataSem.Value) DataSem.Value) := by
      intro h
      cases h
      apply notTypeError
      simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix] using (congrArg Prod.fst run).symm
    have depth' : (WordSemStateFiniteExact.callEnv args1' ss (WordSemStateFiniteExact.pushEnv (first, second)
        hsome (WordSemStateFiniteExact.decClock target))).termdep > 1 := by
      simpa [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock] using depth
    obtain ⟨t1, res1, wordRun, stackBound, space, result⟩ :=
      ih xs args1 body ss env _ ⟨hxs, hfind, hnodup, hcut, rfl, zero⟩ conf n1 n2 n l (some r) mid
        _ ((l1, l2) :: locs) hcall notTE calleeRel depth'
    -- the source outcome after the callee returns
    have sourceAfter : ∀ values, r = .val values →
        values.length = ns.length ∧ ∃ next, DataSem.popEnv mid = some next ∧ res = none ∧
          source1 = DataSem.setVars ns values next := by
      intro values hr
      subst hr
      by_cases hlen : values.length = ns.length
      · cases hpop : DataSem.popEnv mid with
        | none =>
          exfalso; apply notTypeError
          simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix, hlen, hpop] using
            (congrArg Prod.fst run).symm
        | some next =>
          have h : res = none ∧ source1 = DataSem.setVars ns values next := by
            simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix, hlen, hpop] using run.symm
          exact ⟨hlen, next, rfl, h⟩
      · exfalso; apply notTypeError
        simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix, hlen] using
          (congrArg Prod.fst run).symm
    have sourceRaise : ∀ v, r = .err (.raise v) →
        DataSem.evaluate hprog (DataSem.setVar hn v mid) = (res, source1) := by
      intro v hr
      subst hr
      simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix] using run
    have sourceErr : ∀ a, r = .err (.abort a) → res = some (.err (.abort a)) ∧ source1 = mid := by
      intro a hr
      subst hr
      simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix] using run.symm
    have callEq := Flapjack.WordAlloc.evaluate_call_ret_eq target (ns.map adjustVar) (adjustSets names)
      .skip n l dest (args.map adjustVar) hsome words args1' (compileControl conf n1 n2 body).1 ss
      (first, second) wordRead (by simp [notBad]) wordFind (by simp [nonEmpty, adjNodup]) cutsRun tzero
    by_cases nes : res1 = some .notEnoughSpace
    · subst nes
      have spaceFacts := space rfl
      have after : optionLe mid.stackMax source1.stackMax ∧
          mid.ffi.ioEvents <+: source1.ffi.ioEvents ∧
          (source1.safeForSpace = true → mid.safeForSpace = true) := by
        cases r with
        | val values =>
          obtain ⟨_, next, pop, _, rfl⟩ := sourceAfter values rfl
          have pc := DataSem.popEnv_const mid next pop
          have hsafe : next.safeForSpace = mid.safeForSpace := by
            unfold DataSem.popEnv at pop
            split at pop <;> simp at pop <;> subst pop <;> rfl
          refine ⟨?_, ?_, ?_⟩
          · simp [DataSem.setVars, pc.2.2, optionLe_refl]
          · simp [DataSem.setVars, pc.1]
          · simp [DataSem.setVars, hsafe]
        | err e =>
          cases e with
          | raise v =>
            have handlerRun := sourceRaise v rfl
            refine ⟨by simpa [DataSem.setVar] using DataSem.evaluate_stack_of_result _ _ _ _ handlerRun,
              by simpa [DataSem.setVar] using DataSem.evaluate_events_of_result _ _ _ _ handlerRun,
              fun hs => by
                simpa [DataSem.setVar] using
                  DataSem.evaluate_safety_of_result _ _ _ _ ⟨handlerRun, hs⟩⟩
          | abort a =>
            obtain ⟨_, rfl⟩ := sourceErr a rfl
            exact ⟨optionLe_refl _, List.prefix_refl _, id⟩
      refine ⟨t1, some .notEnoughSpace, ?_, optionLe_trans stackBound after.1, ?_, by simp⟩
      · rw [compiled, callEq, wordRun]
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
        obtain ⟨ws, lens, calleeRet, rfl⟩ := h
        obtain ⟨vlen, next, pop, rfl, rfl⟩ := sourceAfter values rfl
        obtain ⟨t2, tpop, dom, rel2, smax⟩ := callReturnValues conf l1 l2 n l locs ns hnodup values
          mid next target t1 ws _ args1' ss (first, second) hsome wordRun calleeRet lens vlen pop
        have pc := DataSem.popEnv_const mid next pop
        refine ⟨WordSemStateFiniteExact.setVars (ns.map adjustVar) ws t2, none, ?_, ?_, by simp,
          fun _ => ⟨rel2, rfl⟩⟩
        · have lenW : ws.length = (ns.map adjustVar).length := by simp [lens, vlen]
          rw [compiled, callEq, wordRun]
          simp [Flapjack.WordAlloc.callRetTail, lenW, tpop, dom, WordSemStateFiniteExact.evaluate]
        · simpa [WordSemStateFiniteExact.setVars, DataSem.setVars, smax, pc.2.2] using stackBound
      | err e =>
        cases e with
        | raise v =>
          have handlerRun := sourceRaise v rfl
          obtain ⟨hf, w, l5, l6, rest, rfl, hjump⟩ := h
          have callPresent : WordSemStateFiniteExact.jumpExc
              (WordSemStateFiniteExact.callEnv args1' ss (WordSemStateFiniteExact.pushEnv (first, second)
                hsome (WordSemStateFiniteExact.decClock target))) ≠ none := by
            rw [jumpExc_callEnv, Ne, (jumpExc_pushEnv_none_iff _ (.ln, .ln) _).2.2]
            exact jumpExc_pushEnv_some _ _ _ _ _ _
          obtain ⟨hl, hrel⟩ := hjump callPresent
          have sameLen := evaluate_pushEnv_raise_stackLength body args1 ss env source mid v hcall
          rw [sameLen, stackLen, wordSemLastN_length_succ] at hl
          simp only [List.cons.injEq, Prod.mk.injEq] at hl
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hl
          have loc : mkLoc (width := width) (WordSemStateFiniteExact.jumpExc
              (WordSemStateFiniteExact.callEnv args1' ss (WordSemStateFiniteExact.pushEnv (first, second)
                hsome (WordSemStateFiniteExact.decClock target)))) = .loc n (l + 1) :=
            mkLoc_jumpExc args1' ss (first, second) hn n (l + 1) q1 target
          have dom := evaluate_imp_domainEq_exception _ args1' ss (first, second) (adjustVar hn) n (l + 1)
            q1 target t1 _ w wordRun
          have keys := evaluate_pushEnv_exception_keys _ args1' ss (first, second) (adjustVar hn) n (l + 1)
            q1 target t1 _ w wordRun
          have locEq := mkLoc_pushEnv_exception _ args1' ss (first, second) (adjustVar hn) n (l + 1)
            q1 target t1 _ w wordRun
          have depthH : (WordSemStateFiniteExact.setVar (adjustVar hn) w t1).termdep > 1 := by
            have clockFacts := WordSemStateFiniteExact.evaluate_clock _ _ _ _ wordRun
            change t1.termdep > 1
            rw [clockFacts.2]
            simpa [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, hsome,
              WordSemStateFiniteExact.decClock] using depth
          obtain ⟨t2, res2, hRun, hBound, hSpace, hResult⟩ :=
            ihHandler xs args1 body ss env _ mid v ⟨hxs, hfind, hnodup, hcut, rfl, zero, hcall⟩
              conf n (l + 2) l1 l2 res source1 (WordSemStateFiniteExact.setVar (adjustVar hn) w t1) locs
              handlerRun notTypeError (hrel hn) depthH
          have setFacts := jumpExc_setVar t1 (adjustVar hn) w
          refine ⟨t2, res2, ?_, hBound, hSpace, ?_⟩
          · rw [compiled, callEq, wordRun]
            have domU : sptDomainEqUnion t1.locals first second := fun k => Iff.of_eq (congrFun dom k)
            simp [Flapjack.WordAlloc.callRetTail, hsome, loc, domU]
            exact hRun
          · intro hs
            have hr := hResult hs
            cases res with
            | none => exact hr
            | some r =>
              cases r with
              | val values => exact hr
              | err err =>
                cases err with
                | raise value =>
                  obtain ⟨hf2, w2, l7, l8, rest2, hres2, hjump2⟩ := hr
                  refine ⟨hf2, w2, l7, l8, rest2, ?_, ?_⟩
                  · rw [hres2, setFacts.1, locEq]
                  · intro present
                    apply hjump2
                    intro empty
                    have t1None := setFacts.2.mp empty
                    exact ((jumpExc_keyEq_iff t1 target ⟨keys.1, keys.2.symm⟩).mp present) t1None
                | abort a => cases a <;> exact hr
        | abort a =>
          cases a with
          | typeError => exact absurd rfl notTE
          | timeoutError =>
            obtain ⟨rfl, rfl⟩ := sourceErr _ rfl
            obtain ⟨rfl, hf⟩ := h
            refine ⟨t1, _, ?_, stackBound, space, fun _ => ⟨rfl, hf⟩⟩
            rw [compiled, callEq, wordRun]
            simp [Flapjack.WordAlloc.callRetTail]
          | ffiError f =>
            obtain ⟨rfl, rfl⟩ := sourceErr _ rfl
            obtain ⟨rfl, hf⟩ := h
            refine ⟨t1, _, ?_, stackBound, space, fun _ => ⟨rfl, hf⟩⟩
            rw [compiled, callEq, wordRun]
            simp [Flapjack.WordAlloc.callRetTail]

end Flapjack.Compiler.Backend.DataToWord.Proofs
