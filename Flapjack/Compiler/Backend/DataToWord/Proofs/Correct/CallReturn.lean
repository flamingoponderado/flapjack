module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.CallTail
public import Flapjack.Compiler.Backend.DataToWord.Proofs.PopEnvSetVars
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutState
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutEnvs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.EvaluateDomain
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.DataRaiseStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.EvaluateMkLoc
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall
public import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PopEnvConst
public import Flapjack.Compiler.Backend.DataSpace.Proofs.State
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Call

@[expose] public section

/-! The returning, handler-free branch of the `Call` case of the data-to-word
evaluator simulation (`data_to_wordProofScript.sml` lines 968-1037), with
helpers shared by the handler branch. Flapjack-specific case infrastructure
for `data_compile_correct`. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- HOL `LASTN_TL` specialized to the location lists used here. -/
theorem wordSemLastN_cons_of_le {α : Type} (n : Nat) (x : α) (xs : List α)
    (h : n ≤ xs.length) : wordSemLastN n (x :: xs) = wordSemLastN n xs := by
  simp only [wordSemLastN, List.reverse_cons]
  rw [List.take_append_of_le_length (by simpa using h)]

/-- HOL `LASTN_ADD1` at the location lists used here. -/
theorem wordSemLastN_length_succ {α : Type} (x : α) (xs : List α) :
    wordSemLastN (xs.length + 1) (x :: xs) = x :: xs := by
  simp [wordSemLastN, List.take_of_length_le]

/-- Updating a local leaves the exception location and its presence unchanged. -/
theorem jumpExc_setVar {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : Nat) (w : WordLocW width) :
    mkLoc (width := width) (WordSemStateFiniteExact.jumpExc (WordSemStateFiniteExact.setVar k w t)) =
      mkLoc (width := width) (WordSemStateFiniteExact.jumpExc t) ∧
    (WordSemStateFiniteExact.jumpExc (WordSemStateFiniteExact.setVar k w t) = none ↔
      WordSemStateFiniteExact.jumpExc t = none) := by
  unfold WordSemStateFiniteExact.jumpExc WordSemStateFiniteExact.setVar
  simp only
  exact ⟨trivial, trivial⟩

/-- Entering a callee frame without a handler leaves the exception location
and its presence unchanged. -/
theorem jumpExc_callEnv_pushEnv_none {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (args : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) :
    mkLoc (width := width) (WordSemStateFiniteExact.jumpExc
        (WordSemStateFiniteExact.callEnv args ss
          (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock t)))) =
      mkLoc (width := width) (WordSemStateFiniteExact.jumpExc t) ∧
    (WordSemStateFiniteExact.jumpExc
        (WordSemStateFiniteExact.callEnv args ss
          (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock t))) = none ↔
      WordSemStateFiniteExact.jumpExc t = none) := by
  rw [jumpExc_callEnv]
  constructor
  · rw [mkLoc_jumpExc_stackMax,
      (jumpExc_pushEnv_none (out1 := width) (out2 := width) (out3 := width) _ envs none).2.1]
    exact jumpExc_decClock t
  · rw [(jumpExc_pushEnv_none_iff _ (.ln, .ln) _).2.2, (jumpExc_pushEnv_none_iff _ envs none).2.1]
    exact (jumpExc_pushEnv_none_iff t (.ln, .ln) none).1

/-- The timeout state of a returning call records the same maximum stack size
as the clock-decremented callee state. -/
theorem callEnv_pushEnv_stackMax {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (args : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (opt : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (WordSemStateFiniteExact.callEnv args ss (WordSemStateFiniteExact.pushEnv envs opt t)).stackMax =
      (WordSemStateFiniteExact.callEnv args ss
        (WordSemStateFiniteExact.pushEnv envs opt (WordSemStateFiniteExact.decClock t))).stackMax := by
  have h := WordSemStateFiniteExact.pushEnv_decClock_stack envs opt t
  simp only [WordSemStateFiniteExact.callEnv, h.1, h.2]

/-- The normal-return part shared by both returning branches: the returned
roots are stored after popping the related frames. -/
theorem callReturnValues {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 n l : Nat) (locs : List (Nat × Nat))
    (ns : List Nat) (hnodup : ns.Nodup) (values : List DataSem.Value)
    (mid next : DataSem.State C F) (target t1 : WordSemStateFiniteExact width C F)
    (ws : List (WordLocW width)) (body : WordLangProgHOL (BitVec width))
    (args : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (opt : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (wordRun : WordSemStateFiniteExact.evaluate body
        (WordSemStateFiniteExact.callEnv args ss
          (WordSemStateFiniteExact.pushEnv envs opt (WordSemStateFiniteExact.decClock target))) =
      (some (.result (.loc n l) ws), t1))
    (calleeRel : stateRel conf n l mid t1 (some (values.zip ws)) ((l1, l2) :: locs))
    (lens : ws.length = values.length) (vlen : values.length = ns.length)
    (pop : DataSem.popEnv mid = some next) :
    ∃ t2, WordSemStateFiniteExact.popEnv t1 = some t2 ∧
      sptDomainEqUnion t2.locals envs.1 envs.2 ∧
      stateRel conf l1 l2 (DataSem.setVars ns values next)
        (WordSemStateFiniteExact.setVars (ns.map adjustVar) ws t2) none locs ∧
      t2.stackMax = t1.stackMax := by
  obtain ⟨t2, l8, l9, ll, tpop, locations, rel⟩ :=
    stateRel_popEnv_setVars conf n l mid t1 values ws ((l1, l2) :: locs) ns next
      ⟨calleeRel, lens.symm, vlen.symm, hnodup, pop⟩
  simp only [List.cons.injEq, Prod.mk.injEq] at locations
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := locations
  have domain := evaluate_imp_domainEq body args ss envs opt target t1 t2 (.loc n l) ws
    ⟨wordRun, tpop⟩
  refine ⟨t2, tpop, ?_, rel, (WordSemStateFiniteExact.popEnvConst t1 t2 tpop).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  intro k
  exact Iff.of_eq (congrFun domain k)

/-- `bad_dest_args` is false for the adjusted arguments of a successful source call. -/
theorem badDestArgs_adjust (dest : Option Nat) (args : List Nat)
    (xs : List DataSem.Value) (hxs : DataSem.getVars args (locals : Spt DataSem.Value) = some xs)
    (good : ¬ wordSemBadDestArgs dest xs = true) :
    wordSemBadDestArgs dest (args.map adjustVar) = false := by
  cases dest with
  | some _ => rfl
  | none =>
    cases args with
    | nil =>
      simp [DataSem.getVars] at hxs
      subst hxs
      simp [wordSemBadDestArgs] at good
    | cons _ _ => rfl

/-- The returning, handler-free branch of `data_compile_correct`'s `Call` case,
under the evaluator induction hypothesis for the callee body. -/
theorem dataCompileCorrect_callReturn {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.Compiler.Backend.DataSem.State C F) (dest : Option Nat) (args : List Nat)
    (ns : List Nat) (names : NumSet)
    (ih : ∀ xs args1 prog ss env s1,
      DataSem.getVars args source.locals = some xs ∧
      DataSem.findCode dest xs source.code source.stackFrameSizes = some (args1, prog, ss) ∧
      ns.Nodup ∧ DataSem.cutEnv names source.locals = some env ∧
      s1 = DataSem.callEnv args1 ss (DataSem.pushEnv env false (DataSem.decClock source)) ∧
      source.clock ≠ 0 →
      dataCompileCorrectInduction (width := width) prog s1) :
    dataCompileCorrectInduction (width := width) (.call (some (ns, names)) dest args none) source := by
  intro conf n l l1 l2 res source1 target locs run notTypeError related depth
  have compiled : (compileControl (width := width) conf n l (.call (some (ns, names)) dest args none)).1 =
      .call (some (ns.map adjustVar, adjustSets names, .skip, n, l)) dest (args.map adjustVar) none := by
    have h := compileControl_option (width := width) conf n l (.call (some (ns, names)) dest args none)
    simp [compileControl?] at h
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
    findCode_return conf l1 l2 n l source target locs args xs words dest source.stackFrameSizes
      args1 body ss names env (first, second) ⟨related, hxs, wordRead, hfind, hcut, cutsRun⟩
  rw [← hsize] at wordFind
  have notBad := badDestArgs_adjust dest args xs hxs (dataFindCode dest xs args1 _ _ body ss hfind)
  have nonEmpty : ¬ sptDomainEmpty (adjustSets names).1 := by
    intro empty
    exact empty 0 (by simp [adjustSets, sptMem, sptDomain, sptLookup])
  have adjNodup : (ns.map adjustVar).Nodup :=
    hnodup.map (fun a b h => by simp only [adjustVar] at h; omega)
  by_cases zero : source.clock = 0
  · have sourceEq : res = some (.err (.abort .timeoutError)) ∧
        source1 = { DataSem.callEnv args1 ss (DataSem.pushEnv env false (DataSem.decClock source)) with
          stack := [], locals := .ln } := by
      simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero] using run.symm
    obtain ⟨rfl, rfl⟩ := sourceEq
    have calleeBound : optionLe
        (WordSemStateFiniteExact.callEnv args1' ss (WordSemStateFiniteExact.pushEnv (first, second) none
          (WordSemStateFiniteExact.decClock target))).stackMax
        (DataSem.callEnv args1 ss (DataSem.pushEnv env false (DataSem.decClock source))).stackMax :=
      calleeRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    let timeoutState : WordSemStateFiniteExact width C F :=
      { target with
        stack := []
        stackMax := (WordSemStateFiniteExact.callEnv args1' ss
          (WordSemStateFiniteExact.pushEnv (first, second) none target)).stackMax }
    refine ⟨WordSemStateFiniteExact.flushState true timeoutState, some .timeOut, ?_, ?_, by simp, ?_⟩
    · simp [compiled, WordSemStateFiniteExact.evaluate, wordRead, notBad, wordSemAddRetLoc,
        wordFind, hclock, zero, nonEmpty, adjNodup, cutsRun, timeoutState]
    · simpa [WordSemStateFiniteExact.flushState, ← callEnv_pushEnv_stackMax] using calleeBound
    · intro _
      simpa [WordSemStateFiniteExact.flushState, DataSem.callEnv, DataSem.pushEnv,
        DataSem.decClock] using hffi
  · have tzero : target.clock ≠ 0 := by rw [hclock]; exact zero
    cases hcall : DataSem.evaluate body
        (DataSem.callEnv args1 ss (DataSem.pushEnv env false (DataSem.decClock source))) with
    | mk r mid =>
    have dataFix : DataSem.fixClock
        (DataSem.callEnv args1 ss (DataSem.pushEnv env false (DataSem.decClock source)))
        (DataSem.evaluate body
          (DataSem.callEnv args1 ss (DataSem.pushEnv env false (DataSem.decClock source)))) =
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
        none (WordSemStateFiniteExact.decClock target))).termdep > 1 := by
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
    have sourceErr : ∀ e, r = .err e → res = some (.err e) ∧ source1 = mid := by
      intro e hr
      subst hr
      cases e with
      | raise v => simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix] using run.symm
      | abort a => simpa [DataSem.evaluate, hxs, hfind, hnodup, hcut, zero, dataFix] using run.symm
    have locFacts := jumpExc_callEnv_pushEnv_none target args1' ss (first, second)
    have callEq := Flapjack.WordAlloc.evaluate_call_ret_eq target (ns.map adjustVar) (adjustSets names)
      .skip n l dest (args.map adjustVar) none words args1' (compileControl conf n1 n2 body).1 ss
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
          obtain ⟨_, rfl⟩ := sourceErr e rfl
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
          mid next target t1 ws _ args1' ss (first, second) none wordRun calleeRet lens vlen pop
        have pc := DataSem.popEnv_const mid next pop
        refine ⟨WordSemStateFiniteExact.setVars (ns.map adjustVar) ws t2, none, ?_, ?_, by simp,
          fun _ => ⟨rel2, rfl⟩⟩
        · have lenW : ws.length = (ns.map adjustVar).length := by simp [lens, vlen]
          rw [compiled, callEq, wordRun]
          simp [Flapjack.WordAlloc.callRetTail, lenW, tpop, dom, WordSemStateFiniteExact.evaluate]
        · simpa [WordSemStateFiniteExact.setVars, DataSem.setVars, smax, pc.2.2] using stackBound
      | err e =>
        obtain ⟨rfl, rfl⟩ := sourceErr e rfl
        cases e with
        | raise v =>
          obtain ⟨hf, w, l5, l6, rest, rfl, hjump⟩ := h
          refine ⟨t1, _, ?_, stackBound, space, fun _ => ⟨hf, w, l5, l6, rest, ?_, ?_⟩⟩
          · rw [compiled, callEq, wordRun]
            simp [Flapjack.WordAlloc.callRetTail]
          · rw [locFacts.1]
          · intro present
            obtain ⟨hl, hrel⟩ := hjump (fun empty => present (locFacts.2.mp empty))
            have shorter := evaluate_raise_stackShorter body args1 ss env source source1 v hcall
            refine ⟨?_, hrel⟩
            rw [← wordSemLastN_cons_of_le _ (l1, l2) locs (by omega)]
            exact hl
        | abort a =>
          cases a with
          | typeError => exact absurd rfl notTE
          | timeoutError =>
            obtain ⟨rfl, hf⟩ := h
            refine ⟨t1, _, ?_, stackBound, space, fun _ => ⟨rfl, hf⟩⟩
            rw [compiled, callEq, wordRun]
            simp [Flapjack.WordAlloc.callRetTail]
          | ffiError f =>
            obtain ⟨rfl, hf⟩ := h
            refine ⟨t1, _, ?_, stackBound, space, fun _ => ⟨rfl, hf⟩⟩
            rw [compiled, callEq, wordRun]
            simp [Flapjack.WordAlloc.callRetTail]

end Flapjack.Compiler.Backend.DataToWord.Proofs
