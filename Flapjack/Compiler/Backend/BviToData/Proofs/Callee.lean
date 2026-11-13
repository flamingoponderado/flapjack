module

public import Flapjack.Compiler.Backend.BviToData.Proofs.CompileCorrect
public import Flapjack.Compiler.Backend.BviToData.Proofs.Thunk
public import Flapjack.Compiler.Backend.BviToData.Proofs.FindCode
public import Flapjack.Compiler.Backend.BviToData.Proofs.Optimise
public import Flapjack.Compiler.Backend.BviToData.Proofs.Jump
public import Flapjack.Compiler.Backend.BviToData.Proofs.CutEnv
public import Flapjack.Compiler.Backend.BviToData.Proofs.Compare
public import Flapjack.Misc.Sptree.FromList.Domain
public import Flapjack.Compiler.Backend.Semantics.DataProps.JumpPush

@[expose] public section

/-! Shared callee reasoning for the BVI-to-data compiler simulation. -/

namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Flapjack infrastructure: correspondence for locals initialized from a list. -/
theorem varCorr_fromList {α β : Type} (f : α → β) (values : List α) :
    DataProps.varCorr (values.map f) (List.range values.length) (sptMap f (sptFromList values)) := by
  apply List.forall₂_iff_get.mpr
  constructor
  · simp
  · intro index leftBound rightBound
    have bound : index < values.length := by simpa using rightBound
    simp [DataSem.getVar, sptLookup_sptMap, sptLookupFromList_getElem?, bound]

/-- Flapjack infrastructure: the full continuing invariant after saving one value. -/
theorem forceValueOutcome {C F : Type} (target next : DataSem.State C F)
    (n : Nat) (corr live : List Nat) (env : List BvlSem.Value) (value : DataSem.Value)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (fresh : ∀ k, n ≤ k → sptLookup k target.locals = none)
    (locals : next.locals = sptInsert n value (sptMkWf (sptInter target.locals (namesOfList (live ++ corr)))))
    (stack : next.stack = target.stack) (handler : next.handler = target.handler) :
    correctOutcome (.val [dataToBviValue value]) target next n (n + 1) corr live [n] env false none none := by
  have mappedReads := DataProps.getVars_thm corr env (sptMap dataToBviValue target.locals) vars
  have corrPresent : ∀ key ∈ corr, sptLookup key target.locals ≠ none := by
    intro key member absent
    have mapped := getVars_present corr (sptMap dataToBviValue target.locals) env mappedReads key member
    simp [sptLookup_sptMap, absent] at mapped
  let saved := sptMkWf (sptInter target.locals (namesOfList (live ++ corr)))
  have sameLocals : next.locals = sptInsert n value saved := locals
  simp only [correctOutcome, true_and, List.mem_singleton, forall_eq]
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, stack.symm, handler.symm, ?_, ?_⟩
  · intro key bound
    have different : key ≠ n := by omega
    rw [sameLocals, sptLookup_sptInsert_ne n key value saved different]
    simp [saved, lookup_cut_namesOfList, fresh key (by omega)]
  · rw [sameLocals]
    apply varCorr_of_lookup_eq dataToBviValue target.locals (sptInsert n value saved) corr env vars
    intro key member
    have different : key ≠ n := by
      intro same
      subst key
      exact corrPresent n member (fresh n (Nat.le_refl n))
    rw [sptLookup_sptInsert_ne n key value saved different]
    simp [saved, lookup_cut_namesOfList, member]
  · intro key dataValue found
    rw [sameLocals] at found
    by_cases same : key = n
    · omega
    · rw [sptLookup_sptInsert_ne n key value saved same] at found
      by_contra bound
      have absent := fresh key (by omega)
      simp [saved, lookup_cut_namesOfList, absent] at found
  · intro key dataValue found needed
    have different : key ≠ n := by
      intro same
      subst key
      have absent := fresh n (Nat.le_refl n)
      rw [found] at absent
      contradiction
    rw [sameLocals, sptLookup_sptInsert_ne n key value saved different]
    have kept : key ∈ live ++ corr := by
      by_cases member : key ∈ live
      · simp [member]
      · simp [needed member]
    simpa [saved, lookup_cut_namesOfList, kept] using found
  · intro available
    cases run : DataSem.jumpExc target with
    | none => exact False.elim (available run)
    | some jumped =>
      have transported := DataSem.jumpExc_transport target next jumped stack handler run
      rw [transported]
      simp
  · rw [sameLocals]
    constructor
    · simp [DataSem.getVar, sptLookup_sptMap, sptLookup_sptInsert_same]
    · constructor

/-- Flapjack infrastructure: transport a genuine callee induction hypothesis through optimization. -/
theorem compileCalleeFull {C F : Type} (body : Bvi.Exp) (args : List DataSem.Value)
    (source sourceNext : BviSem.BviState C F) (target : DataSem.State C F)
    (res : BviSem.BviResult)
    (ih : simulationFor [body] (args.map dataToBviValue) source)
    (run : BviSem.evaluate [body] (args.map dataToBviValue) source = (res, sourceNext))
    (notType : res ≠ .err (.abort .typeError))
    (related : stateRel source target) (locals : target.locals = sptFromList args)
    (jump : isException res → DataSem.jumpExc target ≠ none) :
    ∃ targetNext result ls,
      DataSem.evaluate (compileExp args.length body) target = (some result, targetNext) ∧
      stateRel sourceNext targetNext ∧
      correctOutcome res target targetNext args.length 0 [] [] [] [] true (some result) ls := by
  have vars : DataProps.varCorr (args.map dataToBviValue) (List.range args.length)
      (sptMap dataToBviValue target.locals) := by rw [locals]; exact varCorr_fromList dataToBviValue args
  have fresh : ∀ k, args.length ≤ k → sptLookup k target.locals = none := by
    intro k bound
    rw [locals, sptLookupFromList_getElem?]
    simp [Nat.not_lt.mpr bound]
  obtain ⟨next, prog, pres, vs, nextVar, ls, compiled, targetRun, finalRel, outcome⟩ :=
    ih res sourceNext target args.length (List.range args.length) true [] run notType vars (by simp) fresh related (by simp) jump
  cases pres with
  | none => simp [correctOutcome] at outcome
  | some result =>
    have allowed : (DataSem.evaluate prog target).1 ≠ some (.err (.abort .typeError)) := by
      rw [targetRun]
      intro bad
      have badResult : result = .err (.abort .typeError) := Option.some.inj bad
      by_cases ret : isReturn res
      · obtain ⟨values, valEq, _⟩ := outcome.2.1 ret
        rw [badResult] at valEq
        cases valEq
      · have projected := outcome.1 ret
        rw [badResult] at projected
        exact notType (by simpa [dataToBviResult] using projected.symm)
    have stopped : (DataSem.evaluate prog target).1 ≠ none := by simp [targetRun]
    obtain ⟨safe, peak, smx, lsz, optimized⟩ := optimise_correct prog target allowed stopped
    let final := { next with localsSize := lsz, safeForSpace := safe, peakHeapLength := peak, stackMax := smx }
    have optimizedRun : DataSem.evaluate (compileExp args.length body) target = (some result, final) := by
      simpa [compileExp, compiled, targetRun, final] using optimized
    refine ⟨final, result, ls, optimizedRun, ?_, ?_⟩
    · exact (stateRel_peakSafe sourceNext next safe peak lsz smx).mp finalRel
    · rcases outcome with ⟨projected, returned, stackProof, tailProof, exceptionProof⟩
      refine ⟨projected, returned, ?_, tailProof, ?_⟩
      · intro isResult
        simpa [final] using stackProof isResult
      · intro isException
        have old := exceptionProof isException
        have changed := jumpExc_peakSafe { next with stack := target.stack, handler := target.handler }
          { next with localsSize := ls } safe peak lsz smx old
        simpa [final] using changed

/-- Flapjack infrastructure: remove an ordinary saved frame from an exception jump. -/
theorem jumpExc_stripSaved {C F : Type} (caller state : DataSem.State C F)
    (env : Spt DataSem.Value) (ls : Option Nat) (available : DataSem.jumpExc caller ≠ none)
    (run : DataSem.jumpExc { state with stack := .env caller.localsSize env :: caller.stack, handler := caller.handler } =
      some { state with localsSize := ls }) :
    DataSem.jumpExc { state with stack := caller.stack, handler := caller.handler } = some { state with localsSize := ls } := by
  have inside : caller.handler < caller.stack.length := by
    by_contra h
    apply available
    simp [DataSem.jumpExc, h]
  have shifted : caller.handler < (DataSem.Stack.env caller.localsSize env :: caller.stack).length := by simp; omega
  have offset : (DataSem.Stack.env caller.localsSize env :: caller.stack).length - (caller.handler + 1) =
      (caller.stack.length - (caller.handler + 1)) + 1 := by simp; omega
  have offset' : caller.stack.length - caller.handler =
      (caller.stack.length - (caller.handler + 1)) + 1 := by omega
  have insideLe : caller.handler ≤ caller.stack.length := Nat.le_of_lt inside
  simpa [DataSem.jumpExc, inside, insideLe, shifted, offset, offset', List.drop_succ_cons] using run



end Flapjack.Compiler.Backend.BviToData
