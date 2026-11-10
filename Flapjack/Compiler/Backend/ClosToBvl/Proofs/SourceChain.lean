module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ProgramCode
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainLocations
public import Flapjack.Compiler.Backend.Semantics.ClosSem.InstallGrowth
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyCode
public import Flapjack.Compiler.Backend.Semantics.ClosSem.CodeExtensionEvaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Source closure-code chains used by the top-level compiler. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem

/-- The code map provides each zero-argument entry of a closure expression
chain, using the canonical finite-map representation for `code`. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_installed_def"
  (fmap_as_finite_support_parameters := [code])]
def chainInstalled (start : Nat) (expressions : List ClosLang.Exp)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Prop :=
  ∀ i, i < expressions.length →
    findCode (start + i) ([] : List Value) code = some ([],
      if i + 1 < expressions.length then
        .let .none [@holEl ClosLang.Exp ⟨.var .none 0⟩ i expressions] (.call .none 0 (start + i + 1) [])
      else @holEl ClosLang.Exp ⟨.var .none 0⟩ i expressions)

private def toBroad (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) := code.lookup

private def ofBroad (lookup : Nat → Option (Nat × ClosLang.Exp))
    (finite : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat (Nat × ClosLang.Exp) := ⟨lookup, finite⟩

/-- The canonical code-map parameter roundtrips through lookup and support. -/
theorem holFmapAsFiniteSupportParamWitness_chainInstalled_code
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- A source-code extension retains all installed chain entries. -/
theorem chainInstalled_submap (start : Nat) (expressions : List ClosLang.Exp)
    (code nextCode : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (installed : chainInstalled start expressions code)
    (submap : ∀ key value, code.lookup key = some value → nextCode.lookup key = some value) :
    chainInstalled start expressions nextCode := by
  intro i bound
  have found := installed i bound
  unfold findCode at found ⊢
  cases lookup : code.lookup (start + i) with
  | none => simp [lookup] at found
  | some entry =>
    have nextLookup := submap _ _ lookup
    simpa [lookup, nextLookup] using found

/-- Split the head entry from the remainder of an installed chain. -/
theorem chainInstalled_cons (start : Nat) (first : ClosLang.Exp) (rest : List ClosLang.Exp)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) :
    chainInstalled start (first :: rest) code ↔
      findCode start ([] : List Value) code = some ([], if rest = [] then first else
        .let .none [first] (.call .none 0 (start + 1) [])) ∧ chainInstalled (start + 1) rest code := by
  constructor
  · intro installed
    constructor
    · have head := installed 0 (by simp)
      cases rest <;> simpa [holEl, holHd] using head
    · intro i bound
      have tail := installed (i + 1) (by simp; omega)
      have arithmetic : i + 2 < rest.length + 1 ↔ i + 1 < rest.length := by omega
      simpa [holEl_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, arithmetic] using tail
  · rintro ⟨head, tail⟩ i bound
    cases i with
    | zero => cases rest <;> simpa [holEl, holHd] using head
    | succ i =>
      have tailBound : i < rest.length := by simpa using bound
      have found := tail i tailBound
      have arithmetic : i + 2 < rest.length + 1 ↔ i + 1 < rest.length := by omega
      simpa [holEl_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, arithmetic] using found

/-- The source association-list map selects the first entry at a key. -/
theorem initialSourceCode_cons_lookup (name arity : Nat) (body : ClosLang.Exp)
    (rest : List (Nat × Nat × ClosLang.Exp)) (key : Nat) :
    (initialSourceCode ((name, arity, body) :: rest)).lookup key =
      if key = name then some (arity, body) else (initialSourceCode rest).lookup key := by
  simp [initialSourceCode, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
    List.foldl_append, FUPDATE_HOL]

/-- Any closure evaluation retains an installed chain, regardless of its
result. The evaluator's correspondence with HOL is still to be reviewed. -/
theorem chainInstalled_after_evaluate {C F : Type} (start : Nat) (chain evaluated : List ClosLang.Exp)
    (env : List Value) (source next : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (installed : chainInstalled start chain source.code) (run : evaluate evaluated env source = (result, next)) :
    chainInstalled start chain next.code :=
  chainInstalled_submap start chain source.code next.code installed
    (evaluate_code_growth.1 evaluated env source next result run)

/-- A generated chain discards all but the last successful value and
preserves errors. -/
def sourceChainResult : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value →
    Flapjack.SemanticPrimitivesHOL.Result (List Value) Value
  | .err error => .err error
  | .val values => .val values.getLast?.toList

/-- A failed first expression exits the generated chain without a call. -/
theorem evaluate_sourceChain_first_error {C F : Type} (source next : State C F)
    (first : ClosLang.Exp) (address : Nat) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (run : evaluate [first] [] source = (.err error, next)) :
    evaluate [.let .none [first] (.call .none 0 address [])] [] source = (.err error, next) := by
  rw [evaluate, fixClock_evaluate, run]

/-- A successful chain step spends one extra clock unit for the generated
call and then executes the installed body. -/
theorem evaluate_sourceChain_first_success {C F : Type} (source middle final : State C F)
    (first body : ClosLang.Exp) (address extra : Nat) (value : Value)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (headRun : evaluate [first] [] source = (.val [value], middle))
    (lookup : findCode address ([] : List Value) middle.code = some ([], body))
    (tailRun : evaluate [body] [] { middle with clock := middle.clock + extra } = (result, final)) :
    evaluate [.let .none [first] (.call .none 0 address [])] []
        { source with clock := source.clock + (extra + 1) } = (result, final) := by
  have shifted := evaluate_addClock.1 [first] [] source middle (.val [value]) (extra + 1) headRun (by simp)
  rw [evaluate, fixClock_evaluate, shifted]
  cases entry : middle.code.lookup address with
  | none => simp [findCode, entry] at lookup
  | some pair =>
    obtain ⟨arity, codeBody⟩ := pair
    have entryEq : arity = 0 ∧ codeBody = body := by simpa [findCode, entry, eq_comm] using lookup
    obtain ⟨rfl, rfl⟩ := entryEq
    simpa [evaluate, fixClock, findCode, entry, decClock] using tailRun

/-- An installed nonempty source chain executes an expression list, returning
its last value or the same error after sufficient additional clock. -/
theorem evaluate_sourceChain {C F : Type} (expressions : List ClosLang.Exp) (start : Nat)
    (source final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (nonempty : expressions ≠ []) (installed : chainInstalled start expressions source.code)
    (run : evaluate expressions [] source = (result, final)) :
    ∃ body extra, findCode start ([] : List Value) source.code = some ([], body) ∧
      evaluate [body] [] { source with clock := source.clock + extra } = (sourceChainResult result, final) := by
  induction expressions generalizing start source final result with
  | nil => contradiction
  | cons first rest ih =>
    cases rest with
    | nil =>
      have head := ((chainInstalled_cons start first [] source.code).mp installed).1
      refine ⟨first, 0, by simpa using head, ?_⟩
      cases result with
      | err error => simpa [sourceChainResult] using run
      | val values =>
        have length := (evaluate_length (C := C) (F := F)).1 [first] [] source final values run
        cases values with
        | nil => simp at length
        | cons value tail =>
          cases tail with
          | cons other tail => simp at length
          | nil => simpa [sourceChainResult] using run
    | cons second tail =>
      have chainParts := (chainInstalled_cons start first (second :: tail) source.code).mp installed
      cases headRun : evaluate [first] [] source with
      | mk headResult middle =>
        have decomposed := run
        rw [evaluate, fixClock_evaluate, headRun] at decomposed
        cases headResult with
        | err error =>
          simp at decomposed
          rcases decomposed with ⟨rfl, rfl⟩
          refine ⟨.let .none [first] (.call .none 0 (start + 1) []), 0, ?_, ?_⟩
          · simpa using chainParts.1
          · simpa [sourceChainResult] using evaluate_sourceChain_first_error source middle first (start + 1) error headRun
        | val values =>
          have length := (evaluate_length (C := C) (F := F)).1 [first] [] source middle values headRun
          cases values with
          | nil => simp at length
          | cons value remaining =>
            cases remaining with
            | cons other remaining => simp at length
            | nil =>
              cases tailRun : evaluate (second :: tail) [] middle with
              | mk tailResult last =>
                simp only at decomposed
                rw [tailRun] at decomposed
                have tailInstalled := chainInstalled_after_evaluate (start + 1) (second :: tail) [first]
                  [] source middle (.val [value]) chainParts.2 headRun
                obtain ⟨body, extra, lookup, chainRun⟩ := ih (start + 1) middle last tailResult
                  (by simp) tailInstalled tailRun
                have chained := evaluate_sourceChain_first_success source middle last first body (start + 1) extra value
                  (sourceChainResult tailResult) headRun lookup chainRun
                have resultEq : sourceChainResult result = sourceChainResult tailResult ∧ final = last := by
                  cases tailResult with
                  | err error =>
                    simp at decomposed
                    rcases decomposed with ⟨rfl, rfl⟩
                    simp [sourceChainResult]
                  | val tailValues =>
                    have tailLength := (evaluate_length (C := C) (F := F)).1 (second :: tail) [] middle last tailValues tailRun
                    cases tailValues with
                    | nil => simp at tailLength
                    | cons next more =>
                      simp at decomposed
                      rcases decomposed with ⟨rfl, rfl⟩
                      simp [sourceChainResult]
                obtain ⟨resultEq, rfl⟩ := resultEq
                refine ⟨.let .none [first] (.call .none 0 (start + 1) []), extra + 1, ?_, ?_⟩
                · simpa using chainParts.1
                · simpa [resultEq] using chained

namespace Chain

/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ state : StateBroad C F, (State.ofBroad state).toBroad = state) ∧
      (∀ state : State C F, State.ofBroad state.toBroad = state) :=
  Flapjack.Compiler.Backend.ClosSem.holFmapAsFiniteSupportWitness

/-- Flapjack proof infrastructure: a chain result preserves the original
result classification when payloads are unconstrained. -/
private theorem sourceChainResult_rel (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) :
    Flapjack.SemanticPrimitivesProps.resultRel (fun _ _ => True) (fun _ _ => True)
      (sourceChainResult result) result := by
  cases result with
  | val values => simp [sourceChainResult, Flapjack.SemanticPrimitivesProps.resultRel]
  | err error =>
    cases error <;> simp [sourceChainResult, Flapjack.SemanticPrimitivesProps.resultRel,
      Flapjack.SemanticPrimitivesProps.excRel]

/-- An installed chain has one fixed entry expression that simulates the
nonempty source sequence with the original result relation and FFI equality.
The independent unused binder is present in the HOL statement. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "chain_installed_thm"
  (fmap_as_finite_support := [refs, code])]
theorem chainInstalled_thm {C F A : Type} [Nonempty A] (expressions : List ClosLang.Exp) (start : Nat) :
    ∃ body, ∀ (state : Flapjack.Compiler.Backend.ClosSem.State C F) (_code : A)
      (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
      (final : Flapjack.Compiler.Backend.ClosSem.State C F),
      chainInstalled start expressions state.code ∧ evaluate expressions [] state = (result, final) ∧
        0 < expressions.length →
      ∃ extra targetResult targetFinal,
        findCode start ([] : List Value) state.code = some ([], body) ∧
        evaluate [body] [] { state with clock := state.clock + extra } = (targetResult, targetFinal) ∧
        Flapjack.SemanticPrimitivesProps.resultRel (fun _ _ => True) (fun _ _ => True) targetResult result ∧
        final.ffi = targetFinal.ffi := by
  cases expressions with
  | nil =>
    refine ⟨.var .none 0, ?_⟩
    intro state code result final ⟨_, _, nonempty⟩
    simp at nonempty
  | cons first rest =>
    refine ⟨if rest = [] then first else .let .none [first] (.call .none 0 (start + 1) []), ?_⟩
    intro state code result final ⟨installed, run, _⟩
    have expected := ((chainInstalled_cons start first rest state.code).mp installed).1
    obtain ⟨body, extra, found, evaluation⟩ :=
      evaluate_sourceChain (first :: rest) start state final result (by simp) installed run
    have same : body = if rest = [] then first else .let .none [first] (.call .none 0 (start + 1) []) := by
      have equality := found.symm.trans expected
      exact congrArg Prod.snd (Option.some.inj equality)
    subst body
    exact ⟨extra, sourceChainResult result, final, expected, evaluation, sourceChainResult_rel result, rfl⟩

end Chain

end Flapjack.Compiler.Backend.ClosToBvl
