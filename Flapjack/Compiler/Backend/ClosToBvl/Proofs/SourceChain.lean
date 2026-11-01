import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ProgramCode
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ChainLocations
import Flapjack.Compiler.Backend.Semantics.ClosSem.InstallGrowth
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyCode
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateCodeGrowth

/-! Source closure-code chains used by the top-level compiler. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack Flapjack.Compiler.Backend.ClosSem

/-- The code map provides each zero-argument entry of a closure expression
chain. This candidate remains untagged pending HOL state-carrier review. -/
def chainInstalled (start : Nat) (expressions : List ClosLang.Exp)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) : Prop :=
  ∀ i, i < expressions.length →
    findCode (start + i) ([] : List Value) code = some ([],
      if i + 1 < expressions.length then
        .let .none [@holEl ClosLang.Exp ⟨.var .none 0⟩ i expressions] (.call .none 0 (start + i + 1) [])
      else @holEl ClosLang.Exp ⟨.var .none 0⟩ i expressions)

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

/-- The generated chain is installed in the source association-list code
map, including the empty-list dummy entry. -/
theorem chainInstalled_chainExps (start : Nat) (expressions : List ClosLang.Exp) :
    chainInstalled start expressions (initialSourceCode (chainExps start expressions)) := by
  induction expressions generalizing start with
  | nil => simp [chainInstalled]
  | cons first rest ih =>
    cases rest with
    | nil =>
      rw [chainInstalled_cons]
      constructor
      · simp [chainExps, findCode, initialSourceCode_cons_lookup]
      · simp [chainInstalled]
    | cons second tail =>
      rw [chainInstalled_cons]
      constructor
      · simp [chainExps, findCode, initialSourceCode_cons_lookup]
      · intro i bound
        have found := ih (start + 1) i bound
        have different : start + 1 + i ≠ start := by omega
        simp only [chainExps, findCode, initialSourceCode_cons_lookup, if_neg different]
        exact found

/-- The chain's first zero-argument entry exists even for an empty batch. -/
theorem chainExps_entry (start : Nat) (expressions : List ClosLang.Exp) :
    ∃ body, findCode start ([] : List Value) (initialSourceCode (chainExps start expressions)) = some ([], body) := by
  cases expressions with
  | nil =>
    refine ⟨.op .none (.intOp (.const 0)) [], ?_⟩
    simp [chainExps, findCode, initialSourceCode_cons_lookup]
  | cons first rest =>
    have head := (chainInstalled_cons start first rest _).mp (chainInstalled_chainExps start (first :: rest))
    exact ⟨_, head.1⟩

/-- A dynamic installation cannot invalidate an already installed source
chain, even if installation returns a timeout. -/
theorem chainInstalled_after_install {C F : Type} (start : Nat) (expressions : List ClosLang.Exp)
    (values : List Value) (source next : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List ClosLang.Exp) Value)
    (installed : chainInstalled start expressions source.code) (run : doInstall values source = (result, next)) :
    chainInstalled start expressions next.code :=
  chainInstalled_submap start expressions source.code next.code installed
    (doInstall_code_submap values source next result run)

/-- Successful ordinary primitives leave the installed chain unchanged. -/
theorem chainInstalled_after_primitive {C F : Type} (start : Nat) (expressions : List ClosLang.Exp)
    (op : ClosLang.Op) (values : List Value) (source next : State C F) (value : Value)
    (installed : chainInstalled start expressions source.code) (run : doApp op values source = .val (value, next)) :
    chainInstalled start expressions next.code := by
  have same := (doApp_codeOracle op values source next value run).1
  simpa [same] using installed

/-- Any closure evaluation retains an installed chain, regardless of its
result. The evaluator's correspondence with HOL is still to be reviewed. -/
theorem chainInstalled_after_evaluate {C F : Type} (start : Nat) (chain evaluated : List ClosLang.Exp)
    (env : List Value) (source next : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (installed : chainInstalled start chain source.code) (run : evaluate evaluated env source = (result, next)) :
    chainInstalled start chain next.code :=
  chainInstalled_submap start chain source.code next.code installed
    (evaluate_code_growth.1 evaluated env source next result run)

end Flapjack.Compiler.Backend.ClosToBvl
