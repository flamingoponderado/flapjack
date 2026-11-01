import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.EvaluateCases

/-! Code and oracle safety across closure-language installation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

private theorem everyFnVarsNone_mem (expressions : List ClosLang.Exp)
    (safe : everyFnVarsNone expressions) (body : ClosLang.Exp) (member : body ∈ expressions) :
    everyFnVarsNone [body] := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
    simp only [everyFnVarsNone] at safe
    rcases List.mem_cons.mp member with rfl | member
    · simpa [everyFnVarsNone] using safe.1
    · exact ih safe.2 member

private theorem updateCode_safe (lookup : Nat → Option (Nat × ClosLang.Exp))
    (entries : List (Nat × Nat × ClosLang.Exp))
    (safe : ∀ key arity body, lookup key = some (arity, body) → everyFnVarsNone [body])
    (entriesSafe : ∀ entry ∈ entries, everyFnVarsNone [entry.2.2]) :
    ∀ key arity body, FUPDATE_LIST_HOL lookup entries key = some (arity, body) → everyFnVarsNone [body] := by
  induction entries generalizing lookup with
  | nil => simpa [FUPDATE_LIST_HOL] using safe
  | cons entry rest ih =>
    rw [FUPDATE_LIST_HOL_cons]
    apply ih
    · intro key arity body found
      by_cases same : key = entry.1
      · subst key
        simp [FUPDATE_HOL] at found
        have eq := found
        cases entry with
        | mk key payload =>
          cases payload with
          | mk storedArity storedBody =>
            simp only [Prod.mk.injEq] at eq
            obtain ⟨rfl, rfl⟩ := eq
            exact entriesSafe (key, storedArity, storedBody) (by simp)
      · apply safe key arity body
        simpa [FUPDATE_HOL, same] using found
    · intro e member
      exact entriesSafe e (by simp [member])

/-- A non-type-error installation retains safety of existing code, inserts
only safe oracle bodies, and advances to another safe oracle suffix. -/
theorem doInstall_preserves_safe {C F : Type} (values : List Value) (source next : State C F)
    (result : Result (List ClosLang.Exp) Value)
    (run : doInstall values source = (result, next)) (notType : result ≠ .err (.abort .typeError))
    (code : CodeSafe source) (oracle : OracleSafe source) : CodeSafe next ∧ OracleSafe next := by
  obtain ⟨_, _, _, _, config, expressions, auxiliary, _, _, _, _, oracleEntry, _, _, _, _, _, nextEq, _⟩ :=
    doInstall_nonType_parts values source next result run notType
  have bodies : everyFnVarsNone (auxiliary.map (fun (_, _, body) => body)) := by
    have h := (oracle 0).2
    simpa [oracleEntry] using h
  have entriesSafe : ∀ entry ∈ auxiliary, everyFnVarsNone [entry.2.2] := by
    intro entry member
    apply everyFnVarsNone_mem _ bodies entry.2.2
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [nextEq]
  constructor
  · intro key arity body found
    simp only [HolFiniteMapExact.lookup_updateListEq] at found
    exact updateCode_safe source.code.lookup auxiliary code entriesSafe key arity body found
  · intro index
    exact oracle (index + 1)

/-- Invalid installation requests leave the state unchanged. -/
theorem doInstall_typeError_state {C F : Type} (values : List Value) (source next : State C F)
    (run : doInstall values source = (.err (.abort .typeError), next)) : next = source := by
  unfold doInstall at run
  repeat' first | split at run | simp_all

/-- Installation preserves code and oracle safety for every result,
including rejected requests and timeouts. -/
theorem doInstall_preserves_safe_all {C F : Type} (values : List Value) (source next : State C F)
    (result : Result (List ClosLang.Exp) Value) (run : doInstall values source = (result, next))
    (code : CodeSafe source) (oracle : OracleSafe source) : CodeSafe next ∧ OracleSafe next := by
  by_cases typeError : result = .err (.abort .typeError)
  · subst result
    have same := doInstall_typeError_state values source next run
    simpa [same] using And.intro code oracle
  · exact doInstall_preserves_safe values source next result run typeError code oracle

end Flapjack.Compiler.Backend.ClosAnnotate
