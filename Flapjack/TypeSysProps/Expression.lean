module

public import Flapjack.TypeSysProps.Environment
public import Flapjack.TypeSysProps.Pattern

@[expose] public section

/-! Free-variable bounds for declarative expression typing. -/

namespace Flapjack.TypeSysProps
open Flapjack Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants Flapjack.NamespaceHOL
  Flapjack.Basis.Pure.MlString Flapjack.AstHOL

set_option maxHeartbeats 1200000 in
/-- Expression, expression-list and function typing preserve the source free-variable bounds. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "type_e_freevars"]
theorem typeEFreevars :
    (∀ env b e t, TypeE env b e t → tenvValExpOk b ∧ tenvValOk env.v → checkFreevars (numTvs b) [] t = true) ∧
    (∀ env b es ts, TypeEs env b es ts → tenvValExpOk b ∧ tenvValOk env.v → ts.all (checkFreevars (numTvs b) []) = true) ∧
    (∀ env b fs bs, TypeFuns env b fs bs → tenvValExpOk b ∧ tenvValOk env.v → (bs.map Prod.snd).all (checkFreevars (numTvs b) []) = true) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro env b e t typed
    let P := fun b e t (_ : TypeE env b e t) => tenvValExpOk b ∧ tenvValOk env.v → checkFreevars (numTvs b) [] t = true
    let Ps := fun b es ts (_ : TypeEs env b es ts) => tenvValExpOk b ∧ tenvValOk env.v → ts.all (checkFreevars (numTvs b) []) = true
    let Pf := fun b fs bs (_ : TypeFuns env b fs bs) => tenvValExpOk b ∧ tenvValOk env.v → (bs.map Prod.snd).all (checkFreevars (numTvs b) []) = true
    let Pb := fun b input output clauses (_ : TypeBranches env b input output clauses) => clauses ≠ [] → tenvValExpOk b ∧ tenvValOk env.v → checkFreevars (numTvs b) [] output = true
    first
    | refine TypeE.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    | refine TypeEs.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    | refine TypeFuns.rec (motive_1 := P) (motive_2 := Ps) (motive_3 := Pf) (motive_4 := Pb) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
    all_goals dsimp only [P, Ps, Pf, Pb] at *
    all_goals try simp_all [checkFreevars, checkFreevarsListEqAll, tenvValExpOk, numTvs, List.all_cons]
    case refine_11 =>
      intro localEnv name t args free lookup ok global
      have free' : args.all (checkFreevars (numTvs localEnv) []) = true := by simpa using free
      cases localResult : lookupVarE name localEnv with
      | none =>
        have found : nsLookup env.v name = some (args.length, t) := by simpa [lookupVar, localResult] using lookup
        have closed : checkFreevars args.length [] t = true := by
          have eqDec : (Classical.typeDecidableEq MlString) = inferInstanceAs (DecidableEq MlString) := Subsingleton.elim _ _
          apply global name (args.length, t)
          change @nsLookup _ _ _ (Classical.typeDecidableEq _) (Classical.typeDecidableEq _) _ _ = _
          rw [eqDec]
          exact found
        exact deBruijnSubstCheckFreevars2 (numTvs localEnv) [] t args () () ⟨closed, free'⟩
      | some val =>
        have found : lookupVarE name localEnv = some (args.length, t) := by simpa [lookupVar, localResult] using lookup
        cases name with
        | short n =>
          have l : tveLookup n 0 localEnv = some (args.length, t) := by simpa [lookupVarE] using found
          simpa using tveLookupFreevarsSubst localEnv args n t 0 ⟨by simpa using free', l, ok⟩
        | long m n => simp [lookupVarE] at found
    case refine_17 =>
      intro localEnv name e₁ e₂ t₁ t₂ value body ih₁ ih₂ ok global
      cases name with
      | none => simpa [optBindName] using ih₂ ok global
      | some name =>
        have free := ih₁ ok global
        simpa [optBindName, numTvs] using ih₂ (by simpa [optBindName, tenvValExpOk, numTvs] using And.intro free ok) global
    case refine_18 =>
      intro localEnv funs e t bindings functions body ihf ihb ok global
      have ok' := tenvValExpOkBvlFuns funs bindings env bindings () localEnv ⟨functions, ok⟩
      simpa [numTvsBindVarList] using ihb ok' global
    case refine_26 =>
      intro localEnv input output p body rest bindings distinct pattern expression tail ihe iht ok global
      have checks := (typePFreevars.1 (numTvs localEnv) env p input bindings pattern).2
      have ok' := tenvValExpOkBvl localEnv bindings ⟨ok, checks⟩
      simpa [numTvsBindVarList] using ihe ok' global
end Flapjack.TypeSysProps
