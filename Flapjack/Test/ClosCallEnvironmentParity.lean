import Flapjack.Compiler.Backend.ClosCall.Proofs.Environment

/-! Replay binder and environment cases captured from CakeML/HOL. -/
namespace Flapjack.Test.ClosCallEnvironmentParity
open Flapjack.Compiler.Backend ClosCall ClosLang ClosProps
open Flapjack.Basis.Pure.MlString

private def posCases : List Exp :=
  [.let .none [.var .none 2] (.var .none 2),
   .fn (ofString "f") none none 2 (.var .none 2),
   .letrec [ofString "f", ofString "g"] (some 10) none
     [(1, .var .none 3), (0, .var .none 1)] (.var .none 0),
   .handle .none (.var .none 2) (.var .none 1)]

private def negCases : List Exp :=
  [.let .none [.var .none 2] (.var .none 1),
   .fn (ofString "f") none none 2 (.var .none 1),
   .letrec [ofString "f", ofString "g"] (some 10) none
     [(1, .var .none 1), (0, .var .none 1)] (.var .none 0),
   .handle .none (.var .none 2) (.var .none 0)]

example : freeVars 1 [posCases[0]] ∧ freeVars 0 [posCases[1]] ∧
    freeVars 0 [posCases[2]] ∧ freeVars 0 [posCases[3]] := by
  simp [posCases, freeVars, freeVarExp, freeVarFuns]

example : ¬freeVars 1 [negCases[0]] ∧ ¬freeVars 0 [negCases[1]] ∧
    ¬freeVars 0 [negCases[2]] ∧ ¬freeVars 0 [negCases[3]] := by
  simp [negCases, freeVars, freeVarExp, freeVarFuns]

example : envRel (· = ·) ([1, 2] : List Nat) [1] 0 [(0, .var .none 0)] := by
  simp [envRel, freeVar, freeVars, freeVarExp]

example : ¬envRel (· = ·) ([1, 2] : List Nat) [1] 0 [(0, .var .none 1)] := by
  simp [envRel, freeVar, freeVars, freeVarExp]

example : ¬envRel (· = ·) ([1, 2] : List Nat) [1, 3] 0 [] := by
  simp [envRel, List.forall₂_cons_left_iff]

example : envRel (· = ·) ([1, 2] : List Nat) [1, 2] 0 [] := by
  simp [envRel, List.forall₂_cons_left_iff]

end Flapjack.Test.ClosCallEnvironmentParity
