module

public meta import Lean
public meta import Flapjack.HolRef

public meta section

/-! Prospective elaborated statement audit for guarded unifier equivalence.
    It checks the Lean shape only; source correspondence needs separate review. -/
namespace Flapjack
open Lean Meta

/-- Check the direct binders, original well-formedness guard, and complete
    chosen-unifier/recursion-model equality. This does not establish that the
    two model operations correspond to HOL or validate a representation tag. -/
def unifyEqTunifyStatementProblems (type : Expr) : MetaM (Array String) := do
  forallTelescope type fun args conclusion => do
    unless args.size == 5 do
      return #[s!"expected a type, map, two terms and one premise; got {args.size} binders"]
    let typeDecl ← args[0]!.fvarId!.getDecl
    unless typeDecl.binderInfo == .implicit && (← isDefEq typeDecl.type (mkSort (Level.succ Level.zero))) do
      return #["the first binder must be an implicit Type parameter"]
    let termTy ← mkAppM `Flapjack.HOL.Unification.Term #[args[0]!]
    let mapTy ← mkAppM `Flapjack.HolFiniteMapExact #[mkConst ``Nat, termTy]
    for i in [1:4] do
      let binder ← args[i]!.fvarId!.getDecl
      let expected := if i == 1 then mapTy else termTy
      unless binder.binderInfo == .default && (← isDefEq binder.type expected) do
        return #[s!"binder {i + 1} has the wrong explicit carrier"]
      if i == 1 && binder.userName != `s then
        return #["the finite-map binder must be named s"]
    let premise ← args[4]!.fvarId!.getDecl
    let expectedGuard ← mkAppM `Flapjack.HOL.Unification.wfs #[args[1]!]
    unless premise.binderInfo == .default && premise.type.consumeMData == expectedGuard do
      return #["the sole premise must directly assert wfs of the original map"]
    let chosen ← mkAppM `Flapjack.HOL.Unification.specifiedUnify #[args[1]!, args[2]!, args[3]!]
    let recursive ← mkAppM `Flapjack.HOL.Unification.tunifyAux #[args[1]!, args[2]!, args[3]!]
    let expected ← mkEq chosen recursive
    unless conclusion.consumeMData == expected do
      return #["conclusion must be the exact selected/recursive equality on the original arguments"]
    return #[]

end Flapjack
