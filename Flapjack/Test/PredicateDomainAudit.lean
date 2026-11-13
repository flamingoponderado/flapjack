import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Semantics
import Flapjack.HolRef

/-! Elaborated regression checks for the prospective predicate-domain guard.
These fixtures have no HOL tag and do not authorize the qualifier. -/

open Flapjack Flapjack.Compiler.Backend Lean Meta

set_option linter.unusedVariables false in
private def predicateShape {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (co1 : ClosSem.CompileOracle C₁)
    (cc1 : ClosSem.Compiler C₁) (es1 : List ClosLang.Exp) (code2 : Spt (Nat × Bvl.Exp))
    (co2 : BvlSem.CompileOracle C₂) (cc2 : BvlSem.Compiler C₂) (start : Nat)
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → ClosSem.CompileOracle C₁ →
      ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
      BvlSem.CompileOracle C₂ → BvlSem.Compiler C₂ → Nat → Prop) : Prop :=
  True

set_option linter.unusedVariables false in
private def theoremShape : Prop :=
  ∀ {C₁ C₂ F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code1 : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (co1 : ClosSem.CompileOracle C₁)
    (cc1 : ClosSem.Compiler C₁) (es1 : List ClosLang.Exp) (code2 : Spt (Nat × Bvl.Exp))
    (co2 : BvlSem.CompileOracle C₂) (cc2 : BvlSem.Compiler C₂) (start : Nat)
    (rel : HolFiniteMapExact Nat (Nat × ClosLang.Exp) → ClosSem.CompileOracle C₁ →
      ClosSem.Compiler C₁ → List ClosLang.Exp → Spt (Nat × Bvl.Exp) →
      BvlSem.CompileOracle C₂ → BvlSem.Compiler C₂ → Nat → Prop)
    (h : predicateShape ffi maxApp code1 co1 cc1 es1 code2 co2 cc2 start rel ∧
      ClosSem.semantics ffi maxApp code1 co1 cc1 es1 ≠ .fail)
    (relation : rel code1 co1 cc1 es1 code2 co2 cc2 start),
    BvlSem.semantics ffi code2 co2 cc2 start = ClosSem.semantics ffi maxApp code1 co1 cc1 es1

private partial def editPredicateBinder (type : Expr) (index : Nat)
    (edit : Name → Expr → Expr → BinderInfo → Expr) : Expr :=
  match type with
  | .forallE name domain body info =>
    if index == 0 then edit name domain body info
    else .forallE name domain (editPredicateBinder body (index - 1) edit) info
  | _ => type

private partial def reversePredicateConclusion (type : Expr) : Expr :=
  match type with
  | .forallE name domain body info => .forallE name domain (reversePredicateConclusion body) info
  | .app (.app (.app eq carrier) left) right => mkApp3 eq carrier right left
  | _ => type

run_meta do
  let info ← getConstInfo ``predicateShape
  let good ← predicateDomainSignatureProblems info.type false
  unless good.isEmpty do throwError "valid signature was rejected: {good}"
  let wrongCarrier := editPredicateBinder info.type 10 fun name domain body binderInfo =>
    match domain with
    | .app f (.bvar index) => .forallE name (.app f (.bvar (index + 1))) body binderInfo
    | _ => .forallE name domain body binderInfo
  let hiddenDomain := editPredicateBinder info.type 13 fun name domain body binderInfo =>
    match domain with
    | .forallE n a b _ => .forallE name (.forallE n a b BinderInfo.implicit) body binderInfo
    | _ => .forallE name domain body binderInfo
  let wrongBinder := editPredicateBinder info.type 0 fun name domain body _ =>
    .forallE name domain body BinderInfo.default
  let wrongFfi := editPredicateBinder info.type 3 fun name domain body binderInfo =>
    match domain with
    | .app f (.bvar index) => .forallE name (.app f (.bvar (index + 1))) body binderInfo
    | _ => .forallE name domain body binderInfo
  let wrongUniverse := editPredicateBinder info.type 0 fun name _ body binderInfo =>
    .forallE name (mkSort (Level.succ (Level.succ Level.zero))) body binderInfo
  let wrongMap := editPredicateBinder info.type 13 fun name domain body binderInfo =>
    match domain with
    | .forallE n _ b i => .forallE name (.forallE n (mkConst ``Nat) b i) body binderInfo
    | _ => .forallE name domain body binderInfo
  for (label, bad) in [("compiler carrier", wrongCarrier), ("implicit relation domain", hiddenDomain),
      ("binder information", wrongBinder), ("FFI carrier", wrongFfi), ("universe", wrongUniverse),
      ("relation map domain", wrongMap)] do
    let problems ← predicateDomainSignatureProblems bad false
    if problems.isEmpty then throwError "invalid {label} was accepted"
  let .defnInfo shape ← getConstInfo ``theoremShape | throwError "missing theorem shape"
  -- The fixture stands in for the not-yet-ported evalSim only in this
  -- metaprogram. No declaration or proof is asserted at that name.
  let theoremType := shape.value.replace (fun e =>
    if e.isConstOf ``predicateShape then
      some (mkConst `Flapjack.Compiler.Backend.ClosToBvl.evalSim)
    else none)
  let goodTheorem ← predicateDomainSignatureProblems theoremType true
  unless goodTheorem.isEmpty do throwError "valid theorem signature was rejected: {goodTheorem}"
  let badPremise := editPredicateBinder theoremType 14 fun name _ body binderInfo =>
    .forallE name (mkConst ``True) body binderInfo
  let badRelation := editPredicateBinder theoremType 15 fun name _ body binderInfo =>
    .forallE name (mkConst ``True) body binderInfo
  let badNonfailure := editPredicateBinder theoremType 14 fun name domain body binderInfo =>
    match domain with
    | .app (.app andConst sim) _ =>
      .forallE name (.app (.app andConst sim) (mkConst ``True)) body binderInfo
    | _ => .forallE name domain body binderInfo
  for (label, bad) in [("simulation premise", badPremise), ("nonfailure premise", badNonfailure),
      ("relation premise", badRelation),
      ("conclusion direction", reversePredicateConclusion theoremType)] do
    let problems ← predicateDomainSignatureProblems bad true
    if problems.isEmpty then throwError "invalid {label} was accepted"
