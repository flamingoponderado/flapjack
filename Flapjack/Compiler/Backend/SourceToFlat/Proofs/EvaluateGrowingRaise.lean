import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateGrowingConstructors

/-! Exception-raising expression composition over the preliminary factored
source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- Raising preserves the growing expression step of its operand. -/
theorem dletExpressionStep_raise {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (genv : GlobalEnv) (start finish : NextIndices) (other : Set (Nat × IndexKind))
    (source : State F) (flat : FlatSem.State C F) (sourceEnv : SemEnv Value)
    (trace : List VarN) (compMap : Environment) (gen : EnvironmentGenerationStore) (body : AstHOL.Exp)
    (bodyStep : DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen body) :
    DletExpressionStep interp transform genv start finish other source flat sourceEnv trace compMap gen (.raise body) := by
  obtain ⟨nextGenv, bodySim, post⟩ := bodyStep
  refine ⟨nextGenv, exprSim_raise nextGenv compMap trace sourceEnv ⟨[]⟩ source flat body bodySim, ?_⟩
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at post ⊢
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate ⟨[]⟩ flat [compileExp trace compMap body] = flatResult at post ⊢
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  cases sourceResult with
  | err error =>
    cases error with
    | abort error => simp [EvaluateHOL.evaluate, sourceRun]
    | raise value =>
      cases flatResult <;> simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, sourceRun, flatRun] using post
  | val values =>
    cases flatResult <;> simpa [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate, sourceRun, flatRun] using post

/-- The expression induction hypothesis for `raise` follows from that of
its operand. -/
theorem factoredExpressionIH_raise {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (body : AstHOL.Exp) (bodyIH : FactoredExpressionIH (F := F) interp transform body) :
    FactoredExpressionIH (F := F) interp transform (.raise body) := by
  intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    simp [EvaluateHOL.evaluate, bad]
  exact dletExpressionStep_raise interp transform genv start finish other source flat sourceEnv trace compMap gen body
    (bodyIH genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation bodySafe)

/-- Covered expressions with nested constructors and explicit exception
raising, over the preliminary factored relations. -/
inductive FactoredRaisedExpression : AstHOL.Exp → Prop where
  | simple (expr : AstHOL.Exp) : FactoredSimpleExpression expr → FactoredRaisedExpression expr
  | constructor (name : Option (Ident ModN ConN)) (args : List AstHOL.Exp) :
      (∀ expr, expr ∈ args → FactoredRaisedExpression expr) → FactoredRaisedExpression (.con name args)
  | raise_ (body : AstHOL.Exp) : FactoredRaisedExpression body → FactoredRaisedExpression (.raise body)
  | tannot (expr : AstHOL.Exp) (typ : AstT) : FactoredRaisedExpression expr → FactoredRaisedExpression (.tannot expr typ)
  | lannot (expr : AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs) : FactoredRaisedExpression expr →
      FactoredRaisedExpression (.lannot expr loc)

/-- These expressions satisfy the factored growing induction hypothesis. -/
theorem factoredExpressionIH_raisedTree {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (expr : AstHOL.Exp) (covered : FactoredRaisedExpression expr) :
    FactoredExpressionIH (F := F) interp transform expr := by
  induction covered with
  | simple expr supported =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    exact factoredSimpleExpression_step interp transform genv start finish other source flat sourceEnv trace compMap
      gen expr supported envInv invariant generation safe
  | constructor name args _ ih => exact factoredExpressionIH_constructor interp transform name args ih
  | raise_ body _ ih => exact factoredExpressionIH_raise interp transform body ih
  | tannot expr typ _ ih =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    apply dletExpressionStep_tannot interp transform genv start finish other source flat sourceEnv trace compMap gen expr typ
    apply ih genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation
    intro last bad
    apply safe last
    simpa [EvaluateHOL.evaluate] using bad
  | lannot expr loc _ ih =>
    intro genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation safe
    apply dletExpressionStep_lannot interp transform genv start finish other source flat sourceEnv trace compMap gen expr loc
    apply ih genv start finish other source flat sourceEnv trace compMap gen envInv invariant generation
    intro last bad
    apply safe last
    cases loc
    simpa [EvaluateHOL.evaluate] using bad

end Flapjack.Compiler.Backend.SourceToFlat
