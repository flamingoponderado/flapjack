module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateBoundList

@[expose] public section

/-! Named constructor simulation under a local binding. The factored
relations remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A constructor lookup simulation needs the constructor component of the
global invariant; local variable bindings leave that component unchanged. -/
theorem exprSim_constructor_local_valid {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : State F) (flatState : FlatSem.State C F)
    (id : Ident ModN ConN) (args : List AstHOL.Exp) (stamp : Stamp)
    (sourceLookup : nsLookup sourceEnv.c id = some (args.length, stamp))
    (mapped : ∃ cn group, nsLookup compMap.c id = some (cn, group) ∧
      genv.c.lookup ((cn, group.map Prod.fst), args.length) = some stamp)
    (argsSim : ExprListSim genv compMap trace sourceEnv flatEnv sourceState flatState args.reverse) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.con (some id) args) := by
  obtain ⟨cn, group, compiledLookup, stampLookup⟩ := mapped
  have compiledCtor : typeGroupIdType (some (cn, group)) = some (cn, group.map Prod.fst) := by
    cases group with
    | none => rfl
    | some pair => cases pair; rfl
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv args.reverse with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at argsSim
    cases flatRun : FlatSem.evaluate flatEnv flatState (compileExps trace compMap args).reverse with
    | mk flatNext flatResult =>
      rw [flatRun] at argsSim
      obtain ⟨related, nextRel⟩ := argsSim
      cases related with
      | value valuesRel =>
        have lengthEq := EvaluateProps.evaluateLengthFull sourceState sourceNext sourceEnv args.reverse _ sourceRun
        simp only [List.length_reverse] at lengthEq
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
        simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte,
          Option.bind_some, compiledLookup, compiledCtor, sourceRun, flatRun, buildConv]
        apply And.intro _ nextRel
        apply ResultRel.value
        apply List.Forall₂.cons _ List.Forall₂.nil
        apply valueRel_constructor genv stamp (cn, group.map Prod.fst)
        · exact List.rel_reverse valuesRel
        · simpa [List.length_reverse, lengthEq] using stampLookup
      | raise valueRel =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
        simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte, sourceRun, flatRun]
        exact ⟨.raise valueRel, nextRel⟩
      | abort error =>
        unfold ExprSim
        rw [EvaluateHOL.evaluate, compileExp, FlatSem.evaluate]
        simp only [doConCheck, sourceLookup, beq_self_eq_true, ↓reduceIte, sourceRun, flatRun]
        exact ⟨.abort error, nextRel⟩


end Flapjack.Compiler.Backend.SourceToFlat
