module

public import Flapjack.Compiler.Backend.SourceToFlat.Proofs.OracleStep
public import Flapjack.Compiler.Backend.SourceEval.Proofs

@[expose] public section

/-! Agreement between the source and flat compiler callbacks. -/
namespace Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

instance oracleRelInst1 : Nonempty Config :=
  ⟨{ next := ⟨0, 0, 0⟩, modEnv := emptyEnv, patternCfg := ⟨0⟩, envs := ⟨0, .ln⟩ }⟩

/-- Incremental source-to-flat compilation always emits the global-allocation
expression before its compiled declarations. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "inc_compile_prog_nonempty"]
theorem incCompileProg_nonempty (envId : Nat × Nat) (config next : Config)
    (decs : List Dec) (flatDecs : List FlatLang.Exp)
    (compiled : incCompileProg envId config decs = (next, flatDecs)) : flatDecs ≠ [] := by
  have nonempty : (incCompileProg envId config decs).2 ≠ [] := by
    simp [incCompileProg]
  simpa [compiled] using nonempty

/-- Each source oracle entry corresponds to a flat compilation entry, and a
successful source compiler callback has a matching flat callback result. HOL
types are inhabited; `Nonempty C` supplies the payload needed by `THE`. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_rel_inner_def"]
noncomputable def oracRelInner {C : Type} [Nonempty C] (decode : Value → Option (Config × C))
    (state : EvalOracleState) (compiler : CompilerFun) (transform : List Dec → List Dec)
    (flat : FlatSem.InstallConfig C) : Prop :=
  ∀ k envId stateValue decs, state.oracle k = (envId, stateValue, decs) →
    let decoded := Flapjack.holThe (decode stateValue)
    let flatDecs := (incCompileProg envId decoded.1 (transform decs)).2
    flat.compileOracle k = (decoded.2, flatDecs) ∧
      (compiler (envId, stateValue, decs) ≠ none →
        ∃ bytes words nextFlat nextValue,
          flat.compile decoded.2 flatDecs = some (bytes, words, nextFlat) ∧
          compiler (envId, stateValue, decs) = some (nextValue, bytes, words) ∧
          ∀ nextDecoded, decode nextValue = some nextDecoded → nextDecoded.2 = nextFlat)

/-- Source and flat Eval oracles agree through the source callback. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_rel_def"]
noncomputable def oracRel {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : Option EvalState) (flat : FlatSem.InstallConfig C) : Prop :=
  match interp, source with
  | _, none => True
  | some decode, some (.evalOracle state) =>
    ∃ compiler, state.customDoEval = SourceEval.Proofs.doEvalOracle compiler transform ∧
      oracRelInner decode state compiler transform flat
  | _, _ => False

/-- A related source Eval state must be an oracle with a decoder. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "orac_rel_SOME_eval"]
theorem oracRel_some {C : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec)
    (source : EvalState) (flat : FlatSem.InstallConfig C)
    (related : oracRel interp transform (some source) flat) :
    ∃ decode state, interp = some decode ∧ source = .evalOracle state := by
  cases interp with
  | none => cases source <;> simp [oracRel] at related
  | some decode =>
    cases source with
    | evalDecs state => simp [oracRel] at related
    | evalOracle state => exact ⟨decode, state, rfl, rfl⟩

end Flapjack.Compiler.Backend.SourceToFlat.OracleInvariant
