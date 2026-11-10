module

public import Flapjack.Compiler.Backend.ClosToBvl.Common
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileSemantics
public import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMti
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.Misc.Bag
public import Flapjack.Misc.Option

@[expose] public section

/-! Source syntax and oracle conditions for closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps BackendProps

local instance : Nonempty ClosKnown.Config := ⟨ClosKnown.defaultConfig 0⟩

/-- The original whole-pipeline syntax and state-oracle preconditions. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "syntax_oracle_ok_def"]
noncomputable def syntaxOracleOkCommon {α : Type} (c c' : Config) (es : List ClosLang.Exp)
    (co : Nat → (Nat × Spt ClosKnown.ValApprox × NumSet × α) × ClosSem.Program) : Prop :=
  (∀ n, (co n).2.2 = []) ∧
  (c.doMti → 1 ≤ c.maxApp ∧ (∀ e ∈ es, noMti e) ∧
    ∀ n e, e ∈ (co n).2.1 → noMti e) ∧
  (∃ v : α, (co 0).1 =
    (c'.nextLoc, ClosKnown.optionValApproxSpt c'.knownConf, c'.callState.1, v)) ∧
  (c.doCall → everyFnVarsNone es ∧
    isStateOracle ClosCall.compileInc
      (ClosKnown.knownCo c.knownConf
        (stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co)))) ∧
  (c.knownConf.isSome → 1 ≤ c.maxApp ∧ everyFnVarsNone es ∧
    oracleMonotonic (fun entry => setOfBag (elistGlobals entry.2.1)) (· < ·)
      (setOfBag (elistGlobals es)) co ∧
    isStateOracle (ClosKnown.compileInc (holThe c.knownConf))
      (pureCo (ClosFvs.compileInc (α := List (Nat × Nat × ClosLang.Exp))
        (β := Nat × Nat × ClosLang.Exp)) ∘
        stateCo (ClosNumber.ignoreTable ClosNumber.compileInc)
          (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co)) ∧
    ∀ n, bagAllDistinct (elistGlobals (co n).2.1) ∧
      ∀ e ∈ (co n).2.1, esgcFree e) ∧
  ¬ containsAppSome c.maxApp es ∧ ClosKnown.syntaxOk es ∧
  (∀ n, ¬ containsAppSome c.maxApp (co n).2.1 ∧ everyFnVarsNone (co n).2.1) ∧
  isStateOracle (ClosNumber.ignoreTable ClosNumber.compileInc)
    (pureCo (ClosMti.condCompileInc c.doMti c.maxApp) ∘ co)

end Flapjack.Compiler.Backend.ClosToBvl
