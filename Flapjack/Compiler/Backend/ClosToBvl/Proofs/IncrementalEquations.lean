module

public import Flapjack.Compiler.Backend.ClosAnnotate.Original
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Compiler.Backend.ClosFvs.Source
public import Flapjack.Compiler.Backend.ClosToBvl.SourceInc

@[expose] public section

/-! Source equations for incremental closure preprocessing and lowering. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack

/-- Incremental annotation applies annotation to expressions and code. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "acompile_inc_uncurry"]
theorem acompileInc_uncurry {α : Type}
    (p : List ClosLang.Exp × List (α × Nat × ClosLang.Exp)) :
    ClosAnnotate.compileIncSource p =
      (ClosAnnotate.annotateSource 0 p.1, ClosAnnotate.compileSource p.2) := rfl

/-- Incremental call conversion exposes the result of its traversal. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ccompile_inc_uncurry"]
theorem ccompileInc_uncurry {α : Type} (g : NumSet) (p : List ClosLang.Exp × α) :
    ClosCall.compileInc g p =
      ((ClosCall.calls p.1 (g, [])).2.1, (ClosCall.calls p.1 (g, [])).1,
        (ClosCall.calls p.1 (g, [])).2.2) := by
  cases h : ClosCall.calls p.1 (g, []) with
  | mk es state => cases state; simp [ClosCall.compileInc, h]

/-- Incremental closure-to-BVL compilation chains the extracted program. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_inc_uncurry"]
theorem compileInc_uncurry (maxApp : Nat)
    (p : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    compileInc maxApp p = compileProgExpsHOL maxApp
      (chainExps (extractNameSource p.1).1 (extractNameSource p.1).2 ++ p.2) := by
  cases h : extractNameSource p.1 with
  | mk start es => simp [compileInc, h]

/-- Incremental free-variable removal discards its input auxiliary payload. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "fcompile_inc_uncurry"]
theorem fcompileInc_uncurry {Input Output : Type} (p : List ClosLang.Exp × Input) :
    (ClosFvs.compileIncSource p : List ClosLang.Exp × List Output) =
      (ClosFvs.compileSource p.1, []) := rfl

end Flapjack.Compiler.Backend.ClosToBvl
