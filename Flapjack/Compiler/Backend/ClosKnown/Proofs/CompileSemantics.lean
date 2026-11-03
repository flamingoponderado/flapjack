import Flapjack.Compiler.Backend.ClosKnown.Proofs.SyntaxOracle
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosFvs.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosTicks.Proofs.Semantics
import Flapjack.Compiler.Backend.ClosLetop.Proofs.Semantics

/-! Whole-pass observational composition for the known-function optimizer. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem BackendProps

private abbrev fvsInc : Program → Program := ClosFvs.compileInc
private abbrev ticksInc : Program → Program := ClosTicks.compileInc
private abbrev letopInc : Program → Program := ClosLetop.compileInc

/-- Adapt the downstream compiler to the optional known-function pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_cc_def"]
def knownCc {C : Type} (config : Option Config) (cc : Compiler C) :
    Compiler (Spt ValApprox × C) :=
  match config with
  | some c => pureCc fvsInc
      (stateCc (compileInc c) (pureCc ticksInc (pureCc letopInc cc)))
  | none => stateCc (fun g p => (g, p)) cc

/-- Adapt the compilation oracle to the optional known-function pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_co_def"]
def knownCo {C : Type} (config : Option Config) (co : CompileOracle (Spt ValApprox × C)) :
    CompileOracle C :=
  match config with
  | some c => pureCo letopInc ∘ pureCo ticksInc ∘
      stateCo (compileInc c) (pureCo fvsInc ∘ co)
  | none => stateCo (fun g p => (g, p)) co

/-- The enabled branch of the whole-pass theorem, using the original
syntax-oracle precondition. This composition is Lean infrastructure; the
source theorem also covers the disabled branch and explicit equalities. -/
theorem semanticsCompileSome {C F : Type} (c : Config) (ffi : HolFfiState F) (maxApp : Nat)
    (co : CompileOracle (Spt ValApprox × C)) (cc : Compiler C) (xs : List ClosLang.Exp)
    (ys : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (nonFail : semantics ffi maxApp HolFiniteMapExact.holEmpty co (knownCc (some c) cc) xs ≠ .fail)
    (oracle : syntaxOracleOk c xs co g) (positive : 1 ≤ maxApp)
    (known : knownListTotal c (ClosFvs.compile xs) [] .ln = (ys, g)) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty (knownCo (some c) co) cc
      (compile (some c) xs).2 =
      semantics ffi maxApp HolFiniteMapExact.holEmpty co (knownCc (some c) cc) xs := by
  let fco : CompileOracle (Spt ValApprox × C) := pureCo ClosFvs.compileInc ∘ co
  let kco : CompileOracle C := stateCo (compileInc c) fco
  let tco : CompileOracle C := pureCo ClosTicks.compileInc ∘ kco
  let afterKnown : Compiler C := pureCc ticksInc (pureCc letopInc cc)
  have aux : ∀ n, (co n).2.2 = [] := fun n => (oracle.2.2.2.2 n).2
  have fvsEq := ClosFvs.semantics_compile ffi maxApp co (stateCc (compileInc c) afterKnown) xs
    (by simpa [knownCc, afterKnown] using nonFail) ⟨aux, positive⟩
  have fvsNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty fco
      (stateCc (compileInc c) afterKnown) (ClosFvs.compile xs) ≠ .fail := by
    rw [fvsEq]; simpa [knownCc, afterKnown] using nonFail
  have knownEq := Semantics.semanticsKnownHOL c ffi maxApp fco afterKnown (ClosFvs.compile xs) ys g
    fvsNonfail (syntaxOracleOk_fvsKnownPremises c xs co g ys oracle known)
  have knownNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty kco afterKnown
      (ys.map Prod.fst) ≠ .fail := by rw [knownEq, fvsEq]; simpa [knownCc, afterKnown] using nonFail
  have kaux : ∀ n, (kco n).2.2 = [] := by
    intro n
    simp [kco, fco, stateCo, pureCo, ClosFvs.compileInc, compileInc]
  have ticksEq := ClosTicks.semantics_remove_ticks ffi maxApp kco (pureCc ClosLetop.compileInc cc)
    (ys.map Prod.fst) knownNonfail ⟨kaux, positive⟩
  have ticksNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty tco (pureCc ClosLetop.compileInc cc)
      (ClosTicks.removeList (ys.map Prod.fst)) ≠ .fail := by
    rw [← ticksEq, knownEq, fvsEq]; simpa [knownCc, afterKnown] using nonFail
  have taux : ∀ n, (tco n).2.2 = [] := by simp [tco, pureCo, ClosTicks.compileInc]
  have letopEq := ClosLetop.semantics_let_op ffi maxApp tco cc
    (ClosTicks.removeList (ys.map Prod.fst)) ticksNonfail ⟨taux, positive⟩
  simpa [compile, known, knownCo, knownCc, fco, kco, tco, afterKnown] using
    letopEq.trans (ticksEq.symm.trans (knownEq.trans fvsEq))

end Flapjack.Compiler.Backend.ClosKnown
