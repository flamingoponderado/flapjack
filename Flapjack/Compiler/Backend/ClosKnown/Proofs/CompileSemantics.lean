module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SyntaxOracle
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Semantics
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Semantics
public import Flapjack.Compiler.Backend.ClosTicks.Proofs.Semantics
public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Semantics
public import Flapjack.Compiler.Backend.Semantics.ClosProps.AdjustOracleSimulation
public import Flapjack.Compiler.Backend.BackendProps.OracleCombinators

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Whole-pass observational composition for the known-function optimizer. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosSem BackendProps

/-- The incremental free-variable pass discards its auxiliary input. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "fvs_compile_uncurry"]
theorem fvsCompileUncurry {α β : Type} (p : List ClosLang.Exp × β) :
    (ClosFvs.compileIncSource p : List ClosLang.Exp × List α) =
      (ClosFvs.removeSource 0 p.1, []) := rfl

private noncomputable abbrev fvsInc : Program → Program := ClosFvs.compileIncSource
private noncomputable abbrev ticksInc : Program → Program := ClosTicks.compileIncSource
private noncomputable abbrev letopInc : Program → Program := ClosLetop.compileIncSource

/-- Adapt the downstream compiler to the optional known-function pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_cc_def"]
noncomputable def knownCc {C : Type} (config : Option Config) (cc : Compiler C) :
    Compiler (Spt ValApprox × C) :=
  match config with
  | some c => pureCc fvsInc
      (stateCc (compileInc c) (pureCc ticksInc (pureCc letopInc cc)))
  | none => stateCc (fun g p => (g, p)) cc

/-- Adapt the compilation oracle to the optional known-function pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_co_def"]
noncomputable def knownCo {C : Type} (config : Option Config) (co : CompileOracle (Spt ValApprox × C)) :
    CompileOracle C :=
  match config with
  | some c => pureCo letopInc ∘ pureCo ticksInc ∘
      stateCo (compileInc c) (pureCo fvsInc ∘ co)
  | none => stateCo (fun g p => (g, p)) co

/-- Factor the optional oracle adaptation into pure and stateful stages. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_co_eq_pure_state"]
theorem knownCoEqPureState {C : Type} (config : Option Config)
    (co : CompileOracle (Spt ValApprox × C)) :
    knownCo config co =
      pureCo (if config.isSome then letopInc ∘ ticksInc else id) ∘
        stateCo (match config with | some c => compileInc c | none => fun g p => (g, p))
          (pureCo (if config.isSome then fvsInc else id) ∘ co) := by
  cases config <;> funext n <;> simp [knownCo, pureCo, stateCo, Function.comp_def]

/-- Construct stateful oracle configurations for the optional known pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_mk_co_def"]
noncomputable def knownMkCo {C : Type} (config next : Option Config)
    (mk : (Nat → Program) → Nat → C) : (Nat → Program) → Nat → Spt ValApprox × C :=
  addStateCo (match config with | some c => compileInc c | none => fun g p => (g, p))
    (optionValApproxSpt next)
    (mk ∘ pureCoProgs (if config.isSome then letopInc ∘ ticksInc else id)) ∘
    pureCoProgs (if config.isSome then fvsInc else id)

/-- Transform oracle programs through the optional known pass. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_co_progs_def"]
noncomputable def knownCoProgs (config next : Option Config) : (Nat → Program) → Nat → Program :=
  pureCoProgs (if config.isSome then letopInc ∘ ticksInc else id) ∘
    stateCoProgs (match config with | some c => compileInc c | none => fun g p => (g, p))
      (optionValApproxSpt next) ∘
    pureCoProgs (if config.isSome then fvsInc else id)

/-- The adapted full oracle is the full oracle of the adapted programs. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_co_known_mk_co"]
theorem knownCoKnownMkCo {C : Type} (config next : Option Config)
    (mk : (Nat → Program) → Nat → C) (co : Nat → Program) :
    knownCo config (syntaxToFullOracle (knownMkCo config next mk) co) =
      syntaxToFullOracle mk (knownCoProgs config next co) := by
  cases config <;> funext n <;>
    simp [knownCo, knownMkCo, knownCoProgs, pureCoProgs, pureCo, stateCo,
      syntaxToFullOracle, addStateCo, stateCoProgs, Function.comp_def]

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
  let afterKnown : Compiler C :=
    pureCc (ClosTicks.compileInc : Program → Program) (pureCc (ClosLetop.compileInc : Program → Program) cc)
  have aux : ∀ n, (co n).2.2 = [] := fun n => (oracle.2.2.2.2 n).2
  have fvsEq := ClosFvs.semantics_compile ffi maxApp co (stateCc (compileInc c) afterKnown) xs
    (by simpa [knownCc, afterKnown] using nonFail) ⟨aux, positive⟩
  simp only [ClosFvs.compileIncSource_eq, ClosFvs.compileSource_eq_compile] at fvsEq
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
    (ys.map Prod.fst) (by simpa [ClosTicks.compileIncSource_eq, afterKnown] using knownNonfail) ⟨kaux, positive⟩
  simp only [ClosTicks.compileIncSource_eq, ClosTicks.removeSource_eq_list] at ticksEq
  have ticksNonfail : semantics ffi maxApp HolFiniteMapExact.holEmpty tco (pureCc ClosLetop.compileInc cc)
      (ClosTicks.removeList (ys.map Prod.fst)) ≠ .fail := by
    rw [← ticksEq, knownEq, fvsEq]; simpa [knownCc, afterKnown] using nonFail
  have taux : ∀ n, (tco n).2.2 = [] := by simp [tco, pureCo, ClosTicks.compileInc]
  have letopEq := ClosLetop.semantics_let_op ffi maxApp tco cc
    (ClosTicks.removeList (ys.map Prod.fst)) (by simpa [ClosLetop.compileIncSource_eq] using ticksNonfail) ⟨taux, positive⟩
  simp only [ClosLetop.compileIncSource_eq, ClosLetop.compileSource_eq_list] at letopEq
  simpa [compile, known, knownCo, knownCc, fco, kco, tco, afterKnown] using
    letopEq.trans (ticksEq.symm.trans (knownEq.trans fvsEq))

local instance : Nonempty Config := ⟨defaultConfig 0⟩

/-- The optional known-function pass preserves closure observations under
the source syntax-oracle condition when enabled. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "semantics_compile"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem semanticsCompile {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (co : CompileOracle (Spt ValApprox × C)) (cc1 : Compiler (Spt ValApprox × C))
    (xs : List ClosLang.Exp) (knownConf knownConf' : Option Config) (cc : Compiler C)
    (co1 : CompileOracle C) (es : List ClosLang.Exp)
    (h : semantics ffi maxApp HolFiniteMapExact.holEmpty co cc1 xs ≠ .fail ∧
      cc1 = knownCc knownConf cc ∧ co1 = knownCo knownConf co ∧
      compileSource knownConf xs = (knownConf', es) ∧
      (knownConf.isSome → syntaxOracleOk (Flapjack.holThe knownConf) xs co
        (Flapjack.holThe knownConf').valApproxSpt ∧ 1 ≤ maxApp)) :
    semantics ffi maxApp HolFiniteMapExact.holEmpty co1 cc es =
      semantics ffi maxApp HolFiniteMapExact.holEmpty co cc1 xs := by
  obtain ⟨nonFail, rfl, rfl, compiled, assumption⟩ := h
  rw [compileSource_eq_compile] at compiled
  cases knownConf with
  | none =>
    simp [compile] at compiled
    obtain ⟨rfl, rfl⟩ := compiled
    exact ClosProps.AdjustOracle.semanticsCurryI ffi maxApp HolFiniteMapExact.holEmpty co cc xs
      (by simpa [knownCc] using nonFail)
  | some c =>
    cases known : knownListTotal c (ClosFvs.compile xs) [] .ln with
    | mk ys g =>
      simp [compile, known] at compiled
      obtain ⟨rfl, rfl⟩ := compiled
      have source := assumption (by simp)
      have oracle : syntaxOracleOk c xs co g := by simpa [Flapjack.holThe] using source.1
      have result := semanticsCompileSome c ffi maxApp co cc xs ys g nonFail oracle source.2 known
      simpa [compile, known] using result

end Flapjack.Compiler.Backend.ClosKnown
