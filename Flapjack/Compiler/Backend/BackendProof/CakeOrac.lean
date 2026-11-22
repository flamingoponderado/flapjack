module

public import Flapjack.Compiler.Backend.Backend.IncProgs
public import Flapjack.Compiler.Backend.Backend.Compile
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 317-351 and 487-628: the incremental compiler
oracle `cake_orac`, built from the configurations `cake_configs` threaded by
`compile_inc_progs`, and its unfolding equations. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Backend
open Flapjack.Compiler.Backend.BackendDefs
open Flapjack.Compiler.Backend.BackendProps

/-- Exact HOL `backendProof$cake_configs_def` (`backendProofScript.sml:317-320`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_configs_def"
  (words_as_type_indexed_bitvec)]
noncomputable def cakeConfigs {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config)
    (source : Nat → (Nat × Nat) × List AstHOL.Dec) :
    Nat → Flapjack.Compiler.Backend.Backend.Config :=
  stateOracStates (compileIncProgs true asmConf) c source

/-- Exact HOL `backendProof$cake_orac_def` (`backendProofScript.sml:322-327`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_def"
  (words_as_type_indexed_bitvec)]
noncomputable def cakeOrac {width : Nat} [NeZero width] {α β : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (source : Nat → (Nat × Nat) × List AstHOL.Dec)
    (f : Flapjack.Compiler.Backend.Backend.Config → α) (g : BackendProgs width → β)
    (i : Nat) : α × β :=
  let c := cakeConfigs asmConf c source i
  let (_, progs) := compileIncProgs true asmConf c (source i)
  (f c, g progs)

/-- `cake_orac` as an explicit pair (Flapjack infrastructure; avoids reducing
the incremental compiler while unfolding the destructuring `let`). -/
theorem cakeOrac_eq_pair {width : Nat} [NeZero width] {A B : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (g : Flapjack.Compiler.Backend.Backend.Config → A) (h : BackendProgs width → B) (i : Nat) :
    cakeOrac asmConf c' src g h i =
      (g (cakeConfigs asmConf c' src i),
        h (compileIncProgs true asmConf (cakeConfigs asmConf c' src i) (src i)).2) := by
  rcases hp : compileIncProgs true asmConf (cakeConfigs asmConf c' src i) (src i) with ⟨a, b⟩
  simp only [cakeOrac, hp]

/-- Exact HOL `cake_configs_eq` (`backendProofScript.sml:341-351`). The captured
statement ends with `∀(i :γ). f (cake_configs asm_conf c' src x) = f c`: the
quantifier ranges over an independent type variable and is unused, HOL types
are nonempty, so it is vacuous and omitted here (a quantifier over an empty
Lean type would trivialise the conjunct). `x` stays free as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_configs_eq"
  (words_as_type_indexed_bitvec)]
theorem cakeConfigs_eq {width : Nat} [NeZero width] {α : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec) (x : Nat) :
    ∀ f : Flapjack.Compiler.Backend.Backend.Config → α,
      compile asmConf c prog = some (b, bm, c') ∧ f c' = f c ∧
        (∀ (c : Flapjack.Compiler.Backend.Backend.Config) (p : (Nat × Nat) × List AstHOL.Dec),
          f (compileIncProgs true asmConf c p).1 = f c) →
      f c' = f c ∧ f (cakeConfigs asmConf c' src x) = f c := by
  intro f ⟨_, hc', hstep⟩
  refine ⟨hc', ?_⟩
  unfold cakeConfigs
  induction x with
  | zero => exact hc'
  | succ n ih => simp only [stateOracStates]; rw [hstep]; exact ih

/-- Exact HOL `keep_progs_T` (`backendProofScript.sml:487-491`, `[local]`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "keep_progs_T"]
theorem keepProgs_true {α : Type} : (keepProgs true : List α → List α) = id := rfl

/-- Exact HOL `cake_orac_0` (`backendProofScript.sml:591-596`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_0"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_zero {width : Nat} [NeZero width] {α β : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (f : Flapjack.Compiler.Backend.Backend.Config → α) (g : BackendProgs width → β) :
    cakeOrac asmConf c' src f g 0 = (f c', g (compileIncProgs true asmConf c' (src 0)).2) := by
  rfl

/-- Exact HOL `cake_orac_SUC` (`backendProofScript.sml:598-606`). HOL `I` is `id`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_SUC"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_succ {width : Nat} [NeZero width] {α β : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (f : Flapjack.Compiler.Backend.Backend.Config → α) (g : BackendProgs width → β) (i : Nat) :
    cakeOrac asmConf c' src f g (i + 1) =
      (let (c'', _ps) := cakeOrac asmConf c' src id id i
       let c''' := (compileIncProgs true asmConf c'' (src i)).1
       (f c''', g (compileIncProgs true asmConf c''' (src (i + 1))).2)) := by
  simp only [cakeOrac, cakeConfigs, stateOracStates, id]

/-- Exact HOL `compile_inc_progs_src_env_tup` (`backendProofScript.sml:608-615`,
`[local]`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_inc_progs_src_env_tup"
  (words_as_type_indexed_bitvec)]
theorem compileIncProgs_srcEnvTup {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (cfg : Flapjack.Compiler.Backend.Backend.Config)
    (p : (Nat × Nat) × List AstHOL.Dec) (cfg' : Flapjack.Compiler.Backend.Backend.Config)
    (progs : BackendProgs width) :
    compileIncProgs true asmConf cfg p = (cfg', progs) →
      progs.envId = p.1 ∧ progs.sourceProg = p.2 := by
  intro h
  rw [← (Prod.mk.inj h).2]
  exact ⟨rfl, rfl⟩

/-- Exact HOL `compile_inc_progs_src_env` (`backendProofScript.sml:3033-3038`,
`[local]`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_inc_progs_src_env"
  (words_as_type_indexed_bitvec)]
theorem compileIncProgs_srcEnv {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (envDecs : (Nat × Nat) × List AstHOL.Dec) :
    (compileIncProgs true asmConf c envDecs).2.envId = envDecs.1 ∧
      (compileIncProgs true asmConf c envDecs).2.sourceProg = envDecs.2 :=
  ⟨rfl, rfl⟩

/-- Exact HOL `cake_orac_SUC2` (`backendProofScript.sml:617-628`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_SUC2"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_succ2 {width : Nat} [NeZero width] {α β : Type}
    (asmConf : AsmConfigExact width) (c' : Flapjack.Compiler.Backend.Backend.Config)
    (src : Nat → (Nat × Nat) × List AstHOL.Dec)
    (f : Flapjack.Compiler.Backend.Backend.Config → α) (g : BackendProgs width → β) (i : Nat) :
    cakeOrac asmConf c' src f g (i + 1) =
      (let (c'', ps) := cakeOrac asmConf c' src id id i
       let c''' := (compileIncProgs true asmConf c'' (ps.envId, ps.sourceProg)).1
       (f c''', g (compileIncProgs true asmConf c''' (src (i + 1))).2)) := by
  rw [cakeOrac_succ]
  simp only [cakeOrac, id, (compileIncProgs_srcEnv asmConf _ (src i)).1,
    (compileIncProgs_srcEnv asmConf _ (src i)).2]

/-- Exact HOL `cake_orac_cfg_f_eq_I` (`backendProofScript.sml:3040-3044`).
HOL `(f ## I)` is `Prod.map f id`; `asm_conf`, `c` and `syntax` (`syntaxOrac`) are free in HOL
and explicit here. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "cake_orac_cfg_f_eq_I"
  (words_as_type_indexed_bitvec)]
theorem cakeOrac_cfgF_eq_I {width : Nat} [NeZero width] {α γ : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (syntaxOrac : Nat → (Nat × Nat) × List AstHOL.Dec) :
    ∀ (f : Flapjack.Compiler.Backend.Backend.Config → α) (g : BackendProgs width → γ),
      cakeOrac asmConf c syntaxOrac f g = Prod.map f id ∘ cakeOrac asmConf c syntaxOrac id g := by
  intro f g
  funext i
  rfl

end Flapjack.Compiler.Backend.BackendProof
