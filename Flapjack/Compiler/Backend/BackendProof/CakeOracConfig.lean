module

public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Backend.ClosKnown.Compile
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CompileSemantics
public import Flapjack.Compiler.Backend.SourceToFlat.Eliminate
public import Flapjack.Misc.Option

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 353-484: configuration facts used to show that the
incremental compiler oracle `cake_orac` preserves the static parts of the
backend configuration: the closure optimizer keeps its static settings and
ignores its approximation tree, the source compiler keeps its pattern
settings, and `attach_bitmaps` exposes its successful result. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.ClosKnown
open Flapjack.Compiler.Backend.BackendProps

/-- Flapjack inhabitant used only for the reviewed `holThe` rendering of
HOL `THE` at the concrete closure-optimizer configuration type. -/
instance instNonemptyClosKnownConfig : Nonempty ClosKnown.Config := ⟨ClosKnown.defaultConfig 0⟩

/-- Exact HOL `PAIR_MAP_EQ_EQ` (`backendProofScript.sml:353-357`); HOL `f ## g`
is `Prod.map f g`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "PAIR_MAP_EQ_EQ"]
theorem pairMap_eq_eq {α β γ δ : Type} (f : γ → α) (g : δ → β) (x : γ × δ) (y : α × β) :
    Prod.map f g x = y ↔ ∃ x0 x1, x = (x0, x1) ∧ (f x0, g x1) = y := by
  obtain ⟨a, b⟩ := x
  simp [Prod.map]

/-- Exact HOL `known_compile_IS_SOME` (`backendProofScript.sml:359-366`) for
the original `clos_known$compile`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "known_compile_IS_SOME"]
theorem knownCompile_isSome (kc : Option ClosKnown.Config) (es : List ClosLang.Exp)
    (kc' : Option ClosKnown.Config) (es' : List ClosLang.Exp) :
    compileSource kc es = (kc', es') → (kc'.isSome = true ↔ kc.isSome = true) := by
  cases kc with
  | none =>
      intro h
      simp only [compileSource, Prod.mk.injEq] at h
      rw [← h.1]
  | some c =>
      intro h
      simp only [compileSource] at h
      rw [← (Prod.mk.inj h).1]
      simp

/-- Exact HOL `attach_bitmaps_SOME` (`backendProofScript.sml:368-374`). HOL's
`«NOTFOUND»` is `ofString "NOTFOUND"`, as in the reviewed `attachBitmaps`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "attach_bitmaps_SOME"]
theorem attachBitmaps_some {α β : Type} (names : Spt MlString) (c : Backend.Config) (bm : β)
    (v : Option (α × LabToTarget.Config)) (r : α × β × Backend.Config) :
    Backend.attachBitmaps names c bm v = some r →
      ∃ (bytes : α) (c' : LabToTarget.Config), v = some (bytes, c') ∧
        r = (bytes, bm, { c with
          labConf := c'
          symbols := c'.secPosLen.map fun (n, p, l) =>
            (lookupAny n names (ofString "NOTFOUND"), p, l) }) := by
  cases v with
  | none => simp [Backend.attachBitmaps]
  | some v =>
      obtain ⟨bytes, c'⟩ := v
      intro h
      simp only [Backend.attachBitmaps, Option.some.injEq] at h
      exact ⟨bytes, c', rfl, h.symm⟩

/-- Exact HOL `known_compile_static_conf` (`backendProofScript.sml:376-383`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "known_compile_static_conf"]
theorem knownCompile_staticConf (kc : Option ClosKnown.Config) (es : List ClosLang.Exp)
    (kc' : Option ClosKnown.Config) (es' : List ClosLang.Exp) :
    compileSource kc es = (kc', es') → knownStaticConf kc' = knownStaticConf kc := by
  cases kc with
  | none =>
      intro h
      simp only [compileSource, Prod.mk.injEq] at h
      rw [← h.1]
  | some c =>
      intro h
      simp only [compileSource] at h
      rw [← (Prod.mk.inj h).1]
      simp [knownStaticConf, resetInlineFactor]

/-- Exact HOL `known_option_upd_val_spt_eq` (`backendProofScript.sml:385-392`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "known_option_upd_val_spt_eq"]
theorem known_optionUpdValSpt_eq (spt : Spt ValApprox) (kc : Option ClosKnown.Config) :
    ((optionUpdValSpt spt kc).isSome = true ↔ kc.isSome = true) ∧
    knownStaticConf (optionUpdValSpt spt kc) = knownStaticConf kc := by
  cases kc <;> simp [optionUpdValSpt, knownStaticConf, resetInlineFactor]

/-- Exact HOL `source_compile_pattern_cfg` (`backendProofScript.sml:394-402`):
both the whole-program and the incremental source-to-flat compiler keep the
pattern-compiler configuration. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "source_compile_pattern_cfg"]
theorem sourceCompile_patternCfg (c : SourceToFlat.Config) (p : List AstHOL.Dec)
    (c' : SourceToFlat.Config) (p' : List FlatLang.Exp) (envId : Nat × Nat) :
    (SourceToFlat.compileTotal c p = (c', p') → c'.patternCfg = c.patternCfg) ∧
    (SourceToFlat.incCompile envId c p = (c', p') → c'.patternCfg = c.patternCfg) := by
  constructor
  · intro h
    simp only [SourceToFlat.compileTotal, SourceToFlat.compileProg] at h
    rw [← (Prod.mk.inj h).1]
  · intro h
    simp only [SourceToFlat.incCompile, SourceToFlat.incCompileProg] at h
    rw [← (Prod.mk.inj h).1]

/-- Exact HOL `decide_inline_reset_spt` (`backendProofScript.sml:444-448`): the
inlining decision, as a function of its remaining arguments, ignores the
approximation tree. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "decide_inline_reset_spt"]
theorem decideInline_resetSpt {α : Type} (kc : ClosKnown.Config)
    (f : Spt ValApprox → Spt ValApprox) :
    decideInlineHOL (L := α) { kc with valApproxSpt := f kc.valApproxSpt } =
      decideInlineHOL (L := α) kc := rfl

/-- Flapjack simp infrastructure: the applied inlining decision ignores the
approximation tree. -/
private theorem decideInlineHOL_withSpt {α : Type} (c : ClosKnown.Config) (s : Spt ValApprox)
    (a : ValApprox) (loc : Option α) (n : Nat) :
    decideInlineHOL { c with valApproxSpt := s } a loc n = decideInlineHOL c a loc n := rfl

/-- Flapjack induction infrastructure for `known_reset_spt`: the whole
traversal family ignores the configuration's approximation tree. -/
private theorem knownListTotal_resetSpt (c : ClosKnown.Config) (xs : List ClosLang.Exp)
    (env : List ValApprox) (g : Spt ValApprox) :
    ∀ s, knownListTotal { c with valApproxSpt := s } xs env g = knownListTotal c xs env g := by
  induction c, xs, env, g using knownListTotal.induct
    (motive1 := fun c e env g =>
      ∀ s, knownExprTotal { c with valApproxSpt := s } e env g = knownExprTotal c e env g)
    (motive2 := fun c fns clos env g =>
      ∀ s, knownFunsTotal { c with valApproxSpt := s } fns clos env g =
        knownFunsTotal c fns clos env g) <;>
    (try intro s) <;>
    first
      | rw [knownListTotal.eq_def, knownListTotal.eq_def]
      | rw [knownExprTotal.eq_def, knownExprTotal.eq_def]
      | rw [knownFunsTotal.eq_def, knownFunsTotal.eq_def]
  all_goals first
    | (simp_all [decInlineFactor]; done)
    | (dsimp only
       repeat' split
       all_goals simp_all +zetaDelta [decInlineFactor, decideInlineHOL_withSpt])

/-- Exact HOL `known_reset_spt` (`backendProofScript.sml:450-463`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "known_reset_spt"]
theorem known_resetSpt (f : Spt ValApprox → Spt ValApprox) :
    ∀ kc : ClosKnown.Config,
      knownListTotal { kc with valApproxSpt := f kc.valApproxSpt } = knownListTotal kc := by
  intro kc
  funext xs env g
  exact knownListTotal_resetSpt kc xs env g (f kc.valApproxSpt)

/-- Exact HOL `known_reset_to_static_conf` (`backendProofScript.sml:465-469`).
HOL `THE` is the reviewed `holThe` rendering at the concrete closure-optimizer
configuration type. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "known_reset_to_static_conf"]
theorem known_resetToStaticConf (kc : ClosKnown.Config) :
    knownListTotal (resetInlineFactor kc) =
      knownListTotal (holThe (knownStaticConf (some kc))) := by
  simp only [knownStaticConf, holThe]
  exact (known_resetSpt (fun _ => .ln) (resetInlineFactor kc)).symm

/-- Exact HOL `known_co_eq_state_co_inc` (`backendProofScript.sml:471-484`): the
known-pass oracle adapter is the stateful oracle of the incremental known
compiler at the static configuration. The oracle type is the captured
`num -> (val_approx num_map # α) # exp list # (num # num # exp) list`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "known_co_eq_state_co_inc"]
theorem knownCo_eq_stateCo_inc {α : Type} (kc : Option ClosKnown.Config)
    (co : Nat → (Spt ValApprox × α) × ClosSem.Program) :
    knownCo kc co = stateCo (knownCompileIncSource (knownStaticConf kc)) co := by
  funext n
  cases kc with
  | none => rfl
  | some c =>
      have hk :
          knownListTotal (resetInlineFactor { resetInlineFactor c with valApproxSpt := .ln }) =
          knownListTotal (resetInlineFactor c) :=
        known_resetSpt (fun _ => .ln) (resetInlineFactor c)
      simp only [knownCo, knownStaticConf, stateCo, knownCompileIncSource, compileInc, pureCo,
        Function.comp_apply, hk]

/-- Exact HOL `known_cc_eq_state_cc_inc` (`backendProofScript.sml:2965-2977`):
the known-pass compiler adapter is the stateful compiler of the incremental
known compiler at the static configuration. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "known_cc_eq_state_cc_inc"]
theorem knownCc_eq_stateCc_inc {α : Type} (kc : Option ClosKnown.Config)
    (cc : ClosSem.Compiler α) :
    knownCc kc cc = stateCc (knownCompileIncSource (knownStaticConf kc)) cc := by
  funext cfg p
  cases kc with
  | none => rfl
  | some c =>
      have hk :
          knownListTotal (resetInlineFactor { resetInlineFactor c with valApproxSpt := .ln }) =
          knownListTotal (resetInlineFactor c) :=
        known_resetSpt (fun _ => .ln) (resetInlineFactor c)
      simp only [knownCc, knownStaticConf, stateCc, knownCompileIncSource, compileInc, pureCc, hk]

/-- Exact HOL `known_compile_inc_retreive_spt` (`backendProofScript.sml:2979-2990`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "known_compile_inc_retreive_spt"]
theorem knownCompileInc_retreiveSpt {α : Type} (kcfg1 kcfg2 : Option ClosKnown.Config)
    (p p' : List ClosLang.Exp × List α) (spt : Spt ValApprox) :
    knownCompileIncSource (knownStaticConf kcfg1) (optionValApproxSpt kcfg2) p = (spt, p') ∧
      (kcfg2.isSome = kcfg1.isSome) →
    optionValApproxSpt (optionUpdValSpt spt kcfg2) = spt := by
  rintro ⟨h, hs⟩
  cases kcfg2 with
  | some c => rfl
  | none =>
      cases kcfg1 with
      | none =>
          simp only [knownStaticConf, knownCompileIncSource, Prod.mk.injEq] at h
          exact h.1
      | some _ => simp at hs

end Flapjack.Compiler.Backend.BackendProof
