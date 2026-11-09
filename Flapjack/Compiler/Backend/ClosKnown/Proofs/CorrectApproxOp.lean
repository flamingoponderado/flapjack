module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.CorrectApproxCons
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownOpCorrect

@[expose] public section


/-! Ordinary primitive-operation cases of approximation correctness. -/
namespace Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Op
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort OracleGlobals
open Flapjack.SemanticPrimitivesHOL

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The ordinary-operation proof, with explicit dispatch exclusions. This is
Flapjack infrastructure; source-shaped constructor cases use it below. -/
theorem ordinaryOpApprox {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace op xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace op xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace op xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace op xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace op xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs := by
  rcases h with ⟨known, run, unique, related, approx, disjoint, oracle, safe, envSafe, exprSafe, approxSafe, globalsSafe⟩
  have argsUnique : uniqueSetGlobals xs s0.compileOracle := by
    intro n i
    have bound := unique n i
    simp only [elistGlobals_append, elistGlobals, setGlobals, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, Nat.add_zero, Flapjack.bagUnion, Flapjack.emptyBag] at bound ⊢
    omega
  have ⟨argsDisjoint, opDisjoint⟩ :=
    (mglobalsDisjointRw s0.globals (.var .none 0) (.var .none 0) (.var .none 0) (.var .none 0)
      (.var .none 0) xs trace op [] none none [] 0 0).2.2.2.2.2.2.2.1.mp disjoint
  have argsSafe : ∀ e ∈ xs, esgcFree e := by
    have h := exprSafe (.op trace op xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using h
  cases hk : knownListTotal c xs aenv g0 with
  | mk ea g1 =>
    cases ho : knownOpHOL op (ea.map Prod.snd).reverse g1 with
    | mk a g2 =>
      let out := match op, a with
        | .globOp (.global _), .int i => ClosLang.Exp.op trace (.intOp (.const i)) (ea.map Prod.fst)
        | .globOp (.global _), .tuple tag [] => ClosLang.Exp.op trace (.blockOp (.cons tag)) (ea.map Prod.fst)
        | _, _ => ClosOp.smartOp trace op (ea.map Prod.fst)
      rw [knownListTotal_op, hk] at known
      dsimp only at known
      rw [ho] at known
      change ([(out, a)], g2) = (eas, g) at known
      rcases known with ⟨⟩
      rw [evaluate_ordinaryOp_eq trace op xs (env ++ extra) s0 notInstall notForce] at run
      cases hr : evaluate xs (env ++ extra) s0 with
      | mk argResult middle =>
        have argApprox := argsIH ea g1 env extra s0 argResult middle
          ⟨hk, hr, argsUnique, related, approx, argsDisjoint, oracle, safe, envSafe, argsSafe, approxSafe, globalsSafe⟩
        have middleApprox := OpEvaluateGlobals.stateGlobalsApproxKnownOpEvaluate xs (env ++ extra) s0
          argResult middle op (ea.map Prod.snd).reverse g1 a g trace
          ⟨hr, ho, safe, envSafe, argsSafe, opDisjoint, unique, argApprox.1⟩
        rw [hr] at run
        cases argResult with
        | err error =>
          cases run
          exact ⟨middleApprox, by intro vs impossible; cases impossible⟩
        | val values =>
          dsimp only at run
          cases ha : doApp op values.reverse middle with
          | err error =>
            rw [ha] at run
            cases run
            exact ⟨middleApprox, by intro vs impossible; cases impossible⟩
          | val pair =>
            obtain ⟨value, next⟩ := pair
            rw [ha] at run
            cases run
            have opResult := KnownOpCorrect.knownOpCorrectApprox op (ea.map Prod.snd).reverse g1 a g
              values.reverse middle value s ho ha (List.rel_reverse (argApprox.2 values rfl)) argApprox.1
            exact ⟨opResult.1, by
              intro vs eq
              cases eq
              exact .cons opResult.2 .nil⟩

/-- Label operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpLabel {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : Nat) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.label opArg) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.label opArg) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.label opArg) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.label opArg) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.label opArg) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.label opArg) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

/-- Ffi operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpFfi {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : Basis.Pure.MlString.MlString) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.ffi opArg) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.ffi opArg) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.ffi opArg) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.ffi opArg) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.ffi opArg) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.ffi opArg) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

/-- Int operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpInt {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : ClosLang.IntOp) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.intOp opArg) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.intOp opArg) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.intOp opArg) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.intOp opArg) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.intOp opArg) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.intOp opArg) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

/-- Word operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpWord {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : ClosLang.WordOp) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.wordOp opArg) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.wordOp opArg) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.wordOp opArg) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.wordOp opArg) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.wordOp opArg) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.wordOp opArg) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

/-- Block operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpBlock {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : ClosLang.BlockOp) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.blockOp opArg) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.blockOp opArg) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.blockOp opArg) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.blockOp opArg) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.blockOp opArg) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.blockOp opArg) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

/-- Global operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpGlobal {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : ClosLang.GlobOp) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.globOp opArg) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.globOp opArg) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.globOp opArg) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.globOp opArg) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.globOp opArg) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.globOp opArg) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

/-- Memory operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpMemory {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : ClosLang.MemOp) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.memOp opArg) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.memOp opArg) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.memOp opArg) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.memOp opArg) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.memOp opArg) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.memOp opArg) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

/-- AllocThunk operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpAllocThunk {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : AstHOL.ThunkMode) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.thunkOp (.allocThunk opArg)) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.thunkOp (.allocThunk opArg)) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.thunkOp (.allocThunk opArg)) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.thunkOp (.allocThunk opArg)) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.thunkOp (.allocThunk opArg)) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.thunkOp (.allocThunk opArg)) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

/-- UpdateThunk operation case of the original approximation theorem. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_correct_approx"
  (fmap_as_finite_support := [refs, code])]
theorem knownCorrectApproxOpUpdateThunk {C F : Type} (c : Config) (trace : BackendCommon.Tra)
    (opArg : AstHOL.ThunkMode) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownApproxInvariant C F c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox) (env extra : List ClosSem.Value)
    (s0 : State (Spt ValApprox × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (s : State (Spt ValApprox × C) F)
    (h : knownListTotal c [.op trace (.thunkOp (.updateThunk opArg)) xs] aenv g0 = (eas, g) ∧
      evaluate [.op trace (.thunkOp (.updateThunk opArg)) xs] (env ++ extra) s0 = (res, s) ∧
      uniqueSetGlobals [.op trace (.thunkOp (.updateThunk opArg)) xs] s0.compileOracle ∧ List.Forall₂ ValApproxVal aenv env ∧
      stateGlobalsApprox s0 g0 ∧ mglobalsDisjoint s0.globals [.op trace (.thunkOp (.updateThunk opArg)) xs] ∧
      oracleGapproxDisjoint g0 s0.compileOracle ∧ ssgcFree s0 ∧
      (∀ v ∈ env ++ extra, vsgcFree v) ∧ (∀ e ∈ [ClosLang.Exp.op trace (.thunkOp (.updateThunk opArg)) xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    stateGlobalsApprox s g ∧ ∀ vs, res = .val vs → List.Forall₂ ValApproxVal (eas.map Prod.snd) vs :=
  ordinaryOpApprox c trace (.thunkOp (.updateThunk opArg)) xs aenv g0 (by simp) (by simp) argsIH eas g env extra s0 res s h

end Flapjack.Compiler.Backend.ClosKnown.CorrectApprox.Op
