import Flapjack.Compiler.Backend.FlatToClos.Compile
import Flapjack.Compiler.Backend.FlatToClos.Proofs.GlobalInvariants
import Flapjack.Compiler.Backend.FlatToClos.Proofs.OperatorGlobals
import Flapjack.Compiler.Backend.FlatProps.NoMat

/-! Global-write preservation across flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.FlatProps (GlobalBag emptyGlobalBag unionGlobalBag)

/-- Source globals are shifted by one in the closure language. -/
def shiftGlobalBag (bag : GlobalBag) : GlobalBag :=
  fun key => if key = 0 then 0 else bag (key - 1)

/-- The global-key shift preserves the empty bag. This is Flapjack
infrastructure for the original global-preservation proofs. -/
theorem shiftEmpty : shiftGlobalBag emptyGlobalBag = emptyGlobalBag := by
  funext key
  simp [shiftGlobalBag, emptyGlobalBag]

private theorem shiftUnion (a b : GlobalBag) :
    shiftGlobalBag (unionGlobalBag a b) = unionGlobalBag (shiftGlobalBag a) (shiftGlobalBag b) := by
  funext key
  by_cases h : key = 0 <;> simp [shiftGlobalBag, unionGlobalBag, h]

private theorem shiftOp (op : FlatLang.Op) :
    shiftGlobalBag (FlatProps.opGlobalBag op) = loweredOpBag op := by
  funext key
  simp [shiftGlobalBag, loweredOpBag_shift]

private theorem closGlobals_append (xs ys : List ClosLang.Exp) :
    ClosProps.elistGlobals (xs ++ ys) = unionGlobalBag (ClosProps.elistGlobals xs) (ClosProps.elistGlobals ys) := by
  induction xs with
  | nil => funext key; simp [ClosProps.elistGlobals, unionGlobalBag, emptyGlobalBag]
  | cons x xs ih =>
    simp only [List.cons_append, ClosProps.elistGlobals, ih]
    funext key
    simp only [unionGlobalBag]
    omega

private theorem closGlobals_reverse (xs : List ClosLang.Exp) :
    ClosProps.elistGlobals xs.reverse = ClosProps.elistGlobals xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, closGlobals_append, ih, ClosProps.elistGlobals]
    funext key
    simp [unionGlobalBag, emptyGlobalBag, Nat.add_comm]

/-- Every match-free expression preserves its shifted global-write bag. -/
theorem compileExp_globals (m : List (Option MlString)) (exp : FlatLang.Exp) :
    FlatProps.noMat exp = true → ClosProps.setGlobals (compileExp m exp) = shiftGlobalBag (FlatProps.setGlobals exp) := by
  induction m, exp using compileExp.induct
      (motive2 := fun m fs => FlatProps.noMatFuns fs = true →
        ClosProps.funGlobals (compileFuns m fs) = shiftGlobalBag (FlatProps.funGlobals fs))
      (motive3 := fun m xs => FlatProps.noMatList xs = true →
        ClosProps.elistGlobals (compileExps m xs) = shiftGlobalBag (FlatProps.elistGlobals xs)) with
  | case1 m t e ih => simpa [compileExp, FlatProps.noMat, FlatProps.setGlobals, ClosProps.setGlobals] using ih
  | case2 m t l =>
    intro _
    simpa [compileExp, FlatProps.setGlobals, shiftEmpty] using (compileLit_globalSafe t l).1
  | case3 m t v => simp [compileExp, FlatProps.setGlobals, ClosProps.setGlobals, shiftEmpty]
  | case4 m t tag es ih =>
    intro safe
    simp only [FlatProps.noMat] at safe
    rw [compileExp.eq_def]
    dsimp only
    split <;> simpa [setGlobals_smartCons, closGlobals_reverse, FlatProps.setGlobals] using ih safe
  | case5 m t op es x found ih =>
    intro safe
    obtain ⟨u, rfl, rfl⟩ | ⟨u, rfl, rfl⟩ := destNop_shape op es x found
    all_goals simp [FlatProps.noMat, FlatProps.noMatList] at safe
    all_goals rw [compileExp.eq_def]; dsimp only; rw [found]
    all_goals simpa [FlatProps.setGlobals, FlatProps.elistGlobals, FlatProps.opGlobalBag,
      FlatProps.unionGlobalBag_empty_right] using ih safe
  | case6 m t op es found ih =>
    intro safe
    have hs := ih (by simpa [FlatProps.noMat] using safe)
    simp only [FlatProps.setGlobals, shiftUnion, shiftOp]
    have hop := compileOp_globals t op (compileExps m es).reverse
    simp only [closGlobals_reverse, hs] at hop
    rw [compileExp.eq_def]
    dsimp only
    rw [found]
    rw [hop]
    funext key
    simp [unionGlobalBag, Nat.add_comm]
  | case7 m t v e ih =>
    intro safe
    simp only [FlatProps.noMat] at safe
    simpa [compileExp, FlatProps.noMat, FlatProps.setGlobals, ClosProps.setGlobals] using ih safe
  | case8 m t a b c iha ihb ihc =>
    intro safe
    simp only [FlatProps.noMat, Bool.and_eq_true] at safe
    simp only [compileExp, FlatProps.setGlobals, ClosProps.setGlobals, shiftUnion]
    rw [iha safe.1.1, ihb safe.1.2, ihc safe.2]
  | case9 m t vo a b iha ihb =>
    intro safe
    simp only [FlatProps.noMat, Bool.and_eq_true] at safe
    simp only [compileExp, FlatProps.setGlobals, ClosProps.setGlobals, ClosProps.elistGlobals, shiftUnion]
    rw [iha safe.1, ihb safe.2]
    funext key
    simp [unionGlobalBag, emptyGlobalBag, Nat.add_comm]
  | case10 m t e ps => simp [FlatProps.noMat]
  | case11 m t e ps v h found ihe ihh =>
    have rowsEq := destPat_eq_some ps v h found
    subst ps
    intro safe
    simp only [FlatProps.noMat, Bool.and_eq_true] at safe
    rw [compileExp.eq_def]
    dsimp only
    rw [found]
    simp only [FlatProps.setGlobals, FlatProps.rowGlobals, ClosProps.setGlobals, shiftUnion]
    rw [ihe safe.1, ihh safe.2]
    funext key
    simp [unionGlobalBag, emptyGlobalBag, shiftEmpty]
  | case12 m t e ps found ih =>
    intro safe
    cases ps with
    | nil => simp [FlatProps.noMat] at safe
    | cons row rest =>
      obtain ⟨pat, body⟩ := row
      cases rest with
      | cons next rest => simp [FlatProps.noMat] at safe
      | nil =>
        cases pat <;> simp [FlatProps.noMat] at safe
        case pvar v => simp [destPat] at found
  | case13 m t fs e newM ihf ihe =>
    intro safe
    simp only [FlatProps.noMat, Bool.and_eq_true] at safe
    simp only [compileExp, FlatProps.setGlobals, ClosProps.setGlobals, shiftUnion]
    have namesEq : fs.attach.map (fun x => some x.val.1) = fs.map (fun x => some x.1) :=
      List.attach_map_val (f := fun x : MlString × MlString × FlatLang.Exp => some x.1)
    simp only [newM, namesEq] at ihf ihe
    rw [ihf safe.1, ihe safe.2]
  | case14 m => simp [compileFuns, FlatProps.funGlobals, ClosProps.funGlobals, shiftEmpty]
  | case15 m f v e fs ihe ihfs =>
    rename_i safe
    simp only [FlatProps.noMatFuns, Bool.and_eq_true] at safe
    simp only [compileFuns, FlatProps.funGlobals, ClosProps.funGlobals, shiftUnion]
    rw [ihe safe.1, ihfs safe.2]
  | case16 m => simp [compileExps, FlatProps.elistGlobals, ClosProps.elistGlobals, shiftEmpty]
  | case17 m e es ihe ihes =>
    rename_i safe
    simp only [FlatProps.noMatList, Bool.and_eq_true] at safe
    simp only [compileExps, FlatProps.elistGlobals, ClosProps.elistGlobals, shiftUnion]
    rw [ihe safe.1, ihes safe.2]

private theorem compileExps_globals (m : List (Option MlString)) (xs : List FlatLang.Exp)
    (safe : FlatProps.noMatList xs = true) :
    ClosProps.elistGlobals (compileExps m xs) = shiftGlobalBag (FlatProps.elistGlobals xs) := by
  induction xs with
  | nil => simp [compileExps, FlatProps.elistGlobals, ClosProps.elistGlobals, shiftEmpty]
  | cons x xs ih =>
    simp only [FlatProps.noMatList, Bool.and_eq_true] at safe
    simp only [compileExps, FlatProps.elistGlobals, ClosProps.elistGlobals, shiftUnion]
    rw [compileExp_globals m x safe.1, ih safe.2]

/-- Compiling match-free flat expressions shifts every global write by one. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_set_globals"]
theorem compile_setGlobals (m : List (Option MlString)) (xs : List FlatLang.Exp)
    (safe : ∀ e ∈ xs, FlatProps.noMat e = true) :
    ClosProps.elistGlobals (compile m xs) = shiftGlobalBag (FlatProps.elistGlobals xs) := by
  exact compileExps_globals m xs (by simpa [FlatProps.noMatList_eq_all] using safe)

/-- Tuple-free source statement for an explicitly named compilation result. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_eq_set_globals"]
theorem compileEq_setGlobals (m : List (Option MlString)) (xs : List FlatLang.Exp)
    (ys : List ClosLang.Exp)
    (premises : compile m xs = ys ∧ ∀ e ∈ xs, FlatProps.noMat e = true) :
    ClosProps.elistGlobals ys = shiftGlobalBag (FlatProps.elistGlobals xs) := by
  rw [← premises.1]
  exact compile_setGlobals m xs premises.2

/-- Compiling match-free declarations shifts every global write by one. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_decs_set_globals"]
theorem compileDecs_setGlobals (ds : List FlatLang.Exp) (safe : FlatProps.noMatDecs ds = true) :
    ClosProps.elistGlobals (compileDecs ds) = shiftGlobalBag (FlatProps.elistGlobals ds) := by
  have h : FlatProps.noMatList ds = true := by simpa [FlatProps.noMatDecs_eq_noMatList] using safe
  exact compileExps_globals [] ds h

end Flapjack.Compiler.Backend.FlatToClos
