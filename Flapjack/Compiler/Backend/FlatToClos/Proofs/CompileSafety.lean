import Flapjack.Compiler.Backend.FlatToClos.Proofs.CompileGlobals
import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties
import Flapjack.Compiler.Backend.ClosInterp.Proofs.Globals

/-! Closure-safety preservation during flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.FlatProps (emptyGlobalBag unionGlobalBag)

private theorem shiftEmpty : shiftGlobalBag emptyGlobalBag = emptyGlobalBag := by
  funext key
  simp [shiftGlobalBag, emptyGlobalBag]

private theorem reverseSafe (xs : List ClosLang.Exp) (safe : ClosProps.esgcFreeList xs) :
    ClosProps.esgcFreeList xs.reverse := by
  rw [ClosProps.esgcFreeList_iff] at safe ⊢
  simpa using safe

/-- Match-free expressions preserve the absence of global writes in closures. -/
theorem compileExp_safe (m : List (Option MlString)) (exp : FlatLang.Exp) :
    FlatProps.noMat exp = true → FlatProps.esgcFree exp → ClosProps.esgcFree (compileExp m exp) := by
  induction m, exp using compileExp.induct
      (motive_2 := fun m fs => FlatProps.noMatFuns fs = true →
        FlatProps.funGlobals fs = emptyGlobalBag →
        ClosProps.funGlobals (compileFuns m fs) = emptyGlobalBag)
      (motive_3 := fun m xs => FlatProps.noMatList xs = true → FlatProps.esgcFreeList xs →
        ClosProps.esgcFreeList (compileExps m xs)) with
  | case1 m t e ih => simpa [compileExp, FlatProps.noMat, FlatProps.esgcFree, ClosProps.esgcFree] using ih
  | case2 m t l =>
    intro _ _
    simpa [compileExp] using (compileLit_globalSafe t l).2
  | case3 m t v => simp [compileExp, ClosProps.esgcFree]
  | case4 m t tag es ih =>
    intro noMat safe
    simp only [FlatProps.noMat] at noMat
    simp only [FlatProps.esgcFree] at safe
    simp only [compileExp, esgcFree_smartCons]
    exact reverseSafe _ (ih noMat safe)
  | case5 m t u x ih =>
    intro noMat safe
    simp [FlatProps.noMat, FlatProps.noMatList] at noMat
    simp [FlatProps.esgcFree, FlatProps.esgcFreeList] at safe
    simpa [compileExp] using ih noMat safe
  | case6 m t u x ih =>
    intro noMat safe
    simp [FlatProps.noMat, FlatProps.noMatList] at noMat
    simp [FlatProps.esgcFree, FlatProps.esgcFreeList] at safe
    simpa [compileExp] using ih noMat safe
  | case7 m t op es h1 h2 ih =>
    intro noMat safe
    simp only [FlatProps.noMat] at noMat
    simp only [FlatProps.esgcFree] at safe
    simpa only [compileExp] using compileOp_safe t op _ (reverseSafe _ (ih noMat safe))
  | case8 m t v e ih =>
    intro noMat safe
    simp only [FlatProps.noMat] at noMat
    simp only [FlatProps.esgcFree] at safe
    have h := compileExp_globals (some v :: m) e noMat
    rw [safe, shiftEmpty] at h
    simpa [compileExp, ClosProps.esgcFree] using h
  | case9 m t a b c iha ihb ihc =>
    intro noMat safe
    simp only [FlatProps.noMat, Bool.and_eq_true] at noMat
    simp only [FlatProps.esgcFree] at safe
    simp only [compileExp, ClosProps.esgcFree]
    exact ⟨iha noMat.1.1 safe.1, ihb noMat.1.2 safe.2.1, ihc noMat.2 safe.2.2⟩
  | case10 m t vo a b iha ihb =>
    intro noMat safe
    simp only [FlatProps.noMat, Bool.and_eq_true] at noMat
    simp only [FlatProps.esgcFree] at safe
    simp [compileExp, ClosProps.esgcFree, ClosProps.esgcFreeList, iha noMat.1 safe.1, ihb noMat.2 safe.2]
  | case11 m t e ps => simp [FlatProps.noMat]
  | case12 m t e v h ihe ihh =>
    intro noMat safe
    simp only [FlatProps.noMat, Bool.and_eq_true] at noMat
    simp only [FlatProps.esgcFree, FlatProps.esgcFreeRows] at safe
    simp [compileExp, ClosProps.esgcFree, ihe noMat.1 safe.1, ihh noMat.2 safe.2.1]
  | case13 m t e ps h ih =>
    intro noMat _
    cases ps with
    | nil => simp [FlatProps.noMat] at noMat
    | cons row rest =>
      obtain ⟨pat, body⟩ := row
      cases rest with
      | cons next rest => simp [FlatProps.noMat] at noMat
      | nil =>
        cases pat <;> simp [FlatProps.noMat] at noMat
        case pvar => exact False.elim (h _ body rfl)
  | case14 m t fs e newM ihf ihe =>
    intro noMat safe
    simp only [FlatProps.noMat, Bool.and_eq_true] at noMat
    simp only [FlatProps.esgcFree] at safe
    simp only [compileExp, ClosProps.esgcFree]
    exact ⟨ihf noMat.1 safe.2, ihe noMat.2 safe.1⟩
  | case15 m => simp [compileExps, ClosProps.esgcFreeList]
  | case16 m e es ihe ihes =>
    rename_i noMat safe
    simp only [FlatProps.noMatList, Bool.and_eq_true] at noMat
    simp only [FlatProps.esgcFreeList] at safe
    simp [compileExps, ClosProps.esgcFreeList, ihe noMat.1 safe.1, ihes noMat.2 safe.2]
  | case17 m => simp [compileFuns, ClosProps.funGlobals]
  | case18 m f v e fs ihe ihfs =>
    rename_i noMat safe
    simp only [FlatProps.noMatFuns, Bool.and_eq_true] at noMat
    simp only [FlatProps.funGlobals, FlatProps.unionGlobalBag_eq_empty] at safe
    have h := compileExp_globals (some v :: m) e noMat.1
    rw [safe.1, shiftEmpty] at h
    simp only [compileFuns, ClosProps.funGlobals, h, ihfs noMat.2 safe.2]
    exact (FlatProps.unionGlobalBag_eq_empty _ _).mpr ⟨rfl, rfl⟩

private theorem flatSafeList_iff (xs : List FlatLang.Exp) :
    FlatProps.esgcFreeList xs ↔ ∀ e ∈ xs, FlatProps.esgcFree e := by
  induction xs with
  | nil => simp [FlatProps.esgcFreeList]
  | cons x xs ih => simp [FlatProps.esgcFreeList, ih]

private theorem noMatList_iff (xs : List FlatLang.Exp) :
    FlatProps.noMatList xs = true ↔ ∀ e ∈ xs, FlatProps.noMat e = true := by
  induction xs with
  | nil => simp [FlatProps.noMatList]
  | cons x xs ih => simp [FlatProps.noMatList, ih]

private theorem compileExps_safe (m : List (Option MlString)) (xs : List FlatLang.Exp)
    (noMat : FlatProps.noMatList xs = true) (safe : FlatProps.esgcFreeList xs) :
    ClosProps.esgcFreeList (compileExps m xs) := by
  induction xs with
  | nil => simp [compileExps, ClosProps.esgcFreeList]
  | cons x xs ih =>
    simp only [FlatProps.noMatList, Bool.and_eq_true] at noMat
    simp only [FlatProps.esgcFreeList] at safe
    simp [compileExps, ClosProps.esgcFreeList, compileExp_safe m x noMat.1 safe.1,
      ih noMat.2 safe.2]

/-- Compiling match-free, closure-safe flat expressions preserves closure safety. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_esgc_free"]
theorem compile_esgcFree (m : List (Option MlString)) (xs : List FlatLang.Exp)
    (premises : (∀ e ∈ xs, FlatProps.esgcFree e) ∧ (∀ e ∈ xs, FlatProps.noMat e = true)) :
    ∀ e ∈ compile m xs, ClosProps.esgcFree e := by
  apply (ClosProps.esgcFreeList_iff _).mp
  exact compileExps_safe m xs ((noMatList_iff xs).mpr premises.2) ((flatSafeList_iff xs).mpr premises.1)

/-- Compiling match-free, closure-safe declarations preserves closure safety. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_decs_esgc_free"]
theorem compileDecs_esgcFree (ds : List FlatLang.Exp)
    (premises : (∀ e ∈ ds, FlatProps.esgcFree e) ∧ FlatProps.noMatDecs ds = true) :
    ∀ e ∈ compileDecs ds, ClosProps.esgcFree e := by
  apply compile_esgcFree [] ds
  exact ⟨premises.1, (noMatList_iff ds).mp (by simpa [FlatProps.noMatDecs_eq_noMatList] using premises.2)⟩

private theorem interpreterNoWrites :
    ClosProps.setGlobals ClosInterp.closInterpreter = emptyGlobalBag := by
  funext key
  simp [ClosInterp.closInterpreter, ClosInterp.closInterpreterBody,
    ClosInterp.closInterpEl, ClosInterp.closInterpRev,
    ClosInterp.interpreterVar_eq, ClosInterp.interpreterGetEl_eq,
    ClosInterp.interpreterCons_eq, ClosInterp.interpreterApp_eq,
    ClosInterp.interpreterCall_eq, ClosInterp.interpreterCallList_eq,
    ClosInterp.interpreterIsCase_eq, ClosProps.setGlobals, ClosProps.elistGlobals,
    ClosProps.funGlobals, ClosProps.opGlobalBag, unionGlobalBag, emptyGlobalBag]

private theorem compileInit_safe (b : Bool) : ClosProps.esgcFree (ClosInterp.compileInit b) := by
  cases b <;> simp [ClosInterp.compileInit, ClosInterp.interpreterCons_eq,
    ClosInterp.interpreterVar_eq, ClosProps.esgcFree, ClosProps.esgcFreeList,
    interpreterNoWrites]

/-- Interpreter attachment preserves the closure-safety invariant. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "compile_prog_esgc_free"]
theorem compileProg_esgcFree (ds : List FlatLang.Exp)
    (premises : (∀ e ∈ ds, FlatProps.esgcFree e) ∧ FlatProps.noMatDecs ds = true) :
    ∀ e ∈ compileProg ds, ClosProps.esgcFree e := by
  have safe := compileDecs_esgcFree ds premises
  simpa [compileProg, ClosInterp.attachInterpreter, compileInit_safe] using safe

/-- Incremental compilation retains closure safety after interpreter insertion. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "FST_inc_compile_esgc_free"]
theorem incCompileDecs_esgcFree {α : Type} (ds : List FlatLang.Exp)
    (premises : (∀ e ∈ ds, FlatProps.esgcFree e) ∧ FlatProps.noMatDecs ds = true) :
    ∀ e ∈ (incCompileDecs (α := α) ds).1, ClosProps.esgcFree e := by
  apply (ClosInterp.insertInterp_esgcFree _).mpr
  have safe := compileDecs_esgcFree ds premises
  intro e member
  rcases List.mem_append.mp member with member | member
  · exact safe e member
  · simp [compileDecs, compile, compileExps, compileExp] at member
    subst e
    simp [esgcFree_smartCons, ClosProps.esgcFreeList]

private theorem elistGlobals_append (xs ys : List ClosLang.Exp) :
    ClosProps.elistGlobals (xs ++ ys) =
      unionGlobalBag (ClosProps.elistGlobals xs) (ClosProps.elistGlobals ys) := by
  induction xs with
  | nil => funext key; simp [ClosProps.elistGlobals, unionGlobalBag, emptyGlobalBag]
  | cons x xs ih =>
    simp only [List.cons_append, ClosProps.elistGlobals, ih]
    funext key
    simp only [unionGlobalBag]
    omega

/-- Incremental compilation shifts the source global-write bag by one. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "FST_inc_compile_set_globals"]
theorem incCompileDecs_setGlobals {α : Type} (ds : List FlatLang.Exp)
    (noMat : FlatProps.noMatDecs ds = true) :
    ClosProps.elistGlobals (incCompileDecs (α := α) ds).1 =
      shiftGlobalBag (FlatProps.elistGlobals ds) := by
  have unitGlobals : ClosProps.elistGlobals (compileDecs [.con .none none []]) = emptyGlobalBag := by
    have h := compileDecs_setGlobals [.con .none none []]
      (by simp [FlatProps.noMatDecs, FlatProps.noMat, FlatProps.noMatList])
    have empty : unionGlobalBag emptyGlobalBag emptyGlobalBag = emptyGlobalBag :=
      (FlatProps.unionGlobalBag_eq_empty _ _).mpr ⟨rfl, rfl⟩
    simpa [FlatProps.elistGlobals, FlatProps.setGlobals, empty, shiftEmpty] using h
  simp only [incCompileDecs, ClosInterp.elistGlobals_insertInterp, elistGlobals_append,
    compileDecs_setGlobals ds noMat, unitGlobals]
  funext key
  simp [unionGlobalBag, emptyGlobalBag]

end Flapjack.Compiler.Backend.FlatToClos
