import Flapjack.Compiler.Backend.FlatToClos.Compile
import Flapjack.Compiler.Backend.Semantics.ClosProps.NoMti
import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoMti
import Mathlib.Tactic.Tauto

/-! Pre-multi-argument syntax preserved by flat-to-closure compilation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.BackendCommon Flapjack.Compiler.Backend.ClosProps

private theorem destConstant_noMti (e : ClosLang.Exp) (c : ClosLang.Const)
    (decoded : destConstant e = some c) : noMti e := by
  cases e <;> simp [destConstant] at decoded
  case op t op args =>
    cases args with
    | cons a rest => cases op <;> simp at decoded
    | nil =>
      cases op <;> try simp at decoded
      case intOp op => cases op <;> try simp at decoded <;> simp [noMti, noMtiList]
      case blockOp op => cases op <;> try simp at decoded <;> simp [noMti, noMtiList]

private theorem destConstants_noMti (xs : List ClosLang.Exp) (cs : List ClosLang.Const)
    (decoded : destConstants xs = some cs) : noMtiList xs := by
  induction xs generalizing cs with
  | nil => simp [noMtiList]
  | cons x xs ih =>
    cases first : destConstant x with
    | none => simp [destConstants, first] at decoded
    | some c =>
      cases rest : destConstants xs with
      | none => simp [destConstants, first, rest] at decoded
      | some cs' =>
        simpa [noMtiList] using And.intro (destConstant_noMti x c first) (ih cs' rest)

/-- Constructor folding preserves the pre-multi-argument syntax invariant. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "no_mti_SmartCons"]
theorem noMti_smartCons (t : Tra) (tag : Nat) (xs : List ClosLang.Exp) :
    noMti (smartCons t tag xs) ↔ ∀ e ∈ xs, noMti e := by
  rw [← noMtiList_iff]
  cases xs with
  | nil => simp [smartCons, noMti, noMtiList]
  | cons x xs =>
    cases decoded : destConstants (x :: xs) with
    | none => simp [smartCons, decoded, noMti]
    | some cs =>
      have h := destConstants_noMti (x :: xs) cs decoded
      simp [smartCons, decoded, noMti, noMtiList, h]

private theorem compileArith_noMti (t : Tra) (a : Flapjack.AstHOL.Arith)
    (ty : Flapjack.AstHOL.PrimType) (xs : List ClosLang.Exp)
    (safe : noMtiList xs) : noMti (compileArith t a ty xs) := by
  cases ty <;> cases a <;> simp [compileArith, noMti, noMtiList, safe]

/-- Flapjack helper: primitive lowering preserves pre-MTI syntax. -/
theorem compileOp_noMti (t : Tra) (op : FlatLang.Op) (xs : List ClosLang.Exp)
    (safe : noMtiList xs) : noMti (compileOp t op xs) := by
  cases op with
  | src op =>
    cases op <;> simp [compileOp, noMti, noMtiList, safe, copyByteStr_noMti,
      copyByteAw8_noMti, compileArith_noMti]
    case opapp | opassign =>
      cases xs with
      | nil => simp [arg2, noMti, noMtiList]
      | cons x xs =>
        cases xs with
        | nil => simp [arg2, noMti, safe]
        | cons y ys => cases ys <;> simp [arg2, noMti, noMtiList] at safe ⊢ <;> tauto
    case test test ty =>
      cases ty <;> cases test
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try cases ‹Opb›
      all_goals simp [noMti, safe]
    case fromTo a b =>
      cases a <;> cases b
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try cases ‹Flapjack.AstHOL.WordSize›
      all_goals try simp [noMti, safe]
      all_goals cases xs with
        | nil => simp [arg1, noMti, noMtiList]
        | cons x xs => cases xs <;> simp [arg1, noMti, noMtiList] at safe ⊢ <;> tauto
  | globalVarAlloc n => simp [compileOp, noMti, noMtiList, safe]
  | globalVarInit n => simp [compileOp, noMti, safe]
  | globalVarLookup n => simp [compileOp, noMti, safe]
  | tagLenEq tag n => simp [compileOp, noMti, safe]
  | lenEq n => simp [compileOp, noMti, safe]
  | el n =>
    cases xs with
    | nil => simp [compileOp, arg1, noMti, noMtiList]
    | cons x xs => cases xs <;> simp [compileOp, arg1, noMti, noMtiList] at safe ⊢ <;> tauto
  | id =>
    cases xs with
    | nil => simp [compileOp, arg1, noMti, noMtiList]
    | cons x xs => cases xs <;> simp [compileOp, arg1, noMti, noMtiList] at safe ⊢ <;> tauto

private theorem reverse_noMti (xs : List ClosLang.Exp) (safe : noMtiList xs) :
    noMtiList xs.reverse := by
  rw [noMtiList_iff] at safe ⊢
  simpa using safe

/-- Flapjack helper: each compiled expression has pre-MTI syntax. -/
theorem compileExp_noMti (m : List (Option MlString)) (exp : FlatLang.Exp) :
    noMti (compileExp m exp) := by
  induction m, exp using compileExp.induct
      (motive_2 := fun m fs => noMtiFuns (compileFuns m fs))
      (motive_3 := fun m xs => noMtiList (compileExps m xs)) with
  | case1 m t e ih => simpa [compileExp, noMti] using ih
  | case2 m t l => cases l <;> simp [compileExp, compileLit, noMti, noMtiList]
  | case3 m t v => simp [compileExp, noMti]
  | case4 m t tag es ih =>
    simp only [compileExp, noMti_smartCons, ← noMtiList_iff]
    exact reverse_noMti _ ih
  | case5 m t u x ih | case6 m t u x ih => simpa [compileExp] using ih
  | case7 m t op es h1 h2 ih =>
    simpa only [compileExp] using compileOp_noMti t op _ (reverse_noMti _ ih)
  | case8 m t v e ih => simpa [compileExp, noMti] using ih
  | case9 m t a b c iha ihb ihc => simp [compileExp, noMti, iha, ihb, ihc]
  | case10 m t vo a b iha ihb => simp [compileExp, noMti, noMtiList, iha, ihb]
  | case11 m t e ps => simp [compileExp, noMti, noMtiList]
  | case12 m t e v h ihe ihh => simp [compileExp, noMti, ihe, ihh]
  | case13 m t e ps h ih => simpa only [compileExp] using ih
  | case14 m t fs e newM ihf ihe =>
    simp only [compileExp, noMti, true_and]
    exact ⟨ihe, ihf⟩
  | case15 m => simp [compileExps, noMtiList]
  | case16 m e es ihe ihes => simp [compileExps, noMtiList, ihe, ihes]
  | case17 m => simp [compileFuns, noMtiFuns]
  | case18 m f v e fs ihe ihfs => simp [compileFuns, noMtiFuns, ihe, ihfs]

/-- Flapjack helper: compilation of any flat declaration list has pre-MTI
syntax. The HOL theorem additionally states two other syntax properties. -/
theorem compileDecs_noMti (ds : List FlatLang.Exp) :
    ∀ e ∈ compileDecs ds, noMti e := by
  induction ds with
  | nil => simp [compileDecs, compile, compileExps]
  | cons e ds ih =>
    simp only [compileDecs, compile, compileExps] at ih ⊢
    intro x member
    rcases List.mem_cons.mp member with rfl | member
    · exact compileExp_noMti [] e
    · exact ih x member

private theorem interpreter_noMti : noMti ClosInterp.closInterpreter := by
  simp [ClosInterp.closInterpreter, ClosInterp.closInterpreterBody,
    ClosInterp.closInterpEl, ClosInterp.closInterpRev,
    ClosInterp.interpreterVar_eq, ClosInterp.interpreterGetEl_eq,
    ClosInterp.interpreterCons_eq, ClosInterp.interpreterApp_eq,
    ClosInterp.interpreterCall_eq, ClosInterp.interpreterCallList_eq,
    ClosInterp.interpreterIsCase_eq, noMti, noMtiList, noMtiFuns]

private theorem compileInit_noMti (b : Bool) : noMti (ClosInterp.compileInit b) := by
  cases b <;> simp [ClosInterp.compileInit, ClosInterp.interpreterCons_eq,
    ClosInterp.interpreterVar_eq, noMti, noMtiList, interpreter_noMti]

/-- Flapjack helper: normal flat-to-closure compilation and interpreter
attachment produce pre-MTI syntax. The HOL theorem additionally states two
other syntax properties. -/
theorem compileProg_noMti (ds : List FlatLang.Exp) :
    ∀ e ∈ compileProg ds, noMti e := by
  have safe := compileDecs_noMti ds
  simpa [compileProg, ClosInterp.attachInterpreter, compileInit_noMti] using safe

/-- Flapjack helper: the incremental path produces pre-MTI syntax. The HOL
theorem additionally states two other syntax properties. -/
theorem incCompileDecs_noMti {α : Type} (ds : List FlatLang.Exp) :
    ∀ e ∈ (incCompileDecs (α := α) ds).1, noMti e := by
  intro e member
  apply ClosInterp.insertInterp_noMti e _ member
  intro x sourceMember
  rcases List.mem_append.mp sourceMember with original | unit
  · exact compileDecs_noMti ds x original
  · exact compileDecs_noMti [.con .none none []] x unit

end Flapjack.Compiler.Backend.FlatToClos
