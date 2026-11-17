module

public import Flapjack.Compiler.Inference.TypeDCanon
import Aesop

@[expose] public section

/-! Operator typing is invariant under good type-identifier renamings. -/
namespace Flapjack.Compiler.Inference.TypeDCanon
open Flapjack.AstHOL Flapjack.TypeSystemHOL Flapjack.Compiler.Inference.InferProps

/-- Good identifier renamings preserve every source operator typing rule. -/
@[hol "cakeml/compiler/inference/proofs/type_dCanonScript.sml" "type_op_ts_tid_rename"]
theorem typeOpTsTidRename (f : Nat → Nat) (good : goodRemap f) (op : Op) (ts : List SemanticT) (t : SemanticT)
    (h : typeOp op ts t) : typeOp op (ts.map (tsTidRename f)) (tsTidRename f t) := by
  have fix := mapFixedOnMembers f (TlistNum :: TboolNum :: primTypeNums) good
  have fList : f TlistNum = TlistNum := fix _ (by simp)
  have fBool : f TboolNum = TboolNum := fix _ (by simp)
  have fArray : f TarrayNum = TarrayNum := fix _ (by simp [primTypeNums])
  have fChar : f TcharNum = TcharNum := fix _ (by simp [primTypeNums])
  have fFn : f TfnNum = TfnNum := fix _ (by simp [primTypeNums])
  have fInt : f TintNum = TintNum := fix _ (by simp [primTypeNums])
  have fRef : f TrefNum = TrefNum := fix _ (by simp [primTypeNums])
  have fString : f TstringNum = TstringNum := fix _ (by simp [primTypeNums])
  have fTup : f TtupNum = TtupNum := fix _ (by simp [primTypeNums])
  have fVector : f TvectorNum = TvectorNum := fix _ (by simp [primTypeNums])
  have fWord64 : f Tword64Num = Tword64Num := fix _ (by simp [primTypeNums])
  have fWord8 : f Tword8Num = Tword8Num := fix _ (by simp [primTypeNums])
  have fWord8array : f Tword8arrayNum = Tword8arrayNum := fix _ (by simp [primTypeNums])
  have fDouble : f TdoubleNum = TdoubleNum := fix _ (by simp [primTypeNums])
  have renameOf (ty : PrimType) : tsTidRename f (typeOf ty) = typeOf ty := by
    cases ty <;> simp [typeOf, Tbool, Tint, Tchar, Tstring, Tword8, Tword64, Tdouble,
        tsTidRename, tsTidRenameList, fBool, fInt, fChar, fString, fDouble]
    case wordT w =>
      cases w <;> simp [tsTidRename, tsTidRenameList, fWord8, fWord64]
  unfold typeOp at h
  repeat split at h <;> simp_all [typeOp, tsTidRename, tsTidRenameList, Tfn, Tbool, Tint, Tchar,
    Tstring, Tword8, Tword64, Tword8array, Tref, Ttup, Tlist, Tvector, Tarray,
    ]

  all_goals try (intro x hx; rw [h.1 x hx, renameOf])
  all_goals aesop (add simp [tsTidRename, tsTidRenameList, fVector, fArray, renameOf])

end Flapjack.Compiler.Inference.TypeDCanon
