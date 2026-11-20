module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Build

@[expose] public section

/-! Timestamp preservation for constant construction. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

/-- The induction underlying constant-build timestamp preservation. -/
private theorem doBuildSome {α : Type} (parts : List ClosLang.ConstPart)
    (values : Nat → Value) (index : Nat) (refs : Spt (BvlSem.Ref α)) (ts : Nat) :
    ∃ ts2, (doBuild values index parts refs (some ts)).2.2 = some ts2 := by
  induction parts generalizing values index refs ts with
  | nil => exact ⟨ts, rfl⟩
  | cons part rest ih =>
    cases part with
    | int i => simpa [doBuild, doPart] using ih (fun key => if key = index then .number i else values key) (index + 1) refs ts
    | w64 w => simpa [doBuild, doPart] using ih (fun key => if key = index then .word64 w else values key) (index + 1) refs ts
    | con tag indices =>
      cases indices with
      | nil => simpa [doBuild, doPart] using ih (fun key => if key = index then .block 0 tag [] else values key) (index + 1) refs ts
      | cons a as => simpa [doBuild, doPart] using ih (fun key => if key = index then .block ts tag ((a :: as).map values) else values key) (index + 1) refs (ts + 1)
    | str text => simpa [doBuild, doPart] using ih (fun key => if key = index then .refPtr true (leastUnusedRef refs) else values key) (index + 1) (sptInsert (leastUnusedRef refs) (.byteArray true text.explode) refs) ts

/-- Constant construction preserves an enabled timestamp. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "do_build_const_IMP_SOME"]
theorem doBuildConstSome {α : Type} (parts : List ClosLang.ConstPart) (refs refs1 : Spt (BvlSem.Ref α))
   (ts : Nat) (v : Value) (ts1 : Option Nat)
   (h : doBuildConst parts refs (some ts) = (v, refs1, ts1)) : ∃ ts2, ts1 = some ts2 := by
  obtain ⟨ts2, ht⟩ := doBuildSome parts (fun _ => .number 0) 0 refs ts
  refine ⟨ts2, ?_⟩
  unfold doBuildConst at h
  rw [h] at ht
  exact ht

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
