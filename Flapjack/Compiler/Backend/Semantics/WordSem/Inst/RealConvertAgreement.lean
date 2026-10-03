import Flapjack.Compiler.Backend.Semantics.WordSem.Inst
import Flapjack.Misc.MachineIeee.ConvertReal

namespace Flapjack.WordSemStateFiniteExact

/-! Flapjack consumer agreements with no separate HOL original: the native
WordSem `FPToInt` and `FPFromInt` clauses equal the same clauses built from the
tagged Mathlib-real ports `holFp64ToIntR` (`fp64_to_int`) and `holRealToFp64R`
(`real_to_fp64`) at `real_of_int i` (HOL `int_to_fp64`), including every
failure branch. No successful evaluation, range or agreement premise is
assumed. Mathlib `ℝ` as HOL `real` is the standard carrier reading; this
proof-only module keeps real-analysis imports out of the compiler. -/

theorem inst_fpToInt_real {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : WordSemStateFiniteExact width C F) :
    inst (.fp (.fpToInt d1 d2)) s =
      match getFpVar d2 s with
      | none => none
      | some f =>
          match holFp64ToIntR .roundTiesToEven f with
          | none => none
          | some i =>
              let w : BitVec 32 := BitVec.ofInt 32 i
              if w.toInt = i then
                (if width = 64 then some (setFpVar d1 (w.setWidth 64) s)
                 else
                  match getFpVar (d1 / 2) s with
                  | none => none
                  | some f =>
                      let (h, l) := if d1 % 2 = 1 then (63, 32) else (31, 0)
                      some (setFpVar (d1 / 2) (holBitFieldInsert h l w f) s))
              else none := by
  have h : holFp64ToInt .roundTiesToEven = holFp64ToIntR .roundTiesToEven :=
    funext (holFp64ToInt_eq_real _)
  simp only [inst]
  rw [h]
  cases getFpVar d2 s <;> rfl

theorem inst_fpFromInt_real {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : WordSemStateFiniteExact width C F) :
    inst (.fp (.fpFromInt d1 d2)) s =
      if width = 64 then
        match getFpVar d2 s with
        | some f =>
            let i := (holWordExtract 31 0 f 32).toInt
            some (setFpVar d1 (holRealToFp64R .roundTiesToEven (i : ℝ)) s)
        | none => none
      else
        match getFpVar (d2 / 2) s with
        | some v =>
            let i := (if d2 % 2 = 1 then holWordExtract 63 32 v width
              else holWordExtract 31 0 v width).toInt
            some (setFpVar d1 (holRealToFp64R .roundTiesToEven (i : ℝ)) s)
        | none => none := by
  have h : holIntToFp64 .roundTiesToEven = fun i : Int => holRealToFp64R .roundTiesToEven (i : ℝ) :=
    funext (holIntToFp64_eq_real _)
  simp only [inst]
  rw [h]
  split
  · cases getFpVar d2 s <;> rfl
  · cases getFpVar (d2 / 2) s <;> rfl

end Flapjack.WordSemStateFiniteExact
