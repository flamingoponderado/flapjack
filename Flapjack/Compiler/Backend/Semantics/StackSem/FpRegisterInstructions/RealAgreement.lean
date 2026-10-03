import Flapjack.Compiler.Backend.Semantics.StackSem.FpRegisterInstructions
import Flapjack.Misc.MachineIeee.ConvertReal
import Flapjack.Misc.MachineIeee.SqrtReal

/-!
# StackSem real-conversion `inst_def` cases over the arbitrary-real IEEE ports

Flapjack consumer agreements with no separate HOL original.  Each of the
`FPSqrt`, `FPToInt` and `FPFromInt` cases of HOL `inst_def`
(`cakeml/compiler/backend/semantics/stackSemScript.sml:558-562, 605-636`) is
proved equal, for every register state and including every failure branch, to
the same clause built from the tagged Mathlib-real ports `holFp64SqrtR`
(`fp64_sqrt`), `holFp64ToIntR` (`fp64_to_int`) and `holRealToFp64R`
(`real_to_fp64`) applied to `real_of_int i` (HOL `int_to_fp64`).  No success,
range or agreement premise is assumed.  Agreement of Mathlib `ℝ` with HOL
`real` is the standard carrier reading; no cross-prover equivalence is claimed.
This proof-only module keeps real-analysis imports out of the compiler.
-/

namespace Flapjack.StackSemFpRegisterInstructions
open StackSemStateOps Compiler.Encoders.Asm

theorem instFpSqrt_real {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) :
    instFpSqrt d1 d2 s =
      match getFpVar d2 s with
      | some f => some (setFpVar d1 (holFp64SqrtR .roundTiesToEven f) s)
      | none => none := by
  have h : holFp64SqrtReal .roundTiesToEven = holFp64SqrtR .roundTiesToEven :=
    funext fun a => (holFp64Sqrt_agreement _ a).symm.trans (holFp64Sqrt_eq_holFp64SqrtR _ a)
  unfold instFpSqrt
  rw [h]
  cases getFpVar d2 s <;> rfl

theorem instFpToInt_real {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) :
    instFpToInt d1 d2 s =
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
  unfold instFpToInt
  rw [h]
  cases getFpVar d2 s <;> rfl

theorem instFpFromInt_real {width : Nat} [NeZero width] {C F : Type}
    (d1 d2 : Nat) (s : StackSemStateFiniteExact width C F) :
    instFpFromInt d1 d2 s =
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
  unfold instFpFromInt
  rw [h]
  split
  · cases getFpVar d2 s <;> rfl
  · cases getFpVar (d2 / 2) s <;> rfl

end Flapjack.StackSemFpRegisterInstructions
