module

public import Flapjack.RiscV.RegisterNames

@[expose] public section

/-!
# The inverse of the `riscv_names` map

`Flapjack.RiscV.RegisterNames` defines the CakeML `riscv_names` map as a
function `riscvForward : Fin 32 → Fin 32` on hardware register indices. This
file gives its explicit inverse `riscvInverse` (and `riscvInverseName` on
register numbers), together with the left and right inverse laws.
-/

namespace Flapjack.RiscV

variable {width : Nat}

/-- The explicit inverse of the `riscv_names` map, computed by an exhaustive
case analysis on the sixteen moved register names. -/
def riscvInverseName (name : Nat) : Nat :=
  match name with
  | 1 => 0
  | 10 => 1
  | 11 => 2
  | 12 => 3
  | 13 => 4
  | 27 => 10
  | 28 => 11
  | 29 => 12
  | 30 => 13
  | 0 => 27
  | 2 => 28
  | 3 => 29
  | 4 => 30
  | other => other

theorem riscvInverseName_lt_32 {name : Nat} (h : name < 32) :
    riscvInverseName name < 32 := by
  unfold riscvInverseName
  split <;> omega

/-- The inverse of the `riscv_names` map on the hardware register file. -/
def riscvInverse (register : Fin 32) : Fin 32 :=
  ⟨riscvInverseName register.val, riscvInverseName_lt_32 register.isLt⟩

/-- `riscvInverse` is a left inverse of `riscvForward`. -/
theorem riscvInverse_riscvForward (register : Fin 32) :
    riscvInverse (riscvForward register) = register := by
  apply Fin.ext
  have hcheck : (List.range 32).all (fun candidate =>
      riscvInverseName (riscvRegisterName candidate) == candidate) = true := by
    decide
  have heval := List.all_eq_true.mp hcheck register.val
    (List.mem_range.mpr register.isLt)
  simpa [riscvInverse, riscvForward, beq_iff_eq] using heval

/-- `riscvInverse` is a right inverse of `riscvForward`. -/
theorem riscvForward_riscvInverse (register : Fin 32) :
    riscvForward (riscvInverse register) = register := by
  apply Fin.ext
  have hcheck : (List.range 32).all (fun candidate =>
      riscvRegisterName (riscvInverseName candidate) == candidate) = true := by
    decide
  have heval := List.all_eq_true.mp hcheck register.val
    (List.mem_range.mpr register.isLt)
  simpa [riscvInverse, riscvForward, beq_iff_eq] using heval

/-- The internal Cake stack register number whose image is hardware zero. -/
theorem riscvInverse_zero : riscvInverse (0 : Fin 32) = 27 := by decide

end Flapjack.RiscV
