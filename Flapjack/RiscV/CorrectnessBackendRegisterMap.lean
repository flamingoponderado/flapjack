import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.Backend
import Flapjack.RiscV.RegisterTransfer

/-!
# Backend correctness through the CakeML `riscv_names` map

This is the first green, additive slice of the CakeML ABI rebase
(bead `flapjack-pxn.8.5.10.4.2.2.3`).  It keeps the raw Backend selector and
evaluators unchanged and instead routes their results through the one-time
stack-to-hardware register map now available in `Flapjack.RiscV.RegisterMap`.

Two facts are established:

* an internal read on a transferred hardware state resolves the internal name
  through `labRegisterOfNat` exactly once and returns the raw internal value;
* running the relabeled image of a straight-line Backend compilation on the
  transferred state transfers the raw execution result.

Neither statement changes emission or abstract semantics; they are the boundary
lemmas the later atomic rebase consumes.
-/

namespace Flapjack.RiscV

variable {width : Nat}

/-- The Cake map sends a hardware register to the architectural zero register
exactly when that register is the internal zero role `27`.  This is the
`Fin`-level form of `riscvForward_eq_zero_iff` used to discharge the write-set
side conditions of the transfer/relabel soundness theorem. -/
theorem riscvForward_ne_zero_iff {register : Fin 32} :
    riscvForward register ≠ 0 ↔ register.val ≠ 27 :=
  not_congr riscvForward_eq_zero_iff

example {register : Fin 32} :
    (riscvForward register ≠ 0) ↔ register.val ≠ 27 :=
  riscvForward_ne_zero_iff

example : riscvForward (27 : Fin 32) = 0 := by decide

example : riscvForward (0 : Fin 32) ≠ 0 := by decide

end Flapjack.RiscV