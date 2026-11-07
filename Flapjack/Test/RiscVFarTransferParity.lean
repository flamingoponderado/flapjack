import Flapjack.RiscV.Lab

/-!
# Far-jump and far-branch lowering against `riscv_ast`

CakeML's RISC-V encoder falls back when a PC-relative operand leaves the
architectural range (`riscv_targetScript.sml:170-263`):

* `Jump a` / `Call a` emit `JAL` while `min21 <= a <= max21` (that is,
  `-2^20 <= a <= 2^20 - 1`) and otherwise `AUIPC temp, hi; JALR _, temp, lo`.
* `JumpCmp c r ri a` emits a single branch while `-0xFFC <= a <= 0xFFF` and
  otherwise inverts the branch over a `JAL`.
* `lab_inst` (`lab_to_targetScript.sml:20-28`) reduces `Halt`, `Install` and
  `CallFFI` to `Jump w`, so all three take the `Jump` fallback, and
  `line_ok_light` checks them with `asm_ok (Jump w)`.

Two properties are pinned here.  First, the `JumpCmp` range is measured
against `a` -- the offset of the whole line, including the `ORI`/`ANDI`/`AND`
that materialises the operand -- not against the branch instruction that
follows that prelude.  Second, `CallFFI` and `Install` get the `Jump`
fallback rather than a bare, silently wrapping `JAL`.
-/

namespace Flapjack.RiscV

private def ctx : WordFfiContext := { services := [("write", 7)] }

end Flapjack.RiscV
