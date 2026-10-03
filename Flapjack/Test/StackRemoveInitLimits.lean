import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
namespace Flapjack.Test.StackRemoveInitLimits
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits

-- Rows of scripts/hol-probes/stack_remove_init_make_probe.out (original EVAL).
-- limit_prime_64_a
example : getStackHeapLimitPrime 1000 (0x1000#64) (0x5000#64) (0x9000#64) = (3048, 500) := by rfl
-- limit_prime_64_b: guarded heap product overflows, so the bound word is -1w
example : getStackHeapLimitPrime (2 ^ 62) (0x1000#64) (0x5000#64) (0x9000#64) = (2000, 1024) := by
  rfl
-- limit_prime_64_c: small heap bound selected
example : getStackHeapLimitPrime 3 (0x1000#64) (0x5000#64) (0x9000#64) = (4046, 1) := by rfl
-- limit_prime_64_d: wrapped pointer order
example : getStackHeapLimitPrime 1000 (0x9000#64) (0x1000#64) (0x5000#64) = (0, 500) := by rfl
-- limit_prime_32_a
example : getStackHeapLimitPrime 100 (0x100#32) (0x900#32) (0x2000#32) = (1836, 50) := by rfl
-- limit_prime_32_b
example : getStackHeapLimitPrime (2 ^ 30) (0x100#32) (0x900#32) (0x2000#32) = (1424, 256) := by
  rfl
-- limit_prime_mixed_a: independent first and second pointer widths
example : getStackHeapLimitPrime 1000 (0x1000#32) (0x5000#16) (0x9000#64) = (3048, 500) := by rfl
-- limit_prime_mixed_b
example : getStackHeapLimitPrime 3 (0xFFFF1000#32) (0x5000#64) (0x2000#32) = (0, 1) := by rfl
-- limit_64_a: third pointer within the stack-allocation margins
example : getStackHeapLimit 1000 ((0x1000#64), (0x5000#64), (0x9000#64)) = (3048, 500) := by rfl
-- limit_64_b: midpoint used
example : getStackHeapLimit 1000 ((0x1000#64), (0x1100#64), (0x9000#64)) = (3048, 500) := by rfl
-- limit_64_c: wrapped base pointer
example : getStackHeapLimit 7 ((0xFFFFFFFFFFFFF000#64), (0x10#64), (0x2000#64)) = (0, 3) := by
  rfl
-- limit_32_a
example : getStackHeapLimit 50 ((0x1000#32), (0x1004#32), (0x3000#32)) = (1950, 25) := by rfl
-- limit_32_b
example : getStackHeapLimit 5000 ((0x1000#32), (0x2000#32), (0x8000#32)) = (6096, 512) := by rfl

end Flapjack.Test.StackRemoveInitLimits
