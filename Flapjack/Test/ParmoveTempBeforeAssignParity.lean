import Flapjack.Compiler.Backend.Parmove.TempBeforeAssign

namespace Flapjack.Test.ParmoveTempBeforeAssignParity
open Flapjack.Compiler.Backend.Parmove

/-! Literal ordered-clause original observations. In particular NONE,NONE
is a read-before-assignment and a valid scratch write stops scanning. -/
-- nt_empty=True
example : notUseTempBeforeAssign ([] : List (Move Nat)) = true := rfl
-- nt_read=False
example : notUseTempBeforeAssign ([(some 1,none)] : List (Move Nat)) = false := rfl
-- nt_both_none=False
example : notUseTempBeforeAssign ([(none,none)] : List (Move Nat)) = false := rfl
-- nt_write_stops=True
example : notUseTempBeforeAssign ([(none,some 1),(some 2,none)] : List (Move Nat)) = true := rfl
-- nt_recursive_read=False
example : notUseTempBeforeAssign ([(some 1,some 2),(some 3,none)] : List (Move Nat)) = false := rfl
-- nt_recursive_write=True
example : notUseTempBeforeAssign ([(some 1,some 2),(none,some 3),(some 4,none)] : List (Move Nat)) = true := rfl
-- nt_write=True
example : notUseTempBeforeAssign ([(none,some 1)] : List (Move Nat)) = true := rfl
-- nt_real_chain=True
example : notUseTempBeforeAssign ([(some 1,some 2),(some 2,some 3)] : List (Move Nat)) = true := rfl

end Flapjack.Test.ParmoveTempBeforeAssignParity
