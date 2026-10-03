import Flapjack.RiscV.L3.Defs.SupervisorCSR
namespace Flapjack.Test.L3ExtStatusParity
open Flapjack.RiscV.L3
-- Independent original encodings for all constructors.
example : ([ExtStatus.Off,.Initial,.Clean,.Dirty].map ext_status) =
    ([0,1,2,3] : List (BitVec 2)) := by decide
example (e : ExtStatus) : extStatus (ext_status e) = e := by cases e <;> rfl
end Flapjack.Test.L3ExtStatusParity
