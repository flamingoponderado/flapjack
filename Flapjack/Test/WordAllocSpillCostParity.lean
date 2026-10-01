import Flapjack.Compiler.Backend.WordAlloc.Heuristics

namespace Flapjack.Test.WordAllocSpillCostParity
open Flapjack.WordAlloc

-- spill_zero=0
example : getSpillCost (0,0,0,0,0) true = 0 := rfl

-- spill_call_tail=5
example : getSpillCost (1,0,0,0,0) true = 5 := rfl

-- spill_call_nontail=1
example : getSpillCost (1,0,0,0,0) false = 1 := rfl

-- spill_left_register=2
example : getSpillCost (0,1,0,0,0) false = 2 := rfl

-- spill_left_memory=4
example : getSpillCost (0,0,1,0,0) false = 4 := rfl

-- spill_right_register=2
example : getSpillCost (0,0,0,1,0) false = 2 := rfl

-- spill_right_memory=4
example : getSpillCost (0,0,0,0,1) false = 4 := rfl

-- spill_asymmetric_tail=430
example : getSpillCost (2,3,5,7,11) true = 430 := rfl

-- spill_asymmetric_nontail=86
example : getSpillCost (2,3,5,7,11) false = 86 := rfl

-- spill_large=73786976294838206464
example : getSpillCost (0,0,0,0,18446744073709551616) false = 73786976294838206464 := rfl

end Flapjack.Test.WordAllocSpillCostParity
