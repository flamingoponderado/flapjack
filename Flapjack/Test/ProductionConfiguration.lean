import Flapjack.Compiler.Backend.WordToStack.ProductionConfiguration

namespace Flapjack.Test.ProductionConfiguration
open Flapjack RiscV RiscV.CakeRegAlloc

/-! Kernel fixtures for concrete caller fields/locations, not whole lowering. -/
example : (sourceWordStackConfig 7 { locations := [], nextSpill := 0 } 0).callAbiBase = 0 := rfl
example : (sourceWordStackConfig 7 { locations := [], nextSpill := 0 } 0).abiBase = 1 := rfl
example : (sourceWordStackConfig 7 { locations := [], nextSpill := 0 } 0).addressScratch = 23 := rfl
example : wordStackCallFrameOffset (sourceWordStackConfig 7 { locations := [], nextSpill := 0 } 0) = 0 := rfl
example : wordStackCallFrameOffset (sourceWordStackConfig 7 { locations := [], nextSpill := 2 } 2) = 3 := rfl
example : wordStackPhysicalLocation (sourceWordStackConfig 7 { locations := [], nextSpill := 2 } 2) 0 0 = .register 0 := rfl
example : wordStackPhysicalLocation (sourceWordStackConfig 7 { locations := [], nextSpill := 2 } 2) cakeRiscVRegisterCount 0 = .stack 2 := rfl
example : wordStackPhysicalLocation (sourceWordStackConfig 7 { locations := [], nextSpill := 0 } 0) (cakeRiscVRegisterCount + 10) 0 = .stack 0 := rfl

end Flapjack.Test.ProductionConfiguration
