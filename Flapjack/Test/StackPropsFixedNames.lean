import Flapjack.Compiler.Backend.StackProps.FixedNames
namespace Flapjack.Test.StackPropsFixedNames
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
example {width : Nat} [NeZero width] (names : Flapjack.HolFiniteMapExact Nat Nat)
    (c : AsmConfigExact width) (h : c.isa ≠ .x86_64) : StackProps.fixedNames names c := by
  simp [StackProps.fixedNames, h]
example {width : Nat} [NeZero width] (names : Flapjack.HolFiniteMapExact Nat Nat)
    (c : AsmConfigExact width) (h : c.isa = .x86_64) :
    StackProps.fixedNames names c ↔
      StackNames.findName names.lookup 3 = 2 ∧
      StackNames.findName names.lookup 4 = 1 ∧
      StackNames.findName names.lookup 0 = 0 := by
  simp [StackProps.fixedNames, h]
end Flapjack.Test.StackPropsFixedNames
