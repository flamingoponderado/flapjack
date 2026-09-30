import Flapjack.Compiler.Backend.StackProps.FixedNames
namespace Flapjack.Test.StackPropsFixedNames
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
example {width : Nat} [NeZero width] (names : Flapjack.Spt Nat)
    (c : AsmConfigExact width) (h : c.isa ≠ .x86_64) : StackProps.fixedNames names c := by
  simp [StackProps.fixedNames, h]
example {width : Nat} [NeZero width] (names : Flapjack.Spt Nat)
    (c : AsmConfigExact width) (h : c.isa = .x86_64) :
    StackProps.fixedNames names c ↔
      StackNames.findName (fun key => Flapjack.sptLookup key names) 3 = 2 ∧
      StackNames.findName (fun key => Flapjack.sptLookup key names) 4 = 1 ∧
      StackNames.findName (fun key => Flapjack.sptLookup key names) 0 = 0 := by
  simp [StackProps.fixedNames, h]
-- Direct original HOL rows x86_good/x86_empty/x86_bad_zero/riscv_empty.
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (h : c.isa = .x86_64) :
    StackProps.fixedNames (Flapjack.sptInsert 3 2 (Flapjack.sptInsert 4 1 .ln)) c := by
  simp [StackProps.fixedNames, h, StackNames.findName, Flapjack.FLOOKUP,
    Flapjack.sptLookup, Flapjack.sptInsert]
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (h : c.isa = .x86_64) : ¬ StackProps.fixedNames .ln c := by
  simp [StackProps.fixedNames, h, StackNames.findName, Flapjack.FLOOKUP, Flapjack.sptLookup]
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (h : c.isa = .x86_64) :
    ¬ StackProps.fixedNames (Flapjack.sptInsert 0 9 (Flapjack.sptInsert 3 2 (Flapjack.sptInsert 4 1 .ln))) c := by
  simp [StackProps.fixedNames, h, StackNames.findName, Flapjack.FLOOKUP,
    Flapjack.sptLookup, Flapjack.sptInsert]
end Flapjack.Test.StackPropsFixedNames
