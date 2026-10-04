import Flapjack.Compiler.Backend.StackRemove.Comp
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Misc.Sptree

/-! Native code relation used by the full StackRemove state relation.
Code maps retain HOL's Spt carrier, including arbitrary malformed trees. The
only representation qualifier is the positive type-indexed word dimension.
-/

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Literal original code relation: every source lookup has a register-bounded
program and its exact compiled target lookup; the target domain is exactly the
source domain together with the three initializer stub names. HOL sets are
rendered as predicates, so union and the literal three-element set are written
pointwise. No well-formedness, fresh-name or evaluation premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def codeRelHOL {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : Spt (HolProg width)) : Prop :=
  (∀ name program, sptLookup name source = some program →
    Flapjack.Compiler.Backend.StackProps.regBound program pointer ∧
      sptLookup name target = some (comp jump bounds pointer program)) ∧
  sptDomain target = (fun name => sptDomain source name ∨ name = 0 ∨ name = 1 ∨ name = 2)

end Flapjack.Compiler.Backend.StackRemove
