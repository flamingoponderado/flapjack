import Flapjack.Compiler.Backend.ClosLang.Syntax
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.ClosKnown

/-- Complete original value approximation, retaining the actual closure body
and recursive tuple payload rather than an arbitrary syntax parameter. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
inductive ValApprox where
  | closNoInline : Nat → Nat → ValApprox
  | clos : Nat → Nat → ClosLang.Exp → Nat → ValApprox
  | tuple : Nat → List ValApprox → ValApprox
  | int : Int → ValApprox
  | other
  | impossible

/-- The original three alternatives include a complete expression for let-inlining. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
inductive InliningDecision where
  | nothing
  | annotate : Nat → InliningDecision
  | letInline : ClosLang.Exp → InliningDecision

/-- Complete four-field configuration, with the literal spt approximation tree. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
structure Config where
  inlineMaxBodySize : Nat
  inlineFactor : Nat
  initialInlineFactor : Nat
  valApproxSpt : Spt ValApprox

@[hol "cakeml/compiler/backend/clos_knownScript.sml" "default_inline_factor_def"]
def defaultInlineFactor : Nat := 8

@[hol "cakeml/compiler/backend/clos_knownScript.sml" "default_max_body_size_def"]
def defaultMaxBodySize (maxApp inlineFactor : Nat) : Nat :=
  (maxApp + 1) * inlineFactor

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def mkConfig (maxBodySize inlineFactor : Nat) : Config :=
  ⟨maxBodySize, inlineFactor, inlineFactor, .ln⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def defaultConfig (maxApp : Nat) : Config :=
  mkConfig (defaultMaxBodySize maxApp defaultInlineFactor) defaultInlineFactor

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def decInlineFactor (c : Config) : Config :=
  { c with inlineFactor := c.inlineFactor / 2 }

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def resetInlineFactor (c : Config) : Config :=
  { c with inlineFactor := c.initialInlineFactor }

end Flapjack.Compiler.Backend.ClosKnown
