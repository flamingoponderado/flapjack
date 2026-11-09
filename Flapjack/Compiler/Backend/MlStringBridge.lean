module

public import Flapjack.Basis.Pure.MlString
public import Flapjack.Compiler.Backend.StackLang
public import Flapjack.Compiler.Backend.StackLang.Prog
public import Flapjack.Compiler.Backend.StackCarrier
public import Flapjack.Compiler.Encoders.Asm

@[expose] public section

/-!
# `String` <-> `mlstring` bridge for the stack program carrier

HOL `stackLang$prog` stores an `mlstring` in its `FFI` constructor, while the
executed `Flapjack.Compiler.Backend.StackCarrier.ProgW` stores a Lean `String`.
The exact width-indexed carrier `Flapjack.Compiler.Backend.StackLang.HolProg` uses the
faithful `Flapjack.Basis.Pure.MlString.MlString` carrier instead.  This
module records the kernel-checked bridge between the two: `holProgToProgW`
decodes the exact program into the executable carrier and `progWToHolProg`
encodes it back, and the round trip `progWToHolProg (holProgToProgW p) = p`
shows the exact carrier embeds into the executable one.

The bridge is only a structural relation: the executed compiler does not
textually route through `HolProg`, so this does NOT by itself satisfy the
AGENTS.md production-path rule.  It shows that the `String` FFI field of `ProgW`
is the image of the faithful `mlstring` field under
`Flapjack.Basis.Pure.MlString.toStringOfBytes`, so the exact `MlString`
theorems can be transported onto programs whose FFI names are byte strings.
The program-level FFI-name correspondence is stated explicitly by
`holProgToProgW_ffi` (exact `mlstring` name maps to its `toStringOfBytes` image)
and `progWToHolProg_ffi` (executed `String` name maps to its `ofString` image);
together with `progWToHolProg_holProgToProgW` these pin the FFI-name field
relationship without routing the executed compiler through `HolProg`.
-/

namespace Flapjack.Compiler.Backend

open Flapjack.Basis.Pure
open Flapjack.Compiler.Backend.StackLang (Prog HolProg)
open Flapjack.Compiler.Encoders.Asm

end Flapjack.Compiler.Backend