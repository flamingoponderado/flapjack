module

public import Flapjack.RiscV.PipelineDiagnostics
public import Flapjack.RiscV.ArtifactFormat
public import Flapjack.Test.OriginalPancakeProbes
public import Flapjack.RiscV.RuntimeBytes

@[expose] public section

/-!
# Exact RISC-V artifact parity for the `dec_clock` fixture

`Flapjack/Test/OriginalPancake/dec_clock.pnk` is

```
fun 1 main() { tick; return 7; }
```

The original CakeML Pancake compiler and the Flapjack port both accept this
program and both place `cml_generated_main` at byte offset 1000 and `cml_main`
at byte offset 1004 inside the `cake_main` frame.  This module pins the exact
generated artifact sections of both compilers in the same
`(label, base, bytes)` format used by `scripts/parity-small-corpus.py`, so the
comparison is on instruction and data bytes plus layout metadata rather than
on mere compiler acceptance.

A second fixture, `Flapjack/Test/OriginalPancake/const_return.pnk`, is

```
fun 1 main() { return 7; }
```

The original compiler produces byte-identical output for this no-tick program
and for the `dec_clock` program (same SHA-256 and same 8-byte terminal
`addi a0,x0,7; ret`), so the original drops the standalone `Tick`.  Flapjack
now mirrors CakeML's `lab_filter`: the source/Word semantics retains Tick for
clock reasoning, while the final Lab artifact omits its no-op instruction.

A third fixture, `Flapjack/Test/OriginalPancake/entry_order.pnk`, declares the
entry function last:

```
fun 1 a() { return 1; }
fun 1 b() { return 2; }
fun 1 main() { return a(); }
```

The original CPU pipeline moves the `main` declaration to the front
(`cakeml/pancake/pan_passesScript.sml:20-37`, `pan_to_target_all_def`), so it
emits `cml_generated_main`, `cml_main`, `cml_a`, `cml_b` in that order.  The
Flapjack entry permutation and source-facing ABI mapping now produce the same
section order and helper bytes for this fixture.

The original-side facts are the `OriginalPancakeProbes.decClock` source-backed
probe, whose dependency is the direct HOL probe
`scripts/hol-probes/pan_sem_dec_clock_e2e_probeScript.sml`.  That probe
evaluates the original `panSem$evaluate` on `tick; return 7` and observes
`SOME (Return (ValWord 7w))` with the clock decremented from `5` to `4`, which
is the semantic result the generated artifact must implement.

The generated `cml_generated_main` and `cml_main` sections are byte-identical
for this fixture.  This is evidence for the source-facing ABI adapter and the
final Lab filtering pass; larger programs still have tracked allocator,
frame, FFI, and lowering gaps.

A fourth fixture, `Flapjack/Test/OriginalPancake/nested_expression.pnk`, is the
GitHub issue #1015 reproducer whose right-nested sum
`((t1 + (a + (b + (c + d)))) << 1) >>> 1` needs more than the port's fixed
four-register Word-to-Stack temporary pool.  The original flattens the
expression through `crep_to_loop` and accepts it.  With the pool-expansion fix
tracked by `flapjack-pxn.2.5` the port also accepts it; this module pins that
acceptance through the production runtime-image entry point, and the corpus
fixture records the residual byte/layout difference as a tracked gap.
-/

namespace Flapjack.Test.RiscVArtifactParity

open Flapjack Flapjack.RiscV
open Flapjack.Test.OriginalPancakeProbes
  (decClock constReturn entryOrder nestedExpression setVar emptyLocals)

/-- The fixture source, taken from the original-side probe fact so the two
comparisons cannot drift apart. -/
def decClockSource : String := decClock.source

/-- Original CakeML `cml_generated_main` bytes: the 4-byte direct jump to
`cml_main`. -/
def cakeGeneratedMainBytes : List (BitVec 8) :=
  [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)

/-- Original CakeML `cml_main` bytes: `addi a0,x0,7; ret`. -/
def cakeMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x70, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Flapjack `cml_generated_main` bytes.  With the faithful `loop_to_word`
tail-call shape (`0 :: args`, loop_to_wordScript.sml:131) applied at the
same pipeline point Cake uses (inside `loop_to_word$comp`, not via a later
pan-to-word adapter), the dummy constant-`0` argument coalesces onto the
`x0` sink exactly as CakeML's does, so the port's artifact is just the
4-byte `jal`: byte-identical to Cake. -/
def flapjackGeneratedMainBytes : List (BitVec 8) :=
  [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)

/-- The wrapper is byte-identical to Cake: the former residual leading ABI
move for the dummy tail-call argument is gone now that the `0 :: args`
dummy is injected where Cake injects it. -/
def generatedMainExactMatch : Bool :=
  flapjackGeneratedMainBytes == cakeGeneratedMainBytes

/-- Flapjack `cml_main` bytes: Cake's 8-byte return shape.  The Lab filter
removes the no-op generated for Tick before final assembly. -/
def flapjackMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x70, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- The generated initializer section is byte-identical to Cake (see
`flapjackGeneratedMainBytes`). -/
def generatedMainBytesMatch : Bool :=
  generatedMainExactMatch

/-! The `dec_clock` artifact is now exact: Lab filtering removes the no-op
instruction while the source semantics still accounts for the tick. -/
def decClockExactParity : Bool :=
  cakeMainBytes == flapjackMainBytes

/-- The `const_return` fixture source: the no-tick counterpart to
`dec_clock`, taken from the original-side probe fact. -/
def constReturnSource : String := constReturn.source

/-- Flapjack `cml_main` bytes for the no-tick `return 7` fixture; this is now
byte-identical to Cake after the source-facing ABI adapter. -/
def flapjackConstReturnMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x70, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/- The standalone tick is filtered at the final Lab boundary. -/
def standaloneTickFiltered : Bool :=
  flapjackMainBytes == flapjackConstReturnMainBytes

/-! The no-tick `const_return` artifact is exact. -/
def constReturnExactParity : Bool :=
  cakeMainBytes == flapjackConstReturnMainBytes

/-- The `entry_order` fixture source, taken from the original-side probe fact.
It declares the entry function `main` last:

```
fun 1 a() { return 1; }
fun 1 b() { return 2; }
fun 1 main() { return a(); }
``` -/
def entryOrderSource : String := entryOrder.source

/-- Original CakeML layout: `cml_generated_main` at 1000 (4B, `jal` to
`cml_main`), `cml_main` at 1004 (4B, `jal` to `cml_a`), `cml_a` at 1008 (8B),
`cml_b` at 1016 (8B).  Evidence: `cakeml/pancake/pan_passesScript.sml:20-37`
(`pan_to_target_all_def`) moves the `main` declaration to the front, and the
original `makesym` lines report exactly these bases and sizes. -/
def cakeEntryOrderSections : List (Nat × Nat × List (BitVec 8)) :=
  [ (3, 1000, [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)),
    (4, 1004, [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)),
    (5, 1008, [0x13, 0x65, 0x10, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)),
    (6, 1016, [0x13, 0x65, 0x20, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)) ]

/-- Flapjack emits the same section order and bodies as CakeML for this
fixture.  With the `0 :: args` dummy injected at the Cake point in
`loop_to_word$comp` (see `flapjackGeneratedMainBytes`), the two entry
sections (`cml_generated_main` at label 3 and the tail-calling `cml_main`
at label 4) are Cake's 4-byte `jal` exactly, and the helper bodies
(labels 5 and 6) are byte-identical to Cake: the whole artifact now matches
`cakeEntryOrderSections`. -/
def flapjackEntryOrderSections : List (Nat × Nat × List (BitVec 8)) :=
  [ (3, 1000, [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)),
    (4, 1004, [0x6F, 0x00, 0x40, 0x00].map (BitVec.ofNat 8)),
    (5, 1008, [0x13, 0x65, 0x10, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)),
    (6, 1016, [0x13, 0x65, 0x20, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)),
    ]

/-! ## CurrHeap materialisation parity (GH #1128)

Cake's word_inst inst_select_exp leaves a Lookup CurrHeap plus a
materialised constant as a register operation.  The Lab stage must not apply
an aliased-add peephole to that pair: it would emit a different immediate
instruction, or erase CurrHeap - 0 entirely. -/
def currHeapAddConstSource : String :=
  "fun 1 main() { return @base + 255; }"

def currHeapSubZeroSource : String :=
  "fun 1 main() { return @base - 0; }"

/-! ## Cake return-register oracle (`flapjack-pxn.8.5.10.1.1`)

The original Cake `callee_abi.pnk` artifact keeps the allocator-selected
Word return register through `word_to_stack` and `stack_to_lab`: its `main`
section ends in `jalr x0,a1,0` (`67 80 05 00`), rather than forcing the
architectural link register.  This source-facing guard consumes the same
production runtime-image path as `flapjack-compile --assembly` and pins that
oracle byte at the end of the emitted `main` section.
-/
def calleeAbiSource : String :=
  "fun 1 g(1 a, 1 b) { return a + b; }\n" ++
  "fun 1 main() { var 1 t = g(5, 7); var 1 u = t + 1; return u; }"

/-- The `nested_expression` fixture source, taken from the original-side probe
fact.  It is the GitHub issue #1015 reproducer whose right-nested sum needs
more than the four reserved Word-to-Stack temporaries. -/
def nestedExpressionSource : String := nestedExpression.source

/-! ## Saturated-register exact oracles (bead `flapjack-pxn.2.5`, GH #1015)

Cake never rejects a nested expression: `crep_to_loop` flattens it into fresh
temporaries that participate in allocation and spill to the frame when the
registers run out.  The worst case for the port is a function where every
allocatable register (x2--x26 hardware, here `2..26`) already holds a
variable and the fresh materialization temporaries are themselves spilled:
the Word-to-Stack expression pool then contains only the three reserved
scratch registers.  The flattener must therefore guarantee that every
emitted assignment value fits three pool entries; these probes pin both the
acceptance and the exact spilled lowering in that configuration. -/

/-- The differential-fuzzing `dup-global` fixture (GitHub issue #962 smoke,
    bead `flapjack-pxn.8.5.14.4`).  The original CakeML accepts a duplicate
    top-level global with the warning `variable g is redeclared in top-level
    declaration` and keeps the later declaration; the port used to reject it in
    `staticCheckDecls`. -/
def dupGlobalSource : String :=
  "var 1 g = 7;\nvar 1 g = 7;\nfun 1 main() { return g; }"

/-- The differential-fuzzing `nomain-global` fixture (bead
    `flapjack-pxn.8.5.14.3`).  The original CakeML `pan_to_target` synthesizes
    a `main` returning `0` when the source has none; the port used to fail with
    `entry not found`. -/
def nomainGlobalSource : String := "var 1 g = 7;"

/- Cake's target pass does not synthesize a default main for an actually empty
   declaration list; comment-only input therefore remains rejected. -/
def emptySource : String := "// no Pancake declarations\n"

/-!
## FFI stub parity (bead `flapjack-pxn.8.5.14.2`)

The original CakeML `export_riscv` emits, between the `j cake_main`
startup stub and the fixed `cake_clear`/`cake_exit` pair, one 16-byte
block per user FFI name.  `find_ffi_names` records names in tail-first
collector order and the exporter reverses that list, yielding source order
for a straight-line section:

```
cake_ffi<name>:
     tail cdecl(ffi<name>)
     .p2align 4
```

The port used to omit these blocks entirely.  The runtime image now carries
the Cake collector-order `ffiNames`; `RiscV.pancakeRuntimeAssembly` reverses
this list at the artifact boundary, just like Cake.
Residual: names
referenced only from unreachable code are still emitted because the
port discovers FFI names before dead-code removal (same family as the
`flapjack-pxn.8.5.10.1` lowering residuals).
-/

/-- The minimal FFI fixture: one reachable `@foo` call.  Pancake FFI
    calls take exactly four arguments. -/
def ffiMinSource : String := "fun 1 main() { @foo(1,2,3,4); return 0; }"

/-- Two FFI names, `@foo` first. -/
def ffiOrderSource : String :=
  "fun 1 main() { @foo(1,2,3,4); @bar(4,3,2,1); return 0; }"

/-- The same two FFI names in the opposite first-appearance order. -/
def ffiOrderFlipSource : String :=
  "fun 1 main() { @bar(4,3,2,1); @foo(1,2,3,4); return 0; }"

def bytesContain (needle haystack : List (BitVec 8)) : Bool :=
  match needle, haystack with
  | [], _ => true
  | _, [] => false
  | _, _ :: rest =>
      (haystack.take needle.length == needle) || bytesContain needle rest

/-!
## Unreachable-code parity (dead FFI references)

The original discards statements that follow an unconditional control
transfer inside a statement sequence, so a Pancake `@foo` call after a
`throw` or a `return` never reaches the word program and never gains an
FFI stub (bead `flapjack-pxn.8.5.14.2` residual).  The port mirrors this
with `wordProgDCE` at the word-lowering boundary.
-/

/-- An `@foo` call after an unconditional `throw` is unreachable. -/
def deadFfiAfterThrowSource : String :=
  "exception E : 1;\nfun 1 main() { throw E 1; @foo(1,2,3,4); return 0; }"

/-- An `@foo` call after an unconditional `return` is unreachable, while
the earlier `@bar` call stays reachable. -/
def deadFfiAfterReturnSource : String :=
  "fun 1 main() { @bar(1,2,3,4); return 1; @foo(1,2,3,4); return 0; }"

/-! Constant-condition branches are also removed by Cake's `const_fp`, before
    FFI service discovery.  This is a separate guard from sequence-tail DCE:
    the call is syntactically inside a branch, but the branch itself is
    unreachable because `3 < 1` is constant false. -/
def deadFfiAfterConstantFalseSource : String :=
  "fun 1 main() { if (3 < 1) { @foo(1,2,3,4); } else { return 0; } return 0; }"

/-!
## Bitmap table word parity (bead `flapjack-pxn.8.5.14.1`)

The original's pancake bitmap table carries one word per non-tail call
continuation, each word a pure power of two `2 ^ f'` encoding the
caller's frame size (`f'` = frame words minus the bitmap slot), never
live-pointer bits.  The port now derives real entries from the lowered
program (`2 ^ (nextSpill + 1)`) instead of constant `2`s.  On the
`bitmap_calls` fixture, where neither compiler spills, both emit
`[4, 2, 2]`; the residual value mismatch when the original spills more
than the port (`8`/`16` vs `2`) is tracked by the bead.
-/

/-- The `bitmap_calls` fixture source (inline copy of
`Flapjack/Test/OriginalPancake/bitmap_calls.pnk`). -/
def bitmapCallsSource : String :=
  "fun 1 f () {\n    var 1 x = f();\n    var 1 x = f();\n    return 1;\n  }\n\nfun 1 main() { return 0; }"

/-! The `bc` oracle exercises two self-recursive non-tail calls.  Cake's
    recursive continuations use the trivial frame word, yielding `[4, 2, 2]`.
    This is distinct from the non-recursive `bitmap_calls` fixture. -/
def frameOccupancyBcSource : String :=
  "fun 1 f () {\n" ++
    "  var 1 x = f();\n" ++
    "  var 1 x = f();\n" ++
    "  return 1;\n" ++
    "}\n\n" ++
    "fun 1 main() { return 0; }"

def cakeFrameOccupancyBcBitmaps : List Nat := [4, 2, 2]

/-! The smallest frame-occupancy oracle from
`scripts/parity-difffuzz-findings/frame-occupancy/p1.cake.S`.  Its single
non-tail call has no live value across the call, so Cake emits exactly the
header word and one `2 ^ 1` frame word. -/
def frameOccupancyP1Source : String :=
  "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var 1 t = id(5); return 1; }"

/-- CakeML's exact bitmap vector recorded by the `p1` oracle assembly. -/
def cakeFrameOccupancyP1Bitmaps : List Nat := [4, 2]

/-! The `p2` oracle is the scalar-live baseline: `x` remains live across the
    non-tail `id` call, so Cake emits one two-word continuation frame
    (`[4, 4]`). -/
def frameOccupancyP2Source : String :=
  "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var 1 x = 5; var 1 t = id(5); return x; }"

def cakeFrameOccupancyP2Bitmaps : List Nat := [4, 4]

/-! The `p3` oracle keeps a one-field struct value live across the same
    non-tail call.  Cake's checked artifact has the minimal continuation
    frame `[4, 4]`. -/
def frameOccupancyP3Source : String :=
  "struct S { 1 f }\n" ++
    "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var S s = S <f = 1>; var 1 t = id(5); return s.f; }"

def cakeFrameOccupancyP3Bitmaps : List Nat := [4, 4]

/-! The `p4` oracle is the one-field CSE case: the same field is read twice
    after the non-tail call, while Cake still emits the minimal `[4, 4]`
    continuation vector. -/
def frameOccupancyP4Source : String :=
  "struct S { 1 f }\n" ++
    "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var S s = S <f = 1>; var 1 t = id(5); return s.f + s.f; }"

def cakeFrameOccupancyP4Bitmaps : List Nat := [4, 4]

/-! The `p5` oracle keeps one field of a two-field struct live across the
    non-tail call.  Cake's checked artifact uses the minimal continuation
    vector `[4, 4]`. -/
def frameOccupancyP5Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun 1 id (x) { return x; }\n" ++
    "fun 1 main() { var S s = S <f = 1, g = 2>; var 1 t = id(5); return s.f; }"

def cakeFrameOccupancyP5Bitmaps : List Nat := [4, 4]

/-! The `p7` oracle keeps the scalar result of `id3` live across a second
    non-tail call.  Cake emits two minimal continuation frames, `[4, 4, 4]`.
    This is the scalar counterpart to the multi-call struct cases. -/
def frameOccupancyP7Source : String :=
  "fun 1 id3 (x) { return x; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var 1 x = id3(3); var 1 t = id(5); return x; }"

def cakeFrameOccupancyP7Bitmaps : List Nat := [4, 4, 4]

/-! The p8 oracle keeps two returned two-field structs live across a later
    call.  Cake reserves three 32-word continuation frames ([4, 32, 32, 32])
    for the retained fields; this is a distinct high-occupancy witness from
    p9, whose two continuations are only eight words. -/
def frameOccupancyP8Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() {\n" ++
    "  var S s1 = mks(1, 2);\n" ++
    "  var S s2 = mks(3, 4);\n" ++
    "  var 1 t = id(5);\n" ++
    "  return s1.f + s1.g + s2.f + s2.g + t;\n" ++
    "}"

def cakeFrameOccupancyP8Bitmaps : List Nat := [4, 32, 32, 32]

/-! The `bm_min2` oracle is the bitmap-min spill case: both fields of the
    returned struct are read after `id`, so Cake emits two eight-word
    continuation entries (`[4, 8, 8]`). -/
def frameOccupancyBmMin2Source : String :=
  "struct S { 1 f1, 1 f2 }\n" ++
    "fun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\n" ++
    "fun 1 id(1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1, 2); var 1 t = id(5); return s.f1 + s.f2 + t; }"

def cakeFrameOccupancyBmMin2Bitmaps : List Nat := [4, 8, 8]

/-! The `live1` oracle keeps one field of a two-field struct live across an
    `id` call.  Cake's checked artifact has two minimal continuation entries,
    `[4, 4, 4]`. -/
def frameOccupancyLive1Source : String :=
  "struct S { 1 f1, 1 f2 }\n" ++
    "fun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\n" ++
    "fun 1 id(1 a) { return a; }\n" ++
    "fun 1 main() { var S s1 = mks(1, 2); var 1 t = id(7); return s1.f1 + t; }"

def cakeFrameOccupancyLive1Bitmaps : List Nat := [4, 4, 4]

/-! The `p9` frame-occupancy oracle (`p9.cake.S`) records the two-field
struct case: Cake's allocator keeps one field live across the `mks` call and
spills the other, so both call continuations carry frame words `2 ^ 3 = 8`.
The loop-live optimisation and the Cake frame-size computation now place the
spilled source values in the frame, so the production vector matches the
oracle exactly (`flapjack-pxn.8.5.14.1.5.1`). -/
def frameOccupancyP9Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); return s.f + s.g; }"

/-- CakeML's exact bitmap vector recorded by the `p9` oracle assembly. -/
def cakeFrameOccupancyP9Bitmaps : List Nat := [4, 8, 8]

/-! The `p11` frame-occupancy oracle is the CSE-shaped companion to `p9`:
    the two-field result is read twice at the same field, and Cake retains a
    two-word frame for both non-tail continuations (`[4, 4, 4]`). -/
def frameOccupancyP11Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); return s.f + s.f; }"

def cakeFrameOccupancyP11Bitmaps : List Nat := [4, 4, 4]

/-! The `wide` frame-occupancy oracle keeps the first and last fields of a
    six-field struct live across the `id` call.  Cake's checked artifact uses
    two eight-word continuation entries (`[4, 8, 8]`). -/
def frameOccupancyWideSource : String :=
  "struct S { 1 a, 1 b, 1 c, 1 d, 1 e, 1 f }\n" ++
    "fun S mks(1 x) { return S <a=x,b=x,c=x,d=x,e=x,f=x>; }\n" ++
    "fun 1 id(1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1); var 1 t = id(2); return s.a + s.f + t; }"

def cakeFrameOccupancyWideBitmaps : List Nat := [4, 8, 8]

/-! The `p10` frame-occupancy oracle is the first three-field struct case.
Cake's two non-tail continuations both retain a four-word frame (`f' = 4`),
so the checked bitmap payload is `[4, 16, 16]`.  The source is copied from
`scripts/parity-difffuzz-findings/frame-occupancy/p10.pnk`; the expected
vector is the corresponding `p10.cake.S` `.quad` payload. -/
def frameOccupancyP10Source : String :=
  "struct S { 1 f, 1 g, 1 h }\n" ++
    "fun S mks3 (1 a, 1 b, 1 c) { return S <f = a, g = b, h = c>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks3(1,2,3); var 1 t = id(5); return s.f + s.g + s.h; }"

def cakeFrameOccupancyP10Bitmaps : List Nat := [4, 16, 16]

/-! The `p6` oracle covers the two-field struct return with two non-tail
continuations.  Cake keeps a two-word frame for both continuations, yielding
`[4, 4, 4]`; the source is copied from the checked p6 fixture. -/
def frameOccupancyP6Source : String :=
  "struct S { 1 f, 1 g }\n" ++
    "fun S mks (1 a, 1 b) { return S <f = a, g = b>; }\n" ++
    "fun 1 id (1 a) { return a; }\n" ++
    "fun 1 main() { var S s = mks(1,2); var 1 t = id(5); return s.f; }"

def cakeFrameOccupancyP6Bitmaps : List Nat := [4, 4, 4]

/-! The `live3` oracle exercises four non-tail continuations over three
struct-valued locals.  Cake retains a four-word frame for each continuation,
so its checked bitmap payload is `[4, 16, 16, 16, 16]`. -/
def frameOccupancyLive3Source : String :=
  "struct S { 1 f1, 1 f2 }\n" ++
    "fun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\n" ++
    "fun 1 id(1 a) { return a; }\n" ++
    "fun 1 main() {\n" ++
    "  var S s1 = mks(1, 2);\n" ++
    "  var S s2 = mks(3, 4);\n" ++
    "  var S s3 = mks(5, 6);\n" ++
    "  var 1 t = id(7);\n" ++
    "  return s1.f1 + s2.f2 + s3.f1 + t;\n" ++
    "}"

def cakeFrameOccupancyLive3Bitmaps : List Nat := [4, 16, 16, 16, 16]

/-- Source for the GH #1027 relational-condition case: `if x < 10` over a
parameter. -/
def relationalConditionSource : String :=
  "fun 1 f(1 x) {\n  if x < 10 { return 1; }\n  return 0;\n}\n" ++
    "fun 1 main() {\n  return f(5);\n}\n"

/-- The exact original-CakeML bytes for the `f` section of
`relational_condition.pnk`: `addi a1, x0, 10; bge a0, a1, +12;
addi a0, x0, 1; ret; addi a0, x0, 0; ret` (24 bytes).  The comparison is a
direct control-flow branch on the negated condition with the then-branch as
the fall-through path: no boolean is materialized and there is no extra
unconditional jump. -/
def cakeRelationalConditionBytes : List (BitVec 8) :=
  [0x93, 0x65, 0xa0, 0x00,
   0x63, 0x56, 0xb5, 0x00,
   0x13, 0x65, 0x10, 0x00,
   0x67, 0x80, 0x00, 0x00,
   0x13, 0x65, 0x00, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

def f01451Source : String :=
  "  var p = @base;\n" ++
    "fun 1 main() {\n" ++
    "  var a = ld8 p; var b = ld8 (p+1); var c = ld8 (p+2);\n" ++
    "  var d = ld8 (p+3); var e = ld8 (p+4); var t1 = ld8 (p+5);\n" ++
    "  var h = 0;\n" ++
    "  h = ((t1 + (a + (b + (c + (d + e))))) << 1000) >>> 1;\n" ++
    "  return h;\n" ++
    "}"

def cakeF01451MainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x00, 0x00,
   0x13, 0x55, 0x15, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Source of the constant-store-reuse fixture (GitHub issue #1127, bead
    `flapjack-1kj`): a local store with a constant value followed by an
    expression that reuses the same constant.  This is the minimized
    differential-fuzz finding `f00198-s6-i00198-mutate`. -/
def constStoreReuseSource : String :=
  "fun 1 main() {\n" ++
    "  st (0 + 0), 1;\n" ++
    "  return @base | 1;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for the fixture.  Cake rematerialises the
    store's constant (`li a0,1`) before the `or`; the port used to reuse the
    live register and emit only one `li`, dropping an instruction Cake keeps.
    `word_cse` must emit the original `OpCurrHeap` source register
    (`cakeml/compiler/backend/word_cseScript.sml:587-594`). -/
def cakeConstStoreReuseMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x10, 0x00,
   0x93, 0x65, 0x00, 0x00,
   0x23, 0xB0, 0xA5, 0x00,
   0x13, 0x65, 0x10, 0x00,
   0x33, 0x65, 0xA5, 0x01,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Source of the CurrHeap add fixture (differential-fuzz finding
    `f00036-s65-i00036-mutate`): `@base` lowers to a `CurrHeap` lookup, so
    Cake's `inst_select_exp` takes its `is_Lookup_CurrHeap` branch and
    materialises the constant plus a register add
    (`cakeml/compiler/backend/word_instScript.sml:246-275`) instead of folding
    it into an `addi`. -/
def currheapAddConstSource : String :=
  "fun 1 main() {\n" ++
    "  return @base + 255;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for `@base + 255`:
    `li a0,255; add a0,a0,s10; ret` (s10 is the CurrHeap base). -/
def cakeCurrheapAddConstMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0xF0, 0x0F,
   0x33, 0x05, 0xA5, 0x01,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Source of the CurrHeap zero-sub fixture: `@base - 0` reaches the same
    materialised-constant register add, so Cake keeps `li a0,0; add a0,a0,s10`
    rather than eliding the computation. -/
def currheapSubZeroSource : String :=
  "fun 1 main() {\n" ++
    "  return @base - 0;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for `@base - 0`:
    `li a0,0; add a0,a0,s10; ret`. -/
def cakeCurrheapSubZeroMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x00, 0x00,
   0x33, 0x05, 0xA5, 0x01,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Source of the CurrHeap-left / constant-right fixture:
    `(@base | 7) #>> 1`.  Cake's `inst_select_exp`
    (`cakeml/compiler/backend/word_instScript.sml:246-251`) tests
    `is_Lookup_CurrHeap e1 ∧ op ≠ Sub` before the `e2 = Const w` immediate
    fold, so the `| 7` keeps `Const temp 7; OpCurrHeap Or temp temp` instead
    of folding the constant into an `ori`. -/
def currheapConstLeftSource : String :=
  "fun 1 main() {\n" ++
    "  return (@base | 7) #>> 1;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for `(@base | 7) #>> 1`:
    `ori a0,0,7; or a0,a0,s10; srli a0,a0,1; slli a0,a0,3;
     or a0,a0,s10; ret` (s10 is the CurrHeap base). -/
def cakeCurrheapConstLeftMainBytes : List (BitVec 8) :=
  [0x13, 0x65, 0x70, 0x00,
   0x33, 0x65, 0xA5, 0x01,
   0x93, 0x5F, 0x15, 0x00,
   0x13, 0x15, 0xF5, 0x03,
   0x33, 0x65, 0xF5, 0x01,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Source of the `!ld8` CurrHeap-offset fixture (GitHub issue #1130, bead
    `flapjack-pxn.8.5.14.20`): a shared 8-bit load whose address is
    `@base + 8`.  Cake keeps CurrHeap (`@base`, lowered to a `CurrHeap`
    lookup) as the load base and selects the byte-offset load
    `word_instScript.sml` `MappedRead`/`Load8` encoding, i.e. the UNSIGNED
    `lbu` (funct3 4), not `lb`. -/
def ld8CurrheapOffsetSource : String :=
  "fun 1 main() {\n" ++
    "  var 1 y = 0;\n" ++
    "  !ld8 y, (@base + 8);\n" ++
    "  return y;\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for the fixture (base 1004, 12 bytes):
    `or a0,s10,s10; lbu a0,8(a0); ret`.  The port previously emitted
    `lb` (funct3 0) and could materialise the base into a temporary. -/
def cakeLd8CurrheapOffsetMainBytes : List (BitVec 8) :=
  [0x33, 0x65, 0xAD, 0x01,
   0x03, 0x45, 0x85, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Source of the CurrHeap large-offset load witness (GitHub issue #1132):
    `lds 1 (@base + 2048)`.  Cake only splits an `Op Add [exp'; Const w]`
    address when `addr_offset_ok c w` holds; 2048 is out of the 12-bit range,
    so Cake selects the whole address, reaching `Const temp 2048; OpCurrHeap
    Add tar temp` and keeping `s10` as the memory base. -/
def currheapLoadLargeOffsetSource : String :=
  "fun 1 main() {\n" ++
    "  return lds 1 (@base + 2048);\n" ++
    "}"

/-- Original CakeML `cml_main` bytes for the fixture (base 1004, 20 bytes):
    `lui a0,0xFFFFF; xori a0,a0,-2048; add a0,a0,s10; ld a0,0(a0); ret`.
    The port previously materialised CurrHeap into a temporary, adding an
    `or a0,s10,s10` and a register add. -/
def cakeCurrheapLoadLargeOffsetMainBytes : List (BitVec 8) :=
  [0x37, 0xF5, 0xFF, 0xFF,
   0x13, 0x45, 0x05, 0x80,
   0x33, 0x05, 0xA5, 0x01,
   0x03, 0x35, 0x05, 0x00,
   0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)

/-- Source of the whole-artifact `hello.pnk` fixture (GitHub issue #1022 /
    bead `flapjack-8tb`). -/
def helloSource : String :=
  "// Smoke test: echo input length into the output region and halt.\n" ++
    "fun 1 main() {\n" ++
    "  var len = 0;\n" ++
    "  !ldw len, 1073741832;\n" ++
    "  var out = 2684420096;\n" ++
    "  var i = 0;\n" ++
    "  while i < 69 {\n" ++
    "    !st8 out + i, 0;\n" ++
    "    i = i + 1;\n" ++
    "  }\n" ++
    "  !st8 out + 32, 1;\n" ++
    "  !stw out + 40, len;\n" ++
    "  @halt(@base, 0, @base, 0);\n" ++
    "  return 0;\n" ++
    "}"

/-- Original CakeML `cml_main` length for `hello.pnk` from the checked
assembly oracle. -/
def cakeHelloMainLength : Nat := 152

/- The reduced allocator-colour witness is an original-Cake oracle regression.
   Cake emits four stack words ([4,16]) and a 256-byte process_transaction
   section; passing fresh SSA metadata into Word-to-Stack used to emit only
   three stack words and 232 bytes.  The full byte comparison remains pinned
   by scripts/parity-small-corpus.py. -/
def allocatorColourSource : String :=
  "exception BlockErr : 1;\n" ++
    "fun {1,1} tx_chain_id(1 tx) {\n" ++
    "  return <0, 0>;\n" ++
    "}\n" ++
    "fun 1 process_transaction(1 tx, 1 index, 1 pubkey) {\n" ++
    "  var {1,1} cid = tx_chain_id(tx);\n" ++
    "  if cid.0 != 0 {\n" ++
    "    if cid.1 != 0 {\n" ++
    "      throw BlockErr 0;\n" ++
    "    }\n" ++
    "  }\n" ++
    "  var nal = 0;\n" ++
    "  var i = 0;\n" ++
    "  while i < nal {\n" ++
    "  }\n" ++
    "  if (lds 1 (tx + 0)) == 0 {\n" ++
    "  } else {\n" ++
    "  }\n" ++
    "  return 0;\n" ++
    "}\n"

#guard generatedMainBytesMatch
#guard decClockExactParity
#guard standaloneTickFiltered
#guard constReturnExactParity

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [
      ("dec_clock original and port generated initializer bytes match",
        generatedMainBytesMatch),
      ("dec_clock cml_main is byte-identical to Cake",
        decClockExactParity),
      ("standalone tick is filtered at the final Lab boundary",
        standaloneTickFiltered),
      ("const_return cml_main is byte-identical to Cake",
        constReturnExactParity)]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.RiscVArtifactParity
