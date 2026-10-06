import Flapjack.Mips32.NativeSource
import Flapjack.Mips32.Run

/-! End-to-end MIPS32 runs: Pancake programs compiled by the MIPS32 backend and executed on
Ziren's ISA model (`ZirenDet.Isa`, through `mips32Next`) with CakeML's MIPS entry
convention. Each program reports its results through one FFI call, whose array bytes are
checked against values computed by hand from the Pancake source. -/
namespace Flapjack.Test.Mips32Run
open Flapjack Flapjack.Mips32

structure Case where
  name : String
  source : String
  expected : List (String × List Nat)

def arithmetic : Case where
  name := "arithmetic"
  source := "
fun 1 main() {
  var 1 x = 5;
  var 1 y = 7;
  var 1 z = x * y + 3;
  st8 @base, z;
  st8 @base + 1, x - y;
  @out(0, 0, @base, 2);
  return 0;
}"
  expected := [("out", [38, 254])]

def mixed : Case where
  name := "loops, calls, shifts, comparisons and memory"
  source := "
fun 1 fib(1 n) {
  if (n < 2) { return n; }
  var 1 a = fib(n - 1);
  var 1 b = fib(n - 2);
  return a + b;
}
fun 1 sum(1 a, 1 b, 1 c, 1 d, 1 e, 1 f, 1 g) { return a + b + c + d + e + f + g; }
fun 1 main() {
  var 1 i = 0;
  var 1 acc = 0;
  while (i < 10) { acc = acc + i * i; i = i + 1; }
  var 1 f = fib(10);
  var 1 big = 305419896;
  var 1 r = big #>> 8;
  var 1 q = r & 255;
  var 1 neg = 0 - 9;
  var 1 n1 = neg >> 1;
  var 1 n2 = n1 >>> 24;
  var 1 b1 = big << 28;
  var 1 b2 = b1 >>> 28;
  var 1 sh = n2 + b2;
  var 1 sg = 0;
  if (neg < 3) { sg = 1; }
  var 1 ug = 0;
  if (neg <+ 3) { ug = 1; }
  st @base + 8, big;
  var 1 back = lds 1 @base + 8;
  st8 @base, acc;
  st8 @base + 1, f;
  st8 @base + 2, f >> 8;
  st8 @base + 3, q;
  st8 @base + 4, sh;
  st8 @base + 5, sg;
  st8 @base + 6, ug;
  st8 @base + 7, back >> 24;
  var 1 sm = sum(1, 2, 3, 4, 5, 6, 7);
  st8 @base + 12, sm;
  @out(0, 0, @base, 13);
  return 0;
}"
  -- 285 = 0x11d, fib 10 = 55, 0x12345678 ror 8 = 0x78123456, (-5 >>> 24) + 8 = 263 = 0x107
  expected := [("out", [29, 55, 0, 0x56, 7, 1, 0, 0x12, 0x78, 0x56, 0x34, 0x12, 28])]

def check (c : Case) : Except String Unit := do
  let out ← match NativeSource.compile c.source with
    | .error e => .error (NativeSource.sourceErrorDescription e)
    | .ok out => pure out
  let some (bytes, _, config) := out.artifact | .error "backend compilation failed"
  let names := Run.ffiNamesOf config
  let outcome := Run.run {} names (fun _ _ array => array) 200000 0 [] (Run.initialState {} bytes)
  unless outcome.stop == .halted do
    .error s!"stopped with {repr outcome.stop} after {outcome.steps} steps"
  let calls := outcome.calls.map fun call => (call.name, call.array.map BitVec.toNat)
  unless calls == c.expected do
    .error s!"FFI calls {calls}, expected {c.expected}"

def runChecks : IO Bool := do
  let mut ok := true
  for c in [arithmetic, mixed] do
    match check c with
    | .ok () => IO.println s!"PASS MIPS32 on Ziren's ISA model: {c.name}"
    | .error e =>
      IO.eprintln s!"FAIL MIPS32 on Ziren's ISA model: {c.name}: {e}"
      ok := false
  pure ok

end Flapjack.Test.Mips32Run
