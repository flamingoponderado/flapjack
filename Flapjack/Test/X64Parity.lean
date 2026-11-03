import Flapjack.X64.NativeCLIAdapter

/-! x86-64 source-to-assembly parity with the original CakeML Pancake compiler.

Each case under `scripts/x64/parity/` is a Pancake source `.pnk`, the exact GNU
x86-64 assembly expected from the original compiler in `<case>.cake.S`, and the
lowercase hex of that assembly's `.byte` payload in `<case>.cake.hex`.  The
`.cake.S` files were produced by

```sh
cakeml/developers/bin/cake --pancake --target=x64 < <case>.pnk
```

The checked-in fixtures let `lake test` compare the executed Flapjack x86-64
driver without requiring a local CakeML binary.  `scripts/x64/check-parity.py`
regenerates or re-checks the fixtures against the original compiler when it is
available. -/
namespace Flapjack.Test.X64Parity
open Flapjack

def cases : List String :=
  ["01_return", "02_arith_reg", "03_arith_imm", "04_shifts", "05_shifts_reg",
   "06_control", "07_calls", "08_globals", "09_memory", "10_addcarry",
   "11_globals_many", "12_locals_many", "13_ffi", "14_mul", "15_bitmask",
   "16_loadstore_sizes", "17_large_consts", "18_many_args", "19_loop_large",
   "20_ffi_multi", "22_addcarry_chain", "23_shift_reg", "24_rotate", "25_deep"]

def expectedHex (assembly : String) : String :=
  let lines := assembly.splitOn "\n"
  let payloads := lines.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.startsWith ".byte" then
      some ((line.drop 5).toString.splitOn "," |>.filterMap fun byte =>
        let byte := byte.trimAscii.toString
        if byte.startsWith "0x" then
          let digits := (byte.drop 2).toString.toLower
          if digits.length == 2 then some digits else none
        else none)
    else none
  String.intercalate " " (payloads.flatten) ++ "\n"

def check (name : String) : IO (Option String) := do
  let source ← IO.FS.readFile s!"scripts/x64/parity/{name}.pnk"
  let expectedAssembly ← IO.FS.readFile s!"scripts/x64/parity/{name}.cake.S"
  let expectedBytes ← IO.FS.readFile s!"scripts/x64/parity/{name}.cake.hex"
  match X64.NativeCLI.output .assembly source with
  | .error message => pure (some s!"assembly: {message}")
  | .ok (_, assembly) =>
      if assembly != expectedAssembly then
        pure (some "assembly differs from the original CakeML output")
      else
        match X64.NativeCLI.output .hex source with
        | .error message => pure (some s!"hex: {message}")
        | .ok (_, hex) =>
            if hex != expectedBytes then
              pure (some s!"hex bytes differ (got {hex.length} chars, expected {expectedBytes.length})")
            else if expectedHex expectedAssembly != expectedBytes then
              pure (some "fixture error: .cake.hex does not match .cake.S")
            else
              pure none

def runChecks : IO Bool := do
  let mut ok := true
  for name in cases do
    match ← check name with
    | none => IO.println s!"PASS x86-64 parity with CakeML: {name}"
    | some error =>
        IO.eprintln s!"FAIL x86-64 parity with CakeML: {name}: {error}"
        ok := false
  pure ok

end Flapjack.Test.X64Parity
