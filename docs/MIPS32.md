# MIPS32 (Ziren) backend

Flapjack can compile Pancake to little-endian MIPS32r2, the guest ISA of the
[Ziren](https://github.com/ProjectZKM/Ziren) zkVM. The backend reuses the whole
Pancake-to-labLang compiler, which is generic in the word width, at width 32.
It adds a MIPS32 assembler target, whose correctness is proved against Ziren's
executable Lean model of the ISA.

The trust base differs from the RISC-V backend's; see `docs/SOUNDNESS.md`, item 9.

## Semantics

The machine model is `ZirenDet.Isa`, from Ziren's `crates/fv/lean4`. It is a Lake
dependency (`lakefile.toml`) pinned to a Ziren commit. Ziren describes it as
little-endian byte memory, architectural delay slots, `$zero` as a sink, and
separate `HI`/`LO`. The backend's step function `mips32Next`
(`Flapjack/Compiler/Encoders/Mips32/Target.lean`) works as follows:

- It fetches the instruction word at `pc` from memory, decodes it with
  `Isa.decode` and runs it with `Isa.exec`.
- It runs a branch together with its delay slot when the branch leaves the
  sequential path, as CakeML's MIPS64 `mips_next` does. So the asm-level states
  are never inside a delay slot.
- An undecodable word stops the machine.

## Code generation

`mips32Ast` follows CakeML's MIPS64 target (`mips_targetScript.sml`), narrowed to
32 bits:

- Constants take at most `LUI`/`ORI`.
- 64-bit operations become their 32-bit forms.
- Rotations use the MIPS32r2 `ROTR`/`ROTRV` instructions.
- Every branch or jump has a `nop` in its delay slot. The exception is the long
  jump, which restores `$ra` in the `JR` delay slot, as CakeML does.
- Ziren has no `BLTZAL`, so CakeML's "link without branching" idiom becomes `BAL 1`.
- `Loc` always uses its long form.

Registers, immediate ranges and the register names (`mips_names`) are CakeML's
MIPS values. The backend configuration (`Mips32Config/BackendConfig.lean`) is
CakeML's `mips_backend_config` with two changes: little-endian data, and the
32-bit data layout of CakeML's `arm7`/`ag32` targets.

The encoder (`Mips32/Encode.lean`) writes standard MIPS32 instruction words. It
proves that Ziren's decoder reads every emitted instruction back. The emitted
encodings are also pinned against LLVM in `Flapjack/Test/Mips32Encoding.lean`,
which `scripts/mips32/check-encoder-fixtures.py` regenerates with `llvm-mc`.

## Proofs

`Flapjack/Mips32/TargetProof/` proves `mips32_encoder_correct`, which is
`encoder_correct mips32Target`. The files are:

- `Agree`: removes interference environments generically.
- `Simulate`: lifts a run to the assertion chains of `encoder_correct`.
- `Step`: straight-line runs.
- `Branch`: sequences that end in a branch and its delay slot.
- `Arith`, `Mem` and `Control`: one case per asm constructor.

`Mips32Config/Proofs.lean` discharges `mc_conf_ok`, `mc_init_ok` and
`backend_config_ok` for `isMips32MachineConfig`.

`Pancake/Proofs/PanToTarget/Mips32*.lean` instantiates the width-generic
`pan_to_target_compile_semantics` at MIPS32 and carries it to the CLI:

- `Mips32Instance`: the instantiation.
- `Mips32InstanceExecutable` and `Mips32Source`: the callable compiler call.
- `Mips32NativeSourceCorrect`: the parser-backed driver.
- `Mips32NativeCLICorrect`: `mips32CLIOutput_correct`.

## Output and integration

`flapjack-compile --target=mips32` accepts the usual output modes.

`--assembly` (the default) emits a `mipsel` GNU assembler file modelled on
CakeML's `export_mips`:

- `cml_main` passes the entry address in `$a0`, the heap start in `$a1`, the
  stack start in `$a2` and the stack end in `$a3`.
- Each FFI stub, `cake_clear` and `cake_exit` is a 16-byte block before
  `cake_main`. The blocks jump to `ffi<name>` and `cml_exit`.
- The file exports `cml_heap`, `cml_stack` and `cml_stackend` for the runtime to
  fill.

The file assembles with `clang --target=mipsel-linux-gnu -march=mips32r2 -x
assembler-with-cpp`.

Running the code in a Ziren guest needs a runtime that the guest supplies. It
must provide:

- memory for the heap and stack;
- the `ffi<name>` functions, for example mapping output to Ziren's `WRITE` or
  `COMMIT` syscalls and input to `HINT_READ`;
- `cml_exit`, mapped to `HALT`.

Flapjack provides none of this runtime and does not verify it.

`Flapjack/Mips32/Run.lean` is a test harness, not a runtime. It runs compiled
images on Ziren's model with the CakeML entry convention and simulated FFI
calls, and `Flapjack/Test/Mips32Run.lean` uses it.
