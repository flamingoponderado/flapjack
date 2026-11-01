# x86-64 backend: proof status and continuation notes

This note records where the x86-64 port's compiler-correctness proof stands so a
fresh session can continue without reconstructing the history. It is Flapjack
infrastructure, not a HOL mapping document.

## Verified

Every gate in `.github/workflows/lean_action_ci.yml` passes on this branch at
its current head (this note only adds documentation on top of the code):

* `lake build Flapjack` — 6491 jobs.
* `lake test` — exit 0.
* `scripts/check-warnings.sh` — 0 non-test warnings.
* `scripts/check-native-decide.sh` — 9 `native_decide` uses, all allowlisted;
  `check-native-trust.py` finds no `bv_decide`, `ofReduceBool` or
  `trustCompiler` use.
* `scripts/check-hol-refs.py` — 7645 `@[hol]` references checked.
* `scripts/check_hol_theorem_map.py` — 10248 declarations, all 3532 Proofs
  theorems mapped.
* `scripts/check_hol_ref_export.py` — 7645 reviewed theorem-map rows match
  their elaborated attributes (run through `python3`; the file is not
  executable).
* HOL reference unit tests (`test*hol*.py`, 580 tests), RISC-V regression unit
  tests (`test_riscv_*.py`, 357 tests), and `scripts/l3/check-native-model.py`
  (96 tests).
* `scripts/check-parity-goldens.py`, `scripts/check-cli-no-depth.py`,
  `scripts/pan-to-crep-coverage-report.py --check`,
  `scripts/parity-small-corpus.py --flapjack-only` (166 programs, 0 failures),
  `scripts/check-frame-occupancy-parity.py` (17 fixtures),
  `scripts/check-allocator-parity.py` (77 fixtures), and both pinned guest
  builds (`check-guest-parity.py`, accelerated and software).

Plus the two x86-64-specific checks:

* Machine-code parity: `scripts/x64/check-parity.py --cake <cake>` passes on all
  24 fixtures in `scripts/x64/parity/`. The prebuilt pinned-revision compiler at
  `/var/tmp/flapjack-pinned-build-check/cake` reproduces every checked-in
  `.cake.S`; `cakeml/developers/bin/cake` is not built in this checkout.
* Executed-path parity: `lake exe flapjack-compile --target=x64 --pancake` on each
  `scripts/x64/parity/*.pnk` produces byte-identical assembly to that same cake.
* `scripts/x64/fuzz.py` distinguishes an expected input rejection (cake prints
  `### ERROR: ...` and exits nonzero) from an oracle failure (any other nonzero
  exit, or a signal), and fails when fewer than `--min-compared` programs were
  actually compared, so a run cannot pass with no comparisons.
  Differential fuzz and a corpus run over `cakeml/pancake/**/*.sml` passed in an
  earlier session (1500 programs; 244 programs / 87 accepted, 0 failures).

Axiom footprint of the top theorems (`#print axioms` on `x64EncoderCorrect`,
`x64NativeSourceCompile_correct` and `x64CLIOutput_correct`): exactly `propext`,
`Classical.choice`, `Quot.sound`.  Nothing in the x86-64 chain rests on native
computation.  An earlier version used `bv_decide` in `le32_bytes`, `le64_bytes`,
`readXmm_writeXmm_self`, `subFlags_zf`, `writeXmm_low32` and the two
`MachineIeee/SignBits` lemmas; `scripts/check-native-trust.py` (run from
`scripts/check-native-decide.sh`) rejects `bv_decide` outright, so each was
reproved by bit-index case analysis.  See the "Bit-index proofs" section below.

### Encoder correctness

`x64EncoderCorrect : encoderCorrect x64Target` in `Machine/Complete.lean` covers
`target_ok` plus all 42 instruction cases, each in its own module under
`Machine/`:

* `SkipCase` — `case_skip`; `ControlCase` — `case_jump`;
  `VacuousCase` — `case_call`, `case_div`, `case_fpFma` (never emitted);
  `JumpRegCase` — `case_jumpReg`; `LocCase` — `case_loc`.
* `ConstCase` — `case_const`; `ArithBinopCase` — `case_binopRR`, `case_binopRI`;
  `ShiftCase` — `case_shiftImm`, `case_shiftReg`; `MulCase` — `case_longMul`;
  `DivCase` — `case_longDiv`; `CarryCase` — `case_addCarry`, `case_addOverflow`,
  `case_subOverflow`.
* `MemCase` — the eight `load`/`load8`/`load16`/`load32` and
  `store`/`store8`/`store16`/`store32` cases (via the `case_memLoadSpine` /
  `case_memStoreSpine` spines).
* `FpCase` — all fifteen `fp` cases: `fpLess`, `fpLessEqual`, `fpEqual`, `fpMov`,
  `fpAbs`, `fpNeg`, `fpSqrt`, `fpAdd`, `fpSub`, `fpMul`, `fpDiv`, `fpMovToReg`,
  `fpMovFromReg`, `fpToInt`, `fpFromInt`.
* `JumpCmpCase` — `case_jumpCmp_reg`, `case_jumpCmp_imm`.

No `sorry`/`admit` anywhere under `Machine/`, `Backend/X64Config/`, or
`PanToTarget/X64Instance.lean`.

### Backend configuration and the top theorem

* `Flapjack/Compiler/Backend/X64Config/BackendProof.lean` —
  `x64NameInv`, `x64NameInv_map`, `x64NameMap_inv`, `findNameSpt_x64Names`,
  `toInt_ofNat_small`, `x64BackendConfigOkRaw`,
  `backendConfigOk_pancakeX64BackendConfig`, `x64BackendConfigOk`.
* `Flapjack/Compiler/Backend/X64Config/Proofs.lean` — `isX64MachineConfig`
  (`lenReg=6`, `ptrReg=7`, `len2Reg=1`, `ptr2Reg=2`,
  `calleeSavedRegs=[12,13,14]`), `x64MachineConfigOk`, `x64InitOk`.
* `Flapjack/Pancake/Proofs/PanToTarget/X64Instance.lean` —
  `x64PancakeHeapLimit_lt`, `panToTargetCompileSemanticsX64`.
* The driver chain, mirroring the MIPS32 one:
  * `X64InstanceExecutable.lean` — `panToTargetCompileSemanticsX64Executable`
    (compiler premise on the callable `compileProgMaxExecutable`).
  * `X64Source.lean` — `panToTargetCompileSemanticsX64AsmExecutable` (assembler
    config only) and `panToTargetCompileSemanticsX64Source` (compiler premise on
    `mainFirstHOL decls`, semantics of the original `decls`).
  * `X64NativeSourceCorrect.lean` — `x64NativeSourceLogicalBound`,
    `x64NativeSourceCompileDeclarations_eq`, `x64NativeSourceCompile_ok`,
    `x64NativeSourceCompile_full_result`, `x64NativeSourceCompile_correct`.
  * `X64NativeCLICorrect.lean` — `NativeX64Correctness`,
    `x64CLIOutput_correct`: a successful `X64.NativeCLI.output` prints the
    rendering of a compiled tuple satisfying `NativeX64Correctness` for the
    parsed program, which is the same level as `mips32CLIOutput_correct`.
* `Flapjack.lean` imports `Machine/MemCase`, `Machine/FpCase`,
  `Machine/JumpCmpCase`, `Machine/Complete`, `X64Config/BackendProof`,
  `X64Config/Proofs`, `PanToTarget/X64Instance`, `Misc/MachineIeee/SignBits`,
  and the four driver modules above.
* `Flapjack/CompileMain.lean` routes `--target=x64` to `X64.NativeCLI.output`.

## Model fixes

**`zadc`/`zsbb` carry (commit `3c57f074f`).** `Machine/Execute.lean`'s
`execInsn` wrote `a + b` for `.binopRR .zadc` and `.binopRI .zadc` without the
incoming carry flag, while the source `addCarry` semantics (and real x86) include
it. The clauses now special-case `.zadc`/`.zsbb` to add/subtract
`BitVec.ofNat 64 (if s.flags.cf then 1 else 0)`. The `.zsbb` *flags* still omit
the borrow, but the backend never emits `sbb`; this is noted in a comment.

**`PF` parity.** `parityByte` XOR-folded its eight low-byte bits from `false`,
so it reported *odd* parity, while x86 `PF` is set for *even* parity: a zero
result cleared the flag on hardware but set it in the model. The fold now starts
from `true`, with `parityByte_zero`/`parityByte_one` as regression facts. No case
proof changed: `targetStateRel` relates only state, pc, memory, general registers
and FP registers, never flags, and the only emitted parity branch follows
`comisd`, whose `pf` comes from `xmmUnordered`.

**Per-lane `psrlq`/`psllq` (commit `5e390bfb4`).** The SSE model shifted the
whole 128-bit register, so `psrlq`/`psllq` leaked the high lane into the low one.
`psrlqLanes`/`psllqLanes` now shift each 64-bit lane separately. `pslldq`/
`psrldq` (used by `fpToInt`) really are whole-register byte shifts, so those
clauses keep the raw `<<<`/`>>>`.

## `fp64_abs`/`fp64_negate` computation lemmas

`holFp64Abs_eq_and` and `holFp64Negate_eq_xor` (mask by `2^63 - 1` and xor with
`2^63`) live in `Flapjack/Misc/MachineIeee/SignBits.lean`, not beside the
definitions. `scripts/check-hol-refs.py` recognizes the eleven reviewed real-free
`binary_ieee`/`machine_ieee` forms by comparing each one's *body slice* against a
canonical text; the slice of a declaration runs to the next declaration it
recognizes. Adding theorems after `holFp64Negate` extended its slice, the
fail-closed group check then rejected every bit-only form in the tree, and all 15
renderings demanded `(reals_as_rational_cuts)`. Keep new declarations about those
forms out of `Flapjack/Misc/MachineIeee.lean` (a submodule is fine) or the same
cascade returns.

## Bit-index proofs (no native computation)

`scripts/check-native-trust.py` forbids `bv_decide`, so the bit-level facts are
proved by `BitVec.eq_of_getLsbD_eq` plus a case split on the bit index.  Two
traps:

* `getLsbD_append` and `getElem_append` are not `@[simp]`; rewrite the cast away
  first (`simp only [BitVec.getLsbD_cast]`) and then `rw [BitVec.getLsbD_append]`
  once per concatenation level.  `BitVec.getLsbD_and/or/xor/not/setWidth/allOnes/
  extractLsb'` are `@[simp]`, and `Nat.testBit_two_pow_sub_one` /
  `Nat.testBit_two_pow` turn the mask literals into `decide` facts.
* `Flapjack/RiscV/Model.lean` installs homogeneous `ShiftLeft`/`ShiftRight`
  instances for `BitVec width`, so an unannotated shift amount (`x <<< 96` with
  `x : BitVec 128`) elaborates as a *`BitVec`* literal through those instances
  and the core `BitVec.getLsbD_shiftLeft`/`getLsbD_ushiftRight` lemmas do not
  match.  Annotate the amount `(96 : Nat)` to get the `Nat` shift the core
  lemmas cover; `writeXmm_low32` is stated that way.
* `sub_eq_zero` needs the `AddGroup` `Sub` instance, which `BitVec` does not
  use; use `BitVec.sub_eq_iff_eq_add` instead.
* `readXmm_writeXmm_self` closes with `simp only [readXmm, writeXmm];
  bv_normalize` (`bv_normalize` is a kernel-checked rewrite tactic, not
  `bv_decide`).

## Case template (works)

`have st := x64Start _ s1 s2 ms h`; `hok := by simpa [x64Target_config] using
st.asmOk`; extract `asmOkExact` with `simp only [asmOkExact, asmInstOkExact,
asmArithOkExact/asmFpOkExact, x64Config, Bool.and_eq_true] at hok; simp at hok`
(left-nested conjunction); per-field facts from `rw [← st.upd]` +
`simp only [asmUpd, instUpd, updPc, arithUpd/fpUpd/memOp, ...]` (rewrite the
`x64Enc_*` lemma for `pc` before the register rewrites); `mem`/`memDomain`/
`fpRegs` are often `rfl` after `rw [← st.upd]`; multi-instruction bytes via
`bytesInMemory_append` (`Flapjack/Misc/BytesInMemory.lean`); decode via
`decode_bytesInMemory` + `decode_*`; close with `encoderCaseStep _ s1 s2 ms n
hdom hcode (…StepSafe…) (by intro k hk1 hk2; omega) hq`.

Gotchas: inside namespace `Flapjack.Compiler.Encoders.X64`, bare `readReg` is the
machine `X64.readReg (s) (r)`; source reads are `AsmSem.readReg r s`.
`targetStateRel` tracks only stateOk/pc/mem-on-domain/regs/fpRegs — not flags or
failed. `asmStep` supplies `¬ s2.failed`, which is how a source `assert`
success is recovered.

Other traps found while closing the remaining cases:

* Structure updates: `{ s with f := v, g := w }` on one line fails to parse; put
  the fields on following lines.
* `asmCmpOkExact` must be unfolded with `x64Config` in scope, otherwise
  `asmRegImmOkExact`'s `.imm` clause stays folded and the `validImm` extraction
  fails.
* `isTest operator = true` forces `zop = .ztest`, and `decode_binopRR_z64`
  rejects `.ztest`; use `decode_binopRR_test` for the test form (encapsulated in
  `decode_binopCmp`). The `zcmp` path requires `isTest operator = false`.
* `binopRI` immediates: `.ztest` uses `encodeInsn_binopRI_test_rax` (6 bytes,
  `rax`) or `encodeInsn_binopRI_test` (7 bytes); `.zcmp` with a one-byte
  immediate uses `encodeInsn_binopRI_83` (4 bytes), otherwise
  `encodeInsn_binopRI_rax` (6) or `encodeInsn_binopRI_81` (7).
* In `x64Enc_of_flatMap`, pass the fully `rw`-reduced byte list explicitly as the
  second argument; leaving it implicit makes the `simp` in the second subgoal
  unfold the goal before `omega` can use the length hypotheses. Discharge the
  nil check with `simp at this` once lengths are substituted.
* `Int.bmod_def` + `split_ifs` + `decide_ne_decide` is the working recipe for
  signed-comparison flag lemmas.
* `FpCase`'s `setcc_length_fp`/`x64Next_setcc_fp` are renamed copies of
  `CarryCase`'s `setcc_length`/`x64Next_setcc`; keep the suffixes when adding a
  third consumer.

## Remaining work

None of the seven items this note previously listed are open, and the x86-64 driver
now reaches the same level as the MIPS32 one (`x64CLIOutput_correct`). Possible
follow-ups, not required for this port:

* The machine model is a closed model of the emitted instruction subset, not a
  port of CakeML's L3 `x64Script.sml`. Porting the L3 state and transition
  semantics (`NextStateX64`, the `x64_ok` MXCSR/exception condition, the full
  instruction semantics) and proving `x64_encoder_correct` against it — or a
  checked refinement from the closed model — remains open. `docs/SOUNDNESS.md`
  item 11 records that the parity evidence covers emitted bytes only and cannot
  establish that connection.
* `--target=arm8` still stops at `Arm8.NativeCLI.output_ok`; an `arm8CLIOutput_correct`
  would need the ARMv8 analogue of `X64Source.lean` and `X64NativeSourceCorrect.lean`.
* Rebuild `cakeml/developers/bin/cake` from the pinned submodule revision so
  parity runs without the `/var/tmp` binary. This needs HOL4 built from the
  `HOL` submodule, not the unrelated `~/HOL` install.
