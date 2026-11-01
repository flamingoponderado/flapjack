# x86-64 backend: proof status and continuation notes

This note records where the x86-64 port's compiler-correctness proof stands so a
fresh session can continue without reconstructing the history. It is Flapjack
infrastructure, not a HOL mapping document.

## Verified

* Machine-code parity: `scripts/x64/check-parity.py --cake <cake>` passes on all
  25 fixtures in `scripts/x64/parity/`; the emitted bytes are identical to the
  original CakeML `--pancake --target=x64` frontend. Differential fuzz and a
  corpus run over `cakeml/pancake/**/*.sml` also pass (1500 programs, 244
  programs / 87 accepted, 0 failures).
* Gate-green commit: `88a697686` (`lake build Flapjack`, `lake test`,
  `scripts/check-warnings.sh`, `scripts/check-hol-refs.py`,
  `scripts/check_hol_ref_export.py` all pass).
* `encoderCorrect x64Target` constructors proved (16): `case_skip`, `case_jump`,
  `case_call` (vacuous), `case_div` (vacuous), `case_fpFma` (vacuous), `case_loc`,
  `case_jumpReg`, `case_const`, `case_binopRR`, `case_binopRI`, `case_shiftImm`,
  `case_shiftReg`, `case_longMul`, `case_longDiv`, `case_addOverflow`,
  `case_subOverflow`. Files: `Machine/SkipCase.lean`,
  `VacuousCase.lean`, `ControlCase.lean`, `JumpRegCase.lean`, `ConstCase.lean`,
  `ArithBinopCase.lean`, `ShiftCase.lean`, `MulCase.lean`, `DivCase.lean`.

## Model fix (commit `3c57f074f`)

`Machine/Execute.lean`'s `execInsn` wrote `a + b` for `.binopRR .zadc` and
`.binopRI .zadc` without the incoming carry flag, while the source `addCarry`
semantics (and real x86) include it. The clauses now special-case `.zadc` and
`.zsbb` to add/subtract `BitVec.ofNat 64 (if s.flags.cf then 1 else 0)`. The
`.zsbb` *flags* still omit the borrow, but the backend never emits `sbb`; this is
noted in a comment. All existing proofs still hold (`rfl`/`cases` unaffected).

## Remaining work

1. `case_addCarry` in `Machine/CarryCase.lean` (the file already proves
   `case_addOverflow` and `case_subOverflow`). Lowerings and semantics are
   documented in the case template below. 3, 3, and 5 instructions (n = 2, 2, 4).
2. The eight `mem` cases (`load`, `load32`, `load16`, `load8`, `store`, `store32`,
   `store16`, `store8`) — see `Machine/StepAgree.lean`
   (`x64Touched_movRM/movMR/movzxRM`, `sizeBytes`) and `MemDecodeProof.lean`
   (`movRMZ64Bytes`, `movMRZ64Bytes`, `movzxBytes`); the memory domain changes, so
   `hdom` must be derived from `x64Touched` and the source `memOp`.
3. The fifteen `fp` cases (`fpLess`, `fpLessEq`, `fpEqual`, `fpMov`, `fpAbs`,
   `fpNeg`, `fpSqrt`, `fpAdd`, `fpSub`, `fpMul`, `fpDiv`, `fpMovToReg`,
   `fpMovFromReg`, `fpToInt`, `fpFromInt`) — `execSSE` uses the same `holFp64*`
   functions as `fpUpd`, so values agree by construction.
4. `jumpCmp` reg and imm — see `ControlCase.lean` (jump/jumpReg) and
   `StepAgree.lean`'s `decode_jcc_*` lemmas.
5. Assemble `x64EncoderCorrect : encoderCorrect x64Target` in
   `Machine/Complete.lean` (model: `Flapjack/Compiler/Encoders/Arm8/Machine/Complete.lean`
   and `Flapjack/Mips32/TargetProof/Complete.lean`).
6. `Flapjack/Compiler/Backend/X64Config/BackendProof.lean`: the 27
   `backendConfigOk` conjuncts plus `x64NameInv`/`x64NameInv_map`/
   `x64NameMap_inv`/`findNameSpt_x64Names`, modelled on
   `Flapjack/Compiler/Backend/Arm8Config/BackendProof.lean`. `x64Config`'s
   `validImm` is the signed 32-bit range `[x64Min32.toInt, x64Max32.toInt]`.
7. Two prepared but uncompiled files exist untracked in the main checkout:
   `Flapjack/Compiler/Backend/X64Config/Proofs.lean` (`isX64MachineConfig` with
   `lenReg=6`, `ptrReg=7`, `len2Reg=1`, `ptr2Reg=2`, `calleeSavedRegs=[12,13,14]`,
   `x64MachineConfigOk`, `x64InitOk`) and
   `Flapjack/Pancake/Proofs/PanToTarget/X64Instance.lean`
   (`panToTargetCompileSemanticsX64`). They compile only after items 5 and 6.
   Add both plus `Machine/Complete.lean` and the case files to `Flapjack.lean`,
   then run the five gates and re-run parity.

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
