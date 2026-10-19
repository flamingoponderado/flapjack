# ARMv8 (AArch64) backend

Flapjack can compile Pancake to little-endian ARMv8 (AArch64), using CakeML's
`arm8` target. The backend reuses the whole Pancake-to-labLang compiler at word
width 64 and adds an ARMv8 assembler target.

This is a **parity-first** port. Source-to-assembly output is checked
byte-for-byte against the original CakeML compiler. On top of that, Flapjack
proves `encoderCorrect arm8Target` for a closed ARMv8 execution model covering
the emitted instruction subset, and instantiates the full
Pancake-to-target theorem at that model. This is **not** a port of CakeML's full
L3 ARMv8 semantics; the closed model and its limits are described below and in
`docs/SOUNDNESS.md`; faithful-L3 follow-ups are tracked in issue #1229.

## Code generation

- `Flapjack/Compiler/Encoders/Arm8/Encode.lean` implements the instruction
  encodings used by CakeML's `arm8_ast`: move-wide, add/sub immediate and
  shifted-register, logical immediate and shifted-register, bitfield move,
  extract, shifts, division, multiply-high/add-sub, conditional compare and
  select, add/sub with carry, loads and stores, branches and `ADR`.
  `EncodeBitMask`/`DecodeBitMasks` follow the L3-generated definitions.
- `Flapjack/Compiler/Encoders/Arm8/Target.lean` ports `arm8_ast` and `arm8_enc`
  for the instruction forms CakeML's backend emits. Constants use `MOVZ`,
  `MOVN`, a logical immediate, or four `MOVK`s; out-of-range load/store offsets
  are first added into the temporary register 26; long `Loc` values use `ADR`
  plus four `MOVK`s and an add.
- `Flapjack/Compiler/Encoders/Arm8/Configuration.lean` contains the assembler
  configuration: 32 registers, avoid registers 18/26/31, link register 30,
  `temp = 26`, and CakeML's address/byte/jump/conditional-jump/loc ranges.
- `Flapjack/Compiler/Backend/Arm8Config/` contains `arm8_names` and
  `pancakeArm8BackendConfig`, mirroring the MIPS32 configuration modules.

## Command-line use

`flapjack-compile --target=arm8 SOURCE.pnk` emits a GNU AArch64 assembly file
in CakeML's `export_arm8` frame: the `_ldrel` startup code, FFI stubs,
`cake_clear`/`cake_exit`, the code-buffer markers and the `makesym` lines.
`--hex` and `--sections` use the same compiled tuple. The startup convention is
`ret = F`, `pk = T`, matching CakeML's Pancake ARMv8 export.

## Parity evidence

`Flapjack/Test/Arm8Parity.lean` compiles the sources under
`scripts/arm8/parity/` and compares both the whole assembly text and the
code-byte hex with captured original output:

```sh
cakeml/developers/bin/cake --pancake --target=arm8 < case.pnk > case.cake.S
```

The checked-in `.cake.S` and `.cake.hex` fixtures let `lake test` run without a
local CakeML binary. `scripts/arm8/check-parity.py` regenerates or re-checks the
fixtures when the original compiler is available. During development the same
comparison covered all 244 standalone Pancake programs embedded in
`cakeml/pancake/**/*.sml` (with a synthetic `main` where needed), byte-for-byte
and including the `makesym` symbol lines.

## Theorem status

`Flapjack/Compiler/Encoders/Arm8/TargetProof.lean` ports the structural length
lemmas at the start of `arm8_targetProofScript.sml`
(`length_arm8_encode`, `length_arm8_enc`, `arm8_encode_not_nil`) and the first
semantic helpers: the word64 conjunct of `Decode_EncodeBitMask`, `mul_long`,
and the `length mod 4 = 0` half of `arm8_encoding`. They are not tagged as exact
HOL ports because HOL ranges over the full L3 `arm8$instruction` datatype and
uses HOL word/bitstring carriers, while the Lean encoder is fixed at width 64
with `Nat`/`BitVec` carriers.

The remaining helpers `lsl`, `lsr`, `asr2` and `ror` are stated with HOL's
`bitstring`/FCP rotate operations (`#>>`, `v2w`, `w2v`, `shiftr`), which
Flapjack does not yet have; porting them is a separate library task and does not
need the machine semantics.  `asr` is just HOL's library theorem
`word_asr_n2w` specialized to word64, with no ARM8-specific proof content.

The main HOL theorem `arm8_encoder_correct` is stated about CakeML's full L3
ARMv8 model (`HOL/examples/l3-machine-code/arm8/model/arm8Script.sml` and
`step/arm8_stepScript.sml`). Flapjack does not port that L3 model. Instead, the
closed subset model below proves the corresponding `encoderCorrect arm8Target`
obligation for the instructions the backend emits; the Flapjack theorem is
therefore infrastructure, not a port of the HOL theorem.

## Closed ARMv8 machine model (new)

The `Flapjack/Compiler/Encoders/Arm8/Machine/` directory adds a small,
closed ARMv8 execution model for the instruction subset that `arm8_ast`
emits (it is **not** a port of the full L3 `arm8Script.sml` model).  The decoder
is a permissive recognizer: it can also accept some real AArch64 words outside
the emitted subset (for example register-offset loads, conditional-compare
register forms, or instructions that would use `r31` as SP), and gives those
words this closed model's semantics.  The correctness proofs only cover words
that `arm8_ast`/`encodeInsn` emit; no claim is made about other accepted words.

- `State.lean`: registers, flags, memory, failure flag, aligned-PC
  well-formedness, and the `target_ok` projection.
- `Decode.lean`: a 32-bit decoder for the emitted instruction forms.
- `Execute.lean`: `execInsn` and `arm8Next`, including ARM `AddWithCarry`,
  condition codes, shifts, bitfield move, and branch PC arithmetic.
- `Target.lean`: the nonempty `HolAsmTarget` record `arm8Target`, using
  `arm8Config` and `arm8Next`.
- `TargetProof.lean`: `arm8EncOk` and the unconditional `targetOk arm8Target`
  (projection consistency), plus `Loc` offset-length monotonicity.
- `ExecuteProof.lean`: kernel-checked byte reassembly and one-step execution
  from the encoded bytes plus the per-instruction decoder inverse.
- `DecodeProof.lean`: kernel-checked `noOp` and `moveWide` decoder inverses.
- `DecodeProofSimple.lean`: kernel-checked `extractRegister` decoder inverse.
- `DecodeProofSimple2.lean`: kernel-checked decoder inverses for `shift`, `division`,
  `multiplyHigh`, `multiplyAddSub`, `addSubShiftedRegister`, `addSubCarry`,
  `conditionalSelect`, `conditionalCompareImmediate`, and `branchRegister`.
- `DecodeProofConditional.lean`: kernel-checked inverses for the conditional
  data-processing encodings (`addSubImmediate`, `logicalShiftedRegister`,
  `logicalImmediate`, `bitfieldMove`).
- `DecodeProofControl.lean`: kernel-checked inverses for `branchImmediate`,
  `branchConditional`, `address false`, and load/store.  `address false` now
  decodes both `immlo` bits, and `Encode` accepts L3's signed 21-bit ADR range;
  the page (`address true`) form reconstructs the full page-relative offset,
  but only concrete positive, negative, boundary, unaligned, and executor
  checks cover it (`Flapjack/Test/Arm8Encoding.lean`); there is no general
  inverse lemma and no step case because `arm8Ast` does not emit it.  `regsizeWord := true`
  is not recoverable from emitted bytes, so load/store inverses use the
  byte-identical `regsizeWord := false` representative.  The decoder also
  accepts sign-extending load encodings but represents every load with
  `signed := false`, so such words execute zero-extending; emitted loads are
  zero-extending.

The model is deliberately closed: unknown instruction words set `failed`
instead of being interpreted by the full L3 decoder.  The executor now uses
`rm` in `EXTR`, treats condition code 15 (NV) as always true, and follows L3's
ADR/ADRP field geometry.  It does not model the stack-pointer role of `r31`
anywhere: `readReg`/`writeReg` treat `r31` as XZR in every operand position,
including ADD/SUB-immediate, base-register, and ORR-immediate positions where
AArch64 would use SP.  Emitted code uses `r31` only in slots where AArch64
treats it as XZR (CMP's `Rd` and ORR-immediate's `Rn`), not where AArch64 would
select SP; that per-slot fact is not checked by the model.
Because the decoder is still a permissive subset recognizer, it can also accept
non-emitted words: the unsigned-offset mask can treat a CCMP-register word as
ADCS and accepts signed loads, PRFM, and bits 25:24 = 11 as unsigned loads; the
unscaled mask accepts register-offset and pre/post-index forms, signed loads,
LDTR/STTR, and LSE atomics; and the multiply-high mask accepts other variants as
`MULH`.  These words are never emitted, so the closed machine modules
(`Decode.lean`, `Execute.lean`, `Machine/`) carry no `@[hol]` tags.
All twenty instruction forms now have kernel-checked decoder inverses on the
emitted shapes.  The load-shape limits above are the only remaining gaps on
that path.
`Flapjack/Compiler/Backend/Arm8Config/BackendProof.lean` proves
`backendConfigOk arm8Config pancakeArm8BackendConfig`, and
`Flapjack/Compiler/Encoders/Arm8/Machine/Complete.lean` proves
`arm8EncoderCorrect : encoderCorrect arm8Target`. The case split is in
`Machine/SkipCase.lean`, `ControlCase.lean`, `JumpCmpCase.lean`,
`ConstCase.lean`, `ArithCase.lean`, `ShiftCase.lean`/`ShiftCaseFull.lean`,
`MulCarryCase.lean`, and `MemCase.lean`/`MemCaseFull.lean`.
`Flapjack/Pancake/Proofs/PanToTarget/Arm8Instance.lean` then instantiates
`panToTargetCompileSemantics` for ARM8 unconditionally: `backendConfigOk`,
`mcConfOk`, `mcInitOk` and encoder correctness are all discharged, so the
Pancake-to-ARM-machine-code theorem no longer takes an encoder premise. The
parity fixtures remain the executable evidence.
