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
AArch64 would use SP.  Emitted code passes `r31` only in slots where AArch64
defines ZR: ORR-immediate `Rn`, ORR-shifted `Rn`, MADD/MSUB `Ra`, ADC `Rm`,
CSINC `Rn`/`Rm`, CMP `Rd`, TST/ANDS-shifted `Rd`, SUBS-shifted `Rd`, and
ANDS-immediate `Rd`.  The ANDS-immediate case relies on `setflags = true`; in
the non-flag-setting logical-immediate form that slot means SP.  This per-slot
AArch64 fact is an assumption of the closed model, not a theorem about the
emitted path.
Because the decoder is still a permissive subset recognizer, it can also accept
non-emitted words: the add/sub-with-carry mask can treat a CCMP-register word as
ADCS; the unsigned-offset mask accepts signed loads, PRFM, and bits 25:24 = 11
as unsigned loads; the unscaled mask accepts register-offset and pre/post-index
forms, signed loads, LDTR/STTR, LSE atomics, pointer-auth LDRAA/LDRAB, and RCpc
LDAPR; and the multiply-high mask accepts other variants as `MULH`.  These words
are never emitted, so the closed machine modules (`Decode.lean`, `Execute.lean`,
`Machine/`) carry no `@[hol]` tags.
All twenty instruction forms now have kernel-checked decoder inverses on the
emitted shapes.  The load-shape limits above and the unproved per-slot
`r31`/XZR assumption are the remaining gaps on that path.
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

## L3 carrier and validity gate

`Flapjack/Compiler/Encoders/Arm8/L3/Types.lean` ports the L3-generated
carriers from `HOL/examples/l3-machine-code/arm8/model/arm8Script.sml`: the
`arm8_state` record and its control-register records (`ProcState`, `TCR_EL1`,
`TCR_EL2_EL3`, `SCTLRType`, `BranchType`, `exception`), plus `AccType`,
`ExtendType`, `LogicalOp`, `MemOp`, `MemBarrierOp`, `RevOp`, `SystemHintOp`,
`PSTATEField`, `System`, `Debug`, `LoadStore`, `Branch`, `CRCExt`, `Data`,
`instruction` and `MachineCode`.  `ShiftType` and `MoveWideOp` remain in
`Encode.lean`, where they were already ported with Lean constructor names.  The
file is the mechanical output of `scripts/l3_types_to_lean.py` for those
declarations, and `scripts/tests/test_hol_l3_types_to_lean.py` checks it against
the model.

`Flapjack/Compiler/Encoders/Arm8/L3/Target.lean` ports CakeML's `arm8_proj`
and `arm8_ok` over that carrier.  `arm8Ok_of_closed` proves that the closed
model's `arm8StateOk`, under the relation `arm8StateRel`, implies the L3
validity gate; the L3-only privilege, control-register and exception fields are
explicit hypotheses because the closed carrier does not model them.  This is a
validity-condition refinement only.

`Flapjack/Compiler/Encoders/Arm8/L3/Support.lean` provides the library
renderings the model needs: HOL `bitstring` (`List Bool`, most-significant bit
first), the `fcp` `bool ** 'N` carrier as `BitVec N`, and the list, set, word
and integer helpers (`PAD_LEFT`, `FLAT`, `w2v`, `shiftr`, `testbit`, `bxor`,
`word_ror`, `word_msb`, `Num`, etc.).

`Flapjack/Compiler/Encoders/Arm8/L3/Defs.lean` is the mechanical rendering of
the 129-definition HOL closure reachable from `NextStateARM8` and
`Fetch`/`Decode`/`Run`/`Next`/`Encode`, produced by
`scripts/hol_terms_to_lean.py --thy=arm8` from
`scripts/l3/export_arm8_defs.sml`.  118 declarations carry `@[hol]` tags and
are recorded as `pending_statement_review` in `docs/HOL-THEOREM-MAP.json`: the
rendering maps FCP to `BitVec`, bitstrings to `List Bool`, sets to predicates,
`HD []` to `false`, and adds a total default arm to `num2...`, so the equations
are not claimed as exact ports until source review.  The ten
`...2num`/`num2...` conversions and `boolify32` are untagged infrastructure
because the HOL declarations are generated by the L3 `Construct`/bitstring
machinery and `scripts/check-hol-refs.py` cannot resolve them.

`Flapjack/Compiler/Encoders/Arm8/L3/Target.lean` adds `arm8_next = THE ∘
NextStateARM8` over the L3 carrier.  `Flapjack/Compiler/Encoders/Arm8/L3/Ast.lean`
ports the rest of the CakeML target script: `arm8_encode_fail`, `arm8_encode`,
`arm8_enc_mov_imm`, `cmp_cond`, the three `arm8_load_store_ast` variants,
`arm8_ast` (the `asm`-to-L3-`instruction` lowering) and
`arm8_enc = C LIST_BIND arm8_encode o arm8_ast`.
`Flapjack/Compiler/Encoders/Arm8/L3/Configuration.lean` ports `valid_immediate`
and the exact sixteen-field `arm8_config` (`arm8ConfigL3`) over the L3 encoder,
and proves `arm8ConfigL3_encOk`.

`Flapjack/Compiler/Encoders/Arm8/L3/Target/State.lean` assembles
`arm8TargetL3 : HolAsmTarget 64 arm8_state Arm8L3Projection` from the exact L3
configuration and `arm8_next`/`arm8_ok`/`arm8_proj`, and proves
`arm8TargetL3_targetOk`, the `targetOk` half of `encoderCorrect`.  The record is
tagged `arm8_target_def` and recorded as `pending_statement_review`: the
`arm8_ast`/`arm8_enc`/`EncodeBitMask` definitions it depends on are still
mechanically rendered and not source-reviewed.

`Flapjack/Compiler/Encoders/Arm8/L3/CorrectnessEncoding/Skip.lean` proves the
`Skip` constructor case of the L3 `encoder_correct` port
(`arm8_encoder_correct_skip`, tagged `arm8_encoder_correct`): the emitted `NOP`
bytes, the full `Decode`/`Run` reductions for that word, the
`Mem`/`Fetch`/`NextStateARM8` reductions (PC advance by four, `branch_hint`
cleared), the `asmStep`/`targetStateRel` interference simulation with `n = 0`,
and the outside-domain byte conclusion.  The remaining instruction cases and
the assembling `encoderCorrect arm8TargetL3` theorem are #1239;
`encoderCorrect` is proved only for the closed model.

The further case modules under `CorrectnessEncoding/` cover, so far, the
`const` constructors (`MoveWide.lean`, `Bytes.lean`, `Simulate.lean`,
`Const.lean`), the `binop` logical-immediate and shifted-register forms
(`LogicalImmediate.lean`, `LogicalShiftedRegister.lean`,
`LogicalImmediateBinop.lean`), the `binop` add/sub shifted-register and
immediate forms (`Arith.lean`, `AddSubImmediate.lean`), and `shift` with a
register operand plus its `.ror` immediate form (`Shift.lean`,
`ShiftImmediate.lean`), `div` (`Division.lean`), and the `longMul` instruction
pair `MultiplyHigh` + `MultiplyAddSub@64` (`Multiply.lean`, which also proves
that the high half of the unsigned 128-bit product is `r / 2 ^ 64`, plus the
one-step `arm8Next_multiplyHigh` / `arm8Next_multiplyAddSub` reductions and
their `Arm8L3Agree` congruence lemmas and the fact that both steps leave
memory unchanged, plus the eight-byte encoded shape `arm8Enc_longMul`).
`ConditionalSelect.lean` records the same facts for `ConditionalSelect@64`, the
select used by the `addOverflow` and `subOverflow` lowerings, and
`Overflow.lean` adds `ConditionHolds` at `VC`, the flag-setting
`AddSubShiftedRegister@64` step and the two `arm8Next` reductions that the
overflow lowerings need, `Carry.lean`
does the same for `AddSubCarry@64`, which the `addCarry` lowering uses twice,
and `Compare.lean` records `ConditionalCompareImmediate@64`'s word, `e_sf`,
`e_data`/`Encode`, `Run` and decoder inverse.  Each records the emitted word, the `Decode` inverse,
the `Run` reduction and the `asmCaseOne` interference simulation for its
constructor; all are Flapjack case splits of the single HOL theorem
`arm8_encoder_correct` and carry no `@[hol]` tags of their own.

`LongMul.lean` assembles those facts into the two-instruction `longMul` case
theorem with `n = 1` (`asserts 1`, `asserts2 2`), and `Overflow.lean` does the
same for `addOverflow` and `subOverflow`: the flag-setting add or subtract
followed by the `VC` select.

`Loc.lean` records the `Address` instruction's word, its `Encode` shape (given
the in-range reassembly of the 21-bit immediate) and its `Run` semantics; the
`Loc` case theorem itself is not yet assembled.

Still open for #1239: the `shift` `.lsl`/`.lsr`/`.asr` immediate forms (through
`DecodeBitMasks`/`BitfieldMove`), and the `longDiv`, `addCarry`,
`addOverflow`, `subOverflow` (their `ConditionalSelect@64` facts exist in
`ConditionalSelect.lean`), `addCarry` (its `AddSubCarry@64` facts exist in `Carry.lean` and its
`ConditionalCompareImmediate@64` facts in `Compare.lean`), `Mem`,
`Fp`, `Jump`, `JumpCmp`, `Call`, `JumpReg` and `Loc` constructors.  `longDiv` lowers to
`arm8EncodeFail`, so its case cannot be a faithful lowering without the
intended instruction sequence.  The assembling `encoderCorrect arm8TargetL3`
theorem waits on the remaining cases.
