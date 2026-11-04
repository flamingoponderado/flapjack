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
`bitstring`/FCP rotate operations (`#>>`, `v2w`, `w2v`, `shiftr`).
`L3/Support.lean` now supplies those operations (`holRotate`, `holShiftr`,
`holShiftl`, `holField`, `holTestbit`, `holV2w`, `holBitwise`, `holReplicate`),
and `L3/CorrectnessEncoding/ShiftBitfieldMasks.lean` restates HOL's `lsr` and
`lsl` as `arm8LsrMaskIdentity`/`arm8LslMaskIdentity` (tagged,
`pending_statement_review`); `asr_mask` combines HOL's `asr2` mask statement with
the shift reasoning and remains untagged.  `asr` is just HOL's library theorem
`word_asr_n2w` specialized to word64, with no ARM8-specific proof content.

The main HOL theorem `arm8_encoder_correct` is stated about CakeML's full L3
ARMv8 model (`HOL/examples/l3-machine-code/arm8/model/arm8Script.sml` and
`step/arm8_stepScript.sml`). Flapjack now ports that model (`L3/Types.lean`,
`L3/Defs.lean`, `L3/Target.lean`, `L3/Ast.lean`) and proves the corresponding
`encoderCorrect arm8TargetL3` obligation for the instructions the backend emits
in `L3/CorrectnessEncoding/Complete.lean`; see "L3 carrier and validity gate"
below. The closed subset model is retained for the executable driver, which
still runs `arm8Config` rather than `arm8ConfigL3`. The L3 assembling theorem
`arm8EncoderCorrectL3` and its 64 case theorems are tagged
`arm8_encoder_correct` and `reviewed_exact`; the closed-model
`arm8EncoderCorrect` is Flapjack infrastructure with no HOL original, because it
is about the closed model rather than HOL's `arm8_target`.

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
`scripts/l3/export_arm8_defs.sml`; the export is committed as
`scripts/l3/arm8_defs.sexp.gz` and `scripts/l3/check-renderings.py` compares
every definition in the file against it (129 definitions, two documented
handwritten exceptions).  118 declarations carry `@[hol]` tags; 117 are recorded as
`pending_statement_review` in `docs/HOL-THEOREM-MAP.json` and `NoOperation` is
`reviewed_exact`: the
rendering maps FCP to `BitVec`, bitstrings to `List Bool`, sets to predicates,
`HD []` to `false`, and adds a total default arm to `num2...`, so the equations
are not claimed as exact ports until source review.  The ten
`...2num`/`num2...` conversions and `boolify32` are untagged infrastructure
because the HOL declarations are generated by the L3 `Construct`/bitstring
machinery and `scripts/check-hol-refs.py` cannot resolve them.

Regenerating the file is not one command.  Decompress the export
(`gunzip -c scripts/l3/arm8_defs.sexp.gz > /tmp/arm8_defs.sexp`) and run

```
python3 scripts/hol_terms_to_lean.py /tmp/arm8_defs.sexp \
  Flapjack/Compiler/Encoders/Arm8/L3/Types.lean --thy=arm8 \
  arm8=HOL/examples/l3-machine-code/arm8/model/arm8Script.sml \
  arm8_step=HOL/examples/l3-machine-code/arm8/step/arm8_stepScript.sml
```

The generator emits the 129 definitions (and leaves the ten
`...2num`/`num2...` conversions untagged with their `Construct` note), but it
does not emit the file preamble, and it leaves `Poly32Mod2_loop` and
`CountTrailing` without termination evidence, so its output does not compile
as-is.  The committed file prepends the imports, module docstring, namespace,
`set_option maxRecDepth 1000000` and the two `open`s; names the recursion
guards (`if _h : i < 32` and `if h : ...`) and appends

```
termination_by arg0.1
decreasing_by
  show i - 1 < i
  omega
```

for `Poly32Mod2_loop` and

```
termination_by arg0.2.toNat
decreasing_by
  show (w >>> (1 : Nat)).toNat < w.toNat
  have hshift : (w >>> (1 : Nat)).toNat = w.toNat >>> 1 :=
    BitVec.toNat_ushiftRight w 1
  rw [hshift, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self (holCountTrailing_pos b w h) (by decide)
```

for `CountTrailing`, then closes the namespace.  `check-renderings.py` compares
bodies only, so it accepts those annotations as the two documented exceptions
but does not check the preamble, docstrings or tags.

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
tagged `arm8_target_def` and `reviewed_exact`, as are `arm8Ast`, `arm8Enc` and
`arm8ValidImmediate`; the rendered `Encode`/`Decode`/`Run`/`NextStateARM8`
closure it unfolds to remains `pending_statement_review` (see below).

`Flapjack/Compiler/Encoders/Arm8/L3/CorrectnessEncoding/Skip.lean` proves the
`Skip` constructor case of the L3 `encoder_correct` port
(`arm8_encoder_correct_skip`, tagged `arm8_encoder_correct`): the emitted `NOP`
bytes, the full `Decode`/`Run` reductions for that word, the
`Mem`/`Fetch`/`NextStateARM8` reductions (PC advance by four, `branch_hint`
cleared), the `asmStep`/`targetStateRel` interference simulation with `n = 0`,
and the outside-domain byte conclusion.  The other instruction cases live in the
sibling modules under `CorrectnessEncoding/`, and `Complete.lean` assembles them
into `arm8EncoderCorrectL3 : encoderCorrect arm8TargetL3` with no extra
hypothesis.

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

`Loc.lean` records the `Address` instruction's word, `Encode`/`Decode`
inverse, `Run` semantics and `arm8Next` reduction, plus the bit-level
reassembly of the 21-bit immediate and the sign-extend roundtrip from the
signed-20-bit range; `arm8_encoder_correct_loc_small` assembles the in-range
`Loc` case.

`LocBig.lean` records the six-instruction out-of-range lowering from
`arm8_ast`: an `Address` with immediate zero writing `PC` to the destination,
four `MoveWide .k` insertions of the offset into the temporary register 26,
and a final `AddSubShiftedRegister@64` adding the temporary to the
destination.  It proves the lowering shape, the 24-byte encoding, the six
`NextStateARM8` steps, that the four insertions put the offset into register 26
and that the final add writes `PC + offset`; `arm8_encoder_correct_loc_big`
assembles the case with `n = 5`.

`Branch.lean` records the `JMP`-typed `BranchImmediate` instruction: its word
(`btype = CALL` bit, the `00101` opcode and the 26-bit immediate), the
`Encode`/`Decode` inverse, the reassembly of the branch immediate and the
sign-extend roundtrip from the signed-28-bit range, and the `Run` reduction.
The latter needs `arm8_ok`'s `EL = 0`, `TBI0 = false` and `TBI1 = false`: those
make `BranchTo` skip the top-byte masking and write the target to `PC`
unchanged.  `arm8Next_branchImmediate` shows that the branch hint is set, so
`NextStateARM8` does not advance `PC` by four, and
`arm8_encoder_correct_jump` assembles the `Jump` case with `n = 0`.

`Call.lean` repeats that for the `CALL`-typed `BranchImmediate` (bit 31 set):
its word, `Encode`/`Decode` inverse and `Run` reduction, where the return
address `PC + 4` also goes to the link register (`X30`), plus
`arm8_encoder_correct_call` with `n = 0`.

`BranchConditional.lean` records the conditional-branch word
(`01010100 imm19 0 cd`) that `arm8_ast` emits for `JumpCmp`: its
`Encode`/`Decode` inverse (with the `imm19` and `cd` field reassembly), the
byte split, the `Run` semantics (`BranchTo` when the condition holds and an
unchanged state otherwise) and one `NextStateARM8` step, which advances `PC`
by four exactly when the branch is not taken.  It is the prerequisite for the
`JumpCmp` case theorem.

`JumpCmp.lean` records the two flag-setting compare instructions that
`arm8_ast` emits ahead of that branch: for the `is_test` comparisons an
`ANDS` (`LogicalShiftedRegister@64` with `LogicalOp_AND`, `S := T`, opcode
bits `0b11`) into `XZR`, and for the ordering comparisons a `SUBS`
(`AddSubShiftedRegister@64` with `op := T`, `S := T`) into `XZR`.  It proves
the `Encode`/`Decode` inverse for the `ANDS` word, the `Run` state equations
for both compare shapes (the `AND` result's most significant bit and zero-ness
for `ANDS`, `AddWithCarry`'s flags for `SUBS`, with the `XZR` destination
discarded) and one `arm8Next` step for each.

The same module carries the condition-code semantics those two shapes need.
`arm8AddWithCarry_machine` identifies the rendered `AddWithCarry` at 64 bits
with the machine model's `addWithCarry`, so the machine model's
`jumpCmp_flags_c`/`_z`/`_slt` lemmas carry over: `C` is "not below" unsigned,
`Z` is equality, and `N != V` is `BitVec.slt`.  `arm8ConditionTest_cmpCond`
tabulates the rendered `ConditionTest` on the eight `cmp_cond` codes, and
`arm8SubCmp_semantics`/`arm8AndCmp_semantics` conclude
`ConditionHolds (cmp_cond cmp)` after the compare equals
`wordCmpHOL cmp x y`.

`BranchConditional.lean` also carries the nineteen-bit immediate reassembly
(`arm8BranchCondBits`), the signed twenty-one-bit sign extension and
`arm8BranchCondRoundtrip`, mirroring the `Branch` module's 26-bit trio.
`JumpCmp.lean` then records the two-instruction lowering (`arm8Ast_jumpCmp_reg`
and `_imm`), its eight encoded bytes for both the `test` and the ordering
register forms, the `cjump` window facts `asmOkExact` supplies
(`arm8CjumpOk_of_asm`), the encoded offset `a - 4` in the signed 21-bit range
(`arm8CjumpOffsetOk`), and the compare's register-validity conjuncts.

`arm8_encoder_correct_jumpCmp_reg` then assembles the register case: the
compare step at `PC` (the `ANDS` or `SUBS`-into-`XZR` shape, chosen by
`isTest`), the conditional branch at `PC + 4`, and the two `arm8Next` steps at
`n = 1`.  The taken branch goes to `PC + a` with the branch hint set; the
untaken branch advances by four more.  The source side follows `asmUpd`'s
`wordCmpHOL` choice, matched to `ConditionHolds (cmp_cond cmp)` by the flag
semantics above.

The immediate-operand form uses the same branch word and the same two compare
shapes on an immediate operand.  Its `is_test` compare is an `ANDS` on a
`LogicalImmediate@64` (`arm8Run_logicalImmediate_ands_eq`,
`arm8Next_logicalImmediate_ands`, and `arm8Next_logicalImmediate_ands_agree`
for the two-state simulation; the set-flags bit lives in the opcode, as for
`LogicalShiftedRegister@64`).  Its ordering compare is an `AddSubImmediate@64`
with `S := T`, which `arm8AddSubImmediateWord` (hardcoded to `S := F`) does not
cover, so `AddSubImmediate.lean` adds `arm8AddSubImmediateWordS`, the
`e_data` two-branch body `arm8EData_addSubImmediateS`, and the
`Encode`/`Decode` inverses for the low twelve-bit and the shifted high
immediate windows (`arm8Encode_addSubImmediateS_low`/`_high`,
`arm8Decode_addSubImmediateS_low`/`_high`).  `JumpCmp.lean` then records the
`Run` equation `arm8Run_addSubImmediate_setflags_xzr_eq` (flags from
`AddWithCarry` on `Rn - imm`, the `XZR` destination discarded), the one-step
`arm8Next_addSubImmediateS_low`/`_high`, and their `_agree` lemmas.  The
register operand's `SP`-capable `if n = 31 then SP else X n` branch is
discharged from the config's `avoidRegs` list, so the `Run` equations are
stated with `rn ≠ 31`.

`arm8_encoder_correct_jumpCmp_imm` then assembles the immediate case at
`n = 1`, splitting on the three accepted encodings the config's
`valid_immediate` admits: the `ANDS` immediate for `Test`/`NotTest`
(`EncodeBitMask`), and the low and high `SUBS` immediate windows for the six
ordering comparisons (`arm8ValidImmediate_test`/`_ord` and
`arm8CmpOk_of_asm_imm` record that split).

`JumpReg.lean` does the same for `BranchRegister (r, JMP)`: the word, its
`Encode`/`Decode` inverse and the `Run` reduction, where `PC` becomes the
register's value.  The target's alignment is forced by `asm_step`'s
`~s2.failed` premise, since `JumpReg` lowers to `assert (aligned 2 a)`.
`arm8_encoder_correct_jumpReg` assembles that case with `n = 0`.

`LongDiv.lean` records that the `LongDiv` constructor is vacuous too: the
CakeML `arith_ok` admits `LongDiv` only on `x86_64`, while the L3
`arm8_config` has `ISA = ARMv8`, so `asm_step` cannot hold.
`arm8_encoder_correct_longDiv` proves the case from that contradiction,
matching the HOL proof's `LongDiv` branch.

`Fp.lean` records that the `FP` constructor is vacuous: `arm8_ast` lowers it to
the fail list, and `arm8_config` has no FP registers, so `fp_ok` rejects every
FP operation and `asm_step` cannot hold.  `arm8_encoder_correct_fp` proves the
case from that contradiction, matching the HOL proof's `FP` branch.

`AddCarry.lean` closes the `addCarry` lowering, whose five instructions are a
flag-setting `SUBS XZR, r4, #0`, a `ConditionalCompareImmediate@64` on `r2`
against zero under `EQ`, an `AddSubCarry@64` into `r1`, a `MoveWide .z` that
zeroes `r4`, and a final `AddSubCarry@64` into `r4`.  The file generalises the
`AddSubCarry@64` decoder to both `opc`/`s` combinations, records the
`AddWithCarry` facts for the two zero compares
(`arm8AddWithCarry_subs_zero`, `arm8AddWithCarry_add_zero`), gives each of the
five steps its `arm8Next_*` equation, its memory-preservation lemma
(`arm8Next_*_mem`) and its `arm8Ok` preservation, and carries the five
intermediate states `arm8AddCarryT1..T5` with `PC`/`REG`/`exception`/`EL`/
`SCTLR_EL1`/`MEM` projections.  The register effect is stated first in
`readReg` form (`hs2regsR`) so that the goal and `arithUpd`'s body share the
same `Decidable` instances, then rewritten to the `s1.regs` form through
`arm8ReadReg_eq`.  `arm8_encoder_correct_addCarry` proves the case: the carry
out lands in `sr` and the truncated sum in `d`, exactly as
`AsmSem.arithUpd` specifies, matching the HOL proof's `AddCarry` branch
(`next_tac 4`).

`ShiftBitfield.lean` starts the `shift` `.lsl`/`.lsr`/`.asr` immediate forms,
which `arm8_ast` lowers to a single `BitfieldMove@64` guarded by
`DecodeBitMasks`.  It records the emitted word (`arm8BitfieldWord`), the
`Encode` equation and the two rendered `Decode` inverses — the `opc = 2` form
(`inzero = T`, `extend = F`) that `Lsl` and `Lsr` emit and the `opc = 0` form
(`inzero = T`, `extend = T`) that `Asr` emits — plus the `Run` equation for
`dfn'BitfieldMove` with the masks left symbolic.  `ShiftBitfieldMasks.lean`
then ports the mask algebra.  `decodeBitMasks_lsr` and `decodeBitMasks_lsl`
record the two `DecodeBitMasks` shapes the encoder uses;
`tmask_lsr_getLsbD` shows the `Lsr`/`Asr` tmask keeps exactly the low `64 - n`
bits and `wmask_lsr` shows its wmask is the all-ones word;
`arm8LslMask_getLsbD` shows the `Lsl` wmask keeps bits `n` and above.
`lsr_mask`, `asr_mask` and `lsl_mask` are the instantiated identities (masking
the rotate right by these masks is the logical, arithmetic or logical-left
shift), and `arm8LsrMaskIdentity` / `arm8LslMaskIdentity` restate HOL's `lsr`
and `lsl` in their own shape — `DecodeBitMasks` result hypothesis, and for
`lsl` the `Abbrev` definitions of `r` and `q` — carrying `@[hol]` tags with
`pending_statement_review` manifest rows.  HOL's `asr2` is a statement about
the mask value rather than a shift identity, so `asr_mask` remains untagged
Flapjack infrastructure that combines it with the shift reasoning.

`ShiftBitfieldCase.lean` closes the three constructors:
`arm8_encoder_correct_shift_lsr_imm`, `_asr_imm` and `_lsl_imm` compose the
rendered `Encode`/`Decode` inverse, the `Run` equation with the masks
substituted, and the corresponding mask identity, then close through
`asmCaseOne`.  `.lsl` needs its two computed field values (`63w - n2w n` and
`-n2w n`) pinned first; `interval_cases` over the 64 admissible shift amounts
does that.  All four case theorems from this batch (`addCarry` and the three
shift-immediate forms) carry the shared `arm8_encoder_correct` tag and
`reviewed_exact` manifest rows.

`Mem.lean` now records the two `LoadStoreImmediate@64` word shapes
`e_LoadStoreImmediate` emits — the signed nine-bit form and the scaled
twelve-bit form — together with their `e_load_store`/`Encode` equations and
`Decode` inverses for both `MemOp_LOAD` and `MemOp_STORE`, and the `Run`
unfolding to `dfn'LoadStoreImmediate`.  The nine-bit form decodes to the
`b10 = 0` branch (no writeback, `unsigned_offset = false`), which is the branch
the L3 lowering reaches.

`asmCaseOneMem` (`Simulate.lean`) is the memory-aware `CaseGoal` constructor:
it keeps memory inside the source domain following the source update and
preserves it outside, which is what `CaseGoal`'s interference condition asks
for.  `arm8Mem_eight` (`Mem.lean`) reads the eight little-endian bytes of a
word load, the eight-byte analogue of `Bytes.lean`'s `arm8Mem_word`.

`holV2w_eight_bytes` identifies the MSB-first byte list with the OR-of-shifts
form `readBytes_eight` produces, and `arm8Mem_eight_eq_readMemWord` matches the
L3 eight-byte read against the source's `(readMemWord a 8 s).1` — it reuses
`readMemWord_fst` and `readBytes_eight` from the non-L3 `MemCase`, both stated
purely over `AsmState`.  The shift counts are pinned to `Nat` because
`readBytes_eight` uses `Nat` shifts while the L3 side had inferred `BitVec`
ones.

`arm8Run_loadStoreImmediate_load`/`_store` unfold `Run` through
`LoadStoreSingle` for the L3 fields (no writeback, no post-index, `NORMAL`,
`TN = 64`), and `arm8Ast_load_single`/`_store_single` pin the one-instruction
`arm8_ast` branch for an offset that is its own signed nine-bit form.

`arm8Enc_load_single_length`/`_store_single_length` fix the emitted length at
four bytes, and `arm8Mem_eight_value` derives the L3 read from the state
relation plus the eight-address domain fact (the latter comes from
`memLoadDomain` in the non-L3 `MemCase`, reusing `readMemWord_domain`).

The nine-bit `Encode` equations take `unsigned_offset` as a parameter, since
`arm8_load_store_ast` emits the nine-bit form with the field `false` (a negative
offset) as well as `true`.

One semantic point the load case has to discharge: `arm8Ok` does not constrain
`SCTLR_EL1.A`, but the machine's `Mem` calls `CheckAlignment`, which faults
when `¬ Aligned (address, 8)` and `SCTLR_EL1.A` is set.  The source is safe
because `memLoad` ends in `assertState (holAligned (holLOG2 n) a)`, so
`¬ s2.failed` from `asm_step` gives the effective address aligned — and then
`CheckAlignment` leaves the state unchanged.

`arm8MemLoad_aligned` and `arm8MemLoad_domain` derive the two facts a load
case needs from `asm_step`'s `¬ s2.failed`: the effective address is
eight-byte aligned and its eight bytes are in the source domain.  The
alignment half is what makes `CheckAlignment` a no-op regardless of
`SCTLR_EL1.A`; `arm8Aligned_eight_iff` converts between the rendered
`Aligned` and the `8 ∣ a.toNat` form.

`arm8_encoder_correct_mem_load_imm9` (`Mem.lean`) is the first `Mem` case
theorem: the unscaled `imm9` load path.  It takes the two branch conditions as
case hypotheses — the offset is its own signed nine-bit form (`hsx`, what
`arm8_ast` tests) and `e_LoadStoreImmediate`'s scaled twelve-bit clause does
not fire (`hfall`) — then emits the single nine-bit word with
`unsigned_offset = !off.msb`, decodes it back to the same
`LoadStoreImmediate@64`, runs it through `LoadStoreSingle`, and closes with
`asmCaseOneMem`.  The loaded value is `(readMemWord (s1.regs base + off) 8 s1).1`,
matched to `Mem`'s eight-byte read by `arm8Mem_eight_value`.  Two corollaries
discharge `hfall` from the sign: `arm8_encoder_correct_mem_load_neg` (negative,
so `unsigned_offset` is `false` and the scaled clause cannot fire) and
`arm8_encoder_correct_mem_load_pos_unscaled` (non-negative, but not the scaled
form).

`arm8_encoder_correct_mem_load_scaled` (`Mem.lean`) is the scaled twelve-bit
branch: the offset is the scaled form (`hoff`) and the sign is non-negative
(`hmsb`, so `unsigned_offset` is `true` and the encoder's first clause fires).
It does not need `hsx`: `arm8_load_store_ast`'s one-instruction branch is
`a = sw2sw ((8 >< 0) a) \/ (unsigned /\ a = scaled)`, so the scaled disjunct
covers offsets beyond the nine-bit range as well (`arm8ScaledForm_eq` connects
the `setWidth`/`zeroExtend` forms).  It emits the `imm12` word and reuses the
same `Run`/`asmCaseOneMem` tail.  The `Run`
equations for both `LoadStoreImmediate@64` forms now take `unsigned` as a
parameter, because `dfn'LoadStoreImmediate` ignores that encoding field.

`arm8_encoder_correct_mem_store_imm9` and `_mem_store_scaled` are the store
counterparts on the same two branches.  The store writes memory, so the
`asmCaseOneMem` obligations are discharged by `arm8WriteMem_eight`: the L3
`write'Mem` rendering stores the byte `holV2w 8 (holField (8i+7) (8i))` at
`address + i`, while the source's `writeMemWord` shifts the value by eight bits
per step.  `arm8HolByte` identifies the two byte extractions (through
`holField`/`holShiftr`/`holFixwidth` list indices), and `holUpdate_eight`
identifies the eight nested `holUpdate`s with the if-chain `writeMemN` uses.
`arm8WriteMem_eight_out` covers the outside-domain bytes, and
`arm8WriteMem_only_mem` records that `write'Mem` changes only `MEM`.

`arm8Mem_eight_pair` gives the full `Mem` pair (value and unchanged state) from
the byte agreement.  `NextStateARM8` runs the instruction on
`{ ms with branch_hint := none }`, and that pair is re-derived for the cleared
state directly rather than by a congruence lemma: `Mem` unfolds to a `holFor`
fold over the whole state, so the fold is not syntactically invariant under the
record update.

The remaining `Mem` widths and the far-offset path are closed in the same
module.  The two-instruction path is a pair of `AddSubImmediate@64` +
`LoadStoreImmediate` shapes: a negative offset adds `-off - 0x100` into the
scratch register 26 and then loads/stores at `-0x100` against it, and a
non-negative one adds `off - 0xFF` and accesses at `+0xFF`.  Each far case
takes the encodability of that computed immediate (`hlow`) as a hypothesis,
because the L3 `AddSubImmediate@64` word shape needs the immediate in the
twelve-bit window; `arm8FarImm_encodable_of_bounds` proves it from the offset's
window, and `arm8FarLowNeg`/`arm8FarLowPos` instantiate it at
`asmAddrOffsetOkExact`.  The 32/16-bit widths repeat the same three branches at
scaled shifts 2 and 1; the 16-bit offsets are checked by `asmHwOffsetOkExact`,
which has the same `(-4351, 4350)` window, so
`arm8FarLowNegOfBounds`/`arm8FarLowPosOfBounds` supply their `hlow` too.

The 8-bit offsets are bounded by `asmByteOffsetOkExact` at `(-256, 4095)`, so
the far branch is unreachable there: a negative offset is inside `[-256, -1]`
and therefore its own signed nine-bit form (`arm8NineBitForm_of_byte`), while a
non-negative one is below `4096` and therefore the zero-shift scaled form
(`arm8ByteScaledForm`).  The `.mem .load8`/`.store8` dispatchers use those two
facts instead of a far case.

`Complete.lean` assembles the chain.  Per-operation dispatchers
(`arm8MemLoadCase` etc.) split on the offset's sign bit and scaled form and
call the matching case theorem; `arm8MemCase`, `arm8ArithCase` (with
`arm8BinopCase`/`arm8ShiftCase`), and the remaining constructor cases feed the
assembling `arm8EncoderCorrectL3 : encoderCorrect arm8TargetL3`, which depends
only on `propext`, `Classical.choice` and `Quot.sound`.

### Carrier and statement comparison with the pinned HOL source

Checked against the `HOL/` submodule at `a390cbabd3a4521bab4ee20281e3e42933a8a3ae`
and `cakeml/compiler/encoders/arm8/arm8_targetScript.sml`:

- `arm8_state` (`arm8Script.sml:368-375`) has sixteen fields in this order:
  `MEM : word64 -> word8`, `PC : word64`, `PSTATE : ProcState`,
  `REG : word5 -> word64`, `SCTLR_EL1/2/3 : SCTLRType`, `SP_EL0..3 : word64`,
  `TCR_EL1 : TCR_EL1`, `TCR_EL2/3 : TCR_EL2_EL3`,
  `branch_hint : BranchType option`, `exception : exception`.  The Lean
  `structure arm8_state` has the same sixteen fields, in the same order, with
  `BitVec 64`/`BitVec 8`/`BitVec 5` for the fixed-width words and the rendered
  record types for the control registers.
- `arm8_next_def` is `THE o NextStateARM8`; Lean's `arm8Next` is
  `holThe (NextStateARM8 s)`.
- `valid_immediate_def` is the `INL Add`/`INL Sub`/six ordering-comparison
  integer-range test and `IS_SOME (EncodeBitMask i)` otherwise; Lean's
  `arm8ValidImmediate` has the same eight constructors in the same first
  clause and the same `EncodeBitMask` fallback.
- `arm8_config_def`'s constants are `off_max12 = w2w (UINT_MAXw: word12) = 4095`,
  `off_min9 = sw2sw (INT_MINw: 9 word) = -256`, `off_max9 = 255`, so
  `off_min = -4351` and `off_max = 4350`; `byte_offset = (-256, 4095)`,
  `jump_offset = (-134217728, 134217727)`,
  `cjump_offset = (-1048572, 1048579)` and
  `loc_offset = (-2147483648, 2147483647)`.  `arm8ConfigL3` has all sixteen
  fields with exactly these values (`reg_count = 32`, `fp_reg_count = 0`,
  `avoid_regs = [18, 26, 31]`, `link_reg = SOME 30`, `two_reg_arith = F`,
  `big_endian = F`, `code_alignment = 2`, `ISA = ARMv8`, `encode = arm8_enc`).
- `arm8_target_def` lists `next`, `config`, `get_pc`, `get_reg`, `get_byte`,
  `state_ok` and `proj`, and omits `get_fp_reg`.  HOL elaborates a record
  literal as a chain of updates over `ARB` of the record type
  (`src/datatype/record/RecordType.sml`), so the omitted field is exactly
  `(ARB : target).get_fp_reg`; `arm8TargetL3` sets the same seven fields and
  takes `getFpReg` from `(holArb (HolAsmTarget 64 arm8_state Arm8L3Projection)).getFpReg`,
  the same projection of an arbitrary whole target record.

These comparisons confirm the carriers and equations above at the level of
field lists, orders, types and constants.  They promote to `reviewed_exact`
the declarations that match HOL clause-for-clause under the documented
representations (`arm8_state` and the other L3 datatypes, `arm8Proj`,
`arm8Ok`, `arm8Next`, `arm8EncMovImm`, `arm8CmpCond`, `arm8Shv`,
`arm8LoadStoreAst{,32,16}`, `NoOperation`, `arm8EncodeFail`,
`arm8ValidImmediate`, `arm8ConfigL3`, `arm8Encode`, `arm8Ast`, `arm8Enc` and
`arm8TargetL3`).  The assembling theorem `arm8EncoderCorrectL3` and its
`target_ok` conjunct `arm8TargetL3_targetOk` are `reviewed_exact` as well: they
are HOL's `arm8_encoder_correct` and its local `arm8_target_ok`, at the L3
rendering and with no added hypothesis.  The 64 per-constructor case theorems are also
`reviewed_exact`: each is the named branch of HOL's `arm8_encoder_correct`
(`print_tac "Skip"` … `print_tac "Loc"`), states `CaseGoal` for that
instruction under exactly the original `asmStep`/`targetStateRel` premise, and
takes only the lowering's branch tests as parameters.  Those parameters are
HOL's own `Cases_on` branch tests, not added hypotheses: the `Loc` case, for
example, carries `hrange` (in range) or `hfalse` (out of range) exactly as HOL
splits on `sw2sw INT_MINw <= c /\ c <= sw2sw INT_MAXw`, and the dispatchers in
`Complete.lean` split both ways, so nothing survives into
`arm8EncoderCorrectL3`.  Their statements' constant closure reaches the
`(reals_as_rational_cuts)`-tagged FP renderings through `asmStep`'s FP updates,
so their manifest rows record `inherits_reals_as_rational_cuts` and inherit the
`docs/SOUNDNESS.md` item 8 real-rendering assumption.

**What `reviewed_exact` means here.**  It records a declaration-level
comparison: the Lean statement or definition was checked clause-for-clause
against its own HOL declaration under the documented representations.  It does
not certify the rendered `Defs.lean` closure that these statements unfold to
(`Encode`, `Decode`, `Run`, `NextStateARM8`), which remains
`pending_statement_review` -- mechanically rendered, but not individually
compared with HOL.  The exactness of the encoder-correctness chain is therefore
conditional on that rendering assumption: if a rendered equation differed from
HOL, the theorem would be about a slightly different machine.

That assumption is now machine-checked for transcription drift.
`scripts/l3/export_arm8_defs.sml` produces the pinned export, committed as
`scripts/l3/arm8_defs.sexp.gz` (129 definitions), and
`scripts/l3/check-renderings.py` compares every `Arm8/L3/Defs.lean` definition
against the rendered export, with two two-sided handwritten exceptions
(`CountTrailing` and `Poly32Mod2_loop`, whose committed bodies add Lean
elaboration annotations).  The gate proves the Lean definitions are exactly the
generator's rendering of the exported HOL terms; it does not prove the
rendering scheme itself is HOL-equivalent, which is what
`pending_statement_review` still records.

### Transition behaviour and lowering comparison

Checked against the same pinned source:

- `NextStateARM8_def` is `let s1 = Next s0 in if s1.exception = NoException then
  SOME s1 else NONE`.  The rendered `NextStateARM8` has the same shape, with `=`
  rendered as `==` on the `exception` enum, `SOME`/`NONE` as `some`/`none`, and
  `THE` as `holThe` (whose `none` branch is arbitrary, as HOL's `THE`).  The
  case theorems prove `NextStateARM8 ms = some t` (for example
  `arm8Next_word`/`arm8Next_nop`) and then `unfold arm8Next; rw [that]; rfl`,
  which is HOL's `THE (SOME t) = t`.
- `Next` is the `Fetch`/`Decode`/`Run` chain.  `Fetch`, `Decode`, `Run`, `Mem`,
  `write'Mem`, `write'X`, `DecodeBitMasks`, `Encode` and the `dfn'*` execution
  functions are the mechanical rendering of the 129-definition HOL closure
  reachable from `NextStateARM8`.  Their representation choices are: HOL FCP
  vectors become `BitVec` at the same dimension, bitstrings become `List Bool`
  (most-significant bit first), sets become predicates, `HD []` becomes
  `false`, and the `num2...` conversions are total with a default arm.  Those
  choices are recorded beside each declaration and in the
  `pending_statement_review` manifest rows; the equations are not claimed as
  exact ports.
- `arm8_ast_def` is compared clause by clause with `arm8Ast`.  Every clause
  selects the same `instruction` constructor with the same field order:
  `Skip` -> `[NoOperation]`; `Const` -> `MoveWide@64` Z/N/K or
  `LogicalImmediate@64` ORR; `Binop` with a register -> `AddSubShiftedRegister@64`
  or `LogicalShiftedRegister@64`; `Binop` with an immediate ->
  `AddSubImmediate@64`, the inverted `ORR` `LogicalShiftedRegister@64` for
  `Xor -1`, or `LogicalImmediate@64`; `Shift` with an immediate ->
  `BitfieldMove@64` (with the `Lsl` fields `r = -i`, `s = 63 - i` and the
  `Ror` `ExtractRegister@64`) or `arm8_encode_fail`; `Shift` with a register ->
  `Shift@64`; `Div` -> `Division@64`; `LongMul` -> `MultiplyHigh` +
  `MultiplyAddSub@64`; `LongDiv` and `FP` -> `arm8_encode_fail`; `AddCarry` ->
  the five-instruction chain; the two overflow forms -> flag-setting
  `AddSubShiftedRegister@64` + `ConditionalSelect@64`; `Mem` ->
  `arm8_load_store_ast{,32,16}` or the `LoadStoreImmediate@8` word;
  `Jump`/`Call`/`JumpReg` -> the three branch forms; `JumpCmp` -> the compare
  plus `BranchConditional (a - 4w, cmp_cond cmp)`; `Loc` -> `Address` or the
  six-instruction chain through temporary register 26.  The representations
  agree: `(15 >< 0) i` is `BitVec.ofNat 16 ((i >>> 0).toNat)` and likewise for
  the other three halves, `n2w r` is the `Nat`-to-`BitVec 5` cast, `~word_msb a`
  is `!offset.msb`, `x = Asr` is `sh == .asr`, `0x1Fw` is `31`, and `^temp` is
  `26`.  `Loc`'s range test compares against `sw2sw (INT_MINw: word20)` and
  `sw2sw (INT_MAXw: word20)`; HOL's `≤` on words is `word_le`, which is the
  signed comparison (`z ∨ n = v` from the subtraction flags), so Lean's signed
  `BitVec.sle` against `BitVec.signExtend 64 (BitVec.ofNat 20 0x80000)` and
  `BitVec.signExtend 64 (BitVec.ofNat 20 0x7FFFF)` is the same test.
- `arm8_encode_def` maps the `ARM8` word to its four little-endian bytes
  (`(7 >< 0) w` etc. as `BitVec.ofNat 8 ((w >>> k).toNat)`) and `BadCode` to
  four zero bytes; `arm8_encode_fail_def` is `[NoOperation]`; `arm8_enc_def` is
  `C LIST_BIND arm8_encode o arm8_ast`, rendered as
  `(arm8Ast instruction).flatMap arm8Encode`.
- Theorem statements: HOL's `arm8_encoder_correct` is
  `encoder_correct arm8_target`, and its proof splits on `i`, then on the
  `inst`/`arith`/`mem` constructors and on the lowering's branch tests.  The
  Lean case theorems carry the same `arm8_encoder_correct` tag with a suffix
  naming the case, state `CaseGoal` for that constructor under the same
  `asmStep`/`targetStateRel` premise, and take the lowering's branch test as a
  parameter (`hsx`, `hfall`, `hvalid`, `hbop`, `hne`, `hneg`, `hrange`, `hlow`,
  `hmsb`, `hscaled_ne`).  The assembling `arm8EncoderCorrectL3` is
  `encoderCorrect arm8TargetL3`, the same statement as HOL's theorem over the
  L3 target record; its dispatchers supply every branch test through
  `by_cases`, so no extra hypothesis survives.  `arm8Ok`, `arm8Proj`,
  `arm8Next`, `arm8EncMovImm`, `arm8CmpCond`, `arm8Shv`, `isTest` and the three
  `arm8_load_store_ast*` definitions are `reviewed_exact`, as are the four
  `Ast.lean` definitions (`arm8LoadStoreAst{,32,16}` and `arm8Ast`), the
  assembling `arm8EncoderCorrectL3` and `arm8TargetL3_targetOk`, and all 64
  case theorems.  The rendered `Decode`/`Run`/`Encode` equations those
  statements rest on remain `pending_statement_review`; the `Loc` reformulation
  above is reviewed.

## L3 machine configuration and downstream compiler theorem

`Flapjack/Compiler/Backend/Arm8Config/ProofsL3.lean` states CakeML's
`is_arm8_machine_config` over HOL's `arm8_state`/`arm8_proj` carriers
(`isArm8MachineConfigL3`, tagged `is_arm8_machine_config_def` and
`reviewed_exact`) and proves `mc_conf_ok` from it (`arm8MachineConfigOkL3`,
tagged `arm8_machine_config_ok` and `reviewed_exact`): the encoder-correctness
component is
`arm8EncoderCorrectL3`, the encoding invariant `arm8ConfigL3_encOk`, and the
five register guards are decided.  `arm8InitOkL3` (tagged `arm8_init_ok`,
`reviewed_exact`) proves `mc_init_ok arm8_config arm8_backend_config mc` at the
L3 `arm8BackendConfig`; the Pancake form (`pancake_backend_conf
arm8_backend_config`) is the untagged corollary `arm8InitOkL3_pancake`, because
`mcInitOk` reads only `stackConf.regNames` and `dataConf.be`.
`BackendProofL3.lean` proves the 27 `backend_config_ok`
conjuncts (`arm8BackendConfigOkL3`); the only field differing from the closed
`arm8Config` is `valid_imm`, so that proof follows the closed-model one with
`arm8ValidImmediate`.

`Flapjack/Pancake/Proofs/PanToTarget/Arm8L3Instance.lean` instantiates the
tagged `panToTargetCompileSemantics` theorem at that machine configuration
(`panToTargetCompileSemanticsArm8L3`), so the downstream Pancake
compiler-correctness theorem applies to the L3 ARMv8 target with HOL's original
hypotheses (`backend_config_ok`, `mc_conf_ok`, `mc_init_ok`, the register
relations and `pan_installed`).  Like the closed-model `Arm8Instance`, it is
untagged Flapjack infrastructure: it has no single HOL original.  Its encoder
component is the reviewed `arm8EncoderCorrectL3`, so it inherits that theorem's
`docs/SOUNDNESS.md` item 8 real-rendering assumption and nothing else.

Remaining assumptions and open items:

- The carriers, the target record and configuration, the lowering, all 64
  `arm8_encoder_correct` case theorems, the assembling `arm8EncoderCorrectL3`
  and `arm8TargetL3_targetOk` are `reviewed_exact` in
  `docs/HOL-THEOREM-MAP.json`.  The 129-definition `Fetch`/`Decode`/`Run`
  closure in `Defs.lean` remains `pending_statement_review`: those are
  mechanical renderings of the pinned L3 model whose representation mapping is
  documented but not individually certified, so the rendered transition
  equations are compared but not claimed as exact HOL ports, and the
  `reviewed_exact` claims above are conditional on them.  Every declaration
  whose constant closure reaches the `(reals_as_rational_cuts)` FP renderings
  records `inherits_reals_as_rational_cuts` and inherits the
  `docs/SOUNDNESS.md` item 8 real-rendering assumption.
- The ARM8 renderings are drift-gated: `scripts/l3/arm8_defs.sexp.gz` is
  committed and `scripts/l3/check-renderings.py` covers `Arm8/L3/Defs.lean`
  (129 definitions, 2 documented handwritten exceptions).  The remaining gap
  is the rendering scheme itself: `pending_statement_review` records that the
  generator's translation choices (`HD []`, the total `num2...` default arm,
  set-as-predicate, FCP out-of-range values) have not been compared
  declaration-by-declaration with HOL.  That per-declaration review is what
  would let the `Defs.lean` rows become `reviewed_exact`.
- The closed-model and L3 proofs of `is_arm8_machine_config ⇒ mc_conf_ok` and
  `backend_config_ok` are near-duplicates that differ only in the target,
  configuration and `valid_imm`; making them generic is recorded as follow-up
  work rather than churned in this PR.
- The executed compiler path (`Flapjack/Arm8/NativeSource.lean`) still uses the
  closed `arm8Config` and its `validImmediate` (`encodeBitMask`, a `Nat`-valued
  rendering), not `arm8ConfigL3`/`arm8ValidImmediate` (`EncodeBitMask`).  The
  production replacement is tracked separately (#1229).
- ARM parity is compiler-output parity: `Flapjack/Test/Arm8Parity.lean` compares
  the executed driver's assembly and hex against the original CakeML Pancake
  compiler on fifteen checked-in cases, and all fifteen pass.  Compiler-output
  parity alone does not establish semantic agreement with the L3 model; the
  semantic chain above is the evidence for that, modulo the `Defs.lean`
  rendering assumption.
