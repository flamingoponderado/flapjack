# Original Pancake HOL probes

The repository-wide parity workflow is documented in
[`docs/PARITY-TESTING.md`](../../docs/PARITY-TESTING.md).

The files in this directory execute definitions from the CakeML Pancake HOL
development. They are test-data generators, not independent Lean reference
implementations. A parity fixture may be used to close a porting bead only
when it records the original source definition, the probe source, and the
command used to regenerate its output.

`semantics_props_implements_probe.out` prints the proved HOL
`semanticsPropsTheory.implements'_trans` conclusion from
`cakeml/semantics/proofs/semanticsPropsScript.sml:285-295`. The structural
Lean analogue and behavior-extension regressions are in
`Flapjack.Test.SemanticsPropsParity`; the HOL `llist` to Lean
`CakeLazyList` carrier bridge remains unproved, so this evidence does not
qualify those declarations for exact HOL tags.

The probes currently cover the small `loop_to_word` slice used by
`Flapjack.Test.LoopToWord`, the `panSem$mem_load` boundary used by
`Flapjack.Test.PanMemoryParity`, the fixed-width load boundary used by
`Flapjack.Test.PanFixedLoadParity`, and the `panSem$shape_of` boundary used by
`Flapjack.Test.PanShapeParity`, plus the `panSem` word/value helpers used by
`Flapjack.Test.PanWordParity`. The fixed-width store boundary is covered by
`Flapjack.Test.PanFixedStoreParity` (little-endian) and, in both endiannesses
for the executed state-derived `store32` and the exact `panMemStore32HOL`, by
`Flapjack.Test.PanStore32EndianParity` (`pan_store32_endian_probe.out`), and the shared-store payload bytes
(the little-endian `TAKE nb (word_to_bytes w F)` prefix of `sh_mem_store_def`,
observed through an echoing FFI oracle) by `Flapjack.Test.PanShMemStoreBytesParity`
(`pan_sh_mem_store_bytes_probe.out`), and the word-store boundary by
`Flapjack.Test.PanFlatStoreParity`. Value flattening is covered by
`Flapjack.Test.PanFlattenParity`; scoped local restoration (`res_var_def`) is
covered by `Flapjack.Test.PanResVarParity`. Their source references are
respectively
`cakeml/pancake/loop_to_wordScript.sml` and
`cakeml/pancake/semantics/panSemScript.sml`; `Flapjack.Test.PanOpParity`
additionally probes `pan_op_def` at lines 191--193.
`Flapjack.Test.LoopSetVarParity` probes `set_var_def` at
`cakeml/pancake/semantics/loopSemScript.sml:108-110`.
`Flapjack.Test.LoopPropsCutSetsParity` guards the exact `cut_sets_def`
clauses over `HolLoopProg`/`NumSet`; its direct HOL outputs for Skip,
LocValue, Assign, Load32/LoadByte, Seq, If, each Arith variant, and the
catch-all are in `scripts/hol-probes/loop_props_cut_sets_probe.out`.
`Flapjack.Test.LoopPropsCompSyntaxParity` guards the exact Boolean
`comp_syntax_ok_def` clauses over the same carriers, including Loop live-set
equality, Seq cut-set threading, and the If existential fold condition. Its
direct HOL EVAL rows are in `scripts/hol-probes/loop_props_comp_syntax_ok_probe.out`.
The exact proof-side definition is `compSyntaxOkHOLExact` in
`Flapjack.Pancake.Semantics.LoopProps.CompSyntax`; it does not claim production
compiler routing through the list-backed `loopCompSyntaxOk`.
`Flapjack.Test.LoopDecClockParity` probes `dec_clock_def` at lines 42--43 of
the same source.
`Flapjack.Test.LoopFixClockParity` probes `fix_clock_def` at lines 46--49.
`loop_props_survives_probe.out` records direct HOL EVAL rows for every clause
of `survives_def` in `cakeml/pancake/semantics/loopPropsScript.sml:25-38`:
If/Loop/Call (both handler forms)/FFI domain membership, recursive Mark and
Seq, and the catch-all case. The exact width-indexed `HolLoopProg` port
`survivesHOLExact` is in `Flapjack.Pancake.Semantics.LoopProps`; its replay
guards are in `Flapjack.Test.LoopPropsSurvivesParity`. Refresh with
`HOL_PROBE_ONLY=loop_props_survives_probeScript.sml scripts/hol-probes/regenerate.sh`.
`Flapjack.Test.PanEvaluateDeclsParity` probes `evaluate_decls_def` at
`cakeml/pancake/semantics/panSemScript.sml:814-835`, including each declaration
constructor, ordered global updates, local clearing during initializer
evaluation, an in-domain word load, function-code replacement, and
shape/duplicate failure cases.
`Flapjack.Test.PanSemEvaluateDeclsFiniteParity` separately guards the exact
finite-map evaluator against every named row in `pan_evaluate_decls_probe.out`,
including an in-domain byte load in a declaration initializer.
`pan_clock_program_route_probe.out` records direct HOL `evaluate` observations
for duplicate function front-update order (`SOME (Return (ValWord 2w))`), a
duplicate whose shadowed binding has different formal names and return shape
(`SOME (Return (RStruct []))`), and rejection of a nested callee return whose
actual value violates its declared return shape (`SOME Error`). The matching
declaration-level clocked wrapper regressions are in
`Flapjack.Test.PanValueFfiClockMemoryFfi`; they exercise production routing
through the source-owned finite code map. Refresh
with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=pan_clock_program_route_probeScript.sml
scripts/hol-probes/regenerate.sh`.
`pan_sem_state_eval_probe.out` records direct HOL EVAL of `eval_def` at
`cakeml/pancake/semantics/panSemScript.sml:209-297` for in-domain and
out-of-domain word loads, a recursively nested three-word shape load,
little- and big-endian byte loads, 32-bit loads, and list-valued `word_op_def`
operators with accepted and rejected operand counts.
The source-shaped generic definition is `Flapjack.Pancake.wordOpHOL`; its
all-width equation to the production RISC-V target is in
`Flapjack.Pancake.Semantics.CrepRuntimeTarget`. The state-derived Lean
boundary and its matching cases live in
`Flapjack.Pancake.Semantics.PanSemStateEval` and
`Flapjack.Test.PanSemStateEvalParity`. The nested three-word Load row is also
compared with compiled Crep loads under a concrete `state_rel` fixture in
`Flapjack.Test.PanToCrepStateRelParity`; this regression does not prove the
general arbitrary-shape induction case.
`pan_sem_mem_domain_probe.out` pins the ordinary-memory domain boundary used
by the production/exact `PanSemState` bridge: an in-domain `Load One` hit, an
out-of-domain miss even when the total HOL cell holds a word, a statement-level
`Store`/`Load` roundtrip, an out-of-domain `Store` failure, and a raw
`mem_stores`/`mem_load` roundtrip. Its Lean regressions live in
`Flapjack.Test.PanSemStateBridgeParity`.
`pan_sem_e2e_probe.out` records direct HOL evaluation cases for nonempty
state-owned code maps, including recursive Call, DecCall, nested Call/DecCall,
and clock timeout. `pan_sem_call_return_shape_probe.out` adds Call and DecCall
cases where the callee's actual returned value disagrees with the return shape
stored in the code map; HOL returns `SOME Error`, preserves the decremented
clock, and exposes the callee post-state. Their Lean checks live in
`Flapjack.Test.PanEvaluateParity` and exercise the recursive
`PanSemState.code` evaluator. The same probe contains direct `evaluate_def`
ExtCall rows for returned FFI bytes (including the updated memory), failed
byte-array reads, expression failure, nonword arguments, and `FFI_final`;
these are checked by `Flapjack.Test.PanSemExtCallExactParity`. The finite-
carrier source equation is tagged in
`Flapjack.Pancake.Semantics.PanSem.ExtCallCase`.
`pan_sem_ite_e2e_probe.out` records direct HOL `evaluate` rows for the `If`
equation at `cakeml/pancake/semantics/panSemScript.sml:618-622`: a nonzero word
condition selects the then-branch, `0w` selects the else-branch, and a condition
that evaluates to the non-word value `RStruct []` (or fails to evaluate) returns
`SOME Error` while retaining the state. The matching Lean guards for the
measure-driven fragment and the expression-conditioned fragment live in
`Flapjack.Test.PanSemTotalParity`. `pan_sem_total_fragment_stmt_probe.out` adds
`If` selection over the exact `Assign` clause, including the non-word
`RStruct []` condition row `total_if_assign_nonword_result` / `_local`; the
production partial dispatcher's matching `If` guards and kernel-checked
regressions are in `Flapjack.Test.PanSemTotalStepsParity`.
`compile_to_crep_probe.out` records direct HOL EVAL rows for the full
declaration-only `compile_to_crep_def`, including `raise_const`, `handled_pair`,
duplicate exception IDs, and `duplicate_function_names`. The latter confirms
both duplicate function entries remain in source order while the internal
`make_funcs` map uses the first entry's return shape. `Flapjack.Test.CompileToCrepeParity`
replays `raise_const` and `duplicate_function_names` over exact
`DeclHOL`/`CrepProgHOL` carriers through the tagged `compileToCrepExactHOLW`;
the `handled_pair` and duplicate exception rows remain covered by its
production-carrier fixtures. The exact tagged definition remains proof-side;
executable routing is tracked separately by `flapjack-pxn.18.3.1.3`.
Regenerate the direct HOL fixture with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=compile_to_crep_probeScript.sml bash scripts/hol-probes/regenerate.sh`.
`compile_def_probe.out` also records direct HOL evaluations of `Return`
(`return`, `multi_return`, and the empty-struct return), paired
`Store32`/`StoreByte` success and fallback rows, `If`/`While` success and
fallback rows, Global Assign/ShMemLoad Skip fallbacks, Local Assign direct,
overlap-temporary, missing-destination, and length-fallback rows, Primitive
destination present/missing rows, one-word/multiword Store and fallback rows,
scalar/structured Raise and fallback rows, ShMemStore success and missing-head
rows, local ShMemLoad success and fallback rows, and assigned Global call
destinations through `pan_to_crep$compile`, plus scalar/multiword Dec and
shape-length fallback and scalar/multiword DecCall rows. The exact untagged
`compileDecCallExactHOLW` slice and its Lean checks are in
`Flapjack.Test.CompileDefParity`; `call_no_return` checks the HOL `rtyp = NONE`
arm's flattening of argument expressions, with the exact untagged
`compileCallNoReturnExactHOLW` slice checked in the same module.
`call_result_no_handler_present` and `_missing` pin the other arm for
`rtyp = SOME (NONE, NONE)`: lookup of the return shape, fresh result names,
zero initialization, and the empty-result fallback. Its exact untagged helper
is `compileCallResultNoHandlerExactHOLW`. `call_wrapped_result_no_handler`
checks the successful `wrap_rt (FLOOKUP ctxt.vars rt)` arm for a local Call
result: it reuses the looked-up names directly, without temporary allocation
or zero initialization. The exact untagged helper and parity guard are
`compileCallWrappedResultNoHandlerExactHOLW` and
`exactCallWrappedResultNoHandlerParity`. `call_wrapped_result_missing` and
`call_wrapped_result_empty_one` check the two `wrap_rt = NONE` cases, which
emit a flattened tail call without result metadata; their exact helper and
guard are `compileCallWrappedResultFallbackNoHandlerExactHOLW` and
`exactCallWrappedResultFallbackNoHandlerParity`. `call_handler_missing_eid` checks
that an exception handler with a missing `eids` entry takes the same fallback;
the Lean exact subcase is `compileCallHandlerMissingEidExactHOLW`.
`call_wrapped_result_handler_missing_eid` checks the distinct wrapped-result
case: the missing handler EID is discarded, but destination names remain in
the call result metadata. The matching helper and guard are
`compileCallWrappedResultHandlerMissingEidExactHOLW` and
`exactCallWrappedResultHandlerMissingEidParity`.
`call_wrapped_result_handler_present_eid` checks the found-EID branch: result
names remain direct metadata and `exp_hdl` is sequenced before the compiled
handler body. Its matching helper and guard are
`compileCallWrappedResultHandlerPresentEidExactHOLW` and
`exactCallWrappedResultHandlerPresentEidParity`.
`call_wrapped_result_fallback_handler_present_eid` checks the complementary
case where no wrapped result destination exists: the handler remains but the
Call return-name list is empty. Its matching helper and guard are
`compileCallWrappedResultFallbackHandlerPresentEidExactHOLW` and
`exactCallWrappedFallbackHandlerPresentEidParity`.
`call_wrapped_result_fallback_handler_missing_eid` checks the same missing
result destination with no exception-code entry, so HOL drops the handler and
emits `Call NONE`; the matching helper and guard are
`compileCallWrappedResultFallbackHandlerMissingEidExactHOLW` and
`exactCallWrappedFallbackHandlerMissingEidParity`.
`call_handler_present_eid` checks the found-EID branch, including exact
`exp_hdl` global loads and recursive handler sequencing; its exact helper is
`compileCallHandlerPresentEidExactHOLW`.
`extcall_constants` (with `vmax = 400`),
`extcall_high_tail` (with `vmax = 0`), `extcall_shared_high_tail`, and
`extcall_shape_fallback` pin the `ExtCall` case: its freshness bound scans all
operand variables, including a high variable that is not emitted, and ignores
context `vmax`; the four operands must also have shape `One` and nonempty
compiled lists. The exact untagged `compileExtCallExactHOLW` clause slice and
Lean checks live in `Flapjack.Test.CompileDefParity`. Regenerate the direct HOL
fixture with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=compile_def_probeScript.sml bash scripts/hol-probes/regenerate.sh`.
`dec_declared_shape_ignored` confirms that `Dec` stores the shape returned by
`compile_exp`, not its declared shape; the exact compiler guard in
`Flapjack.Test.CompileDefParity` checks the same two-word result.
The fixture also covers absent lookups, the
`One`/empty-list fallback, and inconsistent shape/name-list lengths. The
matching Lean cases live in `Flapjack.Test.CompileDefParity`. The
`struct_skip`, `struct_seq`, `struct_break`, `struct_continue`, `struct_tick`,
and `struct_annot` rows pin the first exact-carrier `compile_def` structural
slice; its supported-subset helper is intentionally untagged and does not
claim the full compiler definition.
`compile_exp_probe.out` records direct HOL EVAL rows for every `compile_exp`
constructor family and defensive fallback. `Flapjack.Test.CompileExpParity`
checks those rows through both the existing production-carrier implementation
and the exact-carrier `compileExpExactHOLW`; the latter is tagged against
`compile_exp_def` and uses the exact Pan/Crepe expression and context carriers.
The general `Load` case regression also pairs one shared 64-bit input across
`compile_exp_probe.out` (`load_one`), `pan_mem_load_probe.out`
(`one_load_one`), `crep_load_shape_probe.out` (`load_one`), and
`crep_eval_load_rv64_probe.out` (`mem_load_one_load_one` and
`eval_load_one_load_one`). The probes observe `compile_exp`, `mem_load`,
`load_shape`, and the Crep `mem_load`/`eval` equations at address `3w`, with
cell value `Word 3w`. The exact-carrier four-conclusion case regression is
`Flapjack.Test.PanToCrepStateRelCarrierParity.loadCaseAllConclusions`; its
oracle guard ties the source result, compiled expression, generated Load,
target memory read, and target expression evaluation to those same rows.
Regenerate the three changed fixtures from the original read-only HOL sources
with:

```sh
CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=pan_mem_load_probeScript.sml scripts/hol-probes/regenerate.sh
CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_load_shape_probeScript.sml scripts/hol-probes/regenerate.sh
CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_eval_load_rv64_probeScript.sml scripts/hol-probes/regenerate.sh
```
The same direct `mem_load_def` probe also records the recursive rows
`recursive_mem_loads_two_words`, `recursive_comb_two_words`, and
`recursive_named_two_fields`. They use a two-cell 64-bit memory with addresses
0 and 8, so the fixture pins `bytes_in_word * size_of_sh_with_ctxt` as well as
the list, `RStruct`, and two-field `NStruct` result shapes. Matching exact
production-to-HOL kernel guards are in
`Flapjack.Test.DeclBridgeParity`; regenerate them with the command above for
`pan_mem_load_probeScript.sml`.

`excp_rel_probe.out` and `ctxt_fc_probe.out` are direct EVALs from
`pan_to_crepProofTheory`, paired with `Flapjack.Test.PanToCrepRelationsParity`.
The `functions_projection` row in `ctxt_fc_probe.out` directly checks the
HOL `ctxt_fc_funcs_eq` theorem at `pan_to_crepProofScript.sml:2295` against
the kernel-checked Lean fixture in that module. The `vmax_nonempty_list` and
`vmax_empty_list` rows directly check `ctxt_fc_vmax` at line 2307 and are
paired with `ctxtFcVmax` Lean fixtures.
The `excp_rel` cases deliberately use a word-valued compiler-code map and a
shape-valued source map, matching the definition's independent HOL value types.
The `ctxt_fc` cases record `with_shape` slot slicing, ZIP truncation, and
`MAX_LIST` on an empty name list.
`pan_to_crep_state_rel_carrier_probe.out` directly evaluates HOL
`pan_to_crepProof$state_rel` (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:45-56`)
on matching fields and a nonempty named struct context, and records its
`mlstring`-named `struct_info` row. It also records the `FLOOKUP` observations
for empty and nonempty globals. HOL EVAL leaves equality of the nonempty
function-backed fmap with `FEMPTY` unreduced, so that row is kept explicitly
as an unevaluated term; it is not reported as a computed `F` result. The exact
carrier checks live in `Flapjack.Test.PanToCrepStateRelCarrierParity`. The
source review is intentionally narrow: it pins the carrier fields consumed by
the state relation, not a port of `state_rel` or a claim that production
String/Shape states satisfy the relation. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=pan_to_crep_state_rel_carrier_probeScript.sml
scripts/hol-probes/regenerate.sh` when using a read-only CakeML checkout whose
compiled theories match the source commit.

`pan_to_crep_ret_inst2_probe.out` evaluates the five premises of
`evaluate_shape_invariant_ret_inst2` at
`pan_to_crepProofScript.sml:3031-3044` on a concrete empty-argument call setup:
the source `OPT_MMAP`, successful code lookup, body `Return (Const 7w)` run,
matching `state_rel`, and empty `locals_rel`. It also records the combined
five-premise row and result constructor. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=pan_to_crep_ret_inst2_probeScript.sml
scripts/hol-probes/regenerate.sh` against the matching built CakeML theories.

`code_rel_probe.out` records the HOL-inferred source/target code-map types,
compiled parameter return, localisation outcomes, function-signature lookup,
and target entry. The probe also proves matching and deliberately mismatching
`code_rel` instances against `code_rel_def`; the corresponding Lean relation
analogue tests live in `Flapjack.Test.PanToCrepCodeRelParity`. The Lean
relation remains untagged until its list-backed compiler body is replaced by
the exact HOL `compile` port tracked by bead `flapjack-pxn.18.3.1.4`.
`globals_lookup_probe.out` records direct HOL EVAL of
`pan_to_crepProof$globals_lookup_def` for a present singleton word and a
missing global; the matching Lean guards live in
`Flapjack.Test.PanToCrepGlobalsLookupParity`.
`crep_store_eval_probe.out` records direct HOL `evaluate_def` Store cases from
`cakeml/pancake/semantics/crepSemScript.sml:267`: successful in-domain write,
address-expression failure, value-expression failure, and address-domain
failure. The matching restricted total state evaluator and Lean guards are in
`Flapjack.Pancake.Semantics.CrepSem.TotalEval` and
`Flapjack.Test.CrepSemTotalStoreParity`; the restricted evaluator has no
whole-definition `@[hol]` tag.
`pan_sem_store_error_probe.out` includes direct HOL `evaluate` rows for
ShMemLoad address-evaluation failure, a non-word address, missing destination,
and shared-memory-domain rejection. `Flapjack.Pancake.Semantics.PanSem.ShMemLoadCase`
ports the literal nested matches from `evaluate_def`; its finite-carrier Lean
guards live in `Flapjack.Test.PanSemShMemLoadCaseParity`.
`crep_arith_dest_const_probe.out` records direct HOL EVAL of
`crep_arith$dest_const_def` at
`cakeml/pancake/crep_arithScript.sml:10-12` for a constant, variable, load,
and multiplication expression. Its Lean constructor checks live in
`Flapjack.Test.CrepeDestConstParity`.
`crep_arith_lookup_code_probe.out` records the original
`OPTION_MAP (simp_prog ## I)` result for a nonempty code map, directly
exercising the result side of the local `lookup_code` lemma at
`cakeml/pancake/proofs/crep_arithProofScript.sml:162`. Its Lean comparison
uses the exact `lookupCrepHolCode` path in
`Flapjack.Test.CrepeArithLookupCodeParity`.
`crep_dest_2exp_probe.out` records direct HOL EVAL of
`crep_arith$dest_2exp_def` at `cakeml/pancake/crep_arithScript.sml:15`, including
the corresponding `word_lsl 1w` results for successful exponents. Its Lean
destination, shift, and width checks live in `Flapjack.Test.CrepeDest2ExpParity`.
The fixture also evaluates representative instances of the proof helper
`dest_2exp_bound` at `cakeml/pancake/proofs/crep_arithProofScript.sml:10`;
the Lean all-dimension support theorem remains untagged until its explicit
finite-index and `word_log2` encodings are reviewed against HOL.
`hol_fcp_index_n2w_probe.out` records direct HOL EVAL of `n2w` plus concrete
instances of `word_index_n2w` and the underlying `BIT` values for zero, one,
and the highest bit of an 8-bit word; it also records `dimindex (:8) = 8` to
show the sampled indices are valid. The original definition is HOL4
`wordsTheory.n2w_def` (`$HOL/src/n-bit/wordsScript.sml:54-56`);
`word_index_n2w` at lines 1765-1774 states the general numeric-index equation.
The kernel-checked canonical `Fin width`/BitVec equation
`holWordBitsToBitVec_n2w` is in `Flapjack.Pancake.Semantics.CrepSem.Eval`; its
zero/one/high-bit examples are in `Flapjack.Test.CrepeSimpExpParity`.
For any explicit `HolFiniteDimension`, `holFiniteWordN2W_at_index` proves that
the arbitrary-index adapter returns `Nat.testBit value (encode index)`, which
is the pointwise FCP `BIT` equation under the chosen finite-index encoding;
the Bool carrier test exercises this at multiple indices.
`hol_word_arithmetic_probe.out` records the direct HOL4 definitions
`word_add_def`, `word_mul_def`, and `word_sub_def` from the same external
`wordsScript.sml`, along with the general `word_add_n2w` and `word_mul_n2w`
theorems and 8-bit simplification examples. Lean's
`holFiniteWordSourceAdd`/`holFiniteWordSourceMul` encode the source `n2w` of
natural arithmetic on `w2n` values, with generic Fin-index transport theorems
and focused 4-bit checks in `CrepeSimpExpParity`. The pointwise `n2w`/`BIT`
equation is proved for explicit finite dimensions. The recursive
`finWordSBitSum` follows the numeric `Fin` indices and proves the `w2n`
weighted `SBIT` sum equals BitVec `toNat`; the operation adapters are also
rewritten to expose their `n2w`-of-SBitSum source shape. `holFiniteWordSourceSub`
uses the corresponding two's-complement natural formula and its transport
theorem; the test checks wraparound subtraction. The remaining representation
gap is identifying a Lean `HolFiniteDimension` witness with HOL's implicit
`finite_index` choice; the full Crep evaluator correspondence is still open.
`word_op_finite_probe.out` records the original CakeML
`wordLangTheory.word_op_def` list folds (And/Add/Or/Xor/Sub), including empty
fold values and malformed subtraction arities. This worktree's CakeML submodule
has no compiled `wordLangTheory.ui`, so regenerate this probe against a
read-only CakeML checkout with matching source and built theories by setting
`CAKEML` (the checked output was generated from matching CakeML source commit
`857f0d98da8f8a3580f3442338e697809308ede`).
`holFiniteWord_wordOp_toBitVec` proves that the explicit finite-dimension
wordOp list behavior maps through the Fin-index/BitVec conversion for every
operator and argument list; Bool-index checks are in
`Flapjack.Test.CrepeSimpExpParity`. This remains untagged because the theorem
uses explicit dimension data.
`word_sh_finite_probe.out` records the original `wordLang$word_sh_def`, its
`dimindex` guard, and zero, valid, width, and above-width examples. Its source
is `cakeml/compiler/backend/wordLangScript.sml`; the direct Lean transport
`holFiniteWord_evalPanShift_toBitVec` covers all four shift operators for every
explicit finite dimension. A Bool-index instance is checked in
`Flapjack.Test.CrepeSimpExpParity`. This is evaluator infrastructure and does
not by itself establish the unrestricted HOL-polymorphic
`simp_exp_correct1` statement. Regenerate against a read-only CakeML checkout
with matching built theories by setting `CAKEML`; the checked output was
generated from source commit `857f0d98da8f8a3580f3442338e697809308ede`.
`pan_fixed_load_probe.out` prints HOL `mem_load_byte_def` and
`mem_load_32_def` directly, together with the imported `byte_align_def`,
`aligned_def`, `align_def`, `get_byte_def`, `byte_index_def`, and
`word_of_bytes_def`. It evaluates domain misses, alignment failure, both
endiannesses, 8-bit/64-bit word instances, and the 24-bit cases
`byte_align 5w = 4w`, little-endian `mem_load_byte ... {4w} F 5w = SOME 51w`,
and big-endian `mem_load_byte ... {4w} T 5w = SOME 17w`. Those rows
also include the width-24 32-bit load at address 4, whose `word32` result is
`0x22113322`. The added width-4 rows cover both endian branches at addresses 0
and 1 with the nonzero four-bit word `0xB`. Little endian uses
`address MOD 0`, so its index is the address: address 0 extracts `0xB`, while
address 1 shifts past the word and extracts zero. Big endian uses natural
subtraction `0 - 1 - (address MOD 0)`, which saturates to zero at both
addresses, so both extract `0xB`. The accompanying `byte_index`/`get_byte`
rows record the little-endian `1 MOD 0` formula directly. Matching Lean guards
live in `Flapjack.Test.PanSemStateEvalParity`. The width-4 `mem_load_32` rows
exercise the same formulas over addresses 0 through 3: little endian packs the
four bytes `[0xB, 0, 0, 0]` to `0xB`, while big endian packs `[0xB, 0xB, 0xB,
0xB]` to `0x0B0B0B0B`. The direct `word_of_bytes` EVAL rows reduce those packed
results to `11w` and `0xB0B0B0Bw`. They differ
from production RISC-V's `panRiscVByteAlign 3 5 = 3`,
which misses the domain containing only address 4. RISC-V rounds by a multiple
of three while the HOL definition aligns using `LOG2 (dimindex DIV 8)`. The
`holByteAlignedRiscVMemoryModel` overlay uses the source alignment formula and
returns the probed byte while leaving the other RISC-V model operations
explicit. Focused checks for the source overlay and production mismatch are in
`Flapjack.Test.PanFixedLoadParity`. The generic finite-word
`holFiniteWordSourceMemoryModel` adapter uses the same alignment formula and
direct HOL `get_byte` index arithmetic; tests cover both endiannesses at width
24, plus a 24-bit 32-bit-load fixture. Its `aligned` operation is now expressed
as divisibility by the requested byte alignment. The `setByte` operation
implements the pointwise bit-slice cases from HOL `set_byte_def`, and
`wordOfBytes` follows the recursive shape from HOL `word_of_bytes_def`.
`word_byte_memory_probe.out` records those source definitions, the width-17
four-write expansion, and direct HOL EVAL for little- and big-endian width-17
fixtures. A generic theorem relating the explicit dimension enumeration to
HOL's native finite-index word operations remains open. The generic
Crep source helpers `crepHolEvalMemLoadByte` and `crepHolEvalMemLoad32`, plus
their equations to `panModelReadByte`/`panModelRead32`, are in
`Flapjack.Pancake.Semantics.CrepSem`; they keep the `PanMemoryModel` explicit
and remain untagged until its operations are related to HOL's word-derived
`byte_align`, `get_byte`, `aligned`, and `word_of_bytes` for arbitrary finite
dimensions.
The direct `crepSem$eval` fixtures `crep_eval_load_byte_probe.out` and
`crep_eval_load_32_probe.out` also cover width 24: `LoadByte` at address 5
returns `Word 51w` little-endian and `Word 17w` big-endian; `Load32` at address
4 returns `Word 0x113322w`. `Flapjack.Test.PanFixedLoadParity` compares those
original rows against the finite-word source evaluator and records the RISC-V
runtime adapter's `none` result at the same alignment boundary.
The direct width-1 rows `load32_aligned_width1_address0=SOME ...` and
`load32_unaligned_width1_address1=NONE` were refreshed
with `HOL4=/home/zksecurity/HOL CAKEML=/home/zksecurity/flapjack2/cakeml
HOL_PROBE_ONLY=pan_fixed_load_probeScript.sml scripts/hol-probes/regenerate.sh`
against matching CakeML source commit `857f0d98da8f8a3580f3442338e697809308ede`.
The `aligned_width1_address0=T` and `aligned_width1_address1=F` rows confirm
that HOL accepts address zero and rejects address one; `byte_align_width1_address1`
records the source `byte_align` definition at that carrier width. The tagged
Lean `panMemLoad32HOL` states the equivalent modulo-four guard directly; the
matching Lean fixture checks that address zero returns `0x00010001` and address
one returns `none`. HOL EVAL leaves the raw width-one pack in
`get_byte`/shift/concatenation form; a direct HOL simplifier/evaluator pass
proves that expression equals `0x00010001w`. The Lean check computes the same
tagged result.
Direct `word_of_bytes` rows pin the four-byte
little-endian and big-endian packs to `0x44332211` and `0x11223344`; the Lean
fixture checks the same `RiscV.panRiscVWordOfBytes` results. The probe driver
runs this script from `pancake/semantics/.hol/objs` when that directory is
present so it resolves the built `panSemTheory` without modifying the source
submodule.
`word_byte_memory_probeScript.sml` is run from HOL4's built
`src/n-bit/.hol/objs` directory and probes `byteTheory` directly, so it does not
depend on built CakeML Pancake theories. Refresh it with
`HOL_PROBE_ONLY=word_byte_memory_probeScript.sml scripts/hol-probes/regenerate.sh`.
The width-17 word fixtures use four distinct bytes, `0x11`, `0x22`, `0x33`,
and `0x44`, so the HOL recursive overwrite order is visible: little-endian
reduces to `0x2211w` and big-endian to `0x1122w`. The nonzero-initial-value
`set_byte` rows use HOL's proved `set_byte_bit_field_insert` rewrite followed
by evaluation, preserving the other bits while reducing to concrete words.
For initial value `0x1abcdw`, byte `0xa5w` at address `1w` reduces to
`0x1a5cdw` little-endian and `0x1aba5w` big-endian.
The width-5 rows record HOL's `MOD_0` theorem and the resulting zero-byte-slot
`byte_index` branches, which the Lean source adapter handles explicitly.
`crep_arith_eval_mul_const_probe.out` records direct HOL EVAL of
`crepSem$eval` after `crep_arith$mul_const` for zero, one, power-of-two, and
general multipliers, with a word-valued local. Its matching production runtime
cases live in `Flapjack.Test.CrepeMulConstParity`.
`crep_simp_exp_probe.out` records direct HOL EVAL of
`crep_arith$simp_exp_def` (`crep_arithScript.sml:59-64`) for constant folding,
left/right constant multiplication, nested multiplication, and recursive
load/word-operation children. It also evaluates the original
`crepSem$eval` before and after simplifying `Crepop Mul [Var 2; Const 8w]`
with local 2 set to `Word 5w`; the simplifier yields `Shift Lsl (Var 2)
(Const 3w)` and both evaluations return `SOME (Word 40w)`. The matching
production source-runtime observation and all-width theorem application are
in `Flapjack.Test.CrepeSimpExpParity`. These checks exercise the result shape,
but do not close the polymorphic evaluator-preservation theorem
`simp_exp_correct1`; the explicit finite-index adapter's relation to HOL's
implicit word carrier remains open.
`crep_eval_probe.out` records direct HOL EVAL of the `Const`, `Var`, `Load`,
`LoadGlob`, `BaseAddr`, and `TopAddr` constructor cases from
`cakeml/pancake/semantics/crepSemScript.sml:90-166`. The width-8 production
checks live in `Flapjack.Test.CrepEvalConstructorParity`; generic word-result
projection equations live beside `evalCrepRuntimeExp` in
`Flapjack/Pancake/Semantics/CrepSem.lean`. These equations cover a constructor
scope slice only: the target-extended runtime state and the remaining
word-operation and byte-load cases still need an evaluator correspondence.
For the isolated `Const` case of local `simp_exp_correct1`, this direct
`eval_def` observation pairs with the constant-preserving simp results in
`crep_simp_exp_probe.out`; the exact word_lab theorem case and Fin 4 fixture
are `crepSimpExpCorrect1ConstHolFiniteWordSourceCase` and its nearby example
in `Flapjack.Test.CrepeSimpExpParity`. The assembling theorem remains open.
`crep_eval_cmp_rv64_probe.out` records direct HOL `crepSem$eval` results for all
eight `asm$word_cmp_def` constructors, including signed-versus-unsigned order,
negations, and overlapping/disjoint bit tests. Matching source-runtime
comparisons are checked in `Flapjack.Test.CrepeSimpExpParity`; the generic
finite-index-to-BitVec comparison equation is `holFiniteWord_evalPanCmp_toBitVec`.
`pan_globals_compile_top_probe.out` records original Pancake HOL evaluation
of `pan_globals$compile_top` for an absent start function (the total empty-list
result), a present `main` entry, and a global initializer in a nonempty
declaration list. Its Lean checks live in
`Flapjack.Test.PanGlobalsCompileTopForStartParity`.
`pan_structs_afindi_map_probe.out` records direct HOL EVAL for the hit and
miss cases of `afindi_MAP_eq` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:356`; its matching Lean
checks live in `Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_afindi_length_probe.out` records direct HOL EVAL of first and
last successful key indices against `afindi_less_length` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:345`; Lean checks the same
rows in `Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_afindi_el_probe.out` records direct HOL EVAL of the first
component at first, middle and last successful `afindi` indices for
`afindi_EL` at `cakeml/pancake/proofs/pan_structsProofScript.sml:430`; Lean
checks the equivalent `getElem?`-based API in
`Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_alookup_afindi_probe.out` records direct HOL EVAL of present,
missing and duplicate-key cases for `ALOOKUP_eq_afindi` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:405`; matching `List.lookup`
regressions live in `Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_compile_correct_probe.out` records direct HOL EVAL of
`convert_v_def` on a named record, source/converted `Skip` evaluator equations,
and zero-clock timeout / positive-clock decrement `Tick` evaluator equations,
plus HOL simplifier reduction of `convert_s_def` over nonempty local, global,
exception-shape, and function-code finite maps using the finite-map lookup
rules. These are used in `compile_correct` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:1034`. These rows only check
the listed evaluator and conversion equations; they do not prove the full
theorem. The finite-map state interface and actual `compile_correct` Skip,
Tick, Break, and Continue case specializations are tracked separately. The
parent theorem remains open while other statement cases and the complete
induction are unfinished. Lean regressions live in
`Flapjack.Test.PanStructsCompileCorrect`.
`pan_structs_res_convert_probe.out` records direct HOL EVAL of the `pan_structs`
result conversion and classification functions at
`cakeml/pancake/proofs/pan_structsProofScript.sml:992-1009` and `:1028-1031`:
`convert_res` on `SOME Break`, the recursive `SOME (Return (ValWord 7w))` and
`SOME (Exception «e» (ValWord 5w))` clauses, and the `NONE`, `Error`, `TimeOut`,
`Continue`, and `FinalFFI` catch-alls; `is_cont_res` on `NONE`, `Break`,
`Continue`, `Error`, `TimeOut`, and `Return`; and `res_vs` on `Return`,
`Exception`, `Break`, `NONE`, and `Continue`. It is regenerated with
`HOL4=/home/zksecurity/HOL CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=pan_structs_res_convert_probeScript.sml
scripts/hol-probes/regenerate.sh`, and the same rows are replayed over the exact
`PanSemResultExact`/`ValueHOL` carriers through `convertResHOL`, `isContResHOL`,
`isContResHOL_eqDisj`, and `resVsHOL` in
`Flapjack.Test.PanStructsResConvertParity`.
`pan_structs_compile_exp_correct_probe.out` records HOL evaluations of Local
and Global variable-constructor instances and Const-, RStruct-, NStruct-,
NField-, RField-, Op-, Load-, and faithful Load32-constructor instances of
`compile_exp_correct`; each
five-element tuple contains old shape, semantic value shape, field validity,
source evaluation, and converted target evaluation. The Var, Const, Shift, and
faithful Load32 cases use `evalPanValueExpFull`; Load32 supplies an explicit
model-backed `read32` access. RStruct, NStruct, NField, RField, Op, Load, and
LoadByte retain their existing evaluator interfaces. These constructor cases
are exercised by finite-map regressions in
`Flapjack.Test.PanStructsCompileCorrect`. They are constructor specializations
of the universal HOL theorem, not a complete induction port, and remain
untagged where the Lean state/evaluator interfaces differ. The RStruct and Op
rows use nonempty expressions: the former checks aggregate construction, while
the latter checks that a binary Op retains exactly its two word operands after
value conversion. Both validate all three constructor conclusions. The
nonempty-list
row separately checks source `OPT_MMAP` success, pointwise compiled-expression
correctness, and the converted `compile_exps` result for the local HOL helper
`compile_exp_correct_mmap_helper`; Lean proves the corresponding production
list-evaluation prerequisite in `panStructCompileExpsEvalOfPointwiseCorrect`.
The Load row directly exercises an explicit two-word memory read and is paired
with a Lean source/converted evaluation fixture. The nested named-load row
checks a multiword `Pair` containing a named `Inner`, including source and
compiled shapes, field validity, and both evaluator results. Its general
constructor case and the required memory-conversion induction remain open. The
`size_of_compile_shape_comb` row separately directly evaluates the HOL
`size_of_compile_shape` prerequisite at
`cakeml/pancake/proofs/pan_structsProofScript.sml:512`; the generic Lean theorem
and concrete fixture live in `Flapjack.Test.PanStructsCompileShapeParity`.
`pan_structs_mem_load_conversion_probe.out` directly evaluates the HOL One
branch, a nested three-word Comb branch, and a nested named `Pair`/`Inner`
branch of `mem_load_conversion` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:609`. The named row prints
the concrete `struct_infos_ok` result separately as `T` (proved from HOL's
`struct_infos_ok_cons`) and prints both the source `NStruct` load and converted
target `RStruct` load values, followed by their expected-value checks. The
corresponding production fuel-loader conversion theorem is kept untagged and
paired with a Lean execution regression in `Flapjack.Test.PanStructsCompileCorrect`.
`pan_structs_shape_context_drop_probe.out` records direct HOL EVAL of
`size_of_sh_with_ctxt_drop` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:99` for `One`, a suffix-found
named structure, and a nested `Comb`. The exact-carrier theorem over
`ShapeHOL`/`StructContextExact` and matching Lean rows live in
`Flapjack.Pancake.Proofs.PanStructs.CompileCorrect` and
`Flapjack.Test.PanStructsShapeContextDropParity`.
`pan_structs_value_validity_probe.out` records direct HOL EVAL of the word,
matching/mismatching named-record, missing-context, and duplicate-key first
match rows for
`v_flds_ok_def` and `is_wf_shape_v_def`; the matching Bool-valued Lean
definitions and regressions live in
`Flapjack.Pancake.Proofs.PanStructs.CompileCorrect` and
`Flapjack.Test.PanStructsValueValidityParity`.
`pan_structs_afindi_append_probe.out` records direct HOL EVAL of prefix-hit,
shifted suffix-hit and missing-key rows for `afindi_append` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:417`; matching Lean cases
live in `Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_dropwhile_afindi_probe.out` records direct HOL EVAL of first-hit,
later-hit and absent-key cases for `dropWhile_afindi` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:334`; matching Lean rows
live in `Flapjack.Test.PanStructsAfindiParity`.
The `longdiv_code_probe.out` fixture probes the original software LongDiv
helper at `cakeml/compiler/backend/data_to_wordScript.sml:829-867` and the
RISC-V target's deliberate LongDiv encoding rejection.
The `prog_if_probe.out` fixture probes the comparison-materialization helper
`prog_if_def` at `cakeml/pancake/crep_to_loopScript.sml:34`, including its
canonical live-set insertion order.
The `compile_crepop_probe.out` fixture probes both RISC-V and ARMv7 `Mul`
branches of `compile_crepop_def` at line 42 of the same source.
`crep_to_loop_compile_exp_probe.out` starts with a direct `prog_if_def` row on
exactly the arguments used by the `cmp` expression row, then records direct HOL
EVAL rows for `compile_exp_def` and its local mutual list helper `compile_exps`,
including variable lookup, Load32 temporary allocation, n-ary Op mapping, Mul
lowering, comparison temporaries/live-set insertion, Shift, and list
compilation. The
exact-carrier Lean equations are in
`Flapjack.Test.CrepToLoopCompileExpExactParity`. The tagged definitions use the
source `context` and Loop carriers; the generic production compiler is not
claimed to route through them yet. Exact `compile_def` is now ported over the
HOL carriers in `Flapjack.Test.CrepToLoopCompileExactParity`; production
routing through it is tracked by bead `flapjack-pxn.18.5.6.28.1`, while the
dependent `comp_func_def` port remains separate work.
`crep_to_loop_compile_probe.out` records direct HOL EVAL results for all 19
constructors in `compile_def`, including a function call with a mapped label,
mapped return, and handler. Its exact-carrier Lean equations are in
`Flapjack.Test.CrepToLoopCompileExactParity`. The compiler is still proof-side;
the production `CrepProg`/`LoopProg` path does not yet use the exact carriers,
and a separate production bridge remains required.
The original Pancake source-level support boundary is also explicit in
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:2285-2291`: `LLongDiv` is
accepted by `loop_inst_ok` only for `x86_64`. Consequently, RISC-V parity must
port the `data_to_word` helper path rather than add a direct RISC-V lowering
for source `LLongDiv`.
`crep_to_loop_locals_rel_probe.out` records direct observations for
`locals_rel_def` at `cakeml/pancake/proofs/crep_to_loopProofScript.sml:101-111`.
HOL `crepLang$varname = num` (`crepLangScript.sml:19`), so the context's `vars`
is a `num |-> num` finite map; the fixture uses a `num`-keyed `vars`
(`0 |-> 2`), a two-member `num_set`, and a nonempty `num_map`. Besides atomic
component rows, it decides the whole relation on a concrete context/locals
pair by kernel-checked proof (`prove` with a `rw`/`fs`/`EVAL_TAC` tactic) since
the relation is universally quantified over `num`: `locals_rel_true=T` is
proved, and `locals_rel_domain_false=F` / `locals_rel_value_false=F` report the
relation's truth value only after the kernel proof of its negation succeeds.
The exact-carrier Lean counterparts are `Flapjack.CrepToLoop.crepToLoopLocalsRelExact`
(tagged `locals_rel_def`) with the kernel-checked examples in
`Flapjack.Test.CrepToLoopParity`.

The same probe also records cut-set rows for
`crep_to_loopProofScript.sml:236-244` `locals_rel_cutset_prop`: `lBig` / `tBig`
extend the fixture set / target map with an extra member (`cutset_set_lookup`,
`cutset_target_lookup`), and the direct kernel-decided rows
`locals_rel_cutset_second_true=T` (the strengthened second relation) and
`locals_rel_cutset_after_true=T` (the relation restricted to the smaller
cut-set) pin the HOL conclusion shape. The exact-carrier counterpart is the
tagged `Flapjack.CrepToLoop.crepToLoopLocalsRelExact_cutset_prop`, whose
`subspt` premise is rendered by `Flapjack.sptSubspt` (see
`Flapjack/Misc/Sptree.lean`).

`pan_globals_mem_functions_probe.out` records direct HOL EVAL of the
`panLang$functions` projection and the membership instance characterized by the
local theorem `MEM_functions` at
`cakeml/pancake/proofs/pan_globalsProofScript.sml:2380-2387` (the theorem is
`[local]`, so it has no theory-database name). The exact word-indexed port
`Flapjack.Pancake.PanLang.functionsHOL` and its membership theorem
`MEM_functionsHOL` are paired with the Lean regression
`Flapjack.Test.PanGlobalsMemFunctionsHOLParity`.

`pan_lang_size_probe.out` loads the real compiled CakeML `panLangTheory` and
prints the `Datatype`-generated size equations `mlstring_size_def`,
`shape_size_def`, and `exp_size_def`, the `MEM_IMP_shape_size` and
`MEM_IMP_exp_size` statements, and concrete `EVAL` rows for representative
`shape_size`/`exp_size` applications. It replaces an earlier version that
reconstructed the datatypes locally, which pinned `MEM_IMP_shape_size` and
`MEM_IMP_exp_size` only by analogy. The equations are transcribed in
`Flapjack/Pancake/PanLang/Shape.lean` and `Flapjack/Pancake/PanLang/Exp.lean`;
the generated equations are not textual HOL declarations, so the transcriptions
and their `@[hol]`-tagged `MEM_IMP_*` theorems cannot reference them directly.
The matching fixtures live in `Flapjack.Test.PanLangGeneratedSizeParity`.
Regenerate with `HOL_PROBE_ONLY=pan_lang_size_probeScript.sml
scripts/hol-probes/regenerate.sh` against a CakeML checkout whose compiled
theories match the submodule source commit.

From the repository root, with HOL4 and the CakeML checkout available,
regenerate both checked-in outputs with:

```sh
scripts/hol-probes/regenerate.sh
```

Normal Lean CI consumes the checked-in output and does not require HOL4. A
reviewer with HOL4 can rerun the command and inspect the diff. Each probe's
declaration and source path make its reference boundary explicit. The script
is incremental: a fixture is rerun only when its probe, the Pancake theory it
observes, or the script itself is newer than that fixture. Delete a fixture
when a forced regeneration is desired. To refresh one fixture while developing,
set `HOL_PROBE_ONLY` to its probe filename, for example:

```sh
HOL_PROBE_ONLY=pan_globals_compile_top_probeScript.sml scripts/hol-probes/regenerate.sh
```

The checked-in source-facing compiler corpus at
`scripts/parity-small-corpus.json` complements these semantic probes. Run
`scripts/parity-small-corpus.py` after building `flapjack-compile` to invoke
the original `cake --pancake --target=riscv` compiler and Flapjack on the same
five supported programs. The manifest records each original Cake stdout hash,
the CakeML semantic definition exercised by the fixture, and the P1 beads that
own any current generated/user-code differences. The runner compares the
complete runtime, generated-entry, and user-function sections; it does not
normalize instruction bytes.

The focused Pan-to-Crep fixtures are summarized in
[`docs/PAN-TO-CREP-PARITY-COVERAGE.md`](../../docs/PAN-TO-CREP-PARITY-COVERAGE.md).
CI validates that each listed direct-HOL case remains present in its committed
probe output and in the corresponding Lean test with
`scripts/pan-to-crep-coverage-report.py --check`.

`loop_sem_lprefix_lub_probe.out` records the empty and singleton results, a
two-element prefix chain, and HOL EVAL of `build_lprefix_lub` for conflicting
non-chain families. HOL leaves the selected event as Hilbert choice (`@x`) at
the first conflicting position; `build_lprefix_lub_thm` only characterizes
the LUB when the input is an `lprefix_chain`. The matching source review is beside
`SemanticsRunResHOL` in `Flapjack/Pancake/Semantics/PanProps.lean`. Refresh it
with `HOL_PROBE_ONLY=loop_sem_lprefix_lub_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`crep_inline_alist_map_probe.out` records direct HOL EVAL of the inline-map
input carrier at `crep_inlineScript.sml:259-269`: `alist_to_fmap` keeps the
first duplicate association-list binding, lookups for another row are
preserved, DOMSUB removes the selected key while retaining other lookups, and
`CARD (FDOM ...)` is 0 for empty, 1 for a single binding, and 2 for duplicate
`f` rows plus a distinct `g` row. The input row order remains visible. The
exact Lean input carrier and regressions are in
`Flapjack.Pancake.CrepInline.Pass` and
`Flapjack.Test.CrepInlineFmapParity`. Refresh it with
`HOL_PROBE_ONLY=crep_inline_alist_map_probeScript.sml scripts/hol-probes/regenerate.sh`.

`crep_inline_helper_probe.out` records direct HOL EVAL checks for the exact
`var_prog_def`/`vmax_prog_def` inputs used by the indexed-carrier ports
`crepVarProgHOLExact` and `crepVmaxProgHOLExact`: call argument/return/handler
ordering, ExtCall's four variable operands, the empty Skip case, and
StoreGlob's ignored address. It also retains the existing `unreach_elim` and
inlining helper rows. Exact-carrier Lean guards are in
`Flapjack.Test.CrepeInline`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_inline_helper_probeScript.sml scripts/hol-probes/regenerate.sh`.

`crep_inline_structural_probe.out` records direct HOL EVAL of the structural
`Dec`, `Seq`, `If`, and `While` clauses of `inline_prog_def`
(`crep_inlineScript.sml:239-248`) on exact eight-bit programs with an empty
inline map. The partial callback-based exact-carrier factoring helper and its
guards are in `Flapjack.Pancake.CrepInline.Pass` and
`Flapjack.Test.CrepInlineStructuralHOLParity`; the helper remains untagged and
does not claim the omitted `Call`/finite-map recursion. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_inline_structural_probeScript.sml scripts/hol-probes/regenerate.sh`.

`crep_inline_transform_eoc_probe.out` records direct HOL EVAL of every arm of
`transform_eoc_def` (`crep_inlineScript.sml:137-145`), including Call return
metadata, recursive handlers, structural control flow, Return/`MAP2` length
truncation, and the default clause. The exact width-indexed Lean port is
`transformEocHOLExact` in `Flapjack.Pancake.CrepInline.Pass`; its guards are in
`Flapjack.Test.CrepInlineTransformEocParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_inline_transform_eoc_probeScript.sml scripts/hol-probes/regenerate.sh`.

`crep_inline_transform_branch_probe.out` records direct HOL EVAL of every arm
of `transform_branch_def` (`crep_inlineScript.sml:155-164`), including nested
While loop-depth increments and current-depth Call handlers. The exact
width-indexed Lean port is `transformBranchHOLExact` in
`Flapjack.Pancake.CrepInline.Pass`; its guards are in
`Flapjack.Test.CrepInlineTransformBranchParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_inline_transform_branch_probeScript.sml scripts/hol-probes/regenerate.sh`.

`crep_inline_nontail_probe.out` records direct HOL EVAL of
`inline_nontail_def` (`crep_inlineScript.sml:193-201`), including zeroed
temporary returns, nested argument loading, caller-result `MAP2` truncation,
and a nested-declaration shape mismatch. The exact width-indexed Lean port is
`inlineNontailHOLExact` in `Flapjack.Pancake.CrepInline.Pass`; guards are in
`Flapjack.Test.CrepInlineNontailParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_inline_nontail_probeScript.sml scripts/hol-probes/regenerate.sh`.

`crep_inline_has_return_probe.out` records direct HOL EVAL of every clause of
`has_return_def` (`crep_inlineScript.sml:41-50`), including the three Call
return-info cases and recursive handlers. The exact width-indexed Lean port is
`hasReturnHOLExact` in `Flapjack.Pancake.CrepInline.Pass`; its guards are in
`Flapjack.Test.CrepInlineHasReturnParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_inline_has_return_probeScript.sml scripts/hol-probes/regenerate.sh`.

`fupdate_list_append_commutes_probe.out` records the imported original HOL
theorem `finite_mapTheory.FUPDATE_LIST_APPEND_COMMUTES` from
`/home/zksecurity/HOL/src/finite_maps/finite_mapScript.sml:2960`, plus direct
HOL evaluation of disjoint and overlapping key examples. The theorem is used
in `cakeml/pancake/proofs/pan_to_crepProofScript.sml:1001,1197`; its exact
HOL-equality Lean port and guards are in `Flapjack.FiniteMap.Basic` and
`Flapjack.Test.FupdateListAppendCommutesParity`. It remains untagged because
`scripts/check-hol-refs.py` currently accepts only `cakeml/...sml` references.
Refresh it with
`HOL_PROBE_ONLY=fupdate_list_append_commutes_probeScript.sml bash scripts/hol-probes/regenerate.sh`.

`eval_nested_decs_seq_res_var_eq_probe.out` records direct HOL EVAL cases for
`pan_to_crepProofScript.sml:596-620`: nested declaration evaluation restores
both previously bound and absent locals, unequal name/expression lengths
produce the HOL `Skip` case, and the four theorem premises are checked with
valid and rejected inputs. The exact evaluator theorem and Lean cases are in
`Flapjack.Pancake.Proofs.PanToCrep.EvaluateNestedDecs` and
`Flapjack.Test.CrepNestedDecsSeqResVarEqParity`. Refresh it with
`HOL_PROBE_ONLY=eval_nested_decs_seq_res_var_eq_probeScript.sml scripts/hol-probes/regenerate.sh`.

`eval_nested_decs_load_globals_probe.out` records direct HOL EVAL instances of
`evaluate_nested_decs_load_globals` at `pan_to_crepProofScript.sml:4139-4176`:
loading one global word while restoring an old local, and loading a two-word
struct while restoring one old local and preserving an absent local. Each row
checks the complete theorem premise conjunction, including `globals_lookup`,
the 32-word limit, distinct target locals, and the exact generated
`load_globals` expression count, then evaluates the theorem's full result and
post-state equation. Refresh with
`HOL_PROBE_ONLY=eval_nested_decs_load_globals_probeScript.sml scripts/hol-probes/regenerate.sh`.

`pan_word_of_bytes_overlong_probe.out` records direct HOL evaluation of
`byteTheory.word_of_bytes` (`/home/zksecurity/HOL/src/n-bit/byteScript.sml:197`),
the decoder installed by the exact shared-memory loads
(`cakeml/pancake/semantics/panSemScript.sml:517,524` and `crepSemScript.sml` as
`word_of_bytes F 0w new_bytes`) for FFI-returned lists longer than one word.  The
rows show that the first byte of each residue wins, so at widths at least 8
overlong lists keep exactly the first `dimindex DIV 8` bytes and discard the
trailing bytes
(`w8_overlong_three=1w`, `w16_overlong_three=513w`, `w64_overlong_ten=
0x807060504030201w`). The `w1`/`w7` rows also pin the sub-byte edge where
`dimindex DIV 8 = 0`: the initial address-zero write retains the available low
bits of the first byte. This is the source oracle for the untagged Lean bridge
`Flapjack.Pancake.Semantics.ShMemBytesBridge` and its `decide` regression
instances (`panWordOfBytesHOL false 0 bs = crepClockWordOfBytes
(bs.map UInt8.ofBitVec)`).  It is rooted at the separate HOL checkout (like
`fupdate_list_append_commutes_probe`), so no CakeML build is needed.  Refresh
with `HOL_PROBE_ONLY=pan_word_of_bytes_overlong_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`sptree_set_ops_probe` evaluates the sptree set operations used by `loop_live`
(`sptree$union`/`inter`/`delete`, `backend_common$list_delete`, `list$oEL`) on
small `fromAList` trees and records their `toAList` key order, emptiness and
`oEL` results.  `Flapjack.Test.SptreeSetOpsParity` checks the Lean renderings
in `Flapjack/Misc/Sptree.lean` against every row.  Refresh with
`HOL_PROBE_ONLY=sptree_set_ops_probeScript.sml scripts/hol-probes/regenerate.sh`.

`sptree_inter_mixed_probe` evaluates the HETEROGENEOUS `sptree$inter`
(`'a num_map -> 'b num_map -> 'a num_map`) on mixed-payload `fromAList` trees and
records that the result keeps the LEFT operand's values on keys present in both
trees; it loads only `bossLib`/`sptreeTheory` (no CakeML `preamble`), so it runs
in a bare HOL session.  `Flapjack.Test.SptreeSetOpsParity.sptreeInterMixedGuard`
checks the Lean `sptInter` against every row.  Refresh with
`HOL_PROBE_ONLY=sptree_inter_mixed_probeScript.sml scripts/hol-probes/regenerate.sh`.
