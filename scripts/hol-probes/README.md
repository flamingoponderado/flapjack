`lab_implicit_section_zero_probe.out` records six original ignored-zero,
implicit-section-base and nonzero-label positions. Executed collectors replay
matching pre-encoding lines using actual instruction counts. This pins the
section-zero convention and exact original target bytes for a direct cross-section
jump followed by Const. It is not complete encoded-line-length or finite-map
correspondence for all inputs or duplicate section names.

`stack_to_lab_executed_input_probe.out` records seven original native fallback
and section observations. The four residual operations flatten to empty lines;
the new Flapjack native boundary rejects them. Skip remains a valid empty
program. Seq and distinct LocValue fields pin original final-label and target
order without extra entry aliases or fresh-label maxima. HOL has no such guard:
these rows do not claim a compiler simulation or original guard declaration.

`stack_to_lab_executed_codec_probe.out` records nine fresh original native
constructor/operand observations, including AddCarry's four positions, an
unsupported overflow result, memory offsets, Cbw's address/value/store order,
embedded NUL/high-byte names, nonzero LabAsm position with byte caches, and an
80-bit constant. StackToLabExecutedCodecParity kernel-replays these source rows
and checks supported conversion/rejection boundaries. The codec is untagged
Flapjack interface infrastructure with independent successful-output recovery;
these rows do not assert a HOL codec, production wiring, or semantic simulation.

ssa_map_bounds_probe.out captures nine complete original map-validity pairs and a kernel replay of the full original local bound-monotonicity proof. Cases include empty/malformed trees, equal/raised/rejected bounds, physical registers, unbounded natural values and overwritten entries. SSAMapBoundsParity replays the same predicates and applies the full theorem to arbitrary maps/bounds. Recursive insertion is unfolded once before predicate simplification to avoid expanding dead recursive branches.
`word_program_max_unrestricted_probe.out` captures eight fresh whole-program
maximum and limit results across Seq, tail Call handler, returning Call with
handler, and Loop containing ordinary 16-bit memory. The existing program
maximum codec theorem now holds without the memory guard. Kernel fixtures check
all four original maxima/limits, actual codec acceptance and unchanged guard
rejection; the earlier 32 constructor rows and five-register rejection remain.
This is carrier correspondence, not an executed native limit route.

ssa_map_bounds_probe.out captures nine complete original map-validity pairs and a kernel replay of the full original local bound-monotonicity proof. Cases include empty/malformed trees, equal/raised/rejected bounds, physical registers, unbounded natural values and overwritten entries. SSAMapBoundsParity replays the same predicates and applies the full theorem to arbitrary maps/bounds. Recursive insertion is unfolded once before predicate simplification to avoid expanding dead recursive branches.
`word_max_inst_route_probe.out` records seven fresh original instruction maxima
and program limits. HOL max_var_inst leaves Mem Load16/Store16 to the zero
fallback, unlike its explicit Load/Store/Load8/Store8/Load32/Store32 clauses.
WordMaxInstRouteParity kernel-checks identical 32/64-bit operands and offsets
against actual production helpers; the instruction correspondence covers every
accepted codec form. Five-register AddCarry remains rejected. This repairs the
production maximum discrepancy; it does not complete the native program route.

`ssa_merge_route_probe.out` captures eight complete original merge_moves outputs
through original fromAList/toAList: empty/missing/equal/unequal, tail-first
fresh numbering, duplicate names, duplicate input-map first-match behavior,
and natural counters larger than64 bits. SSAMergeMovesRouteParity kernel-checks
the actual allocator wrapper at all identical inputs and independently checks
preserved production state counters31/47. MergeMovesRoute invokes the accepted
native definition. ProductionMergeMoves proves an unconditional codec result:
ordered move lists, fresh counter, independent state counters and both map
lookups at every key. Storage order canonicalizes to the original tree traversal;
this is not list-order equality or a full SSA simulation theorem. No performance
exception is claimed; executed compiler parity is required for integration.

`word_simp_duplicate_if_source_probe.out` captures fourteen original source
outputs: seven whole compile_exp trees across Seq/If/MustTerminate/Loop and
all optional Call bodies, plus no-hoist, zero-bound, is_simple and
non-Raise/zero/three dest_Raise_num boundaries. WordSimpDuplicateIfParity
kernel-checks identical observations. Production pre-SSA now directly composes
Seq_assoc, original const_fp, structural simp_duplicate_if and push_out_if.
Hoist probes use const_fp without extra Seq_assoc, enforce original first-result
zero guard, and normalize successful hoists with original Seq_assoc Skip.
Legacy list/fact helpers remain separate from the production composition.
This repairs flapjack-b9gd; original captured pre-SSA tree stays unchanged.

`word_simp_seq_assoc_source_probe.out` records sixteen complete original
`Seq_assoc` outputs: empty/nonempty accumulators, interior/trailing/all Skip,
left association, If, Loop, MustTerminate and both optional Call bodies.
`WordSimpSeqAssocParity` kernel-checks the fifteen accumulator trees; WordFuseConditions checks the
complete original pre-SSA compile_exp tree, now matched by the repaired
composition (flapjack-b9gd). The original expected tree was not changed. The formerly failing
`Seq Tick Skip` input and original Tick oracle are preserved; the production
accumulator now matches the original clause rather than the old Lean rewalk.

`word_simp_constant_domain_probe.out` retains all thirteen original constant-pass
trees unchanged. `WordToStackConstantDomainParity` now kernel-checks thirteen
matches, including the repaired trailing Skip. `ProductionConstantDomain`
proves codec acceptance through the actual accumulator with arbitrary accepted
prefix, arbitrary initial constant knowledge, and the actual wrapper. Its
implication permits constant branches to remove rejected code. Rejection
sentinels cover the five-register primitive inside Loop and both Call bodies.
These untagged carrier proofs do not claim HOL pass semantics, initial source
image acceptance, fusion/hoist closure, native ABI/output correspondence, or
production native routing.
ssa_map_bounds_probe.out captures nine complete original map-validity pairs and a kernel replay of the full original local bound-monotonicity proof. Cases include empty/malformed trees, equal/raised/rejected bounds, physical registers, unbounded natural values and overwritten entries. SSAMapBoundsParity replays the same predicates and applies the full theorem to arbitrary maps/bounds. Recursive insertion is unfolded once before predicate simplification to avoid expanding dead recursive branches.
`word_alloc_limit_arithmetic_probe.out` re-elaborates the numeric class and
strict-bound obligations from the original local `limit_var_props` MOD_PLUS
argument, then captures thirteen exact limit/class/strict-bound/alignment tuples.
The registered `WordAllocLimitArithmeticParity` fixtures match all four residues,
zero, multiples of four, and large unbounded Nat register IDs. Two generic kernel
applications check the actual unconditional infrastructure. These untagged lemmas
have no independent HOL theorem name and do not replace the full native program
`limit_var_props`: that still needs native `max_var_max` and `limit_var_def`.
Regenerate with `HOL_PROBE_ONLY=word_alloc_limit_arithmetic_probeScript.sml`.

`word_alloc_move_head_probe.out` freshly re-elaborates the complete local
`mov_eval_head` from its original proof and runs eleven native Move evaluations.
The matching `WordAllocMoveHeadParity` fixtures retain arbitrary untouched
state fields and compare exact results, Spt traversal order and clock. Cases
cover positive widths 1/32/64/80, parallel reads, self-copy, overwrites, repeated
sources, malformed trees and unbounded Nat destinations. Missing-source and
duplicate-destination failures are explicit sentinels. The public theorem
retains all four original premises and full state equality. Its source lookup
is SOME-guarded; neither proof nor probe claims a value for HOL THE NONE.
Regenerate with `HOL_PROBE_ONLY=word_alloc_move_head_probeScript.sml`.

`ssa_register_class_probe.out` captures eight direct MOD4 class observations, including physical-register guard boundaries and large naturals. It also rechecks the literal original local `is_alloc_var_add`/`is_stack_var_add` statements with their original proof text; source-replay rows are distinct from exported-theorem rows. `Flapjack/Test/SSARegisterClassParity.lean` kernel-replays the observations and applies both ported theorems.

`ssa_locals_rel_probe.out` simplifies the original whole generic relation with literal lookup/domain/THE clauses: eight Bool-valued success/missing-map/missing-target/wrong-value/allocation-bound/malformed-tree observations. `Flapjack/Test/SSALocalsParity.lean` replays identical inputs in the kernel; the full original definition and generic inferred type are captured.

`ssa_map_ok_probe.out` simplifies the literal original SSA map predicate and lookup clauses for five empty/valid/bound/physical/malformed-tree cases; `Flapjack/Test/SSAMapParity.lean` kernel-replays those quantified predicates. The full original definition is printed.

`ssa_setup_probe.out` captures four original word_alloc definitions and nine direct EVAL rows for empty, duplicate, malformed-tree, arbitrary-start renaming and native setup widths 1/32/64/80, plus independent 1-to-80 and 80-to-1 input/output dimensions and the full original inferred function type. `Flapjack/Test/SSASetupParity.lean` kernel-replays identical inputs and observations. Regenerate with `HOL_PROBE_ONLY=ssa_setup_probeScript.sml`.
`word_to_stack_selector_domain_probe.out` records thirteen complete original
`inst_select riscv_config 23` program trees across assignment, Set, Load,
Store, shared Store8, Seq/If/Loop/MustTerminate and optional Call bodies.
`WordToStackSelectorDomainParity` kernel-checks twelve matches and explicitly
records positive-offset Store as false: the production source-shaped Store is
not original Mem/Addr, the existing open `flapjack-pxn.10` integration gap.
The exact production counter-tree remains beside the unchanged original oracle.
`ProductionSelectorDomain` proves structural support equality and actual partial
codec acceptance/rejection equality for the executed selector and its own-
temporary wrapper, using accepted atom/address closure. It is untagged carrier
infrastructure, not universal HOL selector semantics, pre-SSA/source image
closure, native ABI/configuration correspondence, or executed native routing.
Kernel sentinels preserve five-register AddCarry rejection in Seq, Loop and
both Call bodies while accepting the original four-register operation; generic
applications include positive widths1/80 and unbounded natural temporaries.

`parmove_fstep_map_inj_probe.out` records the complete original
`fstep_MAP_INJ` statement and eight pairs of complete original output trees.
The Nat-to-Bool renaming collapses registers outside the state support while
preserving NONE; the probe proves each `inj_on_state` premise before reporting
T. Cases cover empty/self/start/search/emit/cycle/non-cycle/existing scratch.
`ParmoveFstepMapInjParity` kernel-replays both outputs and applies the actual
generic theorem with each proved local-support premise. The theorem retains
independent input/output register carriers and no global injectivity or safety
premise. This is deterministic-step renaming, not full compiler correctness.

`wordconvs_program_mono_probe.out` prints the complete original `every_var_mono`
and eleven same-input predicate pairs replayed by `WordConvsProgramMonoParity`.
These include Call NONE ignoring its populated handler, returning Calls with and
without handlers, loop cut sets, and a false implication sentinel. Regenerate with
`HOL_PROBE_ONLY=wordconvs_program_mono_probeScript.sml` against the read-only original tree.

`wordconvs_name_mono_probe.out` prints the complete original theorem and
five matching cut-set/predicate fixtures in `WordConvsNameMonoParity`, including
a non-well-formed tree and a failed implication sentinel. Regenerate with
`HOL_PROBE_ONLY=wordconvs_name_mono_probeScript.sml` using the read-only original tree.

`wordconvs_exp_mono_probe.out` freshly prints original every_var_exp_mono
and eight same-expression predicate observations. Registered WordConvsExpMonoParity
fixtures apply the full implication non-vacuously at widths1/32/64/80 for
empty/nested/duplicate/Load/Shift/ignored payloads and80-bit registers.
The final shrinking-bound sentinel rejects removal of the global implication
guard. Regression rows do not establish cross-assistant equivalence. Regenerate
with HOL_PROBE_ONLY=wordconvs_exp_mono_probeScript.sml and the read-only prebuilt
CakeML backend semantics directory.

`word_alloc_max_exp_probe.out` captures ten direct original maximum, inclusive
bound, and strict-bound sentinel triples. Registered WordAllocMaxVarExpParity
fixtures check identical recursive syntax at widths1/32/64/80 including empty
Op, duplicate/nested arguments, ignored Const/Lookup and80-bit register numbers.
The final row freshly reconstructs the complete local max_var_exp_max from
its literal proof, using original imported WordConvs monotonicity. These are
regression evidence, not cross-assistant equivalence or full pass correctness.
Regenerate with HOL_PROBE_ONLY=word_alloc_max_exp_probeScript.sml using the
read-only prebuilt CakeML backend semantics theory directory.

`word_alloc_max_inst_probe.out` records 12 direct original maximum/safety rows
and fresh Q.prove re-elaboration of the complete local max_var_inst_max theorem.
The registered WordAllocMaxVarInstParity fixtures check the same instructions
and non-vacuously instantiate the universal bound. Width64 excludes the second
FP transfer register; widths32/80 retain it, and FP-only register numbers are ignored.
These are regression evidence, not cross-assistant equivalence or production routing.
Regenerate with HOL_PROBE_ONLY=word_alloc_max_inst_probeScript.sml and the read-only
prebuilt CakeML backend theory directory.
`word_convs_every_var_inst_mono_probe.out` captures the complete exported original
monotonicity theorem and 15 actual instruction predicate pairs: fourteen valid
implication applications plus a rejecting non-64 FP second register. Kernel
fixtures replay the inputs and prove the original pointwise/source premises
internally. Widths1/8/32/64/80, immediate/register arithmetic, memory and ignored
16-bit/FP operands are covered. Regression observations do not establish
cross-prover equivalence. Regenerate with
`HOL_PROBE_ONLY=word_convs_every_var_inst_mono_probeScript.sml` from the
read-only prebuilt CakeML semantics theory directory.

`parmove_preserves_moves_parmove_probe.out` contains six direct original scheduler
observations for shared sources, a cycle, Bool registers, emitted order, self moves
and empty input. `ParmovePreservesMovesParmoveParity` replays the rows and applies
the full preservation theorem with internally checked original premises. These
fixtures are regression evidence, not a cross-prover equivalence proof. Regenerate
with `HOL_PROBE_ONLY=parmove_preserves_moves_parmove_probeScript.sml` and the
read-only prebuilt CakeML register-allocation theory directory.

`word_to_stack_comp_native_probe.out` contains 19 direct original comp_def observations,
kernel-replayed by WordToStackNativeCompileParity. Includes recursive returning/handled
Calls, valid/invalid immediates and Seq/If/Call bitmap threading. The complete
native traversal is source-reviewed; these rows do not prove cross-prover
equivalence or establish production routing/compiler correctness. Regenerate
with HOL_PROBE_ONLY=word_to_stack_comp_native_probeScript.sml and the read-only
prebuilt CakeML backend theory directory.

`word_to_stack_write_bitmap_type.sml` queries the original HOL constant type
(`α sptree$num_map -> num -> num -> β word list`) from the prebuilt
`word_to_stackTheory`; run `HOL/bin/hol run <absolute script path>` from the
original `cakeml/compiler/backend` theory directory. The payload is generic;
only wLive specializes it to unit cutsets. `word_to_stack_write_bitmap_probe`
also captures `wb_payload_nat` and `wb_payload_bool`, replayed by
`WordToStackLiveBitmapParity`. Existing unit bitmap rows are preserved.

`loop_sem_store_narrow_probe.out` captures sixteen direct original Loop
Store32/StoreByte `evaluate_def` observations at width64 (clauses325-337).
It registers the original recursive theorem with the HOL compset, without a
surrogate evaluator. Rows cover 64-to-32/8 narrowing, both endian placements,
upper-half Store32, alignment/domain/type/memory errors, unchanged other memory
and clock. Every guard in `Flapjack.Test.LoopStoreNarrowParity` cites its row;
missing production memory totalizes to the original Loc0 0 sentinel. These are
adapter checks, not full runtime hook-bundle wiring. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=loop_sem_store_narrow_probeScript.sml scripts/hol-probes/regenerate.sh`.

`stacksem_loop_recursive_probe.out` contains eleven fresh direct original
`stackSem$evaluate (Loop body, state)` observations (stackSemScript.sml:833-837).
The original evaluator performs all recursive re-entry. The Lean replay
`Flapjack.Test.StackSemLoopRecursiveParity` runs real leaf clauses and a
clock-decreasing recursive Loop function, whose factoring equation is checked
against `StackSemControlCases.evaluateLoop`. No callback supplies a preset
terminal timeout. Cases cover Continue0/Skip/Tick repeated entry, zero-clock
Tick, Break0/Break2/Continue2, Return location/error, Raise and Halt. Kernel
coverage certificates show every fixture body is handled by evaluateLeaf;
actual runtime rows compare result, clock, register1 and stack length.
This restricted test evaluator is not the total evaluate_def port. Regenerate
with `HOL_PROBE_ONLY=stacksem_loop_recursive_probeScript.sml scripts/hol-probes/regenerate.sh`.

# Original Pancake HOL probes

`word_to_stack_selector_prelude_probe.out` captures ten fresh original
`inst_select_exp riscv_config 23 23` output trees: constant, variable, CurrHeap
lookup, load, immediate addition, valid/out-of-range shifts, CurrHeap arithmetic,
and valid/large load offsets. `WordToStackSelectorPreludeParity` kernel-checks
all ten matching complete trees after the `.17.2.16` repair: constant
materialization preserves original HOL's right-associated Const/Binop subtree
inside the expression prelude and outer Load sequence. A separate kernel check
rejects the former left-associated production counter-tree. The original oracle
capture is unchanged; these samples do not establish universal selector equality.
Separate theorem applications cover
arbitrary expressions and temporaries at positive widths, including 1/80 bits
and natural register names above 64 bits; a load-tail rejection sentinel keeps
unsupported incoming preludes rejected. `ProductionSelectorPrelude` proves
actual atom/load-tail/address-wrapper carrier closure only. This does not prove
universal HOL instruction-selector equivalence, whole-program selection,
pre-SSA/source-image closure, or production native routing. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_to_stack_selector_prelude_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_to_stack_allocator_stages_probe.out` records four fresh original
pre-allocation stage-chain outputs for Skip, Tick, Raise and tail Call, following
`word_to_word$compile_single`'s SSA/dead/CSE/copy/three-to-two/unreachable/dead
order with original `two_reg_arith = F`. `WordToStackAllocatorCodecParity`
replays the same complete output trees and separately checks actual allocator
success, memory-guard failure and five-register codec rejection.
`ProductionAllocatorCodec` composes the accepted codec closures through the
real allocator wrapper and derives an existential native encoding of its actual
coloured output from accepted input and the real result equation. These finite
observations do not establish universal pass equivalence, acceptance of the
initial source-to-Word image, native ABI/output equivalence, or executed routing.
In particular, this does not source-review the production assignment-based
three-to-two implementation as a universal port of the original pass.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_to_stack_allocator_stages_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_to_stack_retained_frame_probe.out` captures eight fresh original
`compile_prog` frame projections: empty, register-edge, first/second spill,
argument-area dominance, equal demands, zero register count, and a natural
register name above 64 bits. `WordToStackRetainedFrameParity` kernel-checks
the same inputs/results and the five-register codec rejection sentinel.
`ProductionFrame` relates the actual retained allocator result's occupancy
and `cakeWordFrameSlots` to the Option-mapped native compiler frame; rejected
codecs remain `none`. This does not establish codec success, native ABI/config
or output correspondence, or executed native routing. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_to_stack_retained_frame_probeScript.sml scripts/hol-probes/regenerate.sh`.

`ParmoveAllDistinctPmovParity` replays the complete original scheduler outputs
terminal/self/chain/cycle/active from `parmove_final_probe.out` while applying
the full `ALL_DISTINCT_pmov` theorem under its real source premises. The
original quantified theorem is captured as `pm_audit_ALL_DISTINCT_pmov` in
`parmove_preservation_shape_probe.out`. Kernel boundary checks also cover
repeated scratch destinations and duplicate emitted history; scratch safety
is not a premise of this distinctness theorem. Existing original evidence is
reused, with no fresh HOL execution claimed.

`ParmoveTempPmovParity` replays the complete self/chain/cycle/active scheduler
outputs from `parmove_final_probe.out` and applies the full conditional
`pmov_not_use_temp_before_assign` port to each valid, initially safe state.
The full original quantified statement is already captured as
`pm_audit_pmov_not_use_temp_before_assign` in
`parmove_preservation_shape_probe.out`, including the unused arbitrary `i`.
The kernel tests also cover prior scratch history and distinguish captured
rows failing well-formedness or initial safety from valid theorem applications.
This reuses existing original evidence; no fresh HOL execution is claimed.

`parmove_preservation_shape_probe.out` records the original full
`inj_on_state_def` equation and its independent Option input/output carrier
type (`pm_audit_inj_on_state_def`, `pm_audit_type_inj_on_state`).
`ParmoveInjOnStateParity` checks the literal Lean predicate's support and global
NONE boundaries in the kernel, including a noninjective map accepted on a
singleton support and collisions rejected in each of the three state segments.
These checks use the existing original declaration capture; they are not fresh
original-HOL executions or a completed injective scheduler simulation.

`labsem_fp_updates_probe.out` records 29 direct original `labSem$fp_upd`
observations, paired with kernel checks in `LabSemFpUpdatesParity`. All sixteen
constructors are exercised. Cases include NaN/sign payloads, signed zero,
rounding ties, FMA operand order, aliased destinations, failure with retained
overflow writes, odd-half insertion, and actual widths8/32/64/128. The IEEE
definitions and conversions are registered in HOL's EVAL compset as in the
existing machine IEEE probes. These finite observations do not establish full
LabSem evaluator routing or cross-language IEEE equivalence. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=labsem_fp_updates_probeScript.sml scripts/hol-probes/regenerate.sh`.

`linear_scan_pure_props_probe.out` captures eighteen direct original
observations of the proposition-valued `linear_scanScript.sml` definitions:
`check_number_property` (signed bounds, branch numbering), the extra Branch
conjunct of `check_number_property_strong` against the weak form,
`check_startlive_prop` (in-range, `ndef` default, missing end, branch
numbering), `live_tree_registers` membership, `interval_intersect`,
`point_inside_interval`, `THE (SOME x)`, and two `check_intervals` instances
proved in HOL without any fact about `THE NONE` (a missing end, and a colour
clash). Closed instances are decided by EVAL/SIMP_CONV; the two
`check_intervals` rows are HOL `prove` calls. `Flapjack.Test.LinearScanPurePropsParity`
kernel-checks the same propositions over the opaque `holTheNone`. This does
not compare an unspecified `THE NONE` value across provers. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=linear_scan_pure_props_probeScript.sml scripts/hol-probes/regenerate.sh`.

`linear_scan_top_probe.out` captures fourteen direct original EVAL results
of the top-level `linear_scanScript.sml` definitions with raw sparse trees:
`find_bijection_clash_tree` (Seq/Set and Branch with a cut set),
`apply_bij_on_clash_tree`, `apply_bijection`, `size_of_clash_tree`,
`extract_coloration`, the generated `run_i_linear_scan_hidden_state` (success
and Subscript failure), and six end-to-end `linear_scan_reg_alloc` runs
(moves, forced pairs, a spilling branch, physical and stack registers).
`Flapjack.Test.LinearScanTopParity` kernel-checks every full result. These
finite rows do not prove `linear_scan_reg_alloc_correct` or route the
definitions into the compiler. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=linear_scan_top_probeScript.sml scripts/hol-probes/regenerate.sh`.

`linear_scan_generic_types_probe.out` captures the original HOL types of
eleven reg_alloc/linear_scan constants whose carriers are polymorphic:
`check_col`'s `α num_map`, `check_intervals`' colour codomain, the five
generated `*_length` exceptions, `find_last_stealable`'s interval-end
component, `run_i_linear_scan_hidden_state`'s result/exception, the unused
`nmax` argument of `linear_reg_alloc_and_extract_coloration`, and the
`define_run` carrier's field types. `LinearScanGenericTypesParity` elaborates
the Lean declarations at non-default instances of each carrier; the type rows
fix binder generality only. Regenerate with `CAKEML=...
HOL_PROBE_ONLY=linear_scan_generic_types_probeScript.sml scripts/hol-probes/regenerate.sh`.

`linear_scan_monad_probe.out` captures thirty-four direct original EVAL
results of the monadic `linear_scanScript.sml` definitions on a concrete
hidden state, printed with raw sparse-tree constructors: the conditional
interval updates (including a `Subscript` failure), `get_intervals_ct_monad`,
`remove_inactive_intervals`, colour search, spilling, colouring, stealing,
the pass-1/pass-2 steps, register exchange, `st_ex_FOLDL`,
`st_ex_FILTER_good`, `edges_to_adjlist`, the in-array register/move sorts and
list conversions, and the initial states. `Flapjack.Test.LinearScanMonadParity`
kernel-checks every full result value. These finite rows do not prove
allocator soundness or route these definitions into the compiler. Regenerate
with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=linear_scan_monad_probeScript.sml scripts/hol-probes/regenerate.sh`.

`monad_arrays_probe.out` captures eleven direct original EVAL rows of the
ml_monadBase fixed-array primitives (`Msub`/`Mupdate` in and out of range,
`Marray_length`, `Marray_sub`, `Marray_update` with the unchanged state on
failure) and reg_alloc `st_ex_MAP` (success threading the state, and the first
failure stopping the traversal with its state), replayed in
`Flapjack.Test.MonadArraysParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=monad_arrays_probeScript.sml scripts/hol-probes/regenerate.sh`.

`linear_scan_pure_defs_probe.out` captures fifteen direct original
`linear_scanScript.sml` EVAL observations of the pure live-tree and interval
definitions: get_live_tree with a branch cut set, get_live_backward,
fix_domination (both branches of the `live = LN` test), check_live_tree
(success, colour collision, branch merge), numset_list_add_if_lt/gt over a
present key, get_intervals, get_intervals_withlive, get_intervals_ct,
size_of_live_tree and both numset_list_insert variants, each compared with a
full raw sparse-tree value. `Flapjack.Test.LinearScanPureDefsParity`
kernel-replays the identical inputs and outputs. These finite rows do not
prove the allocator theorem or route these definitions into the compiler.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=linear_scan_pure_defs_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_clash_tree_probe.out` captures eight direct original register
allocator checker observations: repeated deletion, duplicate colours,
existing-name skips, partial collisions, Delta's discarded write result,
right-first Seq traversal, Branch merging and fixed-set collisions.
`Flapjack.Test.RegAllocClashTreeParity` kernel-replays the identical inputs and
full output trees. These finite regressions do not prove allocator soundness
or wire the checker into the executed compiler. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_clash_tree_probeScript.sml scripts/hol-probes/regenerate.sh`.

`stacksem_call_indirect_probe.out` captures ten direct original `stackSem$evaluate`
Call INR observations (find_code645-651, returning Call861-892): indirect and
returning success, link/target alias rejection before update, tail alias success,
nonzero entry, Word/missing/code-missing targets, timeout, and wrong returned
location after the link register is written. It projects result, clock, link3,
target4 and stack length. `Flapjack.Test.StackSemCallIndirectParity` kernel- and
runtime-replays every row with the existing source-shaped leaf evaluator for
all actual Return3/Return4 subcalls. The test callback is not a total evaluator;
no unsupported callback is reached, and full StackSem assembly remains open.
Regenerate read-only with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_call_indirect_probeScript.sml scripts/hol-probes/regenerate.sh`.
The pre-existing fourteen direct Call rows are preserved.

`pan_globals_block_alignment_probe.out` records eight original
`alignmentTheory` observations for 32/64-bit block-address subtraction:
ordinary, wrapped, zero, and unaligned addresses. The kernel replay is
`Flapjack.Test.PanGlobalsBlockAlignmentParity`. The supporting theorem is
untagged synthesized GlobalAssign proof infrastructure at the dimensions
already required by `state_rel`; it does not claim a generic external
`byte_aligned_add` port. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=pan_globals_block_alignment_probeScript.sml
scripts/hol-probes/regenerate.sh`. The runner reads original
`HOL/src/n-bit/alignmentScript.sml` and loads the standard CakeML preamble.

`stacksem_loc_value_probe.out` records six original LocValue observations from
`stackSem$evaluate`961-964: zero-offset code membership, missing code, nonzero
return and handler labels, absent return continuation, and a disabled stack.
The probe proves the nonzero label predicates in HOL, then uses those proofs
to reduce the original evaluator. Its code is typed at the actual state word
dimension (`8 stackLang$prog`). `Flapjack.Test.StackSemLocValueParity` proves
the corresponding predicates and replays the state observations in Lean.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_loc_value_probeScript.sml
scripts/hol-probes/regenerate.sh`. Total evaluator assembly remains open.

`stacksem_dynamic_stack_probe.out` captures twenty original `stackSem$evaluate`
observations for StackLoadAny and StackStoreAny (evaluate_def978-1007): disabled
operations, missing and Loc offsets, exact bounds, unaligned Words, nonzero
stack space, Loc payloads, aliased registers, and widths1/8/32/64. The matching
kernel replay is `Flapjack.Test.StackSemDynamicStackCasesParity`; these cases
remain untagged assembly fragments until the total evaluator is assembled.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_dynamic_stack_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`pan_globals_compile_top_probe.out` retains `missing_start`, `global_present`,
and `present_start`, and adds `top_missing`, `top_function`, and
`top_global_exception` for exact `compile_top_def`. The new 64-bit rows cover
parameter and inline/export metadata, absent-global reads, global initializer
address 8, and exception/new-main/function ordering. Regenerate using the built
original theories with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=pan_globals_compile_top_probeScript.sml scripts/hol-probes/regenerate.sh`.
`Flapjack.Test.PanGlobalsCompileTopExactParity` replays the new rows; it does not
claim production top-level routing or the pass semantics theorem.

`crep_inline_prog_size_type_probe.out` prints, from the real
`crep_inlineProofTheory`, the elaborated types of the generated
`crepLang$prog_size`/`exp_size` (`(α -> num) -> α prog -> num`) and the fully
typed `unreach_elim_prog_size` statement (`show_types`). It is the evidence that
the size-function domain is the same type variable `α` that indexes `α word`,
which is why the Lean rendering with an independent `α` is kept untagged
(bead `flapjack-pxn.18.5.5.50`). Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=crep_inline_prog_size_type_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`crep_lang_size_probe.out` prints HOL's Datatype-generated crepLang
`exp_size_def` and `prog_size_def` from the real `crepLangTheory`, plus five
concrete `prog_size (K 0)` `EVAL` rows at 8-bit words. They pin the untagged
transcription `Flapjack.CrepLangGeneratedSize.crepProgSizeHOL` used by the
tagged `unreach_elim_prog_size`; `Flapjack.Test.CrepLangGeneratedSizeParity`
replays the rows. Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=crep_lang_size_probeScript.sml scripts/hol-probes/regenerate.sh`.

The repository-wide parity workflow is documented in
[`docs/PARITY-TESTING.md`](../../docs/PARITY-TESTING.md).

The files in this directory execute definitions from the CakeML Pancake HOL
development and the HOL4 floating-point library. They are test-data
generators, not independent Lean reference implementations. A parity fixture
may be used to close a porting bead only when it records the original source
definition, the probe source, and the command used to regenerate its output.

`machine_ieee_fp64_arith_nan_probe.out` records (1) a kernel-proved HOL
classification theorem for `float_some_qnan`, derived from
`binary_ieeeTheory.some_nan_properties`, and (2) direct HOL EVAL results for
the qNaN-input and invalid-operation branches in
`binary_ieeeScript.sml:587-722`, using the fp64 encoding generated by
`machine_ieeeLib`. EVAL leaves the selected qNaN payload symbolic; the quiet
classification of each listed result follows by combining its exact
`float_some_qnan` branch with the proved source theorem. The rows do not print
concrete `(T,F)` classifications for each fp64 expression. Its probe is
`machine_ieee_fp64_arith_nan_probeScript.sml`; regenerate it with
`HOL_PROBE_ONLY=machine_ieee_fp64_arith_nan_probeScript.sml
scripts/hol-probes/regenerate.sh`. These rows preserve the unspecified
`float_some_qnan` payload and establish only `float_is_nan` and
`float_is_signalling`; they do not compare IEEE flags. The Lean kernel replay is
`Flapjack.Test.MachineIeeeArithNaNParity.allNaNObservations`.

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
`stacksem_labels_probe.out` records direct HOL EVAL observations for
`get_labels_def` and `loc_check_def` from
`cakeml/compiler/backend/semantics/stackSemScript.sml:667-686`. It covers the
empty LocValue/Halt cases, Seq/If/Loop propagation, direct and nested Call
return/handler labels, the source behavior that ignores a handler when the
return continuation is `NONE`, and the zero-offset domain-key case. HOL EVAL
leaves the nonzero code-lookup existential symbolic, so the probe also records
a kernel-proved witness for that alternative. The Lean replay is
`Flapjack.Test.StackSemLabelsParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_labels_probeScript.sml scripts/hol-probes/regenerate.sh`.
`loop_to_word_defs_probe.out` records direct HOL EVAL rows for the exact
`spt`-carrier loop_to_word context definitions `find_var_def`,
`find_reg_imm_def`, `toNumSet_def`, `fromNumSet_def`, and
`mk_new_cutset_def` at `cakeml/pancake/loop_to_wordScript.sml:10-53`; the
kernel-checked Lean replay is `Flapjack.Test.LoopToWordExactParity`.
`loop_to_word_locals_rel_probe.out` records direct HOL proof observations for the
source-shaped `locals_rel_def` in
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:19-24`, including a valid
mapping with an extra target local and failures for odd/zero/non-injective
register mappings, a source local absent from the context, and a mismatched
target value. It also records HOL observations for `locals_rel_insert` and
`locals_rel_insert_unmapped`, including mapped overwrite, permitted unmapped
target insertion, and collision failure (`loop_to_wordProofScript.sml:195-220`).
The same fixture prints the source conclusions for `locals_rel_get_var` and
`locals_rel_get_vars` (`:252-269`) and evaluates successful and missing-list
lookups in the exact LoopSem and WordSem state carriers. The theorem ports are
in `Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups`; the kernel-checked
replay is `Flapjack.Test.LoopToWordLocalsRelLookupsParity`. The earlier exact-
carrier relation replay remains in `Flapjack.Test.LoopToWordExactParity`.
`loop_to_word_take_word_to_bytes_probe.out` prints the proved HOL statement of
`TAKE_1_word_to_bytes`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:1449-1451`) together with
direct HOL EVAL rows for `TAKE 1 (word_to_bytes w F)` and `[get_byte 0w w F]`
at the 32- and 64-bit dimensions admitted by `good_dimindex`; both sides agree
on every row. The theorem port is `takeOneWordToBytesHOL` in
`Flapjack.Pancake.Proofs.LoopToWord.WordToBytes`; the kernel-checked replay is
`Flapjack.Test.LoopToWordTakeWordToBytesParity`.
`loop_to_word_acc_vars_acc_prime_probe.out` records direct HOL EVAL rows for the
specialisation `acc_vars_acc'`
(`cakeml/pancake/proofs/loop_to_wordProofScript.sml:979-980`) of
`loopProps$acc_vars_acc`
(`cakeml/pancake/semantics/loopPropsScript.sml:89`). Each row prints two
booleans for a concrete variable: membership in `domain (acc_vars p (acc_vars q
LN))` and in `domain (acc_vars p LN) UNION domain (acc_vars q LN)`; they agree
on every row for programs exercising Assign, Seq, If, Loop and Call. The
theorem ports are `accVarsAccHOL` in
`Flapjack.Pancake.Semantics.LoopProps.AccVars` and `accVarsAccPrimeHOL` in
`Flapjack.Pancake.Proofs.LoopToWord.AccVarsAcc`; the kernel-checked replay is
`Flapjack.Test.LoopToWordAccVarsAccParity`.
`loop_to_word_comp_exp_probe.out` records direct HOL EVAL rows for the exact
loopLang-to-wordLang expression compiler `comp_exp_def` at
`cakeml/pancake/loop_to_wordScript.sml:22-40`; its kernel-checked Lean replay
is also `Flapjack.Test.LoopToWordExactParity`.
`loop_to_word_comp_probe.out` records direct HOL EVAL rows for the initial
and memory constructor slices of `comp_def` at
`cakeml/pancake/loop_to_wordScript.sml:56-108` (Skip, Assign, valid and
malformed AddCarry Primitive arities, all three Arith constructors, Store,
SetGlobal, and the four direct memory operations), the simple control/result
clauses at `:96-110` (Break/Continue/Raise/Return/Tick/Fail/LocValue), and the
FFI and ShMem clauses at `:141-146` (`comp_ffi` and `comp_shMem`, the latter
compiling `ShMem` to `ShareInst`). Its kernel-checked Lean replay is in
`Flapjack.Test.LoopToWordExactParity`; the partial helper is intentionally
untagged until every `comp_def` clause has an exact Lean port.
`loop_to_word_comp_recursive_probe.out` records direct HOL EVAL rows for the
recursive Seq, If, Loop, and Mark clauses of `comp_def` at
`cakeml/pancake/loop_to_wordScript.sml:107-120,138`, including the threaded
label pair, If/Loop Tick placement, and Loop live cutsets. Its kernel-checked
Lean replay is `Flapjack.Test.LoopToWordRecursiveParity`; the partial helper
remains untagged until the other `comp_def` clauses are ported and assembled.
`loop_to_word_compile_correct_cases_probe.out` rebuilds the specialized
`loopSem$evaluate_ind` used by `loop_to_wordProof$compile_correct` and records
the exact case conjuncts at `cakeml/pancake/proofs/loop_to_wordProofScript.sml`.
The probe now includes Seq, whose two hypotheses are the first-command case
and the second-command case conditional on the first returning `NONE`; its
conclusion retains the complete existential target run and `resultCase`.
Regenerate it with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=loop_to_word_compile_correct_cases_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.
`loop_to_word_globals_rel_probe.out` records direct HOL EVAL rows for
`globals_rel_def` at `cakeml/pancake/proofs/loop_to_wordProofScript.sml:27-30`:
a matching `Temp` value, value/key mismatches, and the one-way empty-source
case. The exact finite-map relation and kernel replay are
`Flapjack.Pancake.LoopToWord.Proofs.RelationsExact` and
`Flapjack.Test.LoopToWordGlobalsRelParity`.
`loop_to_word_comp_call_probe.out` records direct HOL EVAL rows for the Call
clauses of `comp_def` at `cakeml/pancake/loop_to_wordScript.sml:145-166`
(tail-call, non-tail without handler, non-tail with handler), checking link slot
`0`, the computed live cutset, label threading, and the trailing `Tick`. Its
kernel-checked Lean replay is `Flapjack.Test.LoopToWordCallParity`.
`loop_to_word_comp_func_probe.out` records direct HOL EVAL rows for the
executable entry points `comp_func_def` / `compile_prog_def` / `compile_def`
at `cakeml/pancake/loop_to_wordScript.sml:164-177`: `comp_func` with no new
temporaries, with a parameter already assigned, and with a fresh
`acc_vars` temporary; plus the `LENGTH params + 1` mapping of `compile_prog`
and its `compile` alias over a three-entry code list. Its kernel-checked Lean
replay is `Flapjack.Test.LoopToWordCompFuncParity` through the tagged exact
`loopToWordCompFuncHOL` / `loopToWordCompileProgHOL` / `loopToWordCompileHOL`.
`loop_live_comp_probe.out` records direct HOL EVAL rows for
`loop_live$comp` at `cakeml/pancake/loop_liveScript.sml:217`; the Lean replay
is `Flapjack.Test.LoopLiveCompParity`. `loop_live_optimise_probe.out` records
`loop_live$optimise` plus a strict-growth fixedpoint iteration, a direct
`fixedpoint` NONE result for a non-least initial approximation, and the
enclosing Loop shrink result; its replay guards are in
`Flapjack.Test.LoopLiveOptimiseParity`. The FFI optimizer row is also replayed
there. `ocompile_probe.out` includes an ExtCall-to-FFI result from
`crep_to_loop$ocompile`; `Flapjack.Test.OCompileParity` checks that row.
Regenerate these with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=loop_live_optimise_probeScript.sml scripts/hol-probes/regenerate.sh`
and `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=ocompile_probeScript.sml scripts/hol-probes/regenerate.sh` for
the ocompile rows.
`loop_live_domain_list_delete_probe.out` records direct HOL `EVAL` membership
rows for `domain_list_delete` at
`cakeml/pancake/proofs/loop_liveProofScript.sml:561-562`; the kernel-checked
replay is `Flapjack.Test.LoopLiveDomainListDeleteParity`.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=loop_live_domain_list_delete_probeScript.sml
scripts/hol-probes/regenerate.sh`.
`Flapjack.Test.LoopPropsCutSetsParity` guards the exact `cut_sets_def`
clauses over `HolLoopProg`/`NumSet`; its direct HOL outputs for Skip,
LocValue, Assign, Load32/LoadByte, Seq, If, each Arith variant, and the
catch-all are in `scripts/hol-probes/loop_props_cut_sets_probe.out`.
`Flapjack.Test.LoopPropsCompSyntaxOkParity` guards the exact
`comp_syntax_ok_def` over those carriers; direct HOL EVAL rows for positive
and negative Loop/Seq cases and both residual If existential cases are in
`loop_props_comp_syntax_probe.out`.
`Flapjack.Test.CrepToLoopCompFuncParity` replays the canonical direct
`crep_to_loop$comp_func_def` output rows and the right-recursive
`list_to_num_set` rows in `crep_to_loop_comp_func_probe.out` and
`crep_to_loop_list_to_num_set_probe.out`.
`Flapjack.Test.LoopDecClockParity` probes `dec_clock_def` at lines 42--43 of
the same source.
`Flapjack.Test.LoopFixClockParity` probes `fix_clock_def` at lines 46--49.
`crep_to_loop_survives_mapi_assign_probe.out` records direct HOL EVAL for
`survives_MAPi_Assign` at `crep_to_loopProofScript.sml:368-379`: empty,
singleton, three-expression, and zero-offset MAPi Assign lists all evaluate to
`T`. The exact `HolLoopExp`/`HolLoopProg` theorem port is
`Flapjack.Pancake.CrepToLoop.Proofs.holSurvivesMapiAssign`; replay fixtures are
in `Flapjack.Test.CrepToLoopSurvivesMapiAssignParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=crep_to_loop_survives_mapi_assign_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.
`crep_to_loop_write_bytearray_mem_rel_probe.out` records direct HOL EVAL rows
for both sides of `write_bytearray_mem_rel`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:251-256`):
`panSem$write_bytearray` and `wordSem$write_bytearray` on the same address,
three-byte list, domain (full and partial) and endianness from
`wlab_wloc`-related 64-bit memories, read at both affected aligned words.
The Lean replay, including the pointwise `mem_rel` conclusion, is
`Flapjack.Test.CrepToLoopWriteBytearrayMemRelParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=crep_to_loop_write_bytearray_mem_rel_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.
`loop_props_survives_probe.out` records direct HOL EVAL rows for every clause
of `survives_def` in `cakeml/pancake/semantics/loopPropsScript.sml:25-38`:
If/Loop/Call (both handler forms)/FFI domain membership, recursive Mark and
Seq, and the catch-all case. The exact width-indexed `HolLoopProg` port
`survivesHOLExact` is in `Flapjack.Pancake.Semantics.LoopProps`; its replay
guards are in `Flapjack.Test.LoopPropsSurvivesParity`. Refresh with
`HOL_PROBE_ONLY=loop_props_survives_probeScript.sml scripts/hol-probes/regenerate.sh`.
`loop_props_every_prog_probe.out` records direct HOL EVAL rows for every clause
of `every_prog_def` in `cakeml/pancake/semantics/loopPropsScript.sml:10-24`
under a predicate that fails exactly at `Loop` nodes: Seq, Loop, If, Mark, Call
(both handler forms and both handler branches), and the catch-all case. The
exact width-indexed `HolLoopProg` port `everyProgHOL` is in
`Flapjack.Pancake.Semantics.LoopProps.EveryProg`; its replay guards are in
`Flapjack.Test.LoopPropsEveryProgParity`. Refresh with
`HOL_PROBE_ONLY=loop_props_every_prog_probeScript.sml scripts/hol-probes/regenerate.sh`.
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
`crep_arith_sh_mem_op_code_probe.out` records nine direct HOL EVAL rows for the
proof-script-local `sh_mem_op_code` at
`cakeml/pancake/proofs/crep_arithProofScript.sml:173-180`: the `code` projection
of the local `mapc` rewrite, and the eight operator cases of
`sh_mem_op op 1 3w (mapc f s) = (I ## mapc f) (sh_mem_op op 1 3w s)` on
fixtures whose shared-memory domain is empty.  The `mapc` overload is local to
that proof script, so the probe inlines `s with code := FMAP_MAP2 f s.code`.
`Flapjack.Test.CrepArithShMemOpCodeParity` checks the tagged exact
`crepShMemOpExactHOL_mapc` against every row.  Refresh with
`HOL_PROBE_ONLY=crep_arith_sh_mem_op_code_probeScript.sml scripts/hol-probes/regenerate.sh`.
`crep_arith_store_glob_probe.out` records five direct HOL EVAL rows for the
`StoreGlob` case of the proof-script `simp_prog_correct` at
`cakeml/pancake/proofs/crep_arithProofScript.sml:184-212`:
`simp_prog (StoreGlob g exp) = StoreGlob g (simp_exp exp)`
(`crep_arithScript.sml:89`); the successful `evaluate` equation
`evaluate (StoreGlob dst (Const 7w), s) = (NONE, set_globals dst 7w s)`
(`crepSemScript.sml:288-291`); the same row under the local `mapc` rewrite; the
code-only commutation `set_globals dst 7w (mapc f s) = mapc f (set_globals dst 7w s)`;
and the missing-variable failure branch `(SOME Error, s)`. The `mapc` overload
is local to the proof script, so the probe inlines
`st with code := FMAP_MAP2 f st.code`.
`Flapjack.Test.CrepArithStoreGlobParity` replays the rows against the tagged
exact `simpProgCorrectStoreGlobCase` and the exact `CrepSemHOLState.setGlobals`.
Refresh with
`HOL_PROBE_ONLY=crep_arith_store_glob_probeScript.sml scripts/hol-probes/regenerate.sh`.
`crep_arith_store_32_probe.out` records seven direct HOL EVAL rows for the
`Store32` case of the proof-script `simp_prog_correct` at
`cakeml/pancake/proofs/crep_arithProofScript.sml:184-212`:
`simp_prog (Store32 exp1 exp2) = Store32 (simp_exp exp1) (simp_exp exp2)`
(`crep_arithScript.sml:87`); the successful `evaluate` equation
`evaluate (Store32 (Const 4w) (Const 0x11w), s)` returning `NONE`
(`crepSemScript.sml:274-280`); the same row under the local `mapc` rewrite; the
code-only commutation of `mapc f` with the memory update; and the three
failure branches `(SOME Error, s)` (memory domain, `mem_store_32` alignment,
and a failed operand). The `mapc` overload is local to the proof script, so the
probe inlines `st with code := FMAP_MAP2 f st.code`.
`Flapjack.Test.CrepArithStore32Parity` replays the rows against the tagged
exact `simpProgCorrectStore32Case` and the exact `CrepSemHOLState` carriers.
Refresh with
`HOL_PROBE_ONLY=crep_arith_store_32_probeScript.sml scripts/hol-probes/regenerate.sh`.

`crep_arith_if_probe.out` records eight direct HOL EVAL rows for the `If` case
of the proof-script `simp_prog_correct` at
`cakeml/pancake/proofs/crep_arithProofScript.sml:184-212`:
`simp_prog (If exp c1 c2) = If (simp_exp exp) (simp_prog c1) (simp_prog c2)`
(`crep_arithScript.sml:90`); the true- and false-guard `evaluate` equations
`evaluate (If e c1 c2, s)` selecting `c1`/`c2` and their resulting states
(`crepSemScript.sml:307-311`); the absent-condition failure branch
`(SOME Error, s)`; and the code-only commutation of `mapc f` with the selected
branch update. The `mapc` overload is local to the proof script, so the probe
inlines `st with code := FMAP_MAP2 f st.code`.
`Flapjack.Test.CrepArithIfParity` replays the direct `simp_prog_if`,
true/false-guard and absent-condition error rows against the exact
`CrepSemHOLState` carriers; the two code-only `mapc` rows are covered by the
tagged exact `simpProgCorrectIfCase` proof. Refresh with
`HOL_PROBE_ONLY=crep_arith_if_probeScript.sml scripts/hol-probes/regenerate.sh`.

`crep_arith_store_byte_probe.out` records seven direct HOL EVAL rows for the
`StoreByte` case of the proof-script `simp_prog_correct` at
`cakeml/pancake/proofs/crep_arithProofScript.sml:184-212`:
`simp_prog (StoreByte dst src) = StoreByte (simp_exp dst) (simp_exp src)`
(`crep_arithScript.sml:88`); the successful `evaluate` result under a full byte
domain and the same result under the local `mapc` rewrite (both projected onto
their first component, since `=` is undecidable on state pairs); the
out-of-domain and missing-variable failure branches `(SOME Error, s)` and their
`mapc` image; and the code-only commutation `(mapc f s).memory = s.memory`. The
`mapc` overload is local to the proof script, so the probe inlines
`st with code := FMAP_MAP2 f st.code`.
`Flapjack.Test.CrepArithStoreByteParity` replays the rows against the tagged
exact `simpProgCorrectStoreByteCase` and the exact `CrepSemHOLState` memory
update. Refresh with
`HOL_PROBE_ONLY=crep_arith_store_byte_probeScript.sml scripts/hol-probes/regenerate.sh`.
`crep_arith_ext_call_probe.out` records four direct HOL EVAL rows for the
`ExtCall` case of the proof-script `simp_prog_correct` at
`cakeml/pancake/proofs/crep_arithProofScript.sml:184-212`: HOL `simp_prog`
leaves an `ExtCall` unchanged (catch-all at `crep_arithScript.sml:113`), and
`evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s)`
(`crepSemScript.sml:367-379`) reads four locals and calls `call_FFI`, with the
missing-locals failure branch `(SOME Error, s)`. The rows pin the source
identity, the code-only `mapc` rendering, and the failure branch directly and
under `mapc`; the exact Lean `CrepSemHOLState` counterpart and its replay live
in `Flapjack.Test.CrepArithExtCallParity`. Refresh with
`HOL_PROBE_ONLY=crep_arith_ext_call_probeScript.sml scripts/hol-probes/regenerate.sh`.
`crep_dest_2exp_probe.out` records direct HOL EVAL of
`crep_arith$dest_2exp_def` at `cakeml/pancake/crep_arithScript.sml:15`, including
the corresponding `word_lsl 1w` results for successful exponents. Its Lean
destination, shift, and width checks live in `Flapjack.Test.CrepeDest2ExpParity`.
Its `reviewedDefinitionParity` also compares the executable fuel-bounded helper
directly with the reviewed `crepDest2ExpHOL` on all ten recognizer rows.
`crepDest2Exp_eq_HOL` proves that correspondence for every positive width,
starting exponent and input; no successful-recognition or fuel premise is needed.
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
records the source `byte_align` definition at that carrier width and retains
`LOG2 0` symbolically (`pan_fixed_load_probe.out:50`), direct HOL evidence
that the source does not select Lean's `Nat.log2 0 = 0` completion. The source
expression is emitted by `pan_fixed_load_probeScript.sml:94-95` and was
captured with the command above. The untagged
`CrepSem.Log2ZeroParametric` evaluator uses one explicit natural `z` at every
recursive load; its one-bit examples show that completions 0 and 1 can differ,
while a kernel theorem proves all expression results coincide with the current
evaluator at widths at least 8 for every `z`. This is a model parameter, not
reviewed production equivalence or an approved HOL qualifier. The tagged Lean
`panMemLoad32HOL` states the equivalent modulo-four guard directly; the
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
left/right constant multiplication, nested multiplication, recursive
load/word-operation children, and identity Var/Const constructor rows used by
the native `simp_exp_correct1` cases. It also evaluates the original
`crepSem$eval` before and after simplifying `Crepop Mul [Var 2; Const 8w]`
with local 2 set to `Word 5w`; the simplifier yields `Shift Lsl (Var 2)
(Const 3w)` and both evaluations return `SOME (Word 40w)`. The matching
production source-runtime observation and all-width theorem application are
in `Flapjack.Test.CrepeSimpExpParity`; the exact-carrier Var/Const replay is
checked there alongside the tagged native evaluator cases in
`Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc`. These checks exercise the
result shape, but do not close the polymorphic evaluator-preservation theorem
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
`crep_to_loop_compile_prog_probe.out` records direct HOL EVAL rows for the
top-level `compile_prog_def` at `cakeml/pancake/crep_to_loopScript.sml:257-265`:
a one-entry program with `first_name`-offset function numbering (`cp_fnums`),
its `(GENLIST I o LENGTH) params` slot list (`cp_params`), the
`crep_arith$simp_prog` + `loop_live$optimise` compiled body (`cp_body`), the
result length (`cp_length`), and a second one-entry program whose body calls
`«f»` so that `make_funcs`'s `first_name = 64` label flows through `comp_func`'s
`find_lab` (`cp_call_fnums`/`cp_call_params`/`cp_call_body`). The exact-carrier
tagged port `Flapjack.compileProgHOLExact` (`@[hol ... "compile_prog_def"
(words_as_type_indexed_bitvec)]`) and its replay in
`Flapjack.Test.CrepToLoopCompileProgParity` use the exact
`MlString`/`CrepProgHOL`/`HolLoopProg` carriers. Refresh with
`HOL_PROBE_ONLY=crep_to_loop_compile_prog_probeScript.sml scripts/hol-probes/regenerate.sh`.
`crep_to_loop_list_to_num_set_probe.out` records direct HOL EVAL rows for HOL's
`sptree$list_to_num_set_def` (`HOL/src/finite_maps/sptreeScript.sml:2026-2028`),
the live-set builder used by `comp_func_def` at
`cakeml/pancake/crep_to_loopScript.sml:239`. The rows observe membership on
`[]`, `[0]`, `[0;1;2]` and the unsorted `[2;0;3]` via `lookup`, and the final
`ltns_cons_shape` row exposes the right-recursive equation
`list_to_num_set (n::ns) = insert n () (list_to_num_set ns)` with `LN` as the
base case. The untagged Lean helper `Flapjack.listToNumSetHOLExact` in
`Flapjack/Pancake/CrepToLoop/ContextExact.lean` reproduces the same right
recursion. `Flapjack.Test.CrepToLoopCompFuncParity` checks the exact
`comp_func_def` output rows, including the projected initial live set, and
the direct `list_to_num_set` EVAL rows.
Refresh with
`HOL_PROBE_ONLY=crep_to_loop_list_to_num_set_probeScript.sml scripts/hol-probes/regenerate.sh`.
`crep_to_loop_ocompile_probe.out` records direct HOL EVAL rows for
`ocompile_def` at `cakeml/pancake/crep_to_loopScript.sml:216-219`, which
composes `compile` and `loop_live$optimise`. The six rows cover `Skip`, `Tick`,
`Assign`, `Primitive`, `Return`, and a `Call` with a mapped label, mapped
return, and exception handler. The exact width-indexed Lean port
`ocompileHOLExact` in `Flapjack.Pancake.CrepToLoop.ContextExact` is replayed
against those rows by `Flapjack.Test.CrepToLoopOcompileHOLParity`. Refresh with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_to_loop_ocompile_probeScript.sml bash scripts/hol-probes/regenerate.sh`.
The original Pancake source-level support boundary is also explicit in
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:2285-2291`: `LLongDiv` is
accepted by `loop_inst_ok` only for `x86_64`. Consequently, RISC-V parity must
port the `data_to_word` helper path rather than add a direct RISC-V lowering
for source `LLongDiv`.
`crep_to_loop_code_rel_probe.out` records direct HOL EVAL rows for
`code_rel_def` at `cakeml/pancake/proofs/crep_to_loopProofScript.sml:76-88`.
The fixture uses the HOL context `context FEMPTY
(FEMPTY |+ (strlit "f", (42,2))) 0 RISC_V` with `s_code` holding
`([1;2], Skip)` and `t_code = insert 42 ([0;1], Mark Skip) LN`. Besides the
component rows (`FLOOKUP` of the function table and of `s_code`, the generated
argument list `GENLIST I 2 = [0; 1]`, the compiled `Skip`, and the target
lookup), `code_rel_witness=T` evaluates the fully instantiated existential
requirement with the witnesses `loc = 42`, `len = 2`, while
`code_rel_missing_funcs=F` and `code_rel_len_mismatch=F` evaluate the same shape
with the function-table lookup failing and with a length mismatch. HOL
`crepSem$state.code` (and hence `s_code`) is `funname |-> _`, i.e. `mlstring`
keyed; the Lean replay therefore uses the `MlS` key `ofString "f"`. The exact
Lean port `crepToLoopCodeRelExact` in `Flapjack.Pancake.CrepToLoop.StateRel` is
replayed against those rows by `Flapjack.Test.CrepToLoopCodeRelParity`. Refresh
with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_to_loop_code_rel_probeScript.sml bash scripts/hol-probes/regenerate.sh`.
`crep_to_loop_evaluate_io_mono_type_probe.out` prints the exact source
construction of the local `evaluate_io_mono_rephrases` helper
(`crep_to_loopProofScript.sml:4066-4070`), including both `Q.SPECL`
specializations, the `map (SIMP_RULE (srw_ss()) [])`, and `LIST_CONJ`, because
the `[local]` helper is not exported by the theory. It records the two
conjunct-local `!extra` binders and free-variable types, including the Crep and
Loop state carriers. Refresh with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=crep_to_loop_evaluate_io_mono_type_probeScript.sml bash scripts/hol-probes/regenerate.sh`.
`crep_to_loop_locals_rel_probe.out` records direct observations for
`locals_rel_def` at `cakeml/pancake/proofs/crep_to_loopProofScript.sml:101-111`.
HOL `crepLang$varname = num` (`crepLangScript.sml:19`), so the context's `vars`
is a `num |-> num` finite map; the fixture uses a `num`-keyed `vars`
(`0 |-> 0`, with `vmax = 0`), a two-member `num_set`, and a nonempty `num_map`. Besides atomic
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

The same probe records insert rows for
`crep_to_loopProofScript.sml:226-234` `locals_rel_insert_gt_vmax`:
`locals_rel_insert_after_true=T` decides `locals_rel` after inserting the fresh
key `5` (above `ctxt.vmax = 0`) into the target `num_map`, and
`insert_gt_vmax_lookup_unchanged=T` shows the earlier lookup (key `0`) is
unaffected. The companion probe `crep_to_loop_locals_insert_probe.out`
separately pins the raw `sptree$insert` behaviour (`insert_same`,
`insert_other_unchanged`, `gt_vmax_bounded_survives`, `subset_preserved`). The
exact-carrier counterpart is the tagged
`Flapjack.CrepToLoop.crepToLoopLocalsRelExact_insert_gt_vmax` over the exact
`sptInsert`/`Spt`, whose support lemmas `sptLookup_sptInsert_ne` and
`sptMem_sptInsert` live in `Flapjack/Misc/Sptree.lean`.

`crep_primop_loop_primop_probe.out` records direct HOL EVAL of the local
preservation theorem `crep_primop_loop_primop`
(`cakeml/pancake/proofs/crep_to_loopProofScript.sml:2337-2355`) on concrete
8-bit `word_lab` payloads: the source `crepSem$crep_primop`, the target
`loopSem$loop_primop` after `MAP crep_to_loopProof$wlab_wloc`, and the resulting
preservation equation for the valid, overflow, nonzero-carry, short-arity, and
long-arity cases (`crep_valid`, `loop_valid_mapped`, `preserve_valid`, ...,
`preserve_invalid_four`). The exact Lean port is the tagged
`Flapjack.crepPrimopLoopPrimopHOL` in the `crep_to_loopProofScript.sml`
counterpart `Flapjack/Pancake/CrepToLoop/Proofs/Primop.lean`, over the exact
`HolWordLab`(`word_lab`)/`WordLocW`(`word_loc`) carriers and the
`wlabWlocHOL` bridge; the kernel replay guards and `example`s are in
`Flapjack.Test.CrepPrimopLoopPrimopParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=crep_primop_loop_primop_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

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

`lprefix_lub_llist_shorter_probe.out` records original-HOL finite instances of
`llist_shorter` from the pinned external script
`examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml` (`llist_shorter_def`
:122-129, `llist_shorter_fromList` :163-169): shorter/equal/longer finite lists,
the two-empty case, the nil/non-nil directions, and the reverse-order and
equal-length-different-content cases. `llist_shorter` matches on
`(LLENGTH ll1, LLENGTH ll2)`, so the source definition is reduced with the
companion library theorem `LLENGTH_fromList` and the resulting length comparison
is `EVAL`-evaluated. Refresh it with
`HOL_PROBE_ONLY=lprefix_lub_llist_shorter_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`crep_inline_relations_probe.out` records direct HOL simplification/evaluation
of `state_rel_def` and `locals_rel_def` at
`crep_inlineProofScript.sml:12-29`: a nonempty locals map is a submap of an
extension, missing and conflicting bindings fail, `state_rel` ignores locals,
and a code-field difference fails. The exact finite-support Lean replays are
in `Flapjack.Test.CrepInlineRelationsExactParity`. Regenerate with
`HOL_PROBE_ONLY=crep_inline_relations_probeScript.sml scripts/hol-probes/regenerate.sh`.

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

`sptree_difference_probe` is a bare HOL session over the external
`HOL/src/finite_maps/sptreeScript.sml`; it records direct constructor-level
`EVAL` rows for every `sptree$difference` outer/inner clause, heterogeneous
right payloads, and the `mk_BN`/`mk_BS` collapses. The Lean replay checks exact
result trees and left payload preservation. Refresh with
`HOL_PROBE_ONLY=sptree_difference_probeScript.sml scripts/hol-probes/regenerate.sh`.

`sptree_inter_mixed_probe` evaluates the HETEROGENEOUS `sptree$inter`
(`'a num_map -> 'b num_map -> 'a num_map`) on mixed-payload `fromAList` trees and
records that the result keeps the LEFT operand's values on keys present in both
trees; it loads only `bossLib`/`sptreeTheory` (no CakeML `preamble`), so it runs
in a bare HOL session.  `Flapjack.Test.SptreeSetOpsParity.sptreeInterMixedGuard`
checks the Lean `sptInter` against every row.  Refresh with
`HOL_PROBE_ONLY=sptree_inter_mixed_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_sem_evaluate_probe.out` records 36 direct HOL `EVAL` rows for
`wordSem$evaluate_def` (`cakeml/compiler/backend/semantics/wordSemScript.sml:
1016-1260`) at 64-bit words, over record updates of a free state: the
straight-line and control clauses plus `Alloc`, `Store`, `OpCurrHeap`,
`ShareInst`, `CodeBufferWrite`, `DataBufferWrite`, `Install`, and the
returning-`Call` caught-handler exception path (a handler is installed, the
callee `Raise`s with the handler's labels, and the handler body runs).
Rows print `(result, toAList locals, clock)` unless the clause updates another
field, in which case the projection adds the affected field (memory/buffer
contents, code map, `stack_max`/`stack_size`). The kernel-checked Lean replay
is `Flapjack.Test.WordSemEvaluateParity`. Refresh with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_sem_evaluate_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

`word_alloc_colour_exp_probe.out` records original `word_alloc$apply_colour_exp_def`
(`cakeml/compiler/backend/word_allocScript.sml:580-587`) at eight-bit words: nested
Op/Load, a fixed five-bit Temp name, both expression-valued Shift operands,
duplicate variables under an aliasing colouring, and empty Op arguments.
`Flapjack.Test.CakeApplyColourParity.expressionColourExact` checks all three
rows through the production function in the compiled `lake test` executable.
Refresh with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_colour_exp_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

`word_alloc_colour_inst_probe.out` records direct original
`word_alloc$apply_colour_inst_def` observations at 8-bit words. Under
`n + 10`, Load16/Store16 retain registers 3/5 through the catchall, whereas
Load8/Store32 rename them to 13/15 and preserve offset 7w. AddCarry retains
all four operand positions, and FPMovFromReg preserves its float destination
while renaming both integer sources. These rows drive reconciliation of the
executed allocator, whose previous blanket memory renaming differs at 16 bits.
Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=word_alloc_colour_inst_probeScript.sml bash scripts/hol-probes/regenerate.sh`.
# Word allocation key renaming

`word_alloc_key_map_probeScript.sml` evaluates the original `apply_nummap_key`
on unit-valued numeric trees, including mixed traversal order, duplicate input
keys, and noninjective renaming. `CakeWordAllocParity.keyMapRouteGuard` checks
the executed list boundary against these captured rows.

Regenerate with:

```sh
CAKEML=/path/to/built/cakeml HOL_PROBE_ONLY=word_alloc_key_map_probeScript.sml scripts/hol-probes/regenerate.sh
```

## StackSem word bitmap codec

`stacksem_word_bitmap_probeScript.sml` captures eleven original HOL `bit_length`
and `read_bitmap` rows: zero/one/high-bit lengths, empty input, terminal zero/one,
least-significant-first ordering, ignored terminal suffix, missing continuation,
continuation concatenation, and width-one words. Regenerate against read-only
prebuilt theory objects with:

```sh
CAKEML=/home/zksecurity/pancake-lean/cakeml \
HOL_PROBE_ONLY=stacksem_word_bitmap_probeScript.sml scripts/hol-probes/regenerate.sh
```

`Flapjack/Test/StackSemWordBitmapParity.lean` kernel-checks each captured result.
These rows exercise the HOL-shaped word/list ports; they do not establish
Nat-utility refinement or full StackSem evaluator execution.

`word_alloc_live_inst_probe.out` captures nine original `get_live_inst_def`
observations (`word_allocScript.sml:706-752`): Load16 catchall, Load8,
Store32, AddCarry, AddOverflow, and FPMovToReg/FPMovFromReg at 32 and 64 bits.
The exact tree enumeration lists are kernel-replayed and runtime-checked in
`Flapjack.Test.CakeApplyColourParity.instructionLivenessExact`.
`instructionLivenessExecuted` also kernel-replays the first four rows through
the actual allocator list route. Shared production constructors execute
`getLiveInstCore` through `getLiveInstExecutable`; production has no FP
constructors, and its distinct five-register AddCarry retains a separate
Flapjack route. The retained-instruction liveness of `wordDeadInst` uses this
same route. Its keep/drop decisions remain separate work on bead `.11.1.12`.
Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_live_inst_probeScript.sml
scripts/hol-probes/regenerate.sh` (the shared checkout supplies built objects;
its original word_alloc source was compared byte-for-byte).

`word_alloc_live_exp_probe.out` records direct original `get_live_exp_def`
observations for nested expressions, duplicate variables, empty operators,
both Shift operands, constants, and lookups. The captured mixed-tree key order
is kernel-replayed through `getLiveExpExecutable` in
`Flapjack.Test.WordAllocLiveExpressionParity`. The executed dead-code set
boundary calls reviewed `getLiveExp`; duplicate-sensitive occurrence lists
used by clash construction retain their separate representation. Regenerate
with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_live_exp_probeScript.sml
scripts/hol-probes/regenerate.sh` after building original CakeML theories.

`word_alloc_reads_exp_probe.out` records direct original `get_reads_exp_def`
observations (`word_allocScript.sml:1122-1128`) for a single `Var` read, a
`Load` of a `Var`, an `Op` whose nested read lists flatten in argument order,
a `Shift` that concatenates its left operand's reads before its right
operand's, the `Const`/`Lookup` catch-all empty list, and a mixed nested
`Op`/`Load`/`Shift` expression. `Flapjack.Test.WordAllocReadsExpParity`
kernel-replays all seven rows through the exact polymorphic
`getReadsExpHOL`. This proof-side port does not yet replace the executed
caller. Regenerate read-only with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_reads_exp_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`word_sem_cut_names_type_probe.out` prints the original HOL `cut_names`
constant types for `cut_names`, `cut_envs`, and `cut_env` from `wordSemTheory`: independent name-map and environment-map
payload parameters in the first, and generic environment payloads in the latter two. It guards the carrier review of `wordSemCutNames` against
an accidental specialization to unit keys or word-valued locals. Regenerate
with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_sem_cut_names_type_probeScript.sml
scripts/hol-probes/regenerate.sh`; the original wordSem source was compared
byte-for-byte before using the shared checkout's built objects.

`word_alloc_pair_keys_probe.out` records three original `apply_nummaps_key_def`
rows (`word_allocScript.sml:29-33`): independent Boolean/numeric payloads,
unit-map collisions, and an empty component with duplicate input keys.
`Flapjack.Test.CakeApplyColourParity.pairedKeyMapExact` kernel-replays the
heterogeneous exact maps and runtime-checks the actual paired allocator route
for the unit cutsets. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_pair_keys_probeScript.sml
scripts/hol-probes/regenerate.sh`; the original source was compared byte-for-byte
before using the shared checkout's built objects.

## StackSem recursive stack codecs

`stacksem_stack_codec_probeScript.sml` captures26 concrete original HOL
`full_read_bitmap`/`enc_stack`/`dec_stack` rows and their three inferred types.
The standalone definitions have independent bitmap and descriptor/stack word
dimensions; mixed8-bit bitmap/1-bit stack rows guard this distinction. Other rows
cover one-based indexing, sentinel shape, recursive frames, selected and
unselected location values, truncated inputs/roots, extra roots, missing
continuation words and missing final sentinel.

Regenerate read-only with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_stack_codec_probeScript.sml scripts/hol-probes/regenerate.sh`.
`Flapjack/Test/StackSemStackCodecParity.lean` kernel-checks all26 concrete rows.
Full GC/evaluator execution and Nat-machine refinement remain separate work.

`word_alloc_live_exp_probe.out` captures six original `get_live_exp` key
traversals (nested, duplicate, empty, binary Shift, constant, lookup).
`Flapjack.Test.WordAllocLiveExpressionParity` replays all six with kernel
reduction of the executed constant-erasure wrapper. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_live_exp_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_alloc_remove_dead_inst_probe.out` records twelve original
`remove_dead_inst_def` observations (`word_allocScript.sml:854-880`): Skip,
live/dead Const, Load16/Store16/Store32 catchalls, dead Load8, live/dead
four-register carry, a live second LongMul output, and the 32/64-bit FP move
boundary. `CakeApplyColourParity.instructionRemovalExact` kernel-replays all
twelve; `instructionRemovalExecuted` checks the actual retained offset stores,
16-bit load and removable dead Load8/Const. The production decision now calls
the reviewed core through `removeDeadInstExecutable`. This does not assert
completion of the whole `remove_dead` program recursion.
Regenerate read-only with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_remove_dead_inst_probeScript.sml
scripts/hol-probes/regenerate.sh`; the original source was compared byte-for-byte
before using the shared checkout's built objects.

`stacksem_allocation_probe.out` captures eighteen concrete original GC,
unsigned-space and allocation observations plus the independent-dimension
`has_space` type. `Flapjack.Test.StackSemAllocationParity` kernel-replays all
concrete rows (including 1-bit request/8-bit store and rollback/GC post-state
errors). Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_allocation_probeScript.sml scripts/hol-probes/regenerate.sh`.
Full StackSem evaluation and production refinement remain open.

The existing `word_convs_not_created_probe.out` records 15 original HOL
`no_alloc`/`no_install`/`no_mt`/`no_share_inst` observations.
`Flapjack/Test/WordLangNotCreatedParity.lean` checks those rows against the
executable Boolean definitions on `WordLangProgHOL`, both in the kernel and
in the runtime suite. `WordConvs/NotCreated.lean` also proves agreement with
the original inequality predicates for every possible `ARB : memop` choice;
the choice-parametric general checker is deliberately untagged.

`stacksem_expression_probeScript.sml` captures twenty original StackSem word_exp/assign rows: all six constructors, failed/missing/Loc lookups, domain and memory payload rejection, wraparound, invalid arithmetic arity, binary shift bounds, and destination update/failure. Kernel replay: `Flapjack/Test/StackSemExpressionParity.lean`. Full evaluator/production refinement is separate.

`stacksem_loop_control_probeScript.sml` captures 28 direct original
`stackSem$get_var_imm`, `cont_loop`, and `exit_loop` observations from
`stackSemScript.sml:640-644/761-772`. They include Word/Loc/missing registers,
unsigned immediate preservation, all control-result constructors, zero and
positive labels, and unchanged final-event payloads. StackSem Break0 exits
normally, unlike WordSem. Kernel replay and runtime control checks live in
`Flapjack/Test/StackSemLoopControlParity.lean`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_loop_control_probeScript.sml
scripts/hol-probes/regenerate.sh`. Evaluator assembly and its production
refinement remain tracked by y19g/.12.

`stacksem_control_probeScript.sml` captures eleven direct original
`stackSem$evaluate` observations for the structured-control clauses `Seq`, `If`,
and `Loop` (`stackSemScript.sml:811-837`). The `Seq` rows cover a non-`NONE`
first result propagated without running the second program, a `NONE` first
result falling through to the second program, and the `fix_clock` clamp when the
first program is a `Tick`. The `If` rows cover `SOME T` (then-branch), `SOME F`
(else-branch), option-valued `word_cmp = NONE` for a `Loc` operand, and a
missing register lookup (`Error`). The `Loop` rows cover a `Continue 0` re-entry
with a nonzero clock that times out with the emptied environment, a zero-clock
body result that times out immediately, and `Break 1`/`Continue 1` exits that
decrement through `exit_loop`. The observer records result, clock, register 1
and stack length. Kernel replay over a concrete `evaluate` stub lives in
`Flapjack/Test/StackSemControlCasesParity.lean`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_control_probeScript.sml
scripts/hol-probes/regenerate.sh`. The `evaluateSeq`/`evaluateIf`/`evaluateLoop`
fragments are untagged; the tagged ports of `fix_clock_def`, `cont_loop_def`,
`exit_loop_def`, `get_var_imm_def`, `empty_env_def` and `dec_clock_def` live in
`StackSem/Control.lean` and `StackSem/StateOps.lean`, and assembled full
evaluation remains on `y19g`/`y19g.18`.

`stacksem_jumplower_probeScript.sml` records eight direct original
`stackSem$evaluate` observations for the `JumpLower` clause
(`stackSemScript.sml:838-849`): a successful unsigned `Lower` comparison whose
`INL` code lookup finds a `Return` sub-program (the non-bad result propagates
with the decremented clock), a zero-clock timeout that empties the environment,
a missing code target, a false comparison (`NONE` with the state unchanged), a
`Loc` operand (`Error`), and `Break`/`Continue`/`Skip` sub-results
(`bad_fun_return` maps each to `Error` with the recursed state). The observer
records result, clock, register 1 and stack length. Kernel replay over a
concrete `evaluate` stub lives in
`Flapjack/Test/StackSemJumpLowerParity.lean`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_jumplower_probeScript.sml
scripts/hol-probes/regenerate.sh`. The `evaluateJumpLower` fragment is
untagged; the tagged port of `bad_fun_return_def` lives in
`StackSem/Control.lean`, and assembled full evaluation remains on y19g.

`stacksem_rawcall_probeScript.sml` records seven direct original
`stackSem$evaluate` observations for the `RawCall` clause
(`stackSemScript.sml:850-860`): a successful `Seq` code entry whose second
component is a `Return` (the non-bad result propagates with the decremented
clock), a zero-clock timeout that empties the environment, a missing code
target (`Error`), a non-`Seq` code entry (`dest_Seq` returns `NONE`, hence
`Error`), and `Break`/`Continue`/`Skip` sub-results (`bad_fun_return` maps each
to `Error` with the recursed state). The observer records result, clock,
register 1 and stack length. Kernel replay over a concrete `evaluate` stub lives
in `Flapjack/Test/StackSemRawCallParity.lean`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_rawcall_probeScript.sml
scripts/hol-probes/regenerate.sh`. The `evaluateRawCall` fragment is untagged;
the tagged ports of `dest_Seq_def` and `bad_fun_return_def` live in
`StackSem/Control.lean`, and assembled full evaluation remains on y19g.

`stacksem_call_probeScript.sml` records fourteen direct original
`stackSem$evaluate` observations for the `Call` clause
(`stackSemScript.sml:861-892`). The `NONE` tail-call rows cover a successful
`Return` result with the decremented/clamped clock, a present handler rejected
with `Error`, a missing code target (`Error`), and a zero-clock timeout that
empties the environment. The `SOME` returning rows cover a successful result
with the handler absent and present (the `Result` location matches the return
`Loc` and dispatches to `ret_handler`), a mismatched return location (`Error`),
a missing code target (`Error`), a zero-clock timeout, an exception handled at
the matching handler location, an unhandled exception propagated verbatim, an
exception whose location mismatches the handler (`Error`), and `Break`/`Continue`
sub-results (`bad_fun_return` maps each to `Error` with the recursed state). The
observer records result, clock, register 1 and stack length. Kernel replay over a
concrete `evaluate` stub lives in `Flapjack/Test/StackSemCallParity.lean`.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_call_probeScript.sml
scripts/hol-probes/regenerate.sh`. The `evaluateCall` fragment is untagged; the
tagged ports of `find_code_def`, `fix_clock_def`, `set_var_def`,
`bad_fun_return_def` and `dest_Seq_def` live in `StackSem/Control.lean` and
`StackSem/StateOps.lean`, and assembled full evaluation remains on y19g.

`stacksem_buffer_write_probeScript.sml` records five direct original
`stackSem$evaluate` observations for the `CodeBufferWrite` and
`DataBufferWrite` clauses (`stackSemScript.sml:928-944`). The rows cover a
code-buffer write that succeeds through the exact `buffer_write` port with the
byte truncated by `w2w` (260w becomes 4w), a code-buffer write whose address
mismatches the next position (`Error`), a full-width data-buffer write that
succeeds through the 64-bit dimension factor, a data-buffer address mismatch
(`Error`), and `use_stack = F` (`Error` before any register read); the observer
records result plus the affected buffer's position, buffer and space_left.
Kernel replay over concrete `WordSemBuffer` fixtures lives in
`Flapjack/Test/StackSemBufferWriteParity.lean`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_buffer_write_probeScript.sml
scripts/hol-probes/regenerate.sh`. The `evaluateBufferWrite` fragment is
untagged; the tagged `buffer_write_def` port lives in
`Flapjack/Compiler/Backend/Semantics/WordSem/State.lean`, and assembled full
evaluation remains on y19g.

`stacksem_sh_mem_probeScript.sml` records fifteen direct original
`stackSem$sh_mem_op` observations for the shared-memory helpers
(`stackSemScript.sml:194-308`) at 64-bit words. A byte-incrementing FFI oracle
captures the exact configuration and payload bytes through `io_events`, and a
second oracle diverges. The rows cover word/byte/16/32 store and load success,
a plain-word address miss (`a IN sh_mdomain`), a sized-form miss on
`byte_align a`, the guard distinction (a word load at an unaligned address the
sized form accepts is `Error`), both `FFI_final` outcome rows (state unchanged),
and a non-word register (`Loc`, `Error`). Kernel replay over a concrete base
state lives in `Flapjack/Test/StackSemShMemParity.lean`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_sh_mem_probeScript.sml
scripts/hol-probes/regenerate.sh`. The tagged ports of `sh_mem_store_def`,
`sh_mem_load_def`, `sh_mem_store_byte_def`, `sh_mem_store16_def`,
`sh_mem_store32_def`, `sh_mem_load_byte_def`, `sh_mem_load16_def`,
`sh_mem_load32_def` and the `sh_mem_op_def` dispatch live in
`Flapjack/Compiler/Backend/Semantics/StackSem/ShMem.lean`.

`stacksem_sh_mem_op_probeScript.sml` records four direct original
`stackSem$evaluate` observations for the `ShMemOp` clause
(`stackSemScript.sml:922-927`). The effective address is
`word_exp s (Op Add [Var a; Const w])`; a byte-incrementing FFI oracle makes the
successful row observable through the recorded FFI state. The rows cover a
`ShMemOp Load` success with `word_exp` yielding `0w + 8w` and a positive clock
(result `NONE`, clock decremented to 4, FFI state incremented), a `word_exp`
miss on a `Loc` operand (`SOME Error`, state unchanged), a miss on a missing
register (same), and `clock = 0` (`SOME TimeOut`, `empty_env` clearing regs and
the stack). Kernel replay of all four rows lives in
`Flapjack/Test/StackSemShMemOpParity.lean`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_sh_mem_op_probeScript.sml
scripts/hol-probes/regenerate.sh`. The `evaluateShMemOp` fragment is untagged;
the tagged `word_exp_def`, `sh_mem_op_def`, `dec_clock_def` and `empty_env_def`
ports live in `StackSem/Expressions.lean`, `StackSem/ShMem.lean` and
`StackSem/StateOps.lean`, and assembled full evaluation remains on y19g.

`stacksem_ffi_probeScript.sml` records four direct original `stackSem$evaluate`
observations for the `FFI` clause (`stackSemScript.sml:945-960`) at 64-bit words.
The state type is `(64,'c,num)`; `ffi_save_regs = {1; 6}`, `mdomain = {0w}` with
word 0 holding `0xAABBCCDDEEFF0011w`, and the operand registers hold
`configurationLength = 2w`, `configuration = 2w`, `arrayLength = 3w`,
`array = 4w`. The successful oracle returns three constant bytes so the length
check against the three-byte array read passes; a second oracle diverges. The
rows cover `FFI_return` (result `NONE`, `write_bytearray` writes the returned
bytes into word 0, `DRESTRICT` keeps exactly the `ffi_save_regs` keys 1 and 6
and drops 2 and 7, `fp_regs` is emptied, and the FFI state advances with one
`io_event`), `FFI_final` (state unchanged), a byte read outside `mdomain`
(`SOME Error`, state unchanged), and a non-`Word` length register (`SOME
Error`). The probe rewrites `FLOOKUP (DRESTRICT ...)` with `FLOOKUP_DRESTRICT`
because `DRESTRICT` is a non-computational finite-map specification. Kernel
replay of all four rows lives in `Flapjack/Test/StackSemFfiParity.lean`.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_ffi_probeScript.sml
scripts/hol-probes/regenerate.sh`. The `evaluateFfi` fragment is untagged, it
reuses the tagged `mem_load_byte_aux_def`, `write_bytearray_def`,
`read_bytearray_def` and `call_FFI_def` ports, and assembled full evaluation
remains on y19g.

`stacksem_install_probeScript.sml` records six direct original
`stackSem$evaluate` observations for the `Install` clause
(`stackSemScript.sml:893-921`) at 8-bit words with a `num` compiler
configuration and a `num` oracle state. Both the compiler and the compiler
oracle are concrete closures so HOL EVAL reduces the clause: the oracle at step
`n` returns `(n, [(3,Skip)], [0xAA;0xBB])` and the compiler returns
`([0x11;0x22], cfg+1)`, with the code buffer holding `[0x11;0x22]` and the data
buffer holding `[0xAA;0xBB]` at position 0 and the operand registers `1..4`
holding `0w`, `2w`, `0w`, `2w`. `ffi_save_regs = {1; 5}` and `code` holds key 7.
The rows cover a successful install with `use_stack = T` (the appended bitmap,
the code union of keys 3 and 7, the `DRESTRICT` register restriction followed by
the `FUPDATE` at register 1, the emptied `fp_regs`, both `buffer_flush`
positions, and the advanced `shift_seq` oracle), a compiler byte mismatch
(`SOME Error`, state unchanged), an empty `progs` list (`SOME Error`), a compiler
`NONE` (`SOME Error`), the `use_stack = F` arm (the oracle bitmap satisfies the
data equality and the data buffer is left unflushed), and a non-`Word` first
operand (`SOME Error`). The probe rewrites `FLOOKUP` through
`FLOOKUP_UPDATE`/`FLOOKUP_DRESTRICT` because the register update is
non-computational. Kernel replay of all six rows lives in
`Flapjack/Test/StackSemInstallParity.lean`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_install_probeScript.sml
scripts/hol-probes/regenerate.sh`. The `evaluateInstall` fragment is untagged,
it reuses the tagged `buffer_flush_def` and `shift_seq_def` ports and the
untagged `sptUnion`/`sptFromAList` renderings, and assembled full evaluation
remains on y19g.

`pan_globals_fperm_code_probeScript.sml` observes the original
`pan_globalsProof$fperm_code` finite map using its proved
`FLOOKUP_fperm_code'` rewrite followed by HOL EVAL (plain EVAL leaves
FUN_FMAP/preimage finiteness symbolic): both swapped keys, another key whose
body calls a swapped name, a missing key, and equal source/target names.
`Flapjack/Test/PanGlobalsFpermCodeParity.lean` replays all five rows in the
kernel and runtime. Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=pan_globals_fperm_code_probeScript.sml
scripts/hol-probes/regenerate.sh`; original proof theory must already be built.
Full evaluation permutation and remaining single-map equality qualification
are tracked separately on .18.5.2.22.4/.5.

`stacksem_leaf_transfers_probeScript.sml` records sixteen original
`stackSem$evaluate` observations for Skip/Halt/Tick/Return/Raise/Break/Continue
(774-823). Results, clocks, stack lengths and register lookups distinguish
Halt Word/Loc cleanup, missing-register errors, timeout cleanup, successful
Tick decrement and Loc-only Return/Raise. Kernel replay on arbitrary base
states lives in `Flapjack/Test/StackSemLeafTransfersParity.lean`. Regenerate
with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_leaf_transfers_probeScript.sml
scripts/hol-probes/regenerate.sh`. The partial dispatcher is intentionally
untagged; assembled full evaluation remains on y19g.

`stacksem_register_transfers_probeScript.sml` captures thirteen direct original
HOL Get/Set/OpCurrHeap evaluations. It checks word and location payloads,
missing keys, disabled use_store, and arithmetic operand order (8-bit Sub
produces 253 from 7 minus 10). The observer records result, clock, destination
register and CurrHeap lookup. Kernel replay is in
`Flapjack/Test/StackSemRegisterTransfersParity.lean`, over arbitrary base states.
The syntax/state store-name codec preserves every constructor and has both
kernel-checked roundtrips. The dispatcher is untagged assembly infrastructure;
full evaluation remains on y19g. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_register_transfers_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`stacksem_pattern_copy_probeScript.sml` captures twelve direct original HOL
copy_words_for_pattern results. The observer retains returned index/address
and three memory lookups. Cases include zero failure, sentinel-one bypass of
invalid bounds/domain, relocated and plain words, multiword copying, early
and later failure, address/value wraparound, and widths16/4. Width4 has zero
byte stride and overwrites the same address; both HOL and the kernel replay
retain that behavior. `Flapjack/Test/StackSemPatternCopyParity.lean` replays
all rows. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_pattern_copy_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`stacksem_copy_words_probeScript.sml` captures four direct original HOL
`copy_words_def` observations (stackSemScript.sml:711-722) at width 8. The
observer retains the final address and selected memory lookups. Rows cover a
normal relocation whose leading high bit set keeps the loop going
(`normal_continue`, final address `7w` with relocated and plain cells), an
early stop after six writes when the pattern high bit is clear (`stops_early`),
a zero pattern reached during the loop (`zero_pattern`, `NONE`), and an
out-of-range start index (`out_of_range`, `NONE`).
`Flapjack/Test/StackSemCopyWordsParity.lean` replays all rows as kernel-checked
examples and prints a PASS line. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_copy_words_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`stacksem_integer_inst_probeScript.sml` records 33 original StackSem instruction
observations, replayed in `Flapjack/Test/StackSemIntegerInstParity.lean` over
arbitrary base states with all observed fields overridden. The observer uses
w2n on Word payloads, preserving Loc pairs, to canonicalize modular numerals.
The original byteTheory set_byte is nocompute outside its specialized widths;
the probe evaluates, unfolds original set_byte_def/word_slice_alt_def, then
evaluates again. It does not substitute a Lean implementation. Cases cover
same-register Or copying Loc, general arithmetic rejection, signed division,
carry/overflow and alias write order, long division bounds, all memory forms,
64-bit successful 32-bit accesses, endian byte offsets and missing domains.
The dispatcher is untagged assembly infrastructure, with outer NONE reserved
for unhandled FP and inner NONE for original failures. Whole inst assembly
remains on y19g.11.3. HOL words `/` is signed word_quot, unlike Lean BitVec `/`;
the local quotient mirrors HOL's sign cases. Regenerate using
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_integer_inst_probeScript.sml
scripts/hol-probes/regenerate.sh`.

The loop_sem_loop_arith probe additionally captures nine signed LDiv rows:
250/10=0 at width8, each operand-sign combination, minimum/-1 wraparound,
minimum/1, truncation toward zero and zero cases. These are original HOL EVAL
outputs, kernel-replayed in LoopSemEvalExactParity. LDiv is signed word_quot;
LLongDiv retains natural unsigned DIV/MOD and its existing rows. The driver
now registers all seventeen arithmetic labels explicitly.

## StackSem Alloc evaluator clause

`stacksem_evaluate_alloc_probeScript.sml` records eight observations from the
original `evaluate_def` Alloc equation (stackSemScript.sml:779-783): disabled
allocation, missing and location registers, successful Word allocation, GC
failure, missing post-GC AllocSize, location-valued NextFree, and exhausted
space. The latter three retain the collected state; exhaustion additionally
empties the environment and returns Halt (Word 1). GC failure returns the
original state, including its original register and AllocSize.

`Flapjack/Test/StackSemEvaluateAllocCaseParity.lean` kernel-replays all eight
rows over arbitrary base states. The untagged evaluator-case helper includes
four universal dispatch equations and unconditional GC/allocation/case clock
preservation certificates. It calls the reviewed exact allocator; full
evaluator assembly and production routing remain tracked separately. The
initial four-row slice was recovered from released fleet WIP without changing
its shared stash; this slice extends its original HOL failure-path coverage.
Regenerate using the established `scripts/hol-probes/regenerate.sh` workflow.

## StackSem optional StoreConsts stub guard

`stacksem_store_consts_guard_probeScript.sml` captures ten original
`check_store_consts_opt_def` rows (stackSemScript.sml:743-747). NONE
bypasses arbitrary code; SOME requires exactly Seq (StoreConsts t1 t2 NONE)
(Return 0) at that label. Cases distinguish missing/wrong label, each
register mismatch, nested stub, nonzero return, a wrong outer constructor,
and reversed sequence order. Kernel replay lives in
`Flapjack/Test/StackSemStoreConstsGuardParity.lean`.

The structural guard uses the exact shared-word HolProg and Spt code
carriers. Two universal kernel certificates equate its structural decision
and lookup result to actual program equality, without an opaque-payload BEq
or DecidableEq premise. Full StoreConsts evaluation and production routing
remain on the assembly beads. Regenerate read-only with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_store_consts_guard_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

## StackSem store_const_sem definition

`stacksem_store_const_sem_probeScript.sml` captures five direct original
`store_const_sem_def` observations (stackSemScript.sml:729-741, including
`unset_var_def` at :725-727) at width 64. The base state fixes registers
`0 -> 0xAAw`, `1 -> 0w` (copy index), `2 -> 0x100w` (destination),
`3 -> 0x10w` (offset), `4 -> 0xDEADw`, `5 -> 0xBEEFw`, `mdomain = UNIV`,
memory default `Word 0w`, and bitmaps `[0x03w; 0x55w]`. The successful rows
relocate `0x100w` to `bitmaps[1] + off = 0x65w`, return `0x100w + bytes_in_word
= 0x108w`, store `1` into `t1`, `t2` and register `1`, store the returned
address into register `2`, and show the `unset_var 0` arm: `use_alloc = T`
removes register `0`, `use_alloc = F` keeps it. The other rows cover the
duplicate-register guard, a non-word operand, and the `copy_words` `NONE` arm.
`Flapjack/Test/StackSemStoreConstSemParity.lean` kernel-replays all rows.
Regenerate read-only with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_store_const_sem_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

## StackSem evaluate_def StoreConsts clause

`stacksem_store_consts_probeScript.sml` captures six direct original
`evaluate_def` observations for the `StoreConsts` clause
(stackSemScript.sml:784-788) at width 64. The program is `StoreConsts 4 5 stub`
and the base state is the `store_const_sem` fixture. The rows cover all four
guard outcomes and both success arms: `use_store = F -> Error`; `use_alloc = F`
with a `SOME` stub `-> Error`; the exact `check_store_consts_opt` stub guard
failing on empty code `-> Error`; and the `store_const_sem` success reached via
`NONE` stubs with `use_alloc = T`/`F` and via a matching `SOME` stub inserted at
label 7 with `use_alloc = T`. `Flapjack/Test/StackSemStoreConstsParity.lean`
kernel-replays every row; the untagged partial case helper
`Flapjack/StackSemStoreConsts.evaluateStoreConsts` is not the total HOL
`evaluate`. Regenerate read-only with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_store_consts_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

## StackSem FP register movement and sign cases

`stacksem_fpreg_inst_probeScript.sml` captures twenty original `inst_def`
observations for FPMov, FPAbs, FPNeg, FPMovToReg and FPMovFromReg.
The rows cover NaN payloads, signed zero, missing and location operands,
64-bit single-register transfers, 32-bit split/concatenate, unusual 8-bit
truncation, and aliased registers. A 64-bit FromReg ignores its second
register; non-64-bit ToReg writes the high slice last, including aliases.
`Flapjack/Test/StackSemFpRegisterInstParity.lean` kernel-replays every row
over arbitrary base states. The partial case helper is untagged and keeps
unsupported constructors distinct from an instruction failure. Universal
certificates prove successful clock/stack/memory preservation, high-slice
alias behavior, and the 64-bit single-source FromReg equation.
Floating arithmetic, real conversions and complete evaluator routing remain
on the assembling instruction/evaluator beads. Regenerate read-only using
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_fpreg_inst_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

## StackSem FP comparison and arithmetic cases

`stacksem_fp_arith_probeScript.sml` captures fourteen original `inst_def`
observations for FPLess, FPLessEqual, FPEqual, FPAdd, FPSub, FPMul, FPDiv and
FPFma (`cakeml/compiler/backend/semantics/stackSemScript.sml:519-542` for the
comparisons and `:563-587` for the arithmetic). The rows cover true/false
comparisons, a missing FP operand failure, a missing arithmetic operand
failure, and the binary64 results (1+2=3, 3-1=2, 2*3=6, 6/2=3). The FPFma row
is `FPFma 7 2 3` with addend fp7 = 10.0, f2 = fp2 = 2.0 and f3 = fp3 = 3.0:
HOL `fpfma v1 v2 v3 = fp64_mul_add roundTiesToEven v2 v3 v1`
(`fpSemScript.sml:60-62`) permutes the addend to the last slot, so the observed
result is `mul_add 2 3 10 = 16.0` (`0x4030000000000000`), not the
wrongly-ordered `mul_add 10 2 3 = 23.0` (`0x4037000000000000`).
`Flapjack/Test/StackSemFpRegisterInstParity.lean` kernel-replays every row:
structural examples fix each case's exact returned expression, comparison rows
evaluate the computable comparison renderings, and the arithmetic/FMA rows use
the proven computable-rounding bridges of
`Flapjack/Misc/BinaryIeeeArithFp64.lean`. FPMov, FPAbs, FPNeg, FPMovToReg and
FPMovFromReg are already covered by `stacksem_fpreg_inst_probeScript.sml`. The
untagged partial case helper
`Flapjack/Compiler/Backend/Semantics/StackSem/FpRegisterInstructions.lean` is
not the whole HOL `inst_def`. Regenerate read-only using
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_fp_arith_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

`stacksem_fp_convert_probeScript.sml` captures eleven original `inst_def`
observations for FPSqrt, FPToInt and FPFromInt
(`cakeml/compiler/backend/semantics/stackSemScript.sml:558-562` for FPSqrt,
`:605-623` for FPToInt and `:624-636` for FPFromInt). FPSqrt is probed on the
exact square 4.0 (`0x4010000000000000`) whose `isqrtLib` sqrt is
2.0 (`0x4000000000000000`), plus a missing-operand failure. FPToInt covers an
in-range 2.0 -> `2w`, a `2^52` value that fails HOL's `w2i (i2w i) = i` word32
round-trip (out-of-range -> NONE), the 32-bit low/high `bit_field_insert`
split (`FPToInt 14 2` / `FPToInt 15 2` into `d1 DIV 2 = 7`), and a missing
operand. FPFromInt covers the 64-bit low-32-bit read (`0x0000000000000003` ->
3.0), the 32-bit low/high half selection (`FPFromInt 7 14` -> 4.0,
`FPFromInt 7 15` -> 3.0 over `fp7 = 0x0000000300000004`), and a
missing-operand failure. `Flapjack/Test/StackSemFpRegisterInstParity.lean`
kernel-replays every row: the FPSqrt row uses `holFp64Sqrt_rte` from
`Flapjack/Misc/BinaryIeeeSqrtFp64.lean`, the FPFromInt rows use
`holIntToFp64_rte` from `Flapjack/Misc/BinaryIeeeConvert.lean`, and the FPToInt
rows use the computable `holFp64ToInt`. The untagged partial case helper
`Flapjack/Compiler/Backend/Semantics/StackSem/FpRegisterInstructions.lean` is
not the whole HOL `inst_def`. Regenerate read-only using
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stacksem_fp_convert_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.

`stack_props_inst_name_probe.out` records ten direct `inst_name_def` EVAL rows
from original stackPropsTheory, covering every instruction constructor and
logical-register/address, two-register arithmetic, and FP alias failures.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stack_props_inst_name_probeScript.sml bash scripts/hol-probes/regenerate.sh`.
`Flapjack.Test.StackPropsInstructionNames` kernel-replays all ten rows.

`word_alloc_get_live_probe.out` contains three fresh direct original full-program
liveness observations: StoreConsts deletes registers1/2 while adding3/4 and
retaining9; an out-of-range Break returns LN; Return inserts repeated value2
as a set entry. The StoreConsts row distinguishes the earlier compiled clause
from the shadowed duplicate source row. `WordAllocProgramLivenessParity`
kernel-replays the identical inputs. Regenerate using the byte-identical built
original tree with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_get_live_probeScript.sml scripts/hol-probes/regenerate.sh`.
These observations supplement clause review; they do not establish whole-pass
correctness or the pending production liveness route.

### Parallel-move deterministic step

`parmove_fstep_probeScript.sml` directly evaluates original `parmove$fstep`
(parmoveScript.sml:526-546) at option-number registers. Ten equalities cover
every branch, first matching source, cycle save order, and temporary-register
cases without a well-formedness assumption. The output is replayed by
`Flapjack/Test/ParmoveFstepParity.lean`; complete pmov semantics and executed
compiler wiring are separate open tasks.

`word_alloc_get_writes_inst_probe.out` captures seven direct original
`get_writes_inst_def` observations (word_allocScript.sml681-703). Full-tree
equalities cover Const, AddCarry, LongDiv, the literal Load16 catchall,
FPMovToReg at64/32, and the FPMovFromReg catchall. The identical inputs and
outputs are kernel replayed by `Flapjack.Test.WordAllocInstructionWritesParity`.
These regression rows do not establish cross-language equivalence or complete
the production route. Regenerate read-only with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_get_writes_inst_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`word_alloc_get_writes_probe.out` records seven direct original
`get_writes_def` observations (word_allocScript.sml1009-1023). Identical
full-tree inputs/outputs are kernel replayed in
`Flapjack.Test.WordAllocProgramWritesParity`: duplicate Move destinations,
StoreConsts insert order, instruction/shared Load16 distinction, shared-store
fallback, compound Seq fallback, and Install's first destination only.
These rows are regression evidence; the executed compiler route and allocator
correctness remain open. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_get_writes_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`word_to_stack_stack_size_rel_probe.out` records six original frame-size relation
observations (absent/present maximum, failed bound, absent local/frame sizes,
and frame guard) from `word_to_stackProofTheory`. The exact kernel replay is
`Flapjack.Test.WordToStackStackSizeParity`. Regenerate read-only with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_to_stack_stack_size_rel_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_lang_occurrences_exact_probe.out` records twelve original `every_name`,
`every_var` and `every_stack_var` observations, including exact Spt cutsets,
Loop live-set scope and Call handlers under NONE/SOME returns.
`Flapjack.Test.WordLangOccurrencesExactParity` invokes all three new tagged
predicates and kernel-replays each row. Regenerate read-only with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_lang_occurrences_exact_probeScript.sml scripts/hol-probes/regenerate.sh`.

- `word_to_stack_frames_probeScript.sml`: original `handler_val`,
  `is_handler_frame`, and `sorted_env` rows for exact stack-frame predicates.

- `word_to_stack_abs_stack_probeScript.sml`: original abstraction success and failure branches.

- `word_to_stack_index_list_probeScript.sml`: descending indices, value/key projections, guarded first/last lookup, and physical-name division.

- `word_to_stack_bitmap_append_probeScript.sml`: successful bitmap decoding remains unchanged after appending words.
### Parallel-move state semantics

`parmove_semantics_probeScript.sml` captures twelve direct original
windmill/parsem/seqsem/sem/eqenv observations. Function updates use original
`UPDATE_LIST_THM` precedence (last repeated destination wins); parallel sources
are snapshotted, sequential sources are updated, emitted moves are reversed,
and eqenv ignores only NONE. The two eqenv rows use the original
`eqenv_def` and `FORALL_OPTION` simplification; the other rows use EVAL.
`ParmoveSemanticsParity.lean` checks every captured observation; no windmill
premise is imposed on repeated destinations. Full scheduler correctness and
production wiring remain open.

`labsem_updates_probeScript.sml` observes the original LabSem total register/memory updates, sticky assertion failure with retained writes, PC/clock updates, register/immediate decoding, and fixed64 FP register payloads. Its 17 rows are kernel-replayed in `Flapjack.Test.LabSemUpdatesParity`; it does not claim FP arithmetic or a full evaluator port.
- `word_to_stack_map_fst_probeScript.sml`: exact pair-key mapping, collision retention and value projection.
### Literal parallel-move scheduler

`parmove_scheduler_probeScript.sml` captures nine original pmov/parmove outputs:
final emitted suffix, temporary self-move, empty/self/single moves, chain, swap,
three-cycle and repeated destinations. `ParmoveFstepParity.lean` replays them.
The recursion uses the original measure, not fuel. Full semantic correctness
and the executed Word-to-Stack wrapper remain open.

### Parallel-move invariant group

`parmove_invariants_probeScript.sml` captures thirteen original path/wf rows:
empty/single/valid/invalid paths; empty/pending state; repeated destinations;
pending missing source/destination; allowed final temporary source; rejected
FRONT temporary source, active temporary destination and broken active path.
`ParmoveInvariantsParity.lean` kernel replays all rows. `wf_step`/`wf_steps` and
full `parmove_correct` remain open.
- `word_to_stack_abs_stack_prefix_probeScript.sml`: successful bitmap prefix preservation for base, ordinary, handler, recursive and mixed frames.

- `word_to_stack_abs_stack_lengths_probeScript.sml`: exact successful abstraction frame counts for base, ordinary, handler, recursive and mixed frames.

### Literal Word-to-Stack move wrapper

`word_to_stack_wmove_probeScript.sml` captures eleven original64-bit equality
rows for exact DIV2/parmove/format_var/wMoveAux composition. All formatting
branches, register and spill swaps, odd indices and DIV2 collision, truncated
offsets and fprime are replayed by `literalWMoveParityGuard` in the normal
compiler parity suite. Production comp/compile wiring remains open.

### Parallel-move update lemmas

`parmove_updates_probeScript.sml` captures eight original parallel environment
lookups and two temporary-insensitive equivalence directions. Fresh insertion,
snapshot sources, untouched/empty/self/swap cases and repeated-destination
freshness failure are replayed by `ParmoveUpdateLemmasParity.lean`, alongside
generic freshness/windmill theorem applications. Full step invariance and
`parmove_correct` remain open.
`labsem_navigation_probeScript.sml` captures 23 original LabSem fetch, instruction-count, section-entry/positive-label lookup, and following-return-label observations across empty sections. Encoded metadata lengths deliberately differ from instruction positions. The probe simplifies the original existential label guard before EVAL; it defines no substitute evaluator. `Flapjack.Test.LabSemNavigationParity` kernel replays the native definitions using the reviewed classifier.

### Parallel-move path preservation prerequisites

`parmove_path_probeScript.sml` captures ten original SNOC-path and windmill
observations. Empty/single/chain/cycle paths, changed-final-destination and
broken-prefix failures, and fresh/repeated destinations with repeated sources
are replayed in the kernel by `ParmovePathParity.lean`. Generic source-shaped
path_change_start/windmill_cons applications retain the original premises.
Full wf preservation and scheduler correctness remain open.

### ParMove environment-change observations

`parmove_environment_probeScript.sml` evaluates eight direct original HOL rows.
Repeated destinations with equal source maps overwrite differing input values;
untouched values differ when the conditional premise is absent, and changed
source values break equality. Empty and snapshot observations are included.
`ParmoveEnvironmentParity.lean` replays the rows and applies the exact lemma
with its original conjunction. Full scheduler preservation remains open.

`labsem_arithmetic_probeScript.sml` captures 44 original observations across all eight LabSem integer-arithmetic constructors: Loc/self-OR guards, invalid shift/division writes, sticky failure, signed overflow and aliased destinations. Original arithmetic `DIV_0`/`MOD_0` simplify the otherwise unreduced zero-divisor cases after EVAL; no replacement arithmetic evaluator is defined. `Flapjack.Test.LabSemArithmeticParity` replays all rows by direct kernel reduction on otherwise arbitrary native source states.

### ParMove permutation observations

`parmove_permutation_probeScript.sml` captures ten direct original HOL values.
Three destination lookups agree under reversal with shared sources; snapshot,
swap, and empty examples are included. Repeated destinations give 13 versus 12
under reversal, showing why the original windmill premise cannot be removed.
`ParmovePermutationParity.lean` replays all values and checks the full-function
lemma with a genuine list permutation. Full scheduler correctness remains open.

### ParMove generated relation witnesses

`parmove_steps_probeScript.sml` proves one concrete instance of each of the
six original `step_rules` conjuncts in HOL. A T row is emitted only after
`prove` returns a theorem with exactly the requested conclusion; these are
kernel-derived positive witnesses, not EVAL or production compiler parity.
`ParmoveStepsParity.lean` checks the same six rules and standard RTC reflexivity
and a start/emit two-step chain. Rules, leastness, and exhaustive cases were
also compared against the actual generated HOL theorem conclusions.
Well-formedness and semantic preservation are separate unfinished proofs.


### ParMove no-read observations

`parmove_noread_probeScript.sml` captures eight direct original HOL values.
Paired observations include repeated writes, untouched keys, and self moves.
When the tail reads the changed destination, the two sides give 11 versus 12,
showing the no-read premise is necessary. `ParmoveNoReadParity.lean` replays
all rows and checks the full-function lemma with the original sole premise.
The source function update is expressed as the equivalent conditional.
Full scheduler semantic preservation remains open.

### ParMove well-formedness preservation observations

`parmove_wf_steps_probeScript.sml` evaluates fourteen original HOL states: each
of the six relation rules has a valid pre/post example, and pending temporary
source and broken path examples are false. `ParmoveWfStepsParity.lean` replays
the states and kernel-checks generic one-step/RTC theorem applications plus
a start/emit chain. These observations support state-shape review; the full
universally quantified preservation proofs are independently kernel-checked.
Full scheduler semantic correctness remains open.
`labsem_memory_probeScript.sml` captures 46 original ordinary-memory observations across all eight mem_op cases: retained failed Load/Store writes, narrow type/alignment/aligned-domain checks, endian and resizing, unsupported16 operations, address wrap, sticky failure, and one-/eight-bit dimensions. `LabSemMemoryParity` replays them with targeted simplification and kernel computation. The original unused `is_Loc` classifies `semanticPrimitives.v` (Loc Bool/Nat), not `wordLang.word_loc`, and is tracked separately on `flapjack-og0v`; it is absent from these memory operations.

`parmove_start_extend_probeScript.sml` captures 14 direct original HOL `sem`
values for the Start and Extend states, with nonempty reversed emitted histories,
shared sources and snapshot reads. The final pair deliberately repeats a
destination and differs (27 versus 37): it is outside `wf`, not a valid-step
semantic-equivalence claim. Lean kernel examples replay all rows; the generic
case proofs establish the original quantified `eqenv` conclusion under `wf`.
The other four cases and full `step_sem` assembly remain open.
`labsem_shared_memory_probeScript.sml` evaluates original LabSem shared-memory load/store/op equations (429–488). Its 39 rows check all eight operations and actual mappedRead/mappedWrite configuration and little-endian payloads against guarded canonical FFI oracles. They cover returned host/events/register/PC/clock state, unchanged final state, invalid return length, domain and Loc errors, aliasing, clock zero, width24 LOG2 alignment, width8/1 boundaries, TAKE beyond the word length, size256 configuration truncation, ignored ordinary-memory endianness, and address wrap. Generic-width byte results unfold the original library set_byte definition after EVAL. `Flapjack/Test/LabSemSharedMemoryParity.lean` replays every row in the kernel on an arbitrary remaining source state. Full native evaluate and production routing remain separate work.

`parmove_remove_last_probeScript.sml` captures 16 direct original HOL `sem`
values for RemoveSelf and EmitLast, including nonempty reversed emitted history
and parallel snapshot reads. Two deliberately invalid pairs differ: a repeated
destination fails `wf` (17 versus 37), and a pending source reads the emitted
destination despite valid `wf` (17 versus 27). Lean checks every row and these
premise boundaries. The generic case proofs retain both original premises;
Save, EmitHead and the full semantic-preservation assembly remain open.

`target_sem_encoded_bytes_probeScript.sml` captures ten component observations
and proves the whole `encoded_bytes_in_mem` predicate on the same configuration,
memory and domain. The eleventh row is printed only after checking the theorem's
exact conclusion and empty hypothesis list. `TargetSemEncodedBytesParity.lean`
replays each row, using the same `Jump 0w` and block-index `1` witnesses for the
whole predicate. These concrete checks do not prove compiler correctness.
`labsem_inst_probeScript.sml` checks original native asm_inst dispatch for all five constructors in fourteen direct rows: Skip/Const, Loc-sensitive arithmetic, failed division/shift writes, Loc memory and failed Store updates, unsupported ordinary16, and raw FP payload/sign/register-error paths. `Flapjack/Test/LabSemInstParity.lean` replays identical inputs and expected results in the kernel. `LabSem/Inst.lean` separately proves the full unconditional thirteen-conjunct original asm_inst_consts by unfolding every actual native Arith/Mem/FP case. The FP dependency inherits the existing real-number translation assurance boundary; full native evaluate and production routing remain separate work.
`parmove_save_probeScript.sml` captures 20 original HOL `sem` values for Save,
including a cycle, reversed nonempty emitted history, and the permitted final
`NONE` source. The temporary may change (99 to 67) while real-register results
agree. A deliberately invalid pending `NONE` source yields 99 versus 27 and
fails `wf`; no equivalence is claimed for it. Lean checks all observations and
the input invariants. Save's generic theorem proves the original real-register
equivalence from the full source `wf`, with no extra agreement premise.

`wordlang_max_var_inst_probeScript.sml` captures 26 direct original
`max_var_inst` equations, covering every arithmetic and memory clause, integer
FP comparison results, both 32/64-bit transfer branches, and the FP default.
`WordLangMaxVarInstParity.lean` replays these finite observations in the kernel.
They support regression review, not a cross-prover equivalence proof or
production compiler routing claim.

`word_lang_max_var_exp_probeScript.sml` captures eight original expression frame bounds: variables, nested loads, empty and nested operators, shifts, constants, lookups and mixed expressions. `WordLangMaxVarExpParity.lean` kernel-replays identical inputs. Full program max_var and native compiler wrapper routing remain separate work.
`wordlang_cutsets_max_probeScript.sml` captures eight original `cutsets_max`
equations over both Spt components, including raw and non-well-formed trees.
`WordLangCutsetsMaxParity.lean` kernel-replays the same inputs. These rows are
regression evidence, not a full compiler or cross-prover equivalence proof.
`parmove_emithead_probeScript.sml` captures 26 fresh original sem values, paired
with kernel checks: reversed history, a three-move active path and valid final
NONE source. Two wf-valid boundaries violate the constructor guards: closing
a cycle changes register2 from17 to27; a pending read changes register4 from17
to27. These are not accepted steps. The proof derives active no-read and retains
both original guards. Full step_sem/RTC/scheduler assembly remains open.

`parmove_stepssem_probeScript.sml` freshly captures 12 original semantic
observations along a three-step cycle chain (Save, EmitHead, EmitLast), paired
with kernel computations and an actual RTC constructor proof. Real registers
remain27/17, while NONE changes99 to17. The theorem uses original eqenv,
not equality at the temporary; reflexive closure is kernel checked separately.
No functional scheduler or production-route correctness is inferred.

`wordlang_max_var_probeScript.sml` captures 37 direct original full-program
`max_var` equations. Cases include every constructor, tail-call handler
suppression, returning and exceptional continuations, both Loop cut sets,
and 32/64-bit instruction transfer branches. `WordLangMaxVarParity.lean`
kernel-replays the same inputs. These finite rows support source review;
they do not establish a cross-prover equivalence or production route.

`parmove_final_probeScript.sml` freshly captures seven full original pmov
results: terminal history preservation, self move, dependency chain, cycle,
scratch-register inputs, duplicate destinations and nonempty active/history.
Every full state is kernel paired in ParmoveFinalParity. Scratch and duplicate
inputs deliberately exceed wf: pmov_final is unconditional. It proves empty
pending/active lists and an existential emitted history, not semantic correctness.

`labsem_evaluate_probeScript.sml` checks all full native evaluator branches in 57 whole executions, including installed-code execution, byte/configuration guard rejection, failed-instruction rollback, clock exhaustion, shared-memory sequence shifts, external-call register/FP havoc and exact return/final events. The paired kernel fixtures live in `Flapjack/Test/LabSemEvaluateParity.lean`. Constructor-specific `loc_to_pc` computation equations are derived with `SIMP_CONV [Once loc_to_pc_def]` in the HOL kernel to eliminate the original existential label guard before recursive execution; these preserve the original evaluator and inputs.

`parmove_stepscorrect_probeScript.sml` captures12fresh original parallel and
reversed-sequential values for a cycle and chain. Kernel tests construct the
actual five-step cycle and four-step chain relations and apply steps_correct
for arbitrary environments. The temporary changes99to27 on the cycle; original
eqenv excludes it. No pmov-to-Step relationship is assumed or claimed.


`word_to_stack_programs_native_probeScript.sml` observes the literal native `compile_prog` and generic `compile_word_to_stack` in 21 original executions. Cases cover frame subtraction/MAX boundaries, widths1/8/64, perf, arbitrary identifiers, duplicate preservation, and left-to-right bitmap content/length across multiple programs and multiword insertions. `Flapjack/Test/WordToStackNativeProgramsParity.lean` replays identical inputs and results in the kernel. Native top-level compilation and production caller routing remain separate work.


`parmove_destination_probeScript.sml` observes the real/temporary destinations
of native `pmov` on terminal, self, chain, cycle, scratch, duplicate, and active
states. `ParmoveDestinationParity` replays each row and applies the unconditional
original destination-membership theorem, including malformed states.

`parmove_source_probeScript.sml` observes native `pmov` source-register maps
on eight arbitrary states, including scratch/duplicate/active and real history.
`ParmoveSourceParity` replays each row and applies the unconditional original
source-membership theorem; the cycle-save source is justified from active LAST.

`parmove_dsteps_probeScript.sml` freshly proves nine observations from the original
`reg_alloc/parmove` theory: all six deterministic rules, two guard boundaries,
and Extend with a suffix that still reads the selected register. The last row
checks the source prefix-only NoRead guard. `ParmoveDStepsParity.lean` replays
the same inputs in Lean. These finite observations are regression evidence,
not a cross-prover equivalence proof; the complete rules, induction and cases
statements are source-reviewed in `Parmove/DSteps.lean`.

`parmove_split_source_probeScript.sml` freshly evaluates original splitAtPki
with the index-independent source predicate and pair callback used by fstep.
Seven full partition outputs are kernel paired with actual splitSource: empty,
first/middle/absent matches, NONE, duplicate destinations and late zero. Generic
untagged SplitSource laws derive prefixNoRead, suffixheadmatch and empty-suffix
NoRead equivalence. They are Flapjack infrastructure, not a general indexed
combinator port or completed functional scheduler simulation.

`word_to_stack_native_config_probeScript.sml` captures seven fresh original
configuration record projections and updates. Empty, singleton, raw BS and
non-well-formed BN trees are retained without a validity restriction.
`WordToStackNativeConfigParity.lean` kernel-replays the same records. This
carrier prerequisite does not establish the top compiler or its executed route;
those remain tracked on the WordToStack compiler beads.

`parmove_destination_probeScript.sml` observes the real/temporary destinations
of native `pmov` on terminal, self, chain, cycle, scratch, duplicate, and active
states. `ParmoveDestinationParity` replays each row and applies the unconditional
original destination-membership theorem, including malformed states.


`labsem_semantics_probeScript.sml` proves four whole behavior observations through original `semantics_def`: Error, success, resource limit, and self-loop divergence with the entire arbitrary input trace retained. Evaluator equations are derived in the original HOL kernel and record-update left-hand sides normalized before rewriting the quantified clocks. The loop equation covers every natural clock by induction; the divergent trace uses the actual constant-image and prefix-chain/LUB uniqueness theorems. `Flapjack/Test/LabSemSemanticsParity.lean` proves the corresponding native observations, including arbitrary Halt word values. Neither side substitutes a finite timeout for divergence.

`parmove_dstep_step_probeScript.sml` captures six original wf premises and nine cycle semantic values before Save, after Save, and after EmitHead. Kernel fixtures prove all six actual DStep-to-Steps applications with the original wf premise. The temporary changes99to17 on Save; no functional scheduler simulation is assumed.

`word_to_stack_compile_keys_probeScript.sml` captures seven fresh original
key-list projections of the actual recursive compiler, retaining empty, generic,
duplicate and reordered identifiers, bitmap-changing bodies and width-one
inputs. `WordToStackCompileKeysParity.lean` applies the full reviewed theorem
to the same actual compiler results. The source theorem preserves the entire
key list; it does not establish pass simulation or final binary correctness.


`word_alloc_total_colour_probeScript.sml` records eight direct original
`total_colour` lookups: absent physical/virtual keys (including large keys),
mapped physical/virtual keys, and a mapped zero colour. Same-input kernel
fixtures are registered in the actual CompilerParity test root.
`word_alloc_even_locals_probeScript.sml` computes the original starting-local domain predicate on six full native word/location trees: empty, zero, sparse even keys, odd, mixed and duplicate overwrite. Standard finite-domain logical rewrites normalize its universal quantifier; actual Spt insertion-domain lemmas replay the same six inputs in kernel fixtures imported by CompilerParity. This predicate is a prerequisite, not the whole allocator theorem.
`parmove_destination_wrapper_probeScript.sml` freshly captures seven whole
public-wrapper destination lists. Self removal and duplicate destinations are
unrestricted; the cycle emits scratch NONE while nested-option registers
include the distinct real identifier SOME NONE.
`ParmoveDestinationWrapperParity.lean` kernel-computes the same lists and
applies the full source one-way membership theorem to each input. It is
imported by the actual Lake test driver as well as the umbrella. These rows
support regression review, not a cross-prover equivalence or algorithm
semantic-correctness claim.

`word_to_stack_live_length_probeScript.sml` observes the full native frame
bitmap length bound and preserved count-minus-flattened-length equation on six
inputs: zero frame, empty bitmap, positive slack, nested AppList, raw non-wf
Spt and width-eight packing. `WordToStackLiveLengthParity` kernel-applies the
full source theorem to the same actual native outputs; it is imported in the
actual CompilerParity test driver. These finite observations are regression
evidence, not a cross-prover equivalence or compiler-correctness proof.

`word_to_stack_live_prefix_probeScript.sml` freshly observes the actual frame
bitmap prefix on seven inputs, including zero frame, nested AppList, raw
non-wf Spt, width-eight packing and an input count below flattened length.
`WordToStackLivePrefixParity` applies the full source theorem to the same
actual native outputs in the real CompilerParity test driver. No input count
bound is needed. These observations provide regression evidence, not a
cross-prover equivalence or whole-compiler correctness proof.

`word_to_stack_insert_prefix_probeScript.sml` freshly observes seven insertion
prefix equations over the original payload-polymorphic operation: empty and
nested trees, a count below flattened length, positive slack, Bool and Option
Nat payloads. `WordToStackInsertPrefixParity` kernel-applies the full original
statement to the same actual insertion outputs in the CompilerParity driver.
No word dimension or count bound is required. These observations are regression
evidence, not a cross-prover equivalence or whole-compiler correctness proof.

`word_alloc_merge_stack_sets_probeScript.sml` evaluates eight literal full-tree merge equations: empty, retained right payload, left-biased new entries, right-only entries, removal, fixed-set bias, malformed tree, and generic payloads. Same-input kernel fixtures are imported by CompilerParity. This helper does not establish the whole allocator theorem.
`word_alloc_remove_temp_stack_probeScript.sml` captures eight original full-tree deletion equations: empty, root key, duplicate, missing, untouched fixed tree, raw non-wf tree, and two generalized payload/second-component inputs. The native right fold and same-input kernel fixtures preserve arbitrary payload/second-component generality; actual CompilerParity registers them. This helper does not establish allocator correctness or executed compiler routing.

`word_alloc_merge_stack_only_probeScript.sml` captures nine original full-tree equations for every move-analysis branch: present alloc/physical/stack source, absent stack alloc/physical source, missing/root deletion, fixed overwrite, and raw non-wf trees. Same-input kernel fixtures are registered in actual CompilerParity. This helper is not full stack analysis or allocator correctness.

`parmove_correct_probeScript.sml` kernel-proves seven universal-environment instances of original `parmove_correct`, deriving the windmill premise by EVAL: empty, self, chain, cycle, fan-out, reordered chain and Boolean register/value carriers. Matching Lean kernel applications are imported by CompilerParity; this is theorem replay, not an executable compiler parity measurement.
`target_sem_mapped_memory_probeScript.sml` checks both literal mapped instruction templates in original HOL: all eight size/opcode choices, invalid sizes, mismatched register/address/bytes, missing domain, wrapped addresses, empty encodings and word8 size wrap. The ignored return-PC parameter remains independently polymorphic. `TargetSemMappedMemoryParity` checks the same 35 observations in the Lean kernel.

`word_alloc_even_colour_probeScript.sml` compares the actual sparse-tree physical-colour constraint with twenty original observations: physical keys require half their key, virtual values are unrestricted, duplicate entries use original first precedence, arbitrary large natural keys and malformed trees remain accepted inputs. `WordAllocEvenColourParity` checks the same results in the Lean kernel; no well-formedness or complete-domain assumption is added.

`spt_union_algebra_probeScript.sml` checks all four literal universal Spt union/insert statements using their original kernel theorem proofs, then 28 concrete original raw-tree observations. `SptUnionAlgebraParity` applies the matching universal Lean theorems and checks malformed trees, singleton overwrites and left bias. Commutativity is restricted to unit-valued number sets; a Nat-valued counterexample is also checked. Concrete stored numerals are explicitly Nat on both sides.

`word_to_stack_native_top_probeScript.sml` audits the original compile type and checks 24 full top-level result tuples. `WordToStackNativeTopParity` checks identical bitmap words, exact sparse frame maps, complete frame lists and ordered stub/program bodies in the kernel. Boundaries include both performance seeds and narrow wrap, natural register subtraction, duplicate avoid entries/identifiers, unbounded natural IDs, zero frames and ordered multiword bitmap threading. Expected stub subterms use the independently reviewed original/native stub definitions; body and bitmap values are otherwise literal expectations. Executed compiler routing remains separately tracked.

`word_alloc_checker_call_none_probeScript.sml` captures six original full-checker equality observations: empty, one/two arguments, repeated argument, noninjective colour rejection and ignored optional handler. Identical kernel fixtures plus the universal six-premise/five-conclusion Call-NONE case are imported by CompilerParity; returning Call cases remain separate obligations.
`word_to_stack_comp_prefix_probeScript.sml` freshly observes nine whole
compiler-prefix equations: Skip, Alloc, MustTerminate, Seq, If, Loop, returning
Call with perf enabled, returning Call with handler, and StoreConsts. Every
input starts from a nested AppList whose count is deliberately below its
flattened length. `WordToStackCompilePrefixParity` applies the full original
output-equation theorem to the same actual compiler outputs in the real Lake
test driver. These observations are regression evidence, not a cross-prover
equivalence or whole-compiler correctness proof.
`word_alloc_merge_stack_sets_probeScript.sml` evaluates eight literal full-tree merge equations: empty, retained right payload, left-biased new entries, right-only entries, removal, fixed-set bias, malformed tree, and generic payloads. Same-input kernel fixtures are imported by CompilerParity. This helper does not establish the whole allocator theorem.

`word_alloc_loop_checker_probeScript.sml` freshly observes seven original
checker equations: absent and present Break/Continue table lookups, Loop with
Skip and Continue bodies, and a rejected colliding colour. The kernel fixtures
in `WordAllocLoopCheckerParity` replay the same inputs through the actual test
driver. These observations do not establish cross-prover equivalence or the
whole allocator theorem; universal case proofs retain the original motive.
`word_alloc_remove_temp_stack_probeScript.sml` captures eight original full-tree deletion equations: empty, root key, duplicate, missing, untouched fixed tree, raw non-wf tree, and two generalized payload/second-component inputs. The native right fold and same-input kernel fixtures preserve arbitrary payload/second-component generality; actual CompilerParity registers them. This helper does not establish allocator correctness or executed compiler routing.

`word_alloc_merge_stack_only_probeScript.sml` captures nine original full-tree equations for every move-analysis branch: present alloc/physical/stack source, absent stack alloc/physical source, missing/root deletion, fixed overwrite, and raw non-wf trees. Same-input kernel fixtures are registered in actual CompilerParity. This helper is not full stack analysis or allocator correctness.

`parmove_correct_probeScript.sml` kernel-proves seven universal-environment instances of original `parmove_correct`, deriving the windmill premise by EVAL: empty, self, chain, cycle, fan-out, reordered chain and Boolean register/value carriers. Matching Lean kernel applications are imported by CompilerParity; this is theorem replay, not an executable compiler parity measurement.

`word_alloc_coalesce_cost_probeScript.sml` observes eight original native
`get_coalescecost` equations, covering endpoint absence/presence, unequal stored
values, identical endpoints, Bool payloads, zero multiplier, a large natural,
and a malformed tree. `WordAllocCoalesceCostParity` replays the same inputs in
the actual test driver. This definition does not yet replace the executed
allocator heuristics and does not establish whole allocator correctness.
`word_alloc_spillcost_probeScript.sml` captures ten original natural costs: zero, each counter weight, both tail branches on asymmetric counters, and a fifth counter at 2^64. Same-input kernel numeric fixtures are in the actual CompilerParity root. The formula retains source tuple order and multiplies the entire sum; this helper does not establish allocator or executed compiler correctness.

The `word_to_stack_comp_length_probe` checks eighteen actual compiler bitmap-accounting outputs against native kernel fixtures. It covers recursive return/handler and branch threading, nonzero initial count-minus-length gaps, empty and zero-frame inputs, tiny and multiword widths, and an invalid initial bound whose output bound fails. The public full `comp_IMP_LENGTH` theorem retains the source output equation and sole initial bound, and proves both accounting conjuncts over every native constructor.

`WordToStackExpressionMaximumParity` replays the eight original `word_lang_max_var_exp_probe` observations through the actual production `wordExpCakeMaxVar` and existing total expression codec. The unconditional correspondence proof covers every expression, recursively nested argument lists, and arbitrary initial scan maxima at every positive word width. These Flapjack carrier theorems have no HOL original; full program/frame correspondence and native production routing remain separate dependency beads.

`word_to_stack_abs_stack_generality_probe` captures eight original abstraction equations with frame dimensions 1 and 16 independent of bitmap/target-stack dimension 8. Saved cutsets contain nonempty payloads and predicted sizes differ from consumed target frames. `WordToStackAbsStackGeneralityParity` replays them with the generalized declaration and applies both prefix and length lemmas at arbitrary independent positive dimensions. The abstraction remains partial with the original guards.
`word_alloc_heu_counters_probeScript.sml` captures twenty original HOL equations for all five counter updates: absent key, existing asymmetric tuple, repeated update, and preservation of another key. Matching kernel fixtures are in `HeuCountersParity`; these observations do not establish whole allocator equivalence.
`target_sem_mapped_memory_probeScript.sml` checks both literal mapped instruction templates in original HOL: all eight size/opcode choices, invalid sizes, mismatched register/address/bytes, missing domain, wrapped addresses, empty encodings and word8 size wrap. The ignored return-PC parameter remains independently polymorphic. `TargetSemMappedMemoryParity` checks the same 35 observations in the Lean kernel.

`word_alloc_even_colour_probeScript.sml` compares the actual sparse-tree physical-colour constraint with twenty original observations: physical keys require half their key, virtual values are unrestricted, duplicate entries use original first precedence, arbitrary large natural keys and malformed trees remain accepted inputs. `WordAllocEvenColourParity` checks the same results in the Lean kernel; no well-formedness or complete-domain assumption is added.

`spt_union_algebra_probeScript.sml` checks all four literal universal Spt union/insert statements using their original kernel theorem proofs, then 28 concrete original raw-tree observations. `SptUnionAlgebraParity` applies the matching universal Lean theorems and checks malformed trees, singleton overwrites and left bias. Commutativity is restricted to unit-valued number sets; a Nat-valued counterexample is also checked. Concrete stored numerals are explicitly Nat on both sides.

`word_to_stack_native_top_probeScript.sml` audits the original compile type and checks 24 full top-level result tuples. `WordToStackNativeTopParity` checks identical bitmap words, exact sparse frame maps, complete frame lists and ordered stub/program bodies in the kernel. Boundaries include both performance seeds and narrow wrap, natural register subtraction, duplicate avoid entries/identifiers, unbounded natural IDs, zero frames and ordered multiword bitmap threading. Expected stub subterms use the independently reviewed original/native stub definitions; body and bitmap values are otherwise literal expectations. Executed compiler routing remains separately tracked.

`word_alloc_share_checker_probeScript.sml` freshly observes all eight ShareInst
checker cases (Store/Store8/Store16/Store32 and Load/Load8/Load16/Load32) under
identity colouring, with a variable address. The same inputs are kernel-replayed
in `WordAllocShareCheckerParity`, imported by the actual CompilerParity driver.
These finite observations supplement the full original-motive case proofs;
they do not establish cross-prover equivalence or whole allocator correctness.

`parmove_temp_mixed_probeScript.sml` checks four literal scratch-safety clauses with independent bool destination and num source carriers. `ParmoveTempAppendParity` kernel-replays these rows and applies the append theorem to arbitrary independent carriers; existing same-carrier sentinels remain registered.
`word_alloc_share_checker_probeScript.sml` freshly observes all eight ShareInst
checker cases (Store/Store8/Store16/Store32 and Load/Load8/Load16/Load32) under
identity colouring, with a variable address. The same inputs are kernel-replayed
in `WordAllocShareCheckerParity`, imported by the actual CompilerParity driver.
These finite observations supplement the full original-motive case proofs;
they do not establish cross-prover equivalence or whole allocator correctness.
`word_to_stack_comp_prefix_probeScript.sml` freshly observes nine whole
compiler-prefix equations: Skip, Alloc, MustTerminate, Seq, If, Loop, returning
Call with perf enabled, returning Call with handler, and StoreConsts. Every
input starts from a nested AppList whose count is deliberately below its
flattened length. `WordToStackCompilePrefixParity` applies the full original
output-equation theorem to the same actual compiler outputs in the real Lake
test driver. These observations are regression evidence, not a cross-prover
equivalence or whole-compiler correctness proof.

`word_alloc_return_checker_probeScript.sml` freshly observes seven returning
Call equations without an exception handler: empty sets, nonempty cutsets,
duplicate arguments/return variables, Tick and table-routed Break return
programs, and independently rejected return-set/argument-set colour collisions.
`WordAllocReturnCheckerParity` kernel-replays the same inputs through the actual
CompilerParity driver and instantiates the universal original-motive theorem.
These finite observations do not prove cross-prover or whole-allocator equivalence.
`word_alloc_spillcost_probeScript.sml` captures ten original natural costs: zero, each counter weight, both tail branches on asymmetric counters, and a fifth counter at 2^64. Same-input kernel numeric fixtures are in the actual CompilerParity root. The formula retains source tuple order and multiplies the entire sum; this helper does not establish allocator or executed compiler correctness.

`word_alloc_oracle_colour_probeScript.sml` freshly observes ten original oracle
branches: NONE input, empty success, physical-map failure, clash failure,
forced-pair equality/disequality, actual renamed Assign output, stack-bound
equality/failure, and malformed sparse-map input. `WordAllocOracleColourParity`
proves equalities on the same inputs by kernel-checked reduction, without a
program DecidableEq assumption, and is imported by the actual test driver.
This is finite regression evidence, not whole-allocator correctness; the
executed allocator route remains separate work.

`word_to_stack_handler_val_generality_probe` captures eight original `handler_val` equations with independent non-word handler, middle-field and frame-element types. Empty/plain/handler/mixed frames and function-valued middle/frame payloads are kernel replayed in `WordToStackHandlerValGeneralityParity`. The declaration now retains the full source polymorphism under an unqualified tag; it inspects only the handler option constructor and frame-list lengths.
`spt_mapi_probe.out` contains twelve direct original `mapi0_def`/`mapi_def`
observations, kernel-replayed as exact trees in `SptMapiParity`. Cases cover
left/right key order, nested nodes, smart-constructor normalization of raw
malformed trees, nonzero starting indices and Bool/Nat payload changes.
These finite observations do not establish cross-prover equivalence or route
the executed allocator. Regenerate read-only with
`HOL_PROBE_ONLY=spt_mapi_probeScript.sml scripts/hol-probes/regenerate.sh`.
`parmove_seqsem_unchanged_probeScript.sml` captures eight original sequential-evaluator value/equality tuples: empty, chain, cycle, repeated destinations, source-only observed register, written-key negative sentinel, self update, and Bool registers with Nat values. Matching kernel fixtures instantiate the unrestricted preservation theorem. These tests do not establish whole allocator equivalence.
`parmove_temp_mixed_probeScript.sml` checks four literal scratch-safety clauses with independent bool destination and num source carriers. `ParmoveTempAppendParity` kernel-replays these rows and applies the append theorem to arbitrary independent carriers; existing same-carrier sentinels remain registered.


`word_alloc_stack_only_probeScript.sml` captures fifteen original full-tree equalities for native stack analysis: right-fold Move and reverse Seq order, branch operand deletion, recursive wrappers, all Call handler forms, Delta removal and non-Delta preservation, including raw initial trees and the entry projection. Matching kernel fixtures run through CompilerParity. Production allocator routing remains separate.

`parmove_parsem_map_inj_probeScript.sml` captures eight original renamed/original value/equality tuples, including cycles, shared sources, large register IDs, independent Nat-to-Bool register carriers, and a failing domain-injectivity sentinel. Matching kernel fixtures retain arbitrary-carrier theorem application. Finite observations do not prove whole allocator equivalence.
`word_alloc_get_prefs_probeScript.sml` captures seventeen original full-list preference equalities, with nonempty accumulators, duplicates/self moves, branch and sequential ordering, both returning handlers, tail-handler exclusion, loops, nested wrappers, ignored constructors and priority/register naturals exceeding 2^64. Matching actual CompilerParity fixtures reduce in the kernel. Native allocator assembly and production routing remain separate.

`word_alloc_sp_default_probeScript.sml` captures fifteen original `sp_default` and `total_colour` rows: missing physical and virtual registers, present colours overriding the physical default (including zero), raw `BS`/`BN` trees, and keys above 2^64, plus `total_colour` paired with `(\x. 2 * x) o sp_default` at the same inputs. `Flapjack/Test/SpDefaultParity.lean` replays each row in the kernel and applies `totalColourAlt` at every `tc_*` input.

`reg_alloc_in_clash_tree_probeScript.sml` captures eighteen original `in_clash_tree` and `check_clash_tree` rows: `Delta` write/read/miss, `Set` over inserted and raw num_sets, `Branch NONE`/`SOME` left, right, cut-set and miss cases, both `Seq` children, a key above 2^64, and `check_clash_tree` under `f`, `g o f` and a colliding colouring (read through `toAList`). `Flapjack/Test/InClashTreeParity.lean` replays each row and instantiates `checkClashTreeInj` at the probe's tree.

`word_alloc_get_forced_probeScript.sml` captures twenty-eight original `get_forced` rows over `c with ISA := _`: each forced `AddCarry`/`AddOverflow`/`SubOverflow`/`LongMul` ISA guard and its rejected ISA, omitted equal-register pairs, `FPMovToReg`/`FPMovFromReg` at 32 and 64 bits, an unforced instruction, `Seq`/`If`/`MustTerminate`/`Loop`, returning calls with and without a handler, a tail call with a handler, `Skip`, and registers above 2^64. `Flapjack/Test/GetForcedParity.lean` replays each row and instantiates `getForcedInGetClashTree`. These are proof-side ports; the executed RISC-V allocator still uses its own forced-edge traversal.

`data_to_word_config_probeScript.sml` captures six original `data_to_word` pointer-layout rows: `shift_length` and `small_shift_length` of one configuration, and `get_gen_size` for an empty list, an in-range first generation, an overflowing first generation at 64 bits and a 32-bit size. `Flapjack/Test/DataToWordConfigParity.lean` replays every row in the kernel.

`word_gc_functions_probeScript.sml` captures twenty-four original `word_gcFunctions` rows at 64 bits: `ptr_to_addr`, `update_addr`, `decode_length`, both `is_ref_header` outcomes, `memcpy` with its result memory and a failing domain check, `word_gc_move` on a zero and a non-zero `Loc`, a small word, a copied object and a forwarding pointer, `word_gen_gc_move` copying a data object and a reference object, `word_gen_gc_partial_move` outside and inside the young generation, `word_gc_move_roots`, `word_gc_move_list`, `glob_real` on a word and a `Loc`, and the four `new_trig` branches. `Flapjack/Test/WordGcFunctionsParity.lean` replays every row in the kernel, comparing memories at the probed addresses.

`word_remove_must_terminate_probeScript.sml` captures eight original `remove_must_terminate` rows: a `MustTerminate` over a `Seq`, nested `MustTerminate`, a `Seq` of two `MustTerminate`s, an `If` branch, a `Loop` body, a returning call with both a `MustTerminate` return handler and exception handler, a tail call with a `MustTerminate` handler, and the catchall `Tick`. `Flapjack/Test/WordRemoveMustTerminateParity.lean` replays every row in the kernel.

`word_alloc_remove_dead_probeScript.sml` captures twenty-five original `remove_dead`/`remove_dead_prog` rows over one live set (each observed as program, `toAList` keys and dead stores): partial and fully dead `Move`, dead and live `Inst`, `Get`, `OpCurrHeap`, dead `LocValue`, `Set` of a register to a dead and a live store, `Set` of a compound expression, `Seq` dropping a `Skip` and keeping both children, `MustTerminate`, a fully dead `If` and an immediate `If`, a returning call with a handler, a tail call, `Alloc`, `Loop`, `Break`, a `Continue` outside its loop context, the catchall `Tick`, and `remove_dead_prog`. Two `live_store_rel` rows are decided by proving the row or its negation. `Flapjack/Test/WordAllocRemoveDeadParity.lean` replays every row in the kernel.

`word_alloc_nlive_store_probeScript.sml` captures twelve original `nlive_store` rows: a dead and a live `Lookup`, `Var`/`Const`, `Op` with a dead, a live and no argument, live and dead `Load`, `Shift` with each operand dead, and a live `Shift`. `Flapjack/Test/WordAllocNliveStoreParity.lean` proves each `T` row and refutes each `F` row in the kernel.

`reg_alloc_invariants_probeScript.sml` captures thirty original reg_allocProof invariant rows. Quantified `bool` definitions are decided by proving the row or its negation with `TAC_PROOF` and a recorded tactic: `has_edge` (hit, miss, both bounds, a key above 2^64), `undirected`, `good_ra_state` (well-formed, unsorted adjacency, out-of-range move, wrong array length), `no_clash` (distinct, clashing, non-fixed, self loop), `sp_inverts` (inverse, mismatch, inserted pair), `is_clique`, `is_subgraph`, `hide`, `colouring_satisfactory` (injective, clashing, self loop) and the `good_pref`/`good_neg_pref` oracle conditions. `Flapjack/Test/RegAllocInvariantsParity.lean` proves or refutes each row in the kernel and instantiates `spInvertsInsert`.

`reg_alloc_mk_bij_lemmas_probeScript.sml` captures six original `list_remap`/`mk_bij` instances through `toAList`: a repeated and pre-mapped name list from nonempty maps, an inverse pair extended from a nonempty inverse, `wf` of both results, a mixed `Seq`/`Branch SOME`/`Set` tree, and a key above 2^64. `Flapjack/Test/RegAllocMkBijLemmasParity.lean` replays each row and applies `listRemapDomain`, `listRemapWf`, `mkBijAuxDomain`, `mkBijAuxBij` and `mkBijAuxWf` to the probe inputs.

`reg_alloc_accessors_probeScript.sml` captures eighteen original rows of the `ml_monadBaseLib`-generated `ra_state` accessors on one concrete state: `get_dim`/`get_stack`/`get_avail_moves_wl`, `set_dim` and a `set_` that leaves other fields, `adj_ls_length`, in-range and out-of-range (including a key above 2^64) `node_tag_sub`/`adj_ls_sub`/`degrees_sub`/`coalesced_sub`, in-range and out-of-range `update_degrees` (failure keeps the state), `update_move_related`/`update_node_tag`, `st_ex_MAP adj_ls_sub` with and without an out-of-range index, and `Mupdate`. `Flapjack/Test/RegAllocAccessorsParity.lean` replays each row and applies `updateDegreesEqn` and the provisional `degreesSubEqn`/`stExMapAdjLsSub` to the same inputs.

`reg_alloc_colouring_probeScript.sml` captures eighteen original rows of `remove_colours` (empty colours taking priority, no nodes, fixed neighbours, duplicate colours, out-of-range nodes before and after the colours run out), `assign_Atemp_tag` (no-preference and last-colour oracles, no remaining colour, non-`Atemp` node unchanged, out-of-range node), `assign_Atemps` (heuristic order with an out-of-range entry, oracle choice, a single colour) and `first_match_col` (hit, colour outside `ks`, empty list, an index above 2^64). `Flapjack/Test/RegAllocColouringParity.lean` replays each row in the kernel.

`word_alloc_select_reg_alloc_probeScript.sml` captures the original type of `select_reg_alloc` and seven runs for algorithms 0-5: Simple (0, 1), IRC without and with spill costs (2, 3), and linear scan (4, 5) including a spill and a forced pair under a branch cutset, each observed through `toAList` of the returned colouring; the linear-scan rows colour differently from the graph allocator. `Flapjack/Test/WordAllocSelectRegAllocParity.lean` replays each row in the kernel.

`reg_alloc_allocator_probeScript.sml` captures twelve original rows of the complete `reg_alloc` allocator (Simple and IRC, a coalescing move and a move chain, spill choice by cost and by degree with `k = 1`, a forced pair under a branch cutset, physical registers, stack variables, a forced-stack set, high register pressure, and the empty tree), each observed through `toAList` of the returned colouring. `Flapjack/Test/RegAllocAllocatorParity.lean` replays each row in the kernel; it exercises every phase ported in `Flapjack/Compiler/Backend/RegAlloc/Allocator.lean`.

`reg_alloc_exception_functions_probeScript.sml` captures eleven original rows of the generated `raise_Fail`/`raise_Subscript`/`handle_Fail`/`handle_Subscript`: both raises, success passing through, each handler catching its own constructor and passing the other, continuation from the failing state, and `handle_Subscript` around an out-of-range `node_tag_sub`. `Flapjack/Test/RegAllocExceptionFunctionsParity.lean` replays each row in the kernel.

`reg_alloc_stemp_colouring_probeScript.sml` captures the HOL types of `assign_Stemp_tag` and `neg_biased_pref` and eighteen original rows of `tag_col`, `unbound_colour` (empty, gap, entries below the start colour, duplicates), `assign_Stemp_tag` (default and oracle choices, non-`Stemp` node unchanged, out-of-range node), `assign_Stemps` (two start colours), `neg_first_match_col` (hit, excluded colour, out-of-range node) and `neg_biased_pref` (hit, missing move entry, out-of-range partner caught by `handle_Subscript`, node outside `dim`). `Flapjack/Test/RegAllocStempColouringParity.lean` replays each value row in the kernel.
`word_alloc_checker_assembly_probe.out` observes five mixed original checker
equations, kernel-replayed by `WordAllocCheckerAssemblyParity`. Nested control
(Seq/MustTerminate/If/Loop/Break/Continue), returning and handled calls, a tail
call with an ignored malformed handler, and collision rejection are covered.
The full theorem is assembled universally from reviewed constructor cases;
these finite observations do not establish cross-prover equivalence or route
the executed allocator. Regenerate with
`HOL_PROBE_ONLY=word_alloc_checker_assembly_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_to_stack_cutset_maximum_probe` captures twelve original cutset maxima, including duplicate/root keys, reordered and overlapping lists, sparse names and naturals above 2^80. Kernel fixtures replay the same inputs and apply the unconditional full list-to-Spt maximum correspondence. The production frame and compiler route remain separate dependency-linked work.
`parmove_independence_probeScript.sml` proves ten original whole environment-transformer equalities using the original independence/parsem_nil theorems and evaluated windmill premises. Cases cover head/middle/tail extraction, cyclic sources, fanout, self moves, empty surrounding lists and independent Bool/Nat register/value carriers. Matching kernel theorem applications run in CompilerParity; these universal equality observations are not executable compiler parity or whole compiler correctness.
`word_alloc_stack_only_probeScript.sml` captures fifteen original full-tree equalities for native stack analysis: right-fold Move and reverse Seq order, branch operand deletion, recursive wrappers, all Call handler forms, Delta removal and non-Delta preservation, including raw initial trees and the entry projection. Matching kernel fixtures run through CompilerParity. Production allocator routing remains separate.

`word_alloc_get_prefs_probeScript.sml` captures seventeen original full-list preference equalities, with nonempty accumulators, duplicates/self moves, branch and sequential ordering, both returning handlers, tail-handler exclusion, loops, nested wrappers, ignored constructors and priority/register naturals exceeding 2^64. Matching actual CompilerParity fixtures reduce in the kernel. Native allocator assembly and production routing remain separate.

`spt_map_probe.out` contains ten direct original payload-only `sptree$map`
observations, kernel-replayed by `SptMapParity`. Every constructor, malformed
empty internal nodes (which must be retained), nested raw trees and independent
Bool/Nat/Unit payload types are covered. These finite observations do not
establish cross-prover equivalence or route the executed allocator. Regenerate
read-only with `HOL_PROBE_ONLY=spt_map_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_alloc_heu_inst_probe.out` contains fifty direct original instruction
heuristic observations, kernel-replayed as explicit numeric counter trees by
`HeuInstParity`. Every counted clause and FP catchall is covered, including
aliasing, ignored addresses, raw trees, unchanged keys, large Nat counters and
FP moves at widths1/32/64/128 (both integer registers counted at every width).
Finite observations do not establish cross-prover equivalence or route the
executed allocator. Regenerate read-only with
`HOL_PROBE_ONLY=word_alloc_heu_inst_probeScript.sml scripts/hol-probes/regenerate.sh`.
`parmove_independence_probeScript.sml` proves ten original whole environment-transformer equalities using the original independence/parsem_nil theorems and evaluated windmill premises. Cases cover head/middle/tail extraction, cyclic sources, fanout, self moves, empty surrounding lists and independent Bool/Nat register/value carriers. Matching kernel theorem applications run in CompilerParity; these universal equality observations are not executable compiler parity or whole compiler correctness.

`word_alloc_heu_max_probe.out` captures twenty original componentwise maximum
and branch-tree join observations, kernel-replayed by `HeuMaxParity`. Cases
cover large Nat counters, overlapping/disjoint/mixed/nested keys and raw-tree
orientation: untouched left nodes can remain malformed while the indexed map
normalizes the right nodes. Exact trees are compared, not only domains. Finite
observations do not establish cross-prover equivalence or executed allocator
routing. Regenerate read-only with
`HOL_PROBE_ONLY=word_alloc_heu_max_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_to_stack_instruction_maximum_probe` captures fourteen original integer instruction maxima, including immediate/register arithmetic, all arithmetic production constructors with a HOL counterpart, offset-bearing memory and a register name above 2^80. The final two rows expose the zero HOL maximum for Load16/Store16; kernel fixtures verify their existing allocator-guard rejection. The distinct five-register AddCarry has no HOL counterpart and its codec rejection is tested separately. Full arithmetic Option-map equality assumes no codec success, and supported instruction correspondence uses the existing real memory guard. Full program codec closure and executed native routing remain dependency-linked work.

`word_to_stack_colour_domain_probe` captures thirteen original full colouring equations, including unchanged 16-bit memory catchalls, register-renaming memory/arithmetic, collisions, nested control flow, both Call continuations and unbounded colour names above 2^80. Kernel fixtures replay the exact same transformations and expose separate production guard and partial-codec rejection sentinels, including nested five-register AddCarry. The whole-program guard and codec-domain preservation proofs are unconditional for arbitrary programs and colour functions; they do not establish the initial source-to-SSA codec image or the native frame/production compiler route.
`monad_base_probe` evaluates original generic state-exception bind/ignore/return/run/allocation clauses, with changed state on success and failure, zero/three-element allocation and distinct byte-character exception payloads. `MonadBaseParity` replays all ten rows and independent generic carriers. Regression evidence, not a cross-language equivalence proof. Production allocator routing remains open.
`word_to_stack_full_read_bitmap_mixed_probeScript.sml` captures six original universal success-preservation applications at independently chosen bitmap/descriptor widths (8/1, 8/16, 1/32, 16/8, offset 8/32 and same-width 8/8), plus four actual success/zero/location guard equalities. Matching kernel applications include arbitrary independent positive widths. This repairs full_read_bitmap_append type generality; its proof and executed fullReadBitmap definition are unchanged.

`find_index_append_probe` captures ten direct original first-match append observations: empty sides, first-list preference and duplicates, second-list offset, absence, Bool elements and a start above machine width. `FindIndexAppendParity` replays all inputs and applies the full arbitrary-offset theorem. Regression evidence only; scratch safety assembly remains open.
`word_alloc_heu_call_probe.out` captures sixteen original call-name unions,
kernel-replayed as exact trees by `HeuCallParity`. Generic tracked Nat, Bool
and Nat-tuple payloads, overlap/disjoint/deep keys and malformed internal nodes
are covered. Payload-only map retains raw structure and no wf premise is added.
Finite observations do not establish cross-prover equivalence or executed
allocator routing. Regenerate read-only with
`HOL_PROBE_ONLY=word_alloc_heu_call_probeScript.sml scripts/hol-probes/regenerate.sh`.
`word_to_stack_full_read_bitmap_mixed_probeScript.sml` captures six original universal success-preservation applications at independently chosen bitmap/descriptor widths (8/1, 8/16, 1/32, 16/8, offset 8/32 and same-width 8/8), plus four actual success/zero/location guard equalities. Matching kernel applications include arbitrary independent positive widths. This repairs full_read_bitmap_append type generality; its proof and executed fullReadBitmap definition are unchanged.
`word_to_stack_cutset_maximum_probe` captures twelve original cutset maxima, including duplicate/root keys, reordered and overlapping lists, sparse names and naturals above 2^80. Kernel fixtures replay the same inputs and apply the unconditional full list-to-Spt maximum correspondence. The production frame and compiler route remain separate dependency-linked work.

`word_to_stack_instruction_maximum_probe` captures fourteen original integer instruction maxima, including immediate/register arithmetic, all arithmetic production constructors with a HOL counterpart, offset-bearing memory and a register name above 2^80. The final two rows expose the zero HOL maximum for Load16/Store16; kernel fixtures verify their existing allocator-guard rejection. The distinct five-register AddCarry has no HOL counterpart and its codec rejection is tested separately. Full arithmetic Option-map equality assumes no codec success, and supported instruction correspondence uses the existing real memory guard. Full program codec closure and executed native routing remain dependency-linked work.

`word_to_stack_program_maximum_probe` captures thirty-two original full program maxima and kernel-replays the same inputs through the actual production/native codec. Every production constructor appears, including all Call forms, ignored tail handlers, tuple-move scans, duplicate cutsets/loop live sets, nonzero Return accumulators, shared 16-bit memory and names above 2^80. The complete Option-map correspondence uses only the existing allocator memory guard and preserves codec rejection; separate sentinels expose nested five-register AddCarry and ordinary 16-bit rejection. This carrier proof does not establish initial source-to-SSA codec image, native frame/config correspondence or the executed route.
`reg_alloc_remap_probe.out` captures twelve fresh original list remapping and
bijection traversal observations, kernel-replayed by `RegAllocRemapParity`.
Delta/Branch/Seq order, optional sets and their mixed enumeration, repeated
names, raw nodes, large names/counters and arbitrary initial maps are covered.
These finite observations do not establish general cross-prover equivalence or
production allocator routing. Regenerate read-only with
`HOL_PROBE_ONLY=reg_alloc_remap_probeScript.sml scripts/hol-probes/regenerate.sh`.
`word_to_stack_cutset_maximum_probe` captures twelve original cutset maxima, including duplicate/root keys, reordered and overlapping lists, sparse names and naturals above 2^80. Kernel fixtures replay the same inputs and apply the unconditional full list-to-Spt maximum correspondence. The production frame and compiler route remain separate dependency-linked work.

`word_to_stack_ssa_codec_probe` captures eight fresh original full SSA equations, including ABI entry moves, assignment, constant, shift, long multiplication, Raise, Call and Return. Kernel fixtures replay every complete output tree at the same inputs. Nine separate codec-domain sentinels cover ordinary 16-bit memory and nested five-register AddCarry rejection. Untagged universal infrastructure proves actual SSA renaming for arbitrary frames/state and the full ABI wrapper preserve codec acceptance; subsequent optimization passes and the native production route remain open.
`word_alloc_heu_prog_probe.out` captures fifty-two fresh original program
heuristic observations, replayed by `HeuProgParity` in the kernel. Every
program clause and catchall, all shared-memory widths, same-input If joins,
forward Seq, self/other/indirect calls, ignored tail handlers and the source
returning-call no-handler discard are covered. Fixtures also cover raw trees,
unbounded names/counters and widths 1/64/128. These finite observations do not
establish general cross-prover equivalence or production allocator routing.
Regenerate read-only with
`HOL_PROBE_ONLY=word_alloc_heu_prog_probeScript.sml scripts/hol-probes/regenerate.sh`.
`word_to_stack_instruction_maximum_probe` captures fourteen original integer instruction maxima, including immediate/register arithmetic, all arithmetic production constructors with a HOL counterpart, offset-bearing memory and a register name above 2^80. The final two rows expose the zero HOL maximum for Load16/Store16; kernel fixtures verify their existing allocator-guard rejection. The distinct five-register AddCarry has no HOL counterpart and its codec rejection is tested separately. Full arithmetic Option-map equality assumes no codec success, and supported instruction correspondence uses the existing real memory guard. Full program codec closure and executed native routing remain dependency-linked work.

`word_alloc_canonize_sort_probe.out` captures seventeen fresh original mllist
sort observations on the exact inline x/y/priority comparator, replayed by
`CanonizeSortParity`. Empty/base/recursive sizes, duplicates, coordinate
precedence, unnormalized reversed pairs and unbounded names/priorities are
covered. This reuses the existing native MlList sorter; it neither expands
external-source checker trust nor completes normalization/grouping or executed
allocator routing. Source revision/span digest are beside `canonizeMoveLess`.
Regenerate read-only with
`HOL_PROBE_ONLY=word_alloc_canonize_sort_probeScript.sml scripts/hol-probes/regenerate.sh`.

`monad_list_primitives_probe.out` captures twenty-five fresh original Msub,
Mupdate and failure-bound observations, replayed by `MonadListPrimitivesParity`
in the kernel. Head/middle/last/empty/boundary/large indices, duplicates and
independent Nat/Bool/tuple value/exception carriers are covered. Generic theorem
applications retain only the original out-of-range premise. Finite observations
do not establish cross-prover equivalence or completion of successful EL/LUPDATE
equations, state-array accessors or production allocator routing. Regenerate
read-only with
`HOL_PROBE_ONLY=monad_list_primitives_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_state_map_probe.out` captures the original polymorphic st_ex_MAP
type and nineteen fresh result/state equations, replayed by
`RegAllocStateMapParity` in the kernel. Independent input/state/result/exception
carriers, effect order, every failure position, failure-returned state,
state-dependent failure and empty callbacks are covered. The source type is
recorded as an observation; no genericity is inferred from specialized rows
alone. Finite observations do not establish cross-prover equivalence or
completion of generated allocator functions or production routing. Regenerate
read-only with
`HOL_PROBE_ONLY=reg_alloc_state_map_probeScript.sml scripts/hol-probes/regenerate.sh`.
`word_alloc_canonize_moves_aux_probeScript.sml` / `.out` compares the literal
counting recursion at word_allocScript1641-1648 against twelve full output
lists: empty/current zero count, arbitrary accumulator, priority up/down/equal,
changed groups, reverse flush order, unsorted/reversed/self moves, and unbounded
Nat counters/priorities/registers. Kernel pairs live in
`Flapjack/Test/WordAllocCanonizeMovesAuxParity.lean`; this does not establish
the separate sort prerequisite or executed allocator routing.

`misc_find_index_shift_zero_probeScript.sml` / `.out` compares ten whole
original offset-shift equations with kernel theorem applications in
`Flapjack/Test/FindIndexShiftZeroParity.lean`: empty, head/interior/last, missing,
duplicates, zero and unbounded offsets/identifiers, and Boolean carriers.
This supports the Move first-index characterization; it does not establish
the full pass-correctness result.

`parmove_temp_step_probeScript.sml` / `.out` captures nine combined original
wf/source/target scratch-safety observations for all six primitive Step cases,
cycle save, prior-written scratch reads/save, and Boolean registers. Matching
`Flapjack/Test/ParmoveTempStepParity.lean` checks source wf/safety and derives
target safety via the actual Step constructor and full ported theorem.
RTC/pmov and full Move correctness remain separate open obligations.

`word_to_stack_dead_codec_probe` captures thirteen fresh original whole-program dead-code output equations: dead moves/constants/loads, retained ordinary 16-bit memory and stores, observable shared loads, sequence and If pruning, loops, MustTerminate, unchanged tail-call handlers and both transformed returning Call continuations. Kernel fixtures replay the same complete output trees. Separate production-only five-register AddCarry sentinels check deletion, live retention and nested handler rejection; that constructor has no HOL counterpart. The full arbitrary-backward-state theorem and executed wrapper prove one-way actual codec acceptance closure, not equality, since deletion can remove a rejected primitive. Subsequent optimizations and the native compiler route remain open.

`word_to_stack_cse_codec_probe` captures sixteen fresh original complete CSE output equations, covering constant recording, repeated Get/load/offset/shift facts, ordinary 16-bit memory, observable shared loads, loops, MustTerminate, If, unchanged returning and tail Call bodies, and memory-store/call knowledge barriers. Kernel fixtures replay every same-input complete tree. Separate sentinels check nested five-register AddCarry rejection. Untagged infrastructure proves actual CSE preserves codec acceptance exactly for arbitrary knowledge and all program constructors, then derives the executed wrapper; it assumes no valid-knowledge, codec-success, desired-output or pass-success premise. Remaining optimization passes and native routing stay open.
`monad_array_length_probe.out` captures five fresh original Marray_length
equations, kernel replayed in `MonadArrayLengthParity`: empty/duplicate lists,
Bool/list states, Bool values and a large Nat state. Generic pointwise equation
is separately kernel checked. Finite observations do not establish
cross-assistant equivalence or production allocator routing. Regenerate with
`HOL_PROBE_ONLY=monad_array_length_probeScript.sml scripts/hol-probes/regenerate.sh`.
`word_to_stack_instruction_maximum_probe` captures fourteen original integer instruction maxima, including immediate/register arithmetic, all arithmetic production constructors with a HOL counterpart, offset-bearing memory and a register name above 2^80. The final two rows expose the zero HOL maximum for Load16/Store16; kernel fixtures verify their existing allocator-guard rejection. The distinct five-register AddCarry has no HOL counterpart and its codec rejection is tested separately. Full arithmetic Option-map equality assumes no codec success, and supported instruction correspondence uses the existing real memory guard. Full program codec closure and executed native routing remain dependency-linked work.

`word_alloc_canonize_sort_probe.out` captures seventeen fresh original mllist
sort observations on the exact inline x/y/priority comparator, replayed by
`CanonizeSortParity`. Empty/base/recursive sizes, duplicates, coordinate
precedence, unnormalized reversed pairs and unbounded names/priorities are
covered. This reuses the existing native MlList sorter; it neither expands
external-source checker trust nor completes normalization/grouping or executed
allocator routing. Source revision/span digest are beside `canonizeMoveLess`.
Regenerate read-only with
`HOL_PROBE_ONLY=word_alloc_canonize_sort_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_to_stack_unreach_codec_probe` captures sixteen fresh original complete unreachable-pass output equations: Skip and right association, Raise/Return/Break/Continue/tail-call pruning, priority-preserving move composition with duplicate destinations and a residual sequence, loops, MustTerminate, If, unchanged nonreturning handlers and both returning Call continuations. Kernel fixtures replay the same complete outputs. Separate production-only five-register AddCarry sentinels check unreachable deletion, retained rejection and the different handler policies. Untagged infrastructure proves actual sequence simplification, suffix-accumulator flattening and folding preserve acceptance, then derives the executed post-copy wrapper; no output-codec, normal-form, guard or successful-pass premise is assumed. This is one-way closure, since unreachable rejected inputs can be erased; native frame and routing remain open.

`reg_alloc_safe_div_probe` captures fourteen fresh original guarded natural-division equations: zero numerator/denominator, one, below/equal/above divisor, exact/remainder division and numerals above 2^80. Kernel fixtures replay all same inputs and prove the executed `cakeSafeDiv` wrapper is definitionally the reviewed `RegAlloc.safeDiv` at arbitrary Nat inputs. The actual minimum-cost scan and spill selection call this shared definition. These equations do not establish the full spill/allocator success theorem, which remains dependency-linked work.

`parmove_first_index_probe` captures fifteen fresh original predicate/first-read/first-write triples. Empty and ordinary moves, absent writes/reads, simultaneous scratch access, strictly earlier/later writes, repeated occurrences and independent Bool/Nat/function carriers are covered. Kernel fixtures replay the same full triples. The exact tagged characterization retains both zero-offset optional first indices and strict order; local classical equality preserves arbitrary carriers without a public decidable-equality premise. Step/RTC/pmov and complete Move correctness remain separate obligations.
`word_alloc_canonize_moves_probe.out` contains nineteen fresh original full
canonize_moves equations, kernel replayed by `CanonizeMovesParity`. They cover
normalization, strict sorting, maximum priorities, group counts and reverse
group order, including self moves, duplicate orientations, zeros and large
natural numbers. Finite observations do not prove cross-assistant equivalence
or executed allocator routing. Regenerate with
`HOL_PROBE_ONLY=word_alloc_canonize_moves_probeScript.sml scripts/hol-probes/regenerate.sh`.
`word_copy_codec_domain_probe` records eight original copy equations;
`WordCopyCodecDomainParity.lean` replays them and separately checks nested
five-register AddCarry rejection. Codec-domain preservation is Flapjack
infrastructure, not a HOL semantic equivalence theorem.

`parmove_all_distinct_step_probe`, `parmove_state_to_list_probe`, and
`parmove_temp_steps_probe` capture original observations replayed by the
corresponding Lean parity modules. They cover primitive real-destination
distinctness, generic three-list flattening, and RTC scratch safety respectively.
`parmove_preservation_shape_probe` records the original preservation and
renaming statements/types as an audit aid, not a port or equivalence proof.
Its capture omits blank separator lines between printed HOL clauses.

- `parmove_all_distinct_steps_probeScript.sml`: four full destination predicates for zero-step scratch and start/save states. Lean fixtures additionally certify the RTC trace; HOL observations alone do not establish it.
`stackprops_code_labels_probe.out` contains fifteen fresh direct original
`stackProps$get_code_labels` and `stack_get_handler_labels` complete-set
observations, replayed by `Flapjack.Test.StackPropsCodeLabelsParity` at the
identical width64 inputs. Coverage includes direct/indirect and returning/tail
Calls, the differing treatment of a populated handler with no return,
owner-matching and owner-mismatching handler labels, recursive traversal of
both bodies, duplicates, Seq/If/Loop, RawCall entry one, LocValue and optional
StoreConsts stubs. These regressions do not establish compiler label
correctness or cross-language equivalence. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=stackprops_code_labels_probeScript.sml
scripts/hol-probes/regenerate.sh` against the read-only prebuilt theories.
- `parmove_all_distinct_steps_probeScript.sml`: four full destination predicates for zero-step scratch and start/save states. Lean fixtures additionally certify the RTC trace; HOL observations alone do not establish it.
`parmove_map_state_probe` captures ten original equations for mapping both
endpoints through all three lists, including independent Nat-to-Bool carriers
and noninjective maps. `ParmoveMapStateParity` replays the same inputs in Lean;
the finite fixtures do not prove cross-assistant equivalence.

`reg_alloc_sorted_mem_probe` captures twelve original early-stop membership
equations, including unsorted inputs. `RegAllocSortedMemParity` kernel-replays
the same cases and the executed wrapper's equation for arbitrary keys/lists.

`word_alloc_full_ssa_probe` captures 5 original EVAL results of
`full_ssa_cc_trans` at 64-bit words (limit, entry move, renamed body), replayed
in `WordAllocFullSSAParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_full_ssa_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_alloc_ssa_cc_trans_probe` captures 31 original EVAL results of
`ssa_cc_trans` over 64-bit programs covering every clause family (moves,
StoreConsts, instructions, expressions, If merges, cutset restarts for
Alloc/Install/FFI/Call with returns and handlers, ShareInst, Loop/Break/
Continue), replayed by definitional equality in `WordAllocSSACcTransParity`.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_ssa_cc_trans_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_alloc_ssa_helpers_probe` captures 12 original EVAL results of
`list_next_var_rename_move`, `force_rename`, `mk_prio`, `ssa_reconcile` and
`loop_setup` at 64-bit words, replayed by definitional equality in
`WordAllocSSAHelpersParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_ssa_helpers_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_alloc_ssa_trans_inst_probe` captures 28 original EVAL results of
`ssa_cc_trans_inst` (every clause, fixed-register moves, the Load16/FP catchall
and both `dimindex` branches at 64 and 32 bits) and `ssa_cc_trans_exp`,
replayed by definitional equality in `WordAllocSSATransInstParity`. Regenerate
with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_ssa_trans_inst_probeScript.sml scripts/hol-probes/regenerate.sh`.

`word_alloc_fix_inconsistencies_probe` captures 12 original EVAL results of
`option_lookup`, `priority`, `fake_move`, `fake_moves` and
`fix_inconsistencies` at 64-bit words (raw sparse trees), replayed by
definitional equality in `WordAllocFixInconsistenciesParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_alloc_fix_inconsistencies_probeScript.sml scripts/hol-probes/regenerate.sh`.

`hol_sorting_probe` captures the original HOL `SORTED`, `PART` and `PARTITION`
types and 11 EVAL results at the pinned HOL revision (including a
non-transitive relation for `SORTED`), kernel-replayed in `HolSortingParity`.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=hol_sorting_probeScript.sml scripts/hol-probes/regenerate.sh`.

`hol_list_el_probe` captures the original HOL `HD`/`EL` types and six in-range
values at the pinned HOL revision (`HD []` and out-of-range `EL` are
unspecified and not probed), kernel-replayed in `HolListElParity`. Regenerate
with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=hol_list_el_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_move_prep_probe` captures 13 original EVAL results of
`extract_color` (raw sparse result), `coalesce_root`, `full_consistency_ok`
(each rejecting check and an accepted pair) and `update_move`, kernel-replayed
in `RegAllocMovePrepParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_move_prep_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_coalesce_probe` captures 29 original EVAL results of misc
`lookup_any` and reg_alloc `inc_deg`, `consistency_ok`, `coalesce_parent`
(including path compression), `canonize_move`, `st_ex_FIRST`,
`reset_move_related`, `st_ex_list_MAX_deg` and `st_ex_list_MIN_cost`, with full
`ra_state` results, kernel-replayed in `RegAllocCoalesceParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_coalesce_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_worklist_probe` captures 18 original EVAL results of `dec_deg`,
`dec_degree`, `add_simp_wl`, `add_spill_wl`, `add_freeze_wl`,
`add_unavail_moves_wl`, `push_stack` and `respill` with full `ra_state`
results (truncated decrement, duplicate neighbours, out-of-dimension no-op,
partial updates before `Subscript`), kernel-replayed in
`RegAllocWorklistsParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_worklist_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_considered_var_probe` captures 20 original EVAL results of
`is_Fixed`, `is_Atemp`, `is_Fixed_k`, `considered_var` and `deg_or_inf`
(tag kinds, `k` boundaries, out-of-array failures, state preservation),
kernel-replayed in `RegAllocConsideredVarParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_considered_var_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_split_degree_probe` captures 12 original EVAL results of
`is_not_coalesced` and `split_degree` (coalesce targets, degree comparisons,
the `v ≥ d` short-circuit, an out-of-array failure and state preservation),
kernel-replayed in `RegAllocSplitDegreeParity`. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_split_degree_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_graph_construction_probe` captures 20 original EVAL results of
`insert_edge`, `list_insert_edge`, `clique_insert_edge`, `extend_clique`,
`mk_tags`, `mk_graph` (Delta/Set/Branch NONE/Branch SOME/Seq), `extend_graph`
(Bool endpoints) and `init_ra_state` over literal `ra_state` records, with
full result states including `Subscript` failures and their partial updates.
`RegAllocGraphConstructionParity` kernel-replays every row. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_graph_construction_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_move_table_probe` captures the original types and 25 EVAL results
of `tag_col`, `extract_tag`, `unbound_colour` (gaps, duplicates, unsorted
inputs, large naturals), `pri_move_insert`, `undir_move_insert`, `moves_to_sp`
and `resort_moves` (raw sparse trees, Bool payloads, equal priorities).
`RegAllocMoveTableParity` kernel-replays every row and the executed
`cakeUnboundColour`'s definitional equality with the literal definition.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_move_table_probeScript.sml scripts/hol-probes/regenerate.sh`.

`reg_alloc_list_helpers_probe` captures the original types and 23 EVAL results
of `st_ex_FILTER` (accumulator order, state threading, state-dependent
predicates, failure at every position, independent Bool carriers, large
naturals) and `sorted_insert` (accumulator, duplicates, front/middle/end,
unsorted inputs). `RegAllocListHelpersParity` kernel-replays every row and the
executed `cakeSortedInsert`'s definitional equality with the literal
definition. Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=reg_alloc_list_helpers_probeScript.sml scripts/hol-probes/regenerate.sh`.

- `parmove_preserves_moves_step_probeScript.sml`: ten original non-self destination predicates before/after Save, including scratch destination. Lean fixtures certify the steps and witness changes; observations do not prove transition or cross-assistant equivalence.
`word_to_stack_program_bitmaps_probe` captures ten original single-program
and list-compiler bitmap snapshots, replayed in `WordToStackProgramBitmapsParity`.
Cases include invalid initial bounds, width one, repeated identifiers, and
independent Bool identifiers. The general prefix/accounting proofs retain
the original compiler output equations and initial-length bound; finite
snapshots are not a cross-language equivalence proof.

`bytes_in_mem_probe.out` captures eleven fresh original miscTheory observations:
generic Nat/Bool payloads, width-two 3-to-0 wraparound, domain/excluded-set
failures at either position, empty-list guards, and off/hit-region updates.
All eleven rows are kernel-replayed by `BytesInMemParity`. The companion
`bytes_in_mem_type.sml` queries the actual polymorphic beta carrier. Regenerate
read-only with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=bytes_in_mem_probeScript.sml scripts/hol-probes/regenerate.sh`.
Finite observations do not establish cross-language equivalence.
`reg_alloc_sort_moves_probe` captures twelve original priority-sort/merge
equations, including equal priorities and unsorted merge inputs; the matching
Lean fixture replays them. `parmove_all_distinct_steps_probe` captures four
destination-distinctness observations; Lean also applies the full RTC theorem
to zero-step and concrete two-step traces. These fixtures do not establish
cross-language equivalence or whole allocator correctness.

`word_alloc_max3_eq_probe.out` records a fresh replay of the complete local
`max3_eq` statement/proof (word_allocProof10237-10241), using original
`miscTheory.max3_def` and `MAX_DEF`, plus nine EVAL branch/tie/large-Nat
observations. The local theorem is reconstructed, not DB.fetch-ed.
`WordAllocMax3Parity` kernel-checks all nine outputs and the full universal
Lean statement. Reviewer run used a temporary cwd, canonical in-memory
`holpathdb.extend_db` for CAKEMLDIR, and read-only prebuilt theory load paths;
no CakeML files were generated or modified. Standard regeneration selector:
`HOL_PROBE_ONLY=word_alloc_max3_eq_probeScript.sml`.
`lab_to_target_section_lookup_probe.out` captures eight direct original
`labSem$loc_to_pc` observations on section-valid native fixtures. The Lean
`LabToTargetSectionLookupParity` replay rewrites actual lookup through the
original-shaped section-decomposition theorem, covering local labels, missing
labels, preceding instruction offsets and empty-section entries. Recorded byte
lengths deliberately differ from PC counts. This is regression evidence for
that boundary, not a separate oracle for the proof-local helper or a
cross-language equivalence proof. Regenerate with
`HOL_PROBE_ONLY=lab_to_target_section_lookup_probeScript.sml scripts/hol-probes/regenerate.sh`.
- `parmove_preserves_moves_steps_probeScript.sml`: six complete destination/witness observations for Start/Save states. Lean fixtures certify the RTC trace and zero-step case; HOL observations alone do not prove that trace or cross-assistant equivalence.
`wordconvs_code_labels_probe.out` contains twelve fresh direct original
`wordConvs$get_code_labels` complete-set observations, replayed at identical
width64 inputs by `Flapjack.Test.WordConvsCodeLabelsParity`. Cases cover direct
and indirect Calls, both populated bodies, populated handlers with no return,
excluded continuation metadata, duplicate labels, Seq/If/Loop/MustTerminate
and LocValue. These regressions do not establish compiler label correctness or
cross-language equivalence. Regenerate against read-only prebuilt theories with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=wordconvs_code_labels_probeScript.sml
scripts/hol-probes/regenerate.sh`.

`enc_with_nop_source_type.sml` reads the unchanged `enc_with_nop_def` text
from original `lab_to_targetProofScript.sml` and re-elaborates it in an
in-memory HOL theory, without exporting theory artifacts. This type query
checks the generic encoded-list payload of the proof-local relation. The
original proof theory has no prebuilt object in this environment; this is
source re-elaboration, not an observation from that prebuilt theory or a
cross-language equivalence proof. Run `HOL/bin/hol run <absolute script path>`
from the original backend semantics directory, optionally setting `CAKEML`.
# Word-to-Stack native label helpers

`word_to_stack_code_labels_probeScript.sml` evaluates fourteen complete-set
assertions from original `word_to_stackTheory` and `stackPropsTheory`. The
identical inputs are kernel-replayed by `WordToStackCodeLabelsParity`: empty
and repeated stack loads, zero and recursive stack moves, zero and recursive
return copies, both performance/handler flags, arbitrary return payloads,
width one, and zero/nonzero live frames with irregular bitmap counts. The
nonempty continuation includes both code references and an owned handler.
These finite regressions do not prove compiler correctness or cross-language
equivalence. Regenerate with
`CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=word_to_stack_code_labels_probeScript.sml
scripts/hol-probes/regenerate.sh`.
- `parmove_preserves_moves_steps_probeScript.sml`: six complete destination/witness observations for Start/Save states. Lean fixtures certify the RTC trace and zero-step case; HOL observations alone do not prove that trace or cross-assistant equivalence.

`parmove_preserves_moves_pmov_probe.out` records three fresh original scheduler
observations: terminal scratch destination, pending destination, and full pending
output. ParmovePreservesMovesPmovParity kernel-replays the same inputs and applies
the source-shaped preservation theorem with internally discharged well-formedness.
Finite observations are regression evidence, not cross-prover equivalence.
### BackendProps nonzero label sets

`backendprops_nonzero_labels_probeScript.sml` kernel-checks fifteen assertions
from the original definition in `backendPropsTheory`, using standard HOL set
laws without supplying the six restriction theorems. `BackendPropsNonzeroLabelsParity`
replays identical sets, including zero/nonzero entries, label zero with a
nonzero entry, duplicates, naturals larger than 64 bits, non-vacuous subset
and union theorem applications, overlapping/empty set families, and two
membership checks in the infinite `UNIV` set. The final two observations are
`F`: a zero entry is excluded, and a deliberately false subset premise is
rejected. These regressions do not prove cross-language equivalence.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=backendprops_nonzero_labels_probeScript.sml
scripts/hol-probes/regenerate.sh`.

### Register allocator phase closure audit

`reg_alloc_phase_closure_probeScript.sml` captures 29 exported original HOL
definition equations for the five `do_step` phases and their nested helpers.
These are statement captures, not Boolean behavioral parity or Lean theorem
replays. The five success results are local HOL lemmas and were reviewed in
`reg_alloc/proofs/reg_allocProofScript.sml:2075-2838`; no DB export or completed
port is claimed for them. `reg_alloc_phase_closure_audit.json` records the
source-confirmed helper frontier and shared bead IDs under `.10.5.8.6`.

The five phase children remain blocked on genuine helpers. Important retained
details include unspill's two partitions and update order, coalescing's parent
compression even on rejected moves, prefreeze's stateful unavailable-worklist
update, strict spill selector comparisons/tie accumulation, and the full
success existential with good-state/subgraph/dimension/node-tag conclusions.
Native `CakeRegAlloc` helpers are not thereby reviewed as literal state-monad
ports. No source implementation or executed compiler route changes here.

### Native state-exception partition

`reg_alloc_state_partition_probeScript.sml` captures the original generic
`st_ex_PARTITION` type and 22 Boolean equalities over full result/state pairs.
`RegAllocStatePartitionParity.lean` replays the same inputs and outputs in the
Lean kernel. Fixtures cover prepend accumulators, duplicates, reversed input,
large Nat values, state-dependent decisions, all failure positions and
independent Bool/list/product state and exception carriers. The generic empty
case is also checked by `rfl`. Finite parity observations support the literal
source comparison; they do not prove cross-prover equivalence or execute a
production allocator replacement. Native phase proofs and production routing
remain separate work.

`target_props_interference_probe.out` contains eight source-derived HOL
observations of oracle shifts and wrapped FFI regions, replayed by
`TargetPropsInterferenceParity`. The probe reads unchanged original
`shift_interfer_def` and `ffi_entry_pcs_disjoint_def` bodies and re-elaborates
them in memory using the original machine carriers. The original targetProps
proof theory has no prebuilt object here; this is explicitly source-derived
execution, not a prebuilt-theory oracle or cross-language equivalence proof.
No theory artifact is exported. Rows cover identity/composition, preservation
of FFI/target fields, duplicate FFI entries, empty intervals, and wraparound
that first hits an FFI entry. Unresolved logical observations are rejected.
Regenerate with `HOL_PROBE_ONLY=target_props_interference_probeScript.sml scripts/hol-probes/regenerate.sh`.
## Native state-exception iteration

`reg_alloc_state_foreach_probeScript.sml` captures the generic original
`st_ex_FOREACH` type and eleven direct observations. `RegAllocStateForeachParity`
replays order, discarded success values, failure-state retention and tail skipping,
including independent Boolean callback results and List/Boolean states. These finite
rows do not establish full allocator correctness or production routing. Regenerate
with `HOL_PROBE_ONLY=reg_alloc_state_foreach_probeScript.sml` and the read-only
original CakeML reg_alloc theory directory.

`lab_to_target_navigation_types.sml` and its complete `.txt` transcript audit
all three SectionNavigation declarations, their direct dependencies, the
CodeSimilar relation types, the earlier fetch/location theorem binders, and
native nested constructor types. Existing labSem constants are queried from
the original loaded theory. Proof-local definitions and labProps definitions
are re-elaborated from unchanged original source in memory; theorem statements
are parsed from unchanged source and their bound/free variable types printed.
This is type evidence, not a replay of the original proof or a cross-language
equivalence proof. HOL `α line` has one shared word-index parameter; its
instruction/name/memory-operation carriers are fixed by labLang's datatype.
Run `HOL/bin/hol run <absolute script path>` from the original backend semantics
directory and redirect stdout to the paired `.txt`, trimming trailing whitespace
(optionally set `CAKEML`). All printed type and statement content is retained.
`parmove_preserves_moves_pmov_probe.out` records three fresh original scheduler
observations: terminal scratch destination, pending destination, and full pending
output. ParmovePreservesMovesPmovParity kernel-replays the same inputs and applies
the source-shaped preservation theorem with internally discharged well-formedness.
Finite observations are regression evidence, not cross-prover equivalence.

`parmove_all_distinct_wrapper_probe.out` freshly fetches the complete exported
`ALL_DISTINCT_parmove` theorem and captures six whole scheduler outputs
(empty/self/chain/swap/cycle/shared source), plus the duplicate-destination
input/output distinctness boundary `(F,F)`. `ParmoveAllDistinctWrapperParity`
replays all outputs and non-vacuous theorem applications in Lean, with a Bool
carrier check. Original run used a temporary cwd and canonical in-memory
`holpathdb` CAKEMLDIR registration/read-only theory paths; CakeML unchanged.
Selector: `HOL_PROBE_ONLY=parmove_all_distinct_wrapper_probeScript.sml`.
# Full Word-to-Stack compiler label observations

`word_to_stack_comp_code_labels_probeScript.sml` evaluates fourteen original
`word_to_stackTheory.comp` outputs and records complete target code-label sets,
source code-label sets, owned-handler sets, and the original `good_handlers`
guard. The equations cover spilled LocValue, both stubs, sequence/loop, direct
tail calls that drop an arbitrary handler, empty/nonempty indirect dispatch,
returning calls, owned and wrong-owner handlers, a zero frame, and word width one.
Every row is `T`, including the wrong-owner row whose expected guard is `F`.
The assembler configuration remains arbitrary on these config-independent
paths. Captures come from the original prebuilt theory and are regenerated by
the registered runner; the CakeML submodule is read-only.

`Flapjack/Test/WordToStackCompCodeLabelsParity.lean` replays the same full-set
observations in the Lean kernel and nonvacuously applies the unrestricted public
compiler-label theorem with arbitrary assembler config, bitmap state, and frame.
The theorem lives in `WordToStack/Proofs/CompCodeLabels.lean` and was compared
with `word_to_stackProofScript.sml:11748-11812`. These observations are regression
evidence, not a HOL-to-Lean equivalence proof or compiler evaluation simulation.

### Native asmSem arithmetic and state operations

`asmsem_arithmetic_probeScript.sml` evaluates the loaded original `asmSemTheory`
state primitives and all eight `arith_upd_def` constructors. Its 52 captured rows
are replayed by `Flapjack.Test.AsmSemArithmeticParity` against the native
`AsmSem.Arithmetic` definitions, with unrelated state fields arbitrary. Cases
cover ordered aliasing writes, retained writes on failed division and register
shifts, immediate shifts without that register-only guard, prior failure,
carry and signed overflow, and widths 1, 8, 32, and 64. Original DIV_0/MOD_0
simplifications expose zero-divisor quotient/remainder results. These probes
are regression evidence, not cross-language equivalence or full asm evaluation
acceptance. CakeML/HOL remains read-only.

### Native asmProps stride PC coverage

`asmprops_pc_coverage_probeScript.sml` evaluates loaded original
`asmPropsTheory.all_pcs` at 13 length/stride/wrap boundaries and emits direct
membership observations. `Flapjack.Test.AsmPropsPcCoverageParity` kernel-replays
all rows. Cases include zero length, partial/exact stride lengths, repeated
wrapped PCs at width 1, strides equal to or larger than word dimension, and
32/64-bit wrapping. `AsmProps.PcCoverage` separately proves the complete
original recursive characterization and byte-memory domain subset theorem,
with no added length/alignment/uniqueness premise. Probes remain regression
evidence, not cross-language equivalence or full encoder acceptance.
`parmove_all_distinct_wrapper_probe.out` freshly fetches the complete exported
`ALL_DISTINCT_parmove` theorem and captures six whole scheduler outputs
(empty/self/chain/swap/cycle/shared source), plus the duplicate-destination
input/output distinctness boundary `(F,F)`. `ParmoveAllDistinctWrapperParity`
replays all outputs and non-vacuous theorem applications in Lean, with a Bool
carrier check. Original run used a temporary cwd and canonical in-memory
`holpathdb` CAKEMLDIR registration/read-only theory paths; CakeML unchanged.
Selector: `HOL_PROBE_ONLY=parmove_all_distinct_wrapper_probeScript.sml`.
`parmove_scratch_order_wrapper_probe.out` freshly fetches the complete exported
`parmove_not_use_temp_before_assign` theorem and records complete scheduled moves,
first optional scratch-read/write indices, input windmill and the exact option-match
conclusion for empty/self/chain/swap/cycle/shared-source, Bool swap and duplicate
input. Swap/cycle read indices 2/3 follow write index 0; duplicate input is invalid
while its no-read conclusion remains true. `ParmoveScratchOrderWrapperParity`
replays all eight observations and the full generic theorem with seven valid
applications. This is a proof-only wrapper port; the executed scheduler is unchanged.
Selector: `HOL_PROBE_ONLY=parmove_scratch_order_wrapper_probeScript.sml`.

`stackprops_label_safety_probe.out` records ten original whole-program code/handler
safety predicate pairs, including entry zero/one, missing/external labels, infinite
external labels and owned versus foreign handlers. Kernel fixtures replay the
full predicates; these observations are regression evidence, not cross-language
equivalence. Regenerate with HOL_PROBE_ONLY=stackprops_label_safety_probeScript.sml
and the read-only prebuilt backend semantics theories.
`parmove_all_distinct_wrapper_probe.out` freshly fetches the complete exported
`ALL_DISTINCT_parmove` theorem and captures six whole scheduler outputs
(empty/self/chain/swap/cycle/shared source), plus the duplicate-destination
input/output distinctness boundary `(F,F)`. `ParmoveAllDistinctWrapperParity`
replays all outputs and non-vacuous theorem applications in Lean, with a Bool
carrier check. Original run used a temporary cwd and canonical in-memory
`holpathdb` CAKEMLDIR registration/read-only theory paths; CakeML unchanged.
Selector: `HOL_PROBE_ONLY=parmove_all_distinct_wrapper_probeScript.sml`.
### Native asmSem arithmetic and state operations

`asmsem_arithmetic_probeScript.sml` evaluates the loaded original `asmSemTheory`
state primitives and all eight `arith_upd_def` constructors. Its 52 captured rows
are replayed by `Flapjack.Test.AsmSemArithmeticParity` against the native
`AsmSem.Arithmetic` definitions, with unrelated state fields arbitrary. Cases
cover ordered aliasing writes, retained writes on failed division and register
shifts, immediate shifts without that register-only guard, prior failure,
carry and signed overflow, and widths 1, 8, 32, and 64. Original DIV_0/MOD_0
simplifications expose zero-divisor quotient/remainder results. These probes
are regression evidence, not cross-language equivalence or full asm evaluation
acceptance. CakeML/HOL remains read-only.
`parmove_step_map_inj_probe.out` freshly fetches the complete exported
`step_MAP_INJ` theorem and records the complete mapped source/target states of
all six primitive rules under an Option Bool-to-Option Nat renaming. The final
sentinel maps every present natural to `SOME F`: it collapses 4 and 5, but the
original prover verifies `inj_on_state` on the singleton endpoint support 3.
`ParmoveStepMapInjParity` replays these states and all six genuine theorem
applications, the scoped sentinel and an arbitrary carrier identity application.
No global injectivity or decidable equality premise is introduced; this proof-only
port leaves the executed scheduler unchanged.
Selector: `HOL_PROBE_ONLY=parmove_step_map_inj_probeScript.sml`.
### Full native asmSem FP transition

`asmsem_fp_updates_probeScript.sml` uses the loaded original `asmSemTheory`
and original IEEE libraries, evaluating 34 closed claims against the original
`fp_upd`; every capture is resolved `T`. `AsmSemFpUpdatesParity` kernel-replays
them against the native `AsmState` transition using reviewed IEEE refinement
facts. All16 constructors are covered, with widths8/32/64/128, actual-width
concatenation and signed extraction, paired alias/half writes, RTE ties, failed
overflow writes, prior failure, NaN comparisons, sign payloads and FMA order.
These are native raw register words, with no Lab location cases or evaluator
callback. The full original `fp_upd_consts` theorem is separately kernel proved.
The native transition inherits the existing IEEE real-rendering assurance limit
(SOUNDNESS item8); fixed raw arithmetic NaN payload agreement is not asserted.
Probes remain regression evidence, not complete cross-language IEEE equivalence
or whole ASM/compiler routing acceptance.

SSA renaming lookup regressions: `ssa_rename_lookup_probeScript.sml` runs original
`list_next_var_rename` and THE lookups for empty, overwritten, malformed-tree,
reordered and unbounded-Nat inputs. `SSARenameLookupParity.lean` kernel-replays
all five captures and applies the full four-conjunct theorem with arbitrary
initial tree/start. Captures are regression evidence, not a cross-prover proof.
### Generic native ASM assertions

`asmprops_assertions_probeScript.sml` evaluates original `asmPropsTheory`
`asserts`/`asserts2` using its exported `asserts_eval` numeral equations
(the recursive `asserts_def` is marked `nocompute`) and `asserts2_def`.
Its sixteen concrete rows check zero-count behavior, terminal `next 0`,
descending noncommutative update order and reversed GENLIST prefixes,
weakening context bounds, Bool states and independent Nat-state/Bool-
intermediate iteration, count-dependent interference and failed predicates.
`AsmPropsAssertionsParity.lean` kernel-replays the same inputs. Fresh
original full-type queries retain both independent carriers; the definition
ports have no word specialization. These rows are regression evidence,
not HOL-to-Lean equivalence or complete encoder correctness. The full
iteration/weakening theorem chain is a separate dependency.
`word_alloc_max_var_max_probe.out` captures the complete exported theorem and46
fresh original maximum/at-bound/strict-below triples across native constructors,
recursive Call/Loop bodies, ignored fields, non-wellformed cutsets and widths
1/32/64/80. `WordAllocMaxVarMaxParity` checks93 kernel examples against these
inputs and the full premise-free theorem. Run this capture alone with
`HOL_PROBE_ONLY=word_alloc_max_var_max_probeScript.sml`.
### Whole-program Word-to-Stack code labels

`word_to_stack_program_code_labels_probeScript.sml` evaluates seven actual
original `compile_word_to_stack` outputs: target/source/owned-handler label
unions, complete frame lists, bitmap cursor and original EVERY guard. Duplicate
keys, spilled locals, owned and wrong-owner handlers, dropped tail handlers and
bitmap threading are covered. Finite list unions are evaluated as FOLDR UNION
EMPTY, the list form of BIGUNION; a separate original parser check confirms the
theorem's INSERT/UNION grouping. All eight captures resolve T and the seven
output claims are kernel-replayed in `WordToStackProgramCodeLabelsParity`,
alongside a nonvacuous full theorem application with arbitrary configuration,
register count and bitmap input. These are regression checks, not a
HOL-to-Lean equivalence proof or whole compiler correctness acceptance.
Selector: `HOL_PROBE_ONLY=word_to_stack_program_code_labels_probeScript.sml`.

`ssa_merge_moves_probe.out` captures ten complete original merge_moves results,
both maps included, plus the exported definition and full inferred type. Native
`SSAMergeMovesParity` kernel-replays those results, including tail-first order,
duplicate keys, malformed trees and unbounded naturals. Production routing
remains separately tracked; these observations are not a cross-prover proof.
`list_next_var_rename_lemma1_probe.out` records a fresh replay of the complete
local original theorem and proof, plus eight full renaming observations with
selected map lookups and all three arithmetic conclusions. Cases include
duplicate names, overwritten keys, a malformed initial tree, zero and odd
counters, and unbounded naturals. `SSAListRenameArithmeticParity` checks17
kernel examples against identical inputs and the complete theorem. Select
`HOL_PROBE_ONLY=list_next_var_rename_lemma1_probeScript.sml` to regenerate.
### Native StackProps forbidden operations

`stackprops_forbidden_operations_probeScript.sml` records 46 original predicate
pairs for `no_install` and `no_shmemop`: all 34 constructors and 12 nested
Call/Seq/If/Loop boundaries. Both optional Call bodies are inspected independently,
including a forbidden handler when the return field is NONE. Every equality
observation resolves T and is kernel-replayed by
`StackPropsForbiddenOperationsParity`, with additional arbitrary positive-width
and payload applications. The definitions use the reviewed native `HolProg`
carrier and preserve the literal source clauses. These are regression checks,
not cross-language equivalence or full compiler preservation acceptance.
Selector: `HOL_PROBE_ONLY=stackprops_forbidden_operations_probeScript.sml`.
### Full generic ASM assertion iteration

`asmprops_assertions_iteration_probeScript.sml` applies all six original
`asmPropsTheory` iteration/weakening theorems. It matches each complete
conclusion, instantiates remaining source variables, proves every original
premise, checks the resulting theorem has no hypotheses and exactly the
requested conclusion, then evaluates that conclusion. All six rows are `T`;
`AsmPropsAssertionsIterationParity.lean` applies the corresponding full Lean
theorems to the same inputs. Weakening/interference fixtures change functions
above the original count bound, and the intermediate carrier remains Bool
while states are Nat. These regressions do not establish cross-language
equivalence or complete encoder correctness.

`word_alloc_limit_var_probe.out` records the full original definition/type and
twelve native-program maximum/limit/class/strict-bound observations. Inputs
cover all four residues, zero/multiples, widths1/32/64/80, unbounded naturals,
returning Call bodies, ignored tail handlers and ignored Load16 fields.
`WordAllocLimitVarParity` checks thirteen kernel examples against identical
inputs. Select `HOL_PROBE_ONLY=word_alloc_limit_var_probeScript.sml`.
The executed upstream maximum/limit route remains tracked on .30.1.2.1.

`ssa_locals_bounds_probe.out` replays the literal original local
`ssa_locals_rel_more` proof (5195–5203), preserving its generic locals payload
and original conjunction. Existing `ssa_locals_rel_probe.out` observations and
`SSALocalsParity` fixtures cover nonvacuous, rejected, boundary and malformed
relations; that fixture additionally applies the complete bound theorem at
arbitrary payload, trees and counters.

`ssa_locals_swap_probe.out` captures the complete literal local SSA map-swap
proof and inferred free-variable types. Source and target states share only
the word dimension; their code and FFI carriers are independent. The generic
`SSALocalsParity` fixture applies the actual theorem at arbitrary native states.
### SSA renaming properties

`ssa_rename_properties_probeScript.sml` replays the complete local
`list_next_var_rename_props` source proof (word_allocProof5749-5777), with its
two local register-class increment prerequisites also replayed literally. It
then applies this proved theorem to eight original `list_next_var_rename`
results: both classes, empty lists, duplicates, existing and overwritten
bindings, a malformed tree, and unbounded natural indices. Each application
discharges the original equality and class/map premises and checks an empty
hypothesis list. Rows contain `(next,T)`: `EQT_INTRO` renders the **proved full
four-conjunct conclusion** as T. This is distinct from attempting to EVAL a
symbolic universally quantified lookup predicate. The full replay statement is
captured separately; this local theorem is not claimed to be exported in HOL's DB.

### Independent return frame-tail carriers

`word_to_stack_copy_ret_carriers_probeScript.sml` directly evaluates the original
`word_to_stack` definitions with Bool and List Bool third frame components,
independent Nat/Bool return lists, widths 64 and 1, both handler offsets and an
Install continuation. `WordToStackCopyRetCarriersParity` kernel-checks the same
five observations and applies the full code/handler-label theorem with arbitrary
independent frame-tail and list types. Original full type is
`bool -> bool -> num # num # beta -> gamma list -> alpha stackLang$prog -> alpha stackLang$prog`;
its unused frame-tail must not be specialized to Nat. These checks provide
regression evidence and do not prove cross-language equivalence or compiler correctness.

### Native no-install helper theorems

`word_to_stack_no_install_helpers_probeScript.sml` applies the six original
exported helper theorems at twelve concrete inputs, discharging the original
universal callback premises from `no_install_def`. Each result has no assumptions
and its exact conclusion is checked before evaluation. The local
`copy_ret_aux_no_install` theorem is not exported, so its two source definition
instances are evaluated directly. `WordToStackNoInstallHelpersParity` kernel-checks
the same fourteen inputs using all seven complete Lean theorems, plus explicit
false results for Install continuations. Coverage includes zero/positive counts,
all four move operand forms, register/spill branches, bitmap insertion, arbitrary
frame arithmetic and word widths 64/1. This is helper preservation only; the
`copy_ret` wrapper and full compiler preservation remain tracked on bead47.2.
Original observations and kernel checks do not establish cross-language equivalence.
### Full incremental Word-to-Stack handler safety

`word_to_stack_handler_safety_probeScript.sml` observes the original actual
whole-program compiler, EVERY handler guard and full `stack_good_handler_labels`
predicate. Twelve pair-equality claims resolve T: nonzero wrong-owner and nested
wrong-owner failures, zero and existing entry-one exceptions, duplicate owners,
nested valid handlers, dropped tail handlers, bitmap threading and width one
with zero registers. The probe proves finite-list union normalization in HOL,
evaluates the compiler, then discharges finite-set claims; the two negative
predicate cases use the concrete offending `(9,5)` witness. No compiler
correctness theorem is used to prove these observations. Matching kernel
regressions and a nonempty full public theorem application retain arbitrary
positive width/configuration/registers/bitmap input. These are regression checks,
not cross-language equivalence or overall compiler correctness acceptance.
Selector: `HOL_PROBE_ONLY=word_to_stack_handler_safety_probeScript.sml`.

### Native WordConvs whole-program label safety

`wordconvs_label_safety_probeScript.sml` checks fourteen original
`good_code_labels` predicate equality claims, including three false predicates,
infinite UNIV external labels, duplicate owners, cross references, returning and
absent-return handler boundaries, nesting and width one. All claims resolve T.
A local HOL finite-union lemma supports evaluation; missing-label failures use
the concrete label 8. Matching kernel fixtures and an arbitrary positive-width,
unrestricted external-set equation live in `WordConvsLabelSafetyParity`.
These checks do not establish cross-language equivalence or full compiler
preservation. Selector: `HOL_PROBE_ONLY=wordconvs_label_safety_probeScript.sml`.

### Native Word-to-Stack no-shared-memory helpers

`word_to_stack_no_shmemop_helpers_probeScript.sml` evaluates 22 original
helper predicate claims. All resolve T, including four move representations,
empty/multiple lists, both register-write branches, width one, zero/nonzero
bitmap frames, and forbidden continuations whose predicate stays false.
`WordToStackNoShmemopHelpersParity` kernel-replays identical inputs and applies
the full public theorems with unrestricted inputs and original hypotheses.
These regressions do not establish cross-language equivalence or full compiler
preservation. Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_helpers_probeScript.sml`.

### Independent unused handler frame carriers

`word_to_stack_handler_frame_carriers_probeScript.sml` captures both complete
original PushHandler/PopHandler types and twelve full output equality claims.
The frame tails are independently Bool/String or List/Bool; both perf branches,
widths64/1, and Skip/forbidden continuations are covered. All equalities resolve T.
`WordToStackHandlerFrameCarriersParity` kernel-replays identical outputs and
applies universal native/generic transports with arbitrary independent carriers.
Two native erasure certificates prove that changing unused fields and their
carriers leaves complete helper outputs unchanged. This does not establish
cross-language equivalence, instrumentation correctness, or pass simulation.
Selector: `HOL_PROBE_ONLY=word_to_stack_handler_frame_carriers_probeScript.sml`.
`word_alloc_limit_var_probe.out` records the full original definition/type and
twelve native-program maximum/limit/class/strict-bound observations. Inputs
cover all four residues, zero/multiples, widths1/32/64/80, unbounded naturals,
returning Call bodies, ignored tail handlers and ignored Load16 fields.
`WordAllocLimitVarParity` checks thirteen kernel examples against identical
inputs. Select `HOL_PROBE_ONLY=word_alloc_limit_var_probeScript.sml`.
The executed upstream maximum/limit route remains tracked on .30.1.2.1.

### SSA map extension

`ssa_map_extend_probeScript.sml` replays the literal local
`ssa_map_ok_extend` statement and proof (word_allocProof4624-4634). Seven
applications cover empty maps in both nonphysical classes, an existing binding,
an overwrite, a malformed tree, and large natural keys/values. Each original
premise is independently proved; the resulting theorem must have no hypotheses
and exactly the requested map-bound conclusion. `EQT_INTRO` renders that proved
conclusion as T; these are theorem applications rather than direct EVAL of a
symbolic universally quantified lookup predicate. Two further rows EVAL/simplify
the physical-register and at-bound false premises. The complete local theorem
is printed separately and is not claimed to be an exported HOL DB theorem.

### SSA register-class conversion

`ssa_register_flip_probeScript.sml` replays all three complete local source
proofs: `is_alloc_var_flip`, `is_stack_var_flip`, and `flip_rw`. Eight direct
original predicate tuples cover all four residues, both nonphysical classes
after further increments, and large natural indices. The probe applies each
implication three times, discharging its premise by original EVAL, and applies
the unconditional two-equality theorem to all eight inputs. Each result has no
hypotheses; `EQT_INTRO` renders its proved conclusion as T. The three local
replays are captured separately and are not claimed exported HOL DB theorems.
`SSARegisterFlipParity` kernel-checks identical tuples and fourteen full public
theorem applications, without a bounded-register or additional class premise.

`ssa_locals_insert_probe.out` replays both literal original fresh SSA/local
insertion proofs and captures their fully generic locals/value types. Two
concrete original theorem applications match `SSALocalsInsertParity`: insertion
from empty trees and insertion preserving an existing mapped source key/value.
These are checked theorem applications rather than a claim that the original
simplifier decides the quantified relation after insertion.
`ssa_locals_bounds_probe.out` replays the literal original local
`ssa_locals_rel_more` proof (5195–5203), preserving its generic locals payload
and original conjunction. Existing `ssa_locals_rel_probe.out` observations and
`SSALocalsParity` fixtures cover nonvacuous, rejected, boundary and malformed
relations; that fixture additionally applies the complete bound theorem at
arbitrary payload, trees and counters.

### Native return-copy and performance no-shared-memory core

`word_to_stack_no_shmemop_call_core_probeScript.sml` evaluates twelve original
helper predicate claims: zero/one/repeated return copying and complete perf
prefix/suffix syntax over widths1/32/64/80. All claims resolve T. The ordinary
Load/Store instrumentation operations remain distinct from forbidden ShMemOp.
`WordToStackNoShmemopCallCoreParity` replays identical inputs in the kernel and
applies all three full public theorems with arbitrary inputs and positive width.
These regressions do not establish cross-language equivalence or instrumentation
evaluation correctness. Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_call_core_probeScript.sml`.

`ssa_map_step_probe.out` replays the original local plus-two bound proof
using a freshly replayed original local monotonicity proof. Its six complete
predicate pairs are kernel matched in `SSAMapStepParity`, including the
rejected-bound/physical cases, malformed tree and unbounded natural values.
### SSA map intersection and insertion

`ssa_map_preservation_probeScript.sml` replays the complete literal local proofs
from word_allocProof lines 5916–5933 and captures the independently polymorphic
right-map binder type. Thirteen actual theorem applications discharge the full
original premises, require empty hypotheses and the exact requested conclusion,
then render that proven predicate as `T` with `EQT_INTRO`. These rows are not
claimed direct evaluations of a symbolic universally quantified map predicate.
Two false original guard evaluations are separate sentinels. Matching kernel
applications cover empty, preserved/dropped, overwritten, malformed, branching
and large-number maps; they are regressions, not a cross-language proof.

### SSA locals physical-register writes

`ssa_locals_physical_insert_probeScript.sml` replays the complete literal
`ssa_locals_rel_ignore_insert` local proof at word_allocProof 5573–5587 in its
original theory environment. Eight actual theorem applications discharge the
whole original premise, check empty hypotheses and the exact conclusion, then
render that proved relation as `T` via `EQT_INTRO`. Two false guards are direct
original simplifications; the complete statement and inferred generic payload
types are captured separately. The kernel fixture applies the full theorem to
the identical Bool/Nat inputs, including overwritten physical keys, malformed
trees and an unbounded natural key. These regressions are not a cross-language
proof or completion of the full SSA correctness theorem.

`ssa_merge_frame_probe.out` replays the literal complete local `merge_moves_frame`
proof and its local `ssa_map_ok_extend` prerequisite, then freshly evaluates ten
complete original merge results. The same-input kernel tuples in
`SSAMergeMovesParity.lean` cover missing/equal/unequal maps, tail order, duplicate
keys, malformed trees and unbounded natural registers.
`SSAMergeMoveFrameParity.lean` applies the full theorem to arbitrary inputs with
only the original allocation-class premise and all four result conjuncts.
Malformed/physical-counter observation rows test the definition; they do not
claim that the allocation premise holds. No exported local theorem is claimed.

ssa_merge_correct_right_probe.out replays the complete original local merge_moves_correctR proof and its literal local prerequisites, then records all original inferred state/carrier types. CorrectRight proves the same five-conjunct native statement in Lean; no executable change or cross-language equivalence claim.

ssa_merge_correct_left_probe.out replays the full original local merge_moves_correctL proof and its literal prerequisites, recording the complete statement and seven inferred types. CorrectLeft proves all five native evaluator conclusions with original hypotheses. No executable change or cross-language equivalence claim.
### Full WordConvs no-install equations

`word_convs_no_install_def_probeScript.sml` projects all 26 clauses of the
original exported `no_install_def`, matches each complete constructor input,
and checks assumption-free exact clause applications before evaluating the pair
(actual predicate value, original clause conclusion). Three additional width-one
Call rows complete all four return/handler combinations. `WordConvsNoInstallDefParity`
projects the same clauses from the entire Lean conjunction at identical inputs;
Install and recursive failing bodies remain false, every original clause true.
The existing canonical `noInstallSubprogsHOL` predicate is reused. Normalized
Install comparisons simplify by constructor disjointness, so the ShareInst
clause requires no choice of HOL ARB. All source shared inputs remain in the
full theorem; the only qualifier translates positive type-indexed word dimensions.
These regression observations do not establish compiler correctness or replace
source-level HOL/Lean correspondence review.

### Full generic-frame copy-ret no-install theorem

`word_to_stack_copy_ret_no_install_probeScript.sml` evaluates eight original
full `copy_ret_no_install` iff instances together with actual output predicates.
The original theorem is local; this capture evaluates original definitions and
does not claim an exported theorem application. Independent generic frame tails
and return-list types, widths 64/1/16, zero/nonzero counts, both flags and unsafe
Install/handler/loop continuations are replayed by
`WordToStackCopyRetNoInstallParity`. The unrestricted native theorem retains the
full source iff without a continuation-safety assumption.

### Full incremental compiler code-label safety

`word_to_stack_code_label_safety_probeScript.sml` evaluates ten original full
compiler source/target safety pairs, including duplicate keys, spilling, owned
and wrong-owner returning handlers, a dropped tail-handler source reference,
threaded bitmap output and width-one words with an infinite external set.
Missing references and wrong handler ownership give `(F,F)`; the dropped
tail-handler reference gives `(F,T)`. Each row proves the stated pair by
evaluating original definitions, without claiming an exported theorem
application. `WordToStackCodeLabelSafetyParity` kernel-replays identical inputs
and applies the unrestricted full theorem with arbitrary configuration, register
count and bitmap state. These observations do not establish cross-language
equivalence or complete the full compiler correctness goal.

### Generic WordConvs code-label row carriers

`word_convs_code_label_carriers_probeScript.sml` freshly checks the original
`good_code_labels_def` with Bool, Unit, List Bool and Option Bool second row
fields, at widths 64/1/16. `WordConvsLabelSafetyParity` replays the four cases
and quantifies the independent generic field carrier. The original full-type
query revealed that fixing this ignored field to Nat specialized the predicate;
its existing canonical Lean definition now preserves the generic carrier.
The actual compiler theorem still uses Nat there, as required by its original
compiler type. No clauses or executed compiler behavior change.

ssa_physical_state_updates_probe.out freshly replays the literal physical-target setVar and list-insert locals-relation proofs and records their independent source/target code/FFI types. SSALocalsPhysicalStateUpdates retains every original premise including list length, using native Spt locals. No executable change or cross-language equivalence claim.
### Full WordConvs forbidden-constructor equation group

`word_convs_no_alloc_def_probeScript.sml`, `word_convs_no_mt_def_probeScript.sml`
and `word_convs_no_share_inst_def_probeScript.sml` each instantiate all 26
original exported clauses and three further Call option combinations at width
one. Every row records actual predicate truth and the original clause
conclusion. Failing recursive/rejected constructor values remain false;
all original clause conclusions are true. `WordConvsPredicateEquationsParity`
replays the 87 observations through complete conjunction projections, preserving
both optional Call bodies. The public theorems retain all original shared
binders and simplify only constant constructor inequalities/self-equalities;
no ARB representative or extra premise is introduced. The canonical reviewed
predicates are reused. This supporting group does not establish full compiler
preservation or cross-language equivalence.
### Native return wrapper no-shared-memory preservation

`word_to_stack_no_shmemop_return_probeScript.sml` evaluates sixteen original
predicate pairs with safe and forbidden continuations, zero/nonzero return
counts, both flags, widths1/32/64/80, a String frame tail and independent Bool
return list. Each pair is checked against its explicit true/true or false/false
result. `WordToStackNoShmemopReturnParity` kernel-checks the identical inputs
and applies the full theorem at arbitrary independent carriers and positive
width. These regressions do not establish cross-language equivalence.
Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_return_probeScript.sml`.

### Native compiler instruction no-shared-memory case

`word_to_stack_no_shmemop_inst_probeScript.sml` checks all source instruction
subconstructors and extra width1/32/80 FP moves. Forty-two original EVAL
observations jointly check the source no-share guard, actual compiled target
no-shared-memory predicate and unchanged full bitmap pair. The samples include
zero/large registers, zero/nonzero frames, both perf flags, width64/non64 FP
moves and unhandled Load16/Store16. `WordToStackNoShmemopInstructionsParity`
replays identical observations through the actual kernel-checked compiler
equations and applies the original-shaped Inst case at arbitrary inputs.
These regressions do not establish cross-language equivalence or full compiler
preservation. Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_inst_probeScript.sml`.



`word_alloc_limit_props_probe.out` freshly re-elaborates the literal complete
local `limit_var_props` proof, then evaluates twelve complete native program
maximum/limit/allocation/strict-occurrence tuples. The tuples exactly match
`WordAllocLimitVarParity.lean`; `WordAllocLimitPropertiesParity.lean` imports
those kernel fixtures and applies the full public theorem with arbitrary
positive-width programs and the original limit equality premise. Cases retain
all residues, widths1/32/64/80, the original ignored Load16 registers, tail Call
handler exclusion, returning Call body traversal and unbounded Nat registers.
The qualified tag records only the standard HOL type-indexed word translation.

`word_to_stack_no_shmemop_handlers_probe.out` literally replays all three local
PushHandler/PopHandler/StackHandlerArgs no-shmemop proofs and captures their
generic operation types. Sixteen fresh predicate observations cover both perf
flags, independent unused frame carriers, safe and forbidden continuations,
widths1/32/64/80, direct/indirect generic destinations and large frame offsets.
`WordToStackNoShmemopHandlersParity.lean` kernel-replays every observation and
applies each full theorem at arbitrary original carriers. Pop retains false
continuations; no range, safety, valid-frame or execution premises are added.

`stack_to_lab_native_probe.out` records the full original `flatten_def` and
45 complete native output observations, including actual `app_list` tree
association, all If and optional Call branches, all original fallback
constructors, width1/80 words, and exact FFI names. The native counterpart is
`StackToLab/Native.lean`; `StackToLabNativeParity` supplies 45 kernel fixtures,
including arbitrary exact MlString pass-through. HOL's locally overloaded
`++` remains left-associative, so the generic callback bridge's right-associated
tree is not a definition-exact substitute. Production routing remains tracked
on fleet bead `flapjack-52bq.1`.
ssa_rename_property_wrappers_probe.out replays original class-add, full core renaming and both property wrapper proofs, recording original polymorphic Move program type. SSARenamePropertyWrappers retains all original producer equalities, hypotheses and four conclusions on native producers. No executable change or cross-language equivalence claim.
### Real-sqrt rounding agreement source review

`real_sqrt_round_agreement_special_probeScript.sml` freshly records the original
`fp64_sqrt` infinity and negative-zero results for all three directed modes.
The six same-input kernel theorems live in `BinaryIeeeSqrtRoundAgreementParity`.
Two further original whole-flag equalities cover negative finite and quiet-NaN
inputs with arbitrary rounding mode, replayed by generic kernel theorems; the
NaN payload choice is never replaced by a numerical representative.
The existing seven exact-square RTE rows and two RTE special rows were freshly
regenerated unchanged during the review. The built original HOL checkout and
this checkout's read-only HOL submodule both use
`a390cbabd3a4521bab4ee20281e3e42933a8a3ae`.

The reused `RoundAgreement` theorem covers every mode and binary64 input;
lower rational-radicand nonnegativity is discharged internally in the full
float sqrt path. It proves a Lean cut-renderer/Mathlib-real-renderer equality,
without assuming or proving HOL-to-Lean equivalence. Directed finite results
are agreement theorem instances here, without a numeric oracle conversion for
Hilbert choice on the finite float carrier. The two non-square RTE hardware
checks remain supplemental comparisons, not original HOL oracle rows.
Faithful HOL carrier acceptance and complete StackSem instructions/evaluation
remain separate tracked work.

ssa_physical_state_updates_probe.out freshly replays the literal physical-target setVar and list-insert locals-relation proofs and records their independent source/target code/FFI types. SSALocalsPhysicalStateUpdates retains every original premise including list length, using native Spt locals. No executable change or cross-language equivalence claim.

ssa_option_lookup_subset_probe.out replays the full original subset-helper proof and three inferred native map/list types. SSAOptionLookupSubset retains the two original domain premises and complete mapped-name domain conclusion, with generic locals payload. Proof-only regression evidence, not cross-language equivalence.
### SSA merge unchanged lookups

`ssa_merge_move_lookups_probeScript.sml` replays the complete literal original local frame2 and frame3 proofs, specializes frame3 to empty maps, applies it under independently proved guards for an absent-list key and an outside-intersection key, captures both whole merge results, and checks the false guard for a changed common key. Lean `mergeMovesFrame3` retains the full original guard and both lookup equalities for arbitrary native trees.

### Loop-to-Word label threading and handler ownership

`loop_to_word_label_handlers_probeScript.sml` replays all four full literal source proofs: function-label preservation, next-label monotonicity, handler ownership for comp, and per-function ownership for compile_prog. Actual theorem applications use original compiler equalities supplied by EVAL; no extra guard or target evaluation assumption. Complete nested outputs at widths 1/64/80 show return labels, exception labels, both continuations and final counter; the tail case ignores its source handlers. A duplicate-owner compiled list and false-owner sentinel are retained. Matching generic-width kernel fixtures apply the public theorems and check the complete nested output.

`ssa_rename_move_preserve_weak_probe.out` freshly replays the full original move-renaming preservation proof plus its literal local prerequisites and five original inferred carriers; both states share all three type dimensions. No successful target evaluation or post-state relation is assumed.

`ssa_get_set_vars_probe.out` freshly replays the full original generalized prefix/list-insert read and set/read proofs, with nine original inferred state/list/tree types. Native SSAGetSetVars retains every original length, distinctness and disjointness premise and the real WordSem operations.
`stacksem_fp_conversion_types_probeScript.sml` captures seven original full
types for the StackSem FP sqrt/conversion case review: `inst`, FP lookup/update,
three machine-IEEE operations and the generic compile-oracle projection. The
state parameters and fixed word64 FP register carrier are retained; this is
source-shape evidence, not a HOL-to-Lean equivalence proof.
`ssa_rename_move_preserve_weak_probe.out` freshly replays the full original move-renaming preservation proof plus its literal local prerequisites and five original inferred carriers; both states share all three type dimensions. No successful target evaluation or post-state relation is assumed.

`ssa_get_set_vars_probe.out` freshly replays the full original generalized prefix/list-insert read and set/read proofs, with nine original inferred state/list/tree types. Native SSAGetSetVars retains every original length, distinctness and disjointness premise and the real WordSem operations.
### Native compiler flat-effect no-shared-memory cases

`word_to_stack_no_shmemop_flat_probeScript.sml` captures fifty-four original
source-guard/actual-target-predicate observations for twelve flat-effect cases
over widths1/32/64/80, both perf flags and zero/nonzero/large frames. Samples
include move cycles/repeated sources, malformed cutsets, bitmap-producing live
and constant paths, exact byte-backed FFI names and all Set expression branches.
`WordToStackNoShmemopFlatEffectsParity` replays the identical inputs through
actual compiler equations: fifty direct kernel predicate reductions and four
Move observations using accepted preservation for arbitrary scheduled lists.
The latter do not claim direct reduction of the scheduler. Twelve generic
public case applications keep the original guard and compilation equality.
These regressions do not establish cross-language equivalence or the complete
compiler theorem. Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_flat_probeScript.sml`.

### Native compiler recursive no-shared-memory cases

`word_to_stack_no_shmemop_recursive_probeScript.sml` evaluates forty-two
original source/actual-target predicate pairs for MustTerminate, Loop, Seq
and all If operand/validation branches. Widths1/32/64/80, both perf flags,
malformed cutsets and nested bitmap-producing branches are retained. False
source guards include genuinely forbidden output, invalid-address fallback
and an independently checked handler ignored by the tail-call compiler;
explicit false/false and false/true expectations prevent an equivalence claim.
`WordToStackNoShmemopRecursiveParity` kernel-reduces the identical compiler
equations and applies all four generic original-shaped cases with only their
legitimate source-subprogram induction hypotheses. The accepted full source
guard equations are reused. These regressions do not establish cross-language
equivalence or complete the compiler theorem. Selector:
`HOL_PROBE_ONLY=word_to_stack_no_shmemop_recursive_probeScript.sml`.

`ssa_locals_list_rename_probe.out` freshly replays the full original generic list-renaming locals relation, its three local theorem prerequisites and source physical-class tactic, with nine original inferred types confirming generic payload alpha and native tree/list carriers. All seven original premises are retained.

`ssa_setup_props_probe.out` freshly replays the complete original setup-SSA proof, six local prerequisite proofs and two ML tactics, plus four inferred types. State/program/move share their word dimension. The tagged native theorem retains the original allocation/domain premises and all six actual evaluator conclusions; executed setup routing is tracked separately.
`stackprops_state_constants_probeScript.sml` captures the complete thirteen
state-operation constant/commutation statements from stackProps20-168 and
their original free-variable types. It fetches exported HOL theorems; the
local/overwritten declarations at84/90/110/125 are explicitly re-proved with
their original statements and proofs. In particular, empty_env_const has
independently polymorphic x and z states. These are source-shape captures,
not a claim of HOL-to-Lean equivalence or exported status for local helpers.

`ssa_rename_move_preserve_weak_probe.out` freshly replays the full original move-renaming preservation proof plus its literal local prerequisites and five original inferred carriers; both states share all three type dimensions. No successful target evaluation or post-state relation is assumed.
### Loop-to-Word compiled names, membership, and first-match lookup

`loop_to_word_program_names_probeScript.sml` replays all four complete original proofs at lines 1850–1909. It captures entire duplicate-name and distinct-name compiled lists, true/false name-distinctness, the first duplicate lookup, and missing lookup. Generic-width Lean fixtures match these results and apply each public theorem. Lookup preserves the original first-match semantics without a distinct-name premise. Selector: `HOL_PROBE_ONLY=loop_to_word_program_names_probeScript.sml`.

### Executable canonical quiet-NaN arithmetic refinement

`Flapjack/Misc/BinaryIeeeArithExec.lean` supplies five computable word producers and unconditional equality-or-quiet-NaN refinements to the existing arithmetic renderings. The logical operations remain unchanged. `BinaryIeeeArithExecParity.lean` matches all 49 rows of the freshly regenerated `machine_ieee_fp64_arith_nan`, `machine_ieee_fp64_arith_special`, and `machine_ieee_fp64_arith_round` captures: non-choice outputs are bit-exact, while symbolic quiet-NaN choices are matched by canonical quiet NaNs without asserting payload equality. WordSem uses roundTiesToEven and ignores flags for these five clauses. Full instruction/evaluator routing remains open under h29l.10; these new executable producers are Flapjack infrastructure, not separately tagged HOL declarations.

`lab_validity_native_probe.out` freshly records three original native
conversion/validity definitions and sixteen original observations, including
actual eight-bit assembler configuration acceptance/rejection, empty and
mixed sections, and width1/80 memory-conversion boundaries with unbounded
natural registers. `LabValidityNativeParity` has sixteen kernel fixtures,
including generic payload/cache statements. The exact definitions live in
`LabToTarget/Native.lean` and `LabProps/Native.lean`; the generic callback
helpers are separate infrastructure. Native executable routing and full
encoding correctness remain tracked on the fleet dependency graph.

`stack_to_lab_nonrecursive_validity_probe.out` replays the complete literal
original local `flatten_line_ok_pre` proof, then evaluates source validity,
zero-byte-offset validity and the full output-line predicate for CodeBufferWrite
and shared Load inputs. `StackToLabNonrecursiveValidityParity` applies all
31 native nonrecursive cases at arbitrary carriers/parameters and includes
those two concrete theorem applications. Every case retains all original
premises and the full app-list output conclusion. Recursive Seq/If/Loop and
returned Call, the assembling theorem and executable route remain open.
`stacksem_fp_conversion_types_probeScript.sml` captures seven original full
types for the StackSem FP sqrt/conversion case review: `inst`, FP lookup/update,
three machine-IEEE operations and the generic compile-oracle projection. The
state parameters and fixed word64 FP register carrier are retained; this is
source-shape evidence, not a HOL-to-Lean equivalence proof.

`stackprops_clock_support_probeScript.sml` captures the six full original
clock-proof support declarations and free-variable types, including the
independent dec_clock_const states and four pair_map_eq carriers. The original
asm Const type confirms that the program parameter indexes HOL words. Ten
clock_neutral observations cover recursion and rejected Loop/Call/Tick cases
at word dimensions1/16/64; StackPropsClockSupportParity kernel-replays them.
These are source and regression captures, not evaluator equivalence.
`word_alloc_limit_props_probe.out` freshly re-elaborates the literal complete
local `limit_var_props` proof, then evaluates twelve complete native program
maximum/limit/allocation/strict-occurrence tuples. The tuples exactly match
`WordAllocLimitVarParity.lean`; `WordAllocLimitPropertiesParity.lean` imports
those kernel fixtures and applies the full public theorem with arbitrary
positive-width programs and the original limit equality premise. Cases retain
all residues, widths1/32/64/80, the original ignored Load16 registers, tail Call
handler exclusion, returning Call body traversal and unbounded Nat registers.
The qualified tag records only the standard HOL type-indexed word translation.

`word_to_stack_no_shmemop_handlers_probe.out` literally replays all three local
PushHandler/PopHandler/StackHandlerArgs no-shmemop proofs and captures their
generic operation types. Sixteen fresh predicate observations cover both perf
flags, independent unused frame carriers, safe and forbidden continuations,
widths1/32/64/80, direct/indirect generic destinations and large frame offsets.
`WordToStackNoShmemopHandlersParity.lean` kernel-replays every observation and
applies each full theorem at arbitrary original carriers. Pop retains false
continuations; no range, safety, valid-frame or execution premises are added.

### Full native tail Call no-shared-memory case

`word_to_stack_no_shmemop_tail_probeScript.sml` captures twenty-two original
source-guard/compiled-target pairs. Widths1/32/64/80, both perf flags,
direct/indirect destinations, empty arguments, large final registers and full
frames are retained. Safe and forbidden compiler-ignored handlers show why the
original source implication is retained instead of an equivalence.
`WordToStackNoShmemopTailCallParity` reduces the identical native compiler
inputs in the kernel and applies the complete generic original-shaped case.
The guarded nonempty LAST path needs no total-list default assumption.
These fixtures do not prove cross-language equivalence or full compiler correctness.
Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_tail_probeScript.sml`.

### Full returning Call without a handler

`word_to_stack_no_shmemop_returning_probeScript.sml` captures twenty-two
original source/compiled-target predicate pairs for returning Calls with no
handler. Widths1/32/64/80, both perf flags, direct/indirect destinations and
empty/single/multiple arguments and return values are retained. Nested Alloc
and Return bodies exercise actual bitmap threading; valid shared and invalid
address bodies retain false/false and false/true source/target sentinels.
`WordToStackNoShmemopReturningCallParity` kernel-reduces identical compiler
inputs and applies the full generic original-shaped theorem with its genuine
return-body induction hypothesis. These regressions do not establish
cross-language equivalence or full compiler correctness.
Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_returning_probeScript.sml`.

### Full returning Call with a handler

`word_to_stack_no_shmemop_handled_probeScript.sml` captures twenty-six
original source/compiled-target predicate pairs. The return body and handler
both produce bitmaps in the original compiler order. Widths1/32/64/80, both
perf flags, direct/indirect destinations and empty/single/multiple arguments
and return values are retained. Independently and jointly forbidden/invalid
children preserve false/false and false/true observations.
`WordToStackNoShmemopHandledCallParity` kernel-reduces identical inputs and
applies the full generic original case with only the genuine return and handler
induction hypotheses. The three Call cases complete the original constructor
group; other constructors and assembly remain separately tracked. These
regressions do not establish cross-language equivalence or whole compiler correctness.
Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_handled_probeScript.sml`.

`stackprops_state_constants_probeScript.sml` captures the complete thirteen
state-operation constant/commutation statements from stackProps20-168 and
their original free-variable types. It fetches exported HOL theorems; the
local/overwritten declarations at84/90/110/125 are explicitly re-proved with
their original statements and proofs. In particular, empty_env_const has
independently polymorphic x and z states. These are source-shape captures,
not a claim of HOL-to-Lean equivalence or exported status for local helpers.
### Primitive and rejected no-shared-memory compiler cases

`word_to_stack_no_shmemop_primitives_probeScript.sml` captures thirty-two
original source/actual-target predicate pairs for Skip, Assign, Store, Raise,
Break, Continue, Tick and ShareInst. Widths1/32/64/80, both perf flags and full
zero/nonzero/large frames remain explicit. Assign and Store retain the original
compiler's impossible-constructor Skip fallback. Valid and invalid shared Load
and Store keep false/false and false/true results instead of an equivalence.
`WordToStackNoShmemopPrimitivesParity` kernel-reduces identical compiler inputs
and applies all eight full original-shaped cases. The rejected ShareInst proof
uses only its original false source guard, with no target safety premise.
These regressions do not establish cross-language equivalence or full compiler correctness.
Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_primitives_probeScript.sml`.

`ssa_rename_move_preserve_probeScript.sml` replays the literal strong SSA move-preservation proof and local prerequisites, capturing its full statement and five inferred argument types.
`stacksem_fp_case_types_probeScript.sml` captures seven original full type
rows for the complete StackSem FP case, including all sixteen constructor
payloads. Together with freshly regenerated movement/sign, arithmetic and
conversion captures, these support the i81m source review. Generic machine,
compile and FFI carriers and fixed word64 FP registers are preserved.
Captures are regression evidence, not a HOL-to-Lean equivalence proof.
`word_to_stack_scheduler_route_probe.out` captures six fresh original rows:
empty/swap/duplicate-destination scheduling, the actual k=22 NONE slot23, and
full spill-cycle trees at frame3 and frame0. ProductionScheduler kernel-replays
all six numeric observations, plus identity and mixed-location cycles. Its
all-input proof establishes the actual option scheduler equals native parmove,
deriving fuel sufficiency from the source measure. The native wMove tree
fixtures retain both temporary registers and natural frame subtraction; they
do not establish actual move materialization or complete compiler equivalence.
Regenerate with `HOL_PROBE_ONLY=word_to_stack_scheduler_route_probeScript.sml`.
`ssa_locals_list_rename_probe.out` freshly replays the full original generic list-renaming locals relation, its three local theorem prerequisites and source physical-class tactic, with nine original inferred types confirming generic payload alpha and native tree/list carriers. All seven original premises are retained.

`ssa_setup_props_probe.out` freshly replays the complete original setup-SSA proof, six local prerequisite proofs and two ML tactics, plus four inferred types. State/program/move share their word dimension. The tagged native theorem retains the original allocation/domain premises and all six actual evaluator conclusions; executed setup routing is tracked separately.

### Full arbitrary-program comp no-shared-memory preservation

`word_to_stack_comp_no_shmemop_probeScript.sml` freshly captures the exported
original `comp_no_shmemop` theorem and all seven original input/output carrier
types. Twelve original predicate pairs cover deeply nested Loop, MustTerminate,
Seq, If and returning/handled Calls with actual bitmap-producing children over
widths1/32/64/80 and both perf and immediate-validation branches. Ignored tail
handlers retain false-source/true-target sentinels.
`WordToStackCompNoShmemopParity` kernel-reduces identical inputs and applies the
full arbitrary-program theorem, including its actual compiler projections.
The public statement has only the original source guard and compilation equality;
all26 constructor cases and their genuine child IH are discharged internally.
Structural size termination retains complete Call tuple equalities. The captured
exported theorem is not a new literal replay of its original proof. These
regressions do not prove HOL-to-Lean equivalence or whole compiler semantics.
Selector: `HOL_PROBE_ONLY=word_to_stack_comp_no_shmemop_probeScript.sml`.

### Generated machine IEEE FP64 source identities

`machine_ieee_fp64_declarations_probeScript.sml` fetches all 47 reviewed FP64
definitions from the original `machine_ieee` theory and captures their actual
conclusions. The script invokes `machine_ieeeLib.mk_fp_encoding` at
`HOL/src/floating-point/machine_ieeeScript.sml:13-16`; its FP64 tuple at line 16
is `("fp64", 52, 11, SOME "double")`, giving a 64-bit encoding.
The reference checker accepts these generated definition names only with
source line 16, and verifies both Script and Lib against the pinned HOL gitlink
and tracked blobs. Generated theorem names and other formats are outside this
reviewed expansion. These source identities do not approve a Lean statement,
real rendering, carrier translation, or choice behavior; review each port
before tagging it. Regenerate with
`HOL_PROBE_ONLY=machine_ieee_fp64_declarations_probeScript.sml`.

`ssa_fake_moves_correct_left_probeScript.sml` replays the literal left fake-move simulation and local frame/map prerequisites, capturing the full statement and seven types including independent source/target code and FFI dimensions.

`ssa_fake_moves_correct_right_probeScript.sml` replays the literal right fake-move simulation and its local prerequisites, capturing the full five-conclusion statement and seven inferred types.

`ssa_fix_inconsistencies_correct_left_probeScript.sml` replays the literal left reconciliation assembly and its original merge/fake prerequisites; captures the full statement and six types, including identical source/target word/code/FFI dimensions.

`ssa_fix_inconsistencies_correct_right_probeScript.sml` replays the literal right reconciliation assembly and original map-agreement prerequisites, capturing the full returned-left-map result and six inferred types.

- `ssa_cc_trans_exp_correct_probeScript.sml` replays the literal local SSA expression correctness proof (word_allocProof6256–6294) and captures the full theorem plus all six inferred argument carriers.

- `ssa_fix_inconsistencies_props_probeScript.sml` replays literal reconciliation allocation/map bounds with its three original local prerequisites and captures the full theorem and eight argument carriers.
### WordSem partial Word extractors

The final four rows of `word_sem_accessors_probe.out` freshly evaluate the
specified `theWord (Word w) = w` and `get_word (Word w) = w` clauses at
widths 1/64 and 32/80 respectively. No Loc result is evaluated or assigned an
oracle value. The Lean ports retain independent opaque completions indexed by
width and both Loc fields; their Word equations and Word-guarded agreement
are kernel checked in `WordSem.Accessors` and `WordSemAccessorsParity`.
These regressions do not establish a concrete meaning for unspecified Locs.
### Full native program-list no-shared-memory preservation

`word_to_stack_no_shmemop_programs_probeScript.sml` freshly captures the
original exported `compile_word_to_stack_no_share_inst` theorem, all eight
input/output carrier types, and sixteen actual source/compiled-target
predicate pairs. Widths 1/32/64/80 and both performance flags cover empty and
multiple-row lists, duplicate Boolean identifiers, nonzero bitmap state,
bitmap-changing Alloc/StoreConsts, frame arithmetic boundaries, rejected
shared operations, and an ignored tail-call handler. The latter retains a
false source predicate and true target predicate, consistent with implication.
`Flapjack/Test/WordToStackNoShmemopProgramsParity.lean` checks the pairs in the
kernel and applies the full generic-identifier theorem and actual compiler
projections. Captures are regression evidence, not a new proof replay or a
HOL-to-Lean equivalence proof. Whole compiler semantic correctness remains open.

Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_programs_probeScript.sml`.

### Full native top-level no-shared-memory preservation

`word_to_stack_no_shmemop_top_probeScript.sml` captures original exported
`compile_no_shmemop`, its six carriers and sixteen source/actual-target pairs.
Performance is false as in HOL. Both injected stubs, widths1/32/64/80,
zero/underflow/large register counts, duplicate avoid registers/identifiers,
empty/multiple rows, bitmap changes and rejected shared/ignored-handler cases
are covered. `Flapjack/Test/WordToStackNoShmemopTopParity.lean` checks those
pairs and two full-signature applications retaining all four outputs.
Captures are regression evidence, not a new original proof replay or a
HOL-to-Lean equivalence proof. Compiler semantic preservation remains open.

Selector: `HOL_PROBE_ONLY=word_to_stack_no_shmemop_top_probeScript.sml`.

- `ssa_cc_trans_exp_correct_probeScript.sml` replays the literal local SSA expression correctness proof (word_allocProof6256–6294) and captures the full theorem plus all six inferred argument carriers.

- `ssa_fix_inconsistencies_props_probeScript.sml` replays literal reconciliation allocation/map bounds with its three original local prerequisites and captures the full theorem and eight argument carriers.
`stackprops_expression_clock_probeScript.sml` captures six full source/type
rows for `mem_load_with_const`, `word_exp_with_const` and `assign_with_const`,
then22 clocked original expression/assignment/store observations. The first
theorem's original name is misleading: its statement concerns `mem_store`.
The new kernel replay covers domain failure, Loc rejection, missing operands,
operator lists, wraparound, shift bounds and successful/failed assignment.
The full recursive theorem imposes no success, size or clock bound. These
captures provide regression evidence, not HOL-to-Lean equivalence.
`ssa_fake_moves_correct_right_probeScript.sml` replays the literal right fake-move simulation and its local prerequisites, capturing the full five-conclusion statement and seven inferred types.

`ssa_fix_inconsistencies_correct_left_probeScript.sml` replays the literal left reconciliation assembly and its original merge/fake prerequisites; captures the full statement and six types, including identical source/target word/code/FFI dimensions.

`ssa_fix_inconsistencies_correct_right_probeScript.sml` replays the literal right reconciliation assembly and original map-agreement prerequisites, capturing the full returned-left-map result and six inferred types.

`stackprops_instruction_constants_probeScript.sml` captures four complete
original instruction support statements and their full types, plus ten native
observations of success, failure, clock updates and FFI updates. The two local
clock-neutral lemmas replay the original source statement and proof verbatim.
The FFI theorem preserves HOL's independent updated host type. The published
`set_var_with_const` FFI conjunct is likewise repaired to retain that independent
host; its original 26-row state-constants capture was freshly regenerated and
remains unchanged. These probes do not establish cross-language equivalence or
remove the inherited external real-carrier assumption.
### Full native compiler no-install preservation

`word_to_stack_comp_no_install_probeScript.sml` freshly captures original
exported `comp_no_install`, seven input/output types and 39 actual predicate
pairs: all26 source constructors, 12 deep nested/conditional/call cases over
widths1/32/64/80, and a false-source/true-target ignored Install handler.
The source false-performance premise is retained. Shared operations are
allowed by no-install; rejected Install and ignored-handler cases preserve
implication direction. `Flapjack/Test/WordToStackCompNoInstallParity.lean`
checks the observations and two complete arbitrary-program applications.
Captures are regression evidence, not a new original proof replay or a
HOL-to-Lean equivalence proof. Whole compiler semantic correctness is open.

Selector: `HOL_PROBE_ONLY=word_to_stack_comp_no_install_probeScript.sml`.

- `ssa_cc_trans_inst_props_probeScript.sml` replays literal instruction allocation/map properties with original local map-extension and allocation-add proofs, capturing the full theorem and six argument carriers.
### Full native program-list no-install preservation

`word_to_stack_no_install_programs_probeScript.sml` freshly captures exported
original `compile_word_to_stack_no_install`, all eight carriers and sixteen
actual source/target pairs over widths1/32/64/80. Observations retain false
performance, generic Boolean identifiers with duplicates, empty/multiple rows,
bitmap-changing Alloc/StoreConsts and arbitrary frame boundaries. Shared
operations are allowed, and the ignored Install handler remains false source
and true target. `Flapjack/Test/WordToStackNoInstallProgramsParity.lean` checks
all pairs and two full generic-identifier applications with the original
performance equality. Regression evidence is not a new original proof replay
or a HOL-to-Lean equivalence proof. Code-map and compiler semantic correctness
remain open.

Selector: `HOL_PROBE_ONLY=word_to_stack_no_install_programs_probeScript.sml`.

`lab_to_target_encoding_probeScript.sml` reads the original `lab_to_target` assembly encoding definitions (`ffi_offset`, `lab_inst`, `cbw_to_asm`, `enc_line`, `enc_sec`, `enc_sec_list`). Because `enc_line` takes the instruction encoder as a parameter, the probe supplies a concrete encoder at dimension 8 (`Inst Skip` to `[1w]`, every other asm to `[2w;3w]`), so the stored `LENGTH bs` fields and the `skip_len` of `enc_sec_list` are observable. Its 17 rows are kernel-replayed in `Flapjack.Test.LabToTargetEncodingParity`; it does not claim the label-computation or program-transform halves.

`lab_to_target_labels_probeScript.sml` reads the original `lab_to_target` label-computation definitions (`section_labels`, `compute_labels_alt`). Its 13 rows EVAL the source definitions on concrete 8-bit labLang lines/sections: an empty line list and two nonzero accumulators, a six-line section where the zero label is ignored and labels 1 and 2 land at offsets 13 and 17, the empty-label-map case, the two-level `num_map` that `compute_labels_alt` builds over two sections (section 1 seeded at 10 with label 1 at 13; section 2 seeded at 13 with label 2 at 20), absent-section `lookup`, and the nested per-section start/label lookups. The rows are kernel-replayed in `Flapjack.Test.LabToTargetLabelsParity`. Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_labels_probeScript.sml scripts/hol-probes/regenerate.sh`.

`lab_to_target_positions_probeScript.sml` reads the original `lab_to_target` position, label, FFI-index and jump-offset definitions (`find_pos`, `get_label`, `get_ffi_index`, `get_jump_offset`). Its 15 rows EVAL the source definitions on a two-level section map (section 7 to `{0 -> 10, 3 -> 13}`), an `ffiname list` (`[ExtCall a; ExtCall b]`) and `pos = 10` at 64-bit: `find_pos` hit/hit-at-zero/missing-label/missing-section, all five `get_label` clauses (four labels plus the `Lab 0 0` default), `get_ffi_index` hit (`1`) and default (`0`), and the four `get_jump_offset` clauses (`CallFFI b` = `0xFFFFFFFFFFFFFFB6`, `Install` = `0xFFFFFFFFFFFFFFD6`, `Halt` = `0xFFFFFFFFFFFFFFE6`, `Jump (Lab 7 3)` = `3`). The rows are kernel-replayed in `Flapjack.Test.LabToTargetPositionsParity` (bead `flapjack-pxn.18.5.15.10.11`). HOL's result word dimension is independent of the instruction's `reg_imm` word dimension, so the Lean port carries separate positive-width binders. Regenerate with `HOL4=/home/zksecurity/HOL CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_positions_probeScript.sml scripts/hol-probes/regenerate.sh`.

`lab_to_target_secondpass_probeScript.sml` reads the original `lab_to_target` second-pass definitions (`enc_lines_again`, `enc_secs_again`, `lines_upd_lab_len`, `upd_lab_len`). Its 11 rows EVAL the source definitions on concrete 64-bit `labLang$line`/`labLang$sec` values with the same section map (section 7 to `{0 -> 10, 3 -> 13}`) and a concrete encoder returning `[1w;2w;3w]` for every asm: the empty line list; a keep-only list exercising the `Label`/`Asm`/`LabAsm` clauses; a stale `LabAsm` word at `l = 1` (`l1 = 3 > 1`, flag `F`) and at `l = 7` (`l1 = max 3 7 = 7`, flag `T`); the empty section list and a two-section program whose first section re-encodes and second keeps; `lines_upd_lab_len` empty, at even `pos` (label length `0`) and at odd `pos` (label length `1`); and `upd_lab_len` empty and over two sections. The rows are kernel-replayed in `Flapjack.Test.LabToTargetSecondPassParity` (bead `flapjack-pxn.18.5.15.10.13`). Regenerate with `HOL4=/home/zksecurity/HOL CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_secondpass_probeScript.sml scripts/hol-probes/regenerate.sh`.

`lab_to_target_padding_probeScript.sml` reads the original `lab_to_target` label-checking, padding and symbol-collection definitions (`line_ok_light`, `sec_ok_light`, `pad_bytes`, `add_nop`, `pad_section`, `pad_code`, `sec_length`, `get_symbols`). Its 28 rows EVAL the source definitions on concrete 64-bit `labLang$line`/`labLang$sec` values with an 8/64-matching assembler configuration (`code_alignment = 2`, jump/cjump/loc offset bounds `(0, 100)`, `avoid_regs = [3]`, `reg_count = 8`), so a jump target `8` is in range and two-aligned (`T`), `3` is unaligned (`F`), `101` is out of range (`F`), and `Call` is rejected (`F`): `pad_bytes` when `len` fits, appends one repeating byte and appends a two-byte nop chunk; `add_nop` empty, `Label`-then-`Asm` (the `Asm` clause stops recursion), `Asm` head and `LabAsm` head; `pad_section` empty and a `Label`/`Asm`/`Label` list (the second label triggers `add_nop`); `pad_code` empty and two sections; `sec_length` empty (`5`) and a concrete line list (`21`); `get_symbols` empty and two sections (`[(1,10,11); (2,21,3)]`); all ten `line_ok_light` shapes; and two `sec_ok_light` sections. The rows are kernel-replayed in `Flapjack.Test.LabToTargetPaddingParity` (bead `flapjack-pxn.18.5.15.10.14`). Regenerate with `HOL4=/home/zksecurity/HOL CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_padding_probeScript.sml scripts/hol-probes/regenerate.sh`.

`lab_to_target_removelabels_probeScript.sml` reads the original `lab_to_target` zero-label accumulation and label-removal definitions (`zero_labs_acc_of`, `line_get_zero_labs_acc`, `sec_get_zero_labs_acc`, `get_zero_labs_acc`, `zero_labs_acc_exist`, `remove_labels_loop`, `remove_labels`, `line_bytes`, `prog_to_bytes`). Its 22 rows EVAL the source definitions on concrete 64-bit `labLang$line`/`labLang$sec` values; the accumulator observations print `toAList` of the resulting `num_set`: `zero_labs_acc_of` for a `LocValue`/`Jump`/`JumpCmp` with second part `0` (`[(n,())]`), with a non-zero second part (`[]`) and the `Halt` catch-all (`[]`); `line_get_zero_labs_acc` on a `LabAsm`, a `Label` and an `Asm`; `get_zero_labs_acc` empty (`[]`) and over a one-section code with zero labels `{1,3}` whose `toAList` is `[(3,()); (1,())]`; `zero_labs_acc_exist` on a lab map containing both zero labels (`T`) and one missing `3` (`F`); `line_bytes` on a `Label` (`[]`), `Asm` (`[1w;2w]`) and `LabAsm` (`[]`); `prog_to_bytes` empty and over a three-section code where the empty middle section is skipped (`[1w;2w;3w]`); and `remove_labels_loop` at clock `0`/`1` plus `remove_labels` at clock `0` on a one-section program with the 8/64 assembler configuration (encoder discards its argument), each returning `SOME` with the length-adjusted section and recomputed label map. All rows are EVAL-reducible, so none is omitted. The rows are kernel-replayed in `Flapjack.Test.LabToTargetRemoveLabelsParity` (bead `flapjack-pxn.18.5.15.10.16`). Regenerate with `HOL4=/home/zksecurity/HOL CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_removelabels_probeScript.sml scripts/hol-probes/regenerate.sh`.

`misc_lookup_any_find_index_probeScript.sml` records direct original-HOL `EVAL`
rows for the two misc prerequisites of the lab_to_target position lookups:
`misc$lookup_any` (`cakeml/misc/miscScript.sml:344-350`, an `spt` lookup
returning a default on a missing key) and `misc$find_index`
(`cakeml/misc/miscScript.sml:1055-1058`, a first-match list search from a
starting offset). The four `lookup_any` rows cover a hit, a hit at key 0, a
miss returning the default, and the empty map; the four `find_index` rows cover
a hit at offset 0, a hit at an offset greater than 0, a miss returning `NONE`,
and an earlier duplicate that must win. The kernel replay is
`Flapjack.Test.MiscLookupAnyFindIndexParity`, registered in the lake test root
`Flapjack/Test/CompilerParity.lean`. The Lean ports are `lookupAny` in
`Flapjack/Misc/Sptree.lean` and `findIndex` in `Flapjack/Misc/FindIndex.lean`;
HOL `=` is rendered by Lean's standard `DecidableEq` for the generic element
type (bead `flapjack-pxn.18.5.15.10.10`). Regenerate with
`HOL4=/home/zksecurity/HOL CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=misc_lookup_any_find_index_probeScript.sml
scripts/hol-probes/regenerate.sh`. These finite observations are regression
evidence, not a cross-prover equivalence proof.

- `ssa_rename_shifted_properties_probeScript.sml` replays the original raw-list derived pipeline and shifted move wrapper with nine original prerequisites; full statements and twelve type rows distinguish their input map-bound counters and conjunction orders.

`lab_to_target_maplemmas_probeScript.sml` reads the two original `lab_to_target` MAP lemmas directly: `pad_code_MAP` (`pad_code nop = MAP (\x. Section (Section_num x) (pad_section nop (Section_lines x) []))`, line 226) and `prog_to_bytes_MAP` (`!ls. prog_to_bytes ls = FLAT (MAP (FLAT o MAP line_bytes o Section_lines) ls)`, line 341). Its 8 rows EVAL both sides of each theorem on concrete 64-bit `labLang$sec` values: `pad_code_MAP` empty and over a two-section list (`[Section 1 [Label 1 2 0; Asm (Asmi (Inst Skip)) [1w;2w;9w] 3]; Section 2 []]`), printing the equality (`T`) plus the observed left/right-hand section lists; and `prog_to_bytes_MAP` empty and over the three-section `bytesCode` list from the sibling label-removal probe (the empty middle section is skipped, giving `[1w;2w;3w]`), printing the equality (`T`) plus the observed left/right-hand byte lists. The rows are kernel-replayed in `Flapjack.Test.LabToTargetMapLemmasParity` (bead `flapjack-pxn.18.5.15.10.29`). Regenerate with `HOL4=/home/zksecurity/HOL CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_maplemmas_probeScript.sml scripts/hol-probes/regenerate.sh`.
- `ssa_cc_trans_props_move_probeScript.sml` replays the original marked Move case of program allocation/map properties after its original native compiler unfolding, with four original local prerequisites, full case statement and eight carrier captures.

`asmprops_arithmetic_preservation_probeScript.sml` captures the three full
original PC/binop/arithmetic preservation statements and their inferred types,
plus nine native observations. The arithmetic rows include failures from shift
bounds and zero divisors while memory, domain, alignment, link register and
endianness remain preserved. The Lean fixture derives arbitrary-operation
domain preservation from the full theorem and checks the other observed fields.
### WordProps code-map no-install convention

`word_props_no_install_code_probeScript.sml` freshly captures full original
`no_install_code_def`, three carrier queries and sixteen concrete lookup and
source-predicate observations over widths1/80 and all Spt constructors.
Malformed trees, missing keys and actual forbidden Install entries remain in
scope. `Flapjack/Test/WordPropsNoInstallCodeParity.lean` checks the observations
and arbitrary-width empty/safe-malformed/forbidden-map convention properties.
Captures are regressions, not a HOL-to-Lean equivalence proof or new original
proof replay. The predicate does not narrow the source code-map carrier.

Selector: `HOL_PROBE_ONLY=word_props_no_install_code_probeScript.sml`.

### Full native code-map top no-install theorem

`word_to_stack_no_install_top_probeScript.sml` freshly captures full original
`word_to_stack_compile_no_install`, six carriers, sixteen actual
ALL_DISTINCT/source-list/target-list observations and three complete HOL
finite-code guard proofs using original lookup/fromAList definitions.
The safe-first/bad-later duplicate-key map has a true complete code guard but
false source/target list predicates. The theorem therefore retains the
original distinct-key hypothesis. Widths1/32/64/80, underflow/large register
counts and both injected stubs are covered. Matching kernel fixtures retain
complete map guard proofs and full-signature applications. These are
regression observations and small concrete HOL guard proofs, not a new proof
replay of the full compiler theorem or a HOL-to-Lean equivalence proof.
Whole compiler semantic correctness remains unfinished.

Selector: `HOL_PROBE_ONLY=word_to_stack_no_install_top_probeScript.sml`.

- `ssa_cc_trans_props_allocation_probeScript.sml` replays the literal original Alloc/Install/FFI case tactics and native compiler unfolding with original shifted-list derivation and local prerequisites; three full cases and 31 type captures check the counter/map/cutset/loop-table/program and exact mlstring carriers.

- `ssa_cc_trans_props_loop_control_probeScript.sml` specializes the original functional induction rule to the full native program invariant and replays literal Resume Loop/Break/Continue tactics. Three full clauses and29 carrier captures retain Loop setup binders/guards and its actual-context body IH.
`lab_to_target_padding_length_probeScript.sml` exports original `LENGTH_pad_bytes` (lab_to_targetProofScript.sml:3195) and six direct `pad_bytes` EVAL observations over natural-number and Boolean lists: extension, multi-element nop truncation, exact fit, zero length, Boolean payloads, and the empty-nop sentinel outside the theorem premise. The full original premise remains nonempty nop and bytes length at most the requested length. `Flapjack.Test.LabToTargetPaddingLengthParity` kernel-replays all six concrete rows and exercises the public arbitrary-carrier theorem. Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_padding_length_probeScript.sml bash scripts/hol-probes/regenerate.sh`.

### SSA Call allocation/map invariant

`ssa_cc_trans_props_calls_probe.out` specializes the original functional induction at tail/returning Call, replays the literal original marked Calls proof, and captures the complete statements and all actual outer/guarded-handler variable types. Both exact guarded handler IHs are retained in the Lean returning-Call case; input/final map bounds are derived.
`lab_to_target_padding_similarity_probeScript.sml` captures the complete
original add-nop, section-padding and code-padding similarity statements and
full quantified types. Its local add-nop theorem replays the original statement
and proof literally. Six direct padding observations include empty nop chunks,
label-only code, nonempty accumulators and unchanged resolved offsets. Kernel
fixtures replay them and apply the full theorem at arbitrary positive width and
arbitrary accumulator; no full compiler or cross-language equivalence is claimed.

`lab_to_target_encoding_similarity_probeScript.sml` captures four complete
original similarity statements and their inferred types; both local lemmas
replay literal source statements and proofs. Six native observations exercise
initial encoding, unchanged and changed offsets, length growth/failure flags,
nonempty accumulators and multiple sections. The full line theorem retains
HOL's complete result tail `(position, flag)` and arbitrary prefix premise.
Kernel fixtures replay the observations and apply the full section theorem.
### SSA Call allocation/map invariant

`ssa_cc_trans_props_calls_probe.out` specializes the original functional induction at tail/returning Call, replays the literal original marked Calls proof, and captures the complete statements and all actual outer/guarded-handler variable types. Both exact guarded handler IHs are retained in the Lean returning-Call case; input/final map bounds are derived.
### Generic force_rename repair

`ssa_force_rename_generic_probe.out` replays the literal three complete lookup/domain proofs at word_allocProofScript.sml:6347–6381 and captures the original arbitrary-payload definition type. The Lean Bool/Unit fixtures exercise the generalized definition and theorem instances; SSA bounds retain their Nat specialization.

`byte_word_to_bytes_aux_probeScript.sml` directly EVALs pinned original HOL `byteTheory`: 14 concrete observations for arbitrary-count `word_to_bytes_aux`, whole `word_to_bytes`, `byte_index` and `get_byte`. Original `EVAL` residuals at zero modulus are discharged by the pinned `arithmeticTheory.MOD_0` rewrite followed by `EVAL`. It checks little/big endian cyclic extraction beyond 16/32/8-bit word byte counts, zero count, and positive sub-byte width1 with natural MOD0 and modular `n2w` index wrap. `Flapjack.Test.ByteWordToBytesAuxParity` replays all rows in the kernel. This is the exact mapped-write prerequisite of `targetSem.evaluate_def`, whose count is not bounded by the word byte length. Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=byte_word_to_bytes_aux_probeScript.sml bash scripts/hol-probes/regenerate.sh`.

`lab_to_target_section_length_probeScript.sml` evaluates original `section_labels` and `sec_length` for `section_labels_sec_length` (lab_to_targetProofScript.sml:3205). Eight original/kernel rows include empty and mixed native lines, zero and nonzero label numbers/lengths, duplicate labels, arbitrary starting positions and preexisting accumulators. Full pair observations pin the label ordering alongside the position equation. Lean counterpart is `LabToTarget.SectionLength`, and `Flapjack.Test.LabToTargetSectionLengthParity` replays the rows. Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_section_length_probeScript.sml bash scripts/hol-probes/regenerate.sh`.

`lab_to_target_line_len_probeScript.sml` captures five original `line_len_def` observations (lab_to_targetProofScript.sml:3127). They cover all three native constructors, empty bytes with a nonzero annotation, nonempty bytes with a zero annotation, and word widths8/64. The value is always the recorded length, with no byte-length consistency check. `Flapjack.Test.LabToTargetLineLenParity` kernel-replays the rows. Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml HOL_PROBE_ONLY=lab_to_target_line_len_probeScript.sml bash scripts/hol-probes/regenerate.sh`.

The section-length probe additionally captures five `sec_length_add` (lab_to_targetProofScript.sml:3135) observations: arbitrary nonzero additive offsets, empty/mixed lists, zero annotations and empty encoded bytes with a large recorded annotation. All original eight section-label rows remain mandatory. The same Lean parity module kernel-replays all thirteen observations.

`lab_to_target_padding_similarity_probeScript.sml` captures the complete
original add-nop, section-padding and code-padding similarity statements and
full quantified types. Its local add-nop theorem replays the original statement
and proof literally. Six direct padding observations include empty nop chunks,
label-only code, nonempty accumulators and unchanged resolved offsets. Kernel
fixtures replay them and apply the full theorem at arbitrary positive width and
arbitrary accumulator; no full compiler or cross-language equivalence is claimed.

### SSA primitive program invariants
`binary_ieee_real_carrier_source_probeScript.sml` captures all 14 original
real-rounding/sqrt and fixed64 codec definitions, with their full quantified
types (28 rows), for the source review of `BinaryIeeeSqrt.RealCarrier`.
The seven original exact-square observations remain in
`machine_ieee_fp64_sqrt_exact_probe.out`; these source/type captures and examples
provide review/regression evidence, not cross-assistant equivalence.
### SSA Call allocation/map invariant

`ssa_cc_trans_props_primitives_probe.out` captures the original 15 nonrecursive primitive invariant statements and actual constructor types. It replays the literal StoreConsts, instruction, expression tactic, CBW/DBW and ShareInst proofs after the original compiler simplification, including original instruction/extension/allocation prerequisites. The Lean cases derive all three invariants from only the original compiler equality and map/allocation premise.
`ssa_cc_trans_props_calls_probe.out` specializes the original functional induction at tail/returning Call, replays the literal original marked Calls proof, and captures the complete statements and all actual outer/guarded-handler variable types. Both exact guarded handler IHs are retained in the Lean returning-Call case; input/final map bounds are derived.

### SSA recursive control invariants

`ssa_cc_trans_props_control_probe.out` specializes original native functional-induction Seq/MustTerminate/If clauses7/8/9, replays their literal original proof tactics, and captures the complete guarded IH statements and actual context types. The Lean cases retain original scoped guards/order and derive handler-input/final reconciliation bounds.
## Native Word CSE instruction keys

`word_cse_instruction_keys_probeScript.sml` regenerates all ten original
definitions and function types plus 93 evaluations from `word_cseTheory`.
The cases cover every shift, binop, memory operation, arithmetic and FP
constructor, widths 1/32/64/80, unsigned all-ones words, and the instruction
catch-all. `Flapjack/Test/WordCseInstructionKeysParity.lean` kernel-replays
the values. FPFma retains all three registers; the other destination omissions
follow the original. These fixtures are regression evidence, not a CSE
simulation proof. Production carrier replacement and knowledge maps remain
tracked on `flapjack-word-cse-defs`.

## Native Word CSE register and key prerequisites

`word_cse_register_keys_probeScript.sml` exports the six original register
classifier definitions and their inferred types, plus all four unrestricted
encoding injectivity theorems. It replays the complete original proofs with no
remaining hypotheses, and evaluates 104 original observations. The cases cover
all arithmetic and FP constructors, immediate/register splits, carry versus
overflow flags, all memory-operation store classifiers, and widths 8/80.
`Flapjack/Test/WordCseRegisterKeysParity.lean` kernel-replays the observations
and applies the four full injectivity theorems at arbitrary inputs. Regression
fixtures do not prove HOL-to-Lean equivalence or the remaining CSE simulation.

## Word CSE insertion equality

`word_cse_insert_equality_probeScript.sml` exports the complete original
`insert_eq` and literally replays its proof with no open hypotheses. Ten
observations cover equal/unequal writes on empty, leaf, malformed BN/BS and
nested sparse trees. `WordCseInsertEqualityParity.lean` kernel-checks those
cases and applies the unrestricted theorem at arbitrary carriers/trees and an
80-bit carrier with a large Nat key. The original unused `n2` is omitted in
Lean only because it occurs in no premise or conclusion.

## Full Word CSE arithmetic-key simulation

`word_cse_arithmetic_keys_probeScript.sml` captures the entire original
`arith_keys_eq` and literally replays its proof with no open hypotheses. Three
original carrier types and 60 full theorem applications cover all five binops
with both register/immediate operands, all four immediate shifts and signed
division at widths 1/32/64/80. Each application proves the original key/eligibility
premises and retains the full universally quantified faithful evaluation
implication, plus both read/eligibility conclusions.
`WordCseArithmeticKeysParity.lean` applies the complete kernel theorem to all
60 cases and at arbitrary width/state/value. The theorem uses the actual
clocked WordSem evaluator, its reviewed finite-support state and its inherited
IEEE rational-cut assumption (SOUNDNESS item 8). This is a CSE simulation
prerequisite, not the entire CSE invariant/pass or compiler theorem.

### SSA recursive control invariants

`ssa_cc_trans_props_control_probe.out` specializes original native functional-induction Seq/MustTerminate/If clauses7/8/9, replays their literal original proof tactics, and captures the complete guarded IH statements and actual context types. The Lean cases retain original scoped guards/order and derive handler-input/final reconciliation bounds.
### Complete SSA program invariant

`ssa_cc_trans_props_probe.out` kernel-replays all 27 original constructor case proofs and applies the original native functional-induction theorem to their conjunction. It captures the complete all-program theorem and original variable types (the induction theorem names the first four variables v/v1/v2/v3). The Lean assembly uses the faithful native nested datatype induction, discharging every scoped case IH; no IH or stronger assumption remains in its final statement.
### Full target machine evaluator

`target_sem_evaluate_probeScript.sml` evaluates the original `targetSem`
`evaluate_def` over 8-bit configurations, arbitrary untouched target fields,
and natural-number machine/FFI host states. Twenty rows check clock exhaustion,
branch priority, both halt outcomes, cache/FFI oracle shifts, normal success and
post-interference rollback, missing/conflicting MMIO, mapped full/narrow reads
and writes, returned host/event state, terminal-event rollback and guard errors.
The normal-step rows first prove the exact encoded-memory existential with an
`Inst Skip`/zero-drop witness, then use its normalized kernel theorem after
bounded `EVAL`; they do not simplify with the recursive evaluator as an unbounded
rewrite. Every captured row has a kernel example in
`Flapjack.Test.TargetSemEvaluateParity`. These are regression checks, not a
cross-assistant equivalence proof. The compiler executable is not rerouted.
## Full Word CSE load evaluation transports

`word_cse_load_evaluation_probeScript.sml` literally replays all three original
proofs at word_cseProofScript221-270, including the local address-substitution
theorem, and captures their complete conclusions with no open hypotheses. Four
original inferred types and 80 complete theorem applications cover word/byte/16/32
loads at widths 1/32/64/80, both target/address aliasing and write/destination
aliasing. Store cases are excluded only by the original guard; Load16 remains
quantified with the same impossible source-success premise.
`WordCseLoadEvaluationParity.lean` applies the full kernel theorems in all 80
cases on arbitrary host/state/value inputs. The proofs use actual clocked WordSem
evaluation and internally derive the loaded value from insertion equality;
no target evaluation or memory-domain premise is added. Native finite-map/word
translations and the evaluator's inherited IEEE rational-cut assumption
(SOUNDNESS item 8) are retained. These are invariant-update prerequisites,
not a completed CSE/compiler correctness proof.

`target_sem_machine_sem_probeScript.sml` kernel-proves the full original
Terminate/Diverge/Fail clauses for arbitrary machine and FFI carriers, checking
exact conclusions and empty theorem hypotheses before capture. Divergence uses
all clocks and the original IMAGE/UNIV lazy-list least upper bound. Generic Lean
clause checks live in `Flapjack.Test.TargetSemMachineSemParity`; these check
local definition shape and are not a cross-language equivalence theorem.
### Complete SSA program invariant

`ssa_cc_trans_props_probe.out` kernel-replays all 27 original constructor case proofs and applies the original native functional-induction theorem to their conjunction. It captures the complete all-program theorem and original variable types (the induction theorem names the first four variables v/v1/v2/v3). The Lean assembly uses the faithful native nested datatype induction, discharging every scoped case IH; no IH or stronger assumption remains in its final statement.
### SSA recursive control invariants

`ssa_cc_trans_props_control_probe.out` specializes original native functional-induction Seq/MustTerminate/If clauses7/8/9, replays their literal original proof tactics, and captures the complete guarded IH statements and actual context types. The Lean cases retain original scoped guards/order and derive handler-input/final reconciliation bounds.

### SSA reconciliation list prerequisites

`ssa_reconcile_list_props_probe.out` replays the full original move-list rewrite and filtered-name distinctness proofs6485/6500 used by evaluate_ssa_reconcile6609/6612. It captures arbitrary payload/function/map types; the Lean rewrite retains imported exact THE and the HOL inhabited-type convention, with no new lookup-success premise or invented NONE value.
