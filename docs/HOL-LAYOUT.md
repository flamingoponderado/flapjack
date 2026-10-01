# HOL source layout

The primary Pancake modules now use the paths and names of the corresponding
scripts under `cakeml/pancake`. This is a location guide, not a claim that
every definition or theorem in a script has been ported. Declaration-level
provenance is recorded by `@[hol ...]` and checked by
`scripts/check-hol-refs.py --mapping`. The declaration inventory is in
[`HOL-THEOREM-MAP.json`](HOL-THEOREM-MAP.json); CI checks that every tagged
declaration and every theorem or lemma under `Flapjack/Pancake/Proofs` has an
entry, its HOL tag matches the entry, and reviewer and statement-status fields
are present. `pending_statement_review` and
`no_hol_reference_pending_classification` entries are open review work, not
claims of HOL correspondence. `documented_mismatch` records a known source
candidate whose Lean analogue remains untagged because its statement differs;
the mismatch must be explained beside the Lean declaration. The inventory
uses `reviewed_list_as_array` when the HOL list fields are represented by Lean
arrays. For each qualified field, the reference checker requires a same-module
structure field and a `holListArrayWitness_<field>` theorem relating that field
to its HOL list with `RepresentsHOLNodeList`, without assuming that relation in
the witness premises. This checks witness shape and Lean kernel acceptance; it
does not establish cross-language equivalence by itself. Ordinary exact tags retain
`reviewed_exact`. The inventory
recognizes `theorem` and `lemma` declarations only; `#check` commands and
comments do not count as theorem entries or tests. Correctness claims are described in
[`SOUNDNESS.md`](SOUNDNESS.md).

The qualifier covers only the named representation fields; evaluator,
state-transition, error, hypothesis, and conclusion details must still match
HOL. See [`AGENTS.md`](../AGENTS.md#qualify-only-named-list-to-array-state-fields)
for the review rule.

## ML bindings versus declarations

`scripts/check-hol-refs.py` recognizes a HOL declaration in two forms: a
definition/theorem header (`Theorem`, `Triviality`, `Definition`, `Datatype`,
`Inductive`, `CoInductive`, `Overload`, `Type`) or an ML `val NAME = ...`
binding. A theorem-valued binding such as
`val llist_shorter_lnth = Q.prove (...)` is a proved result, so a Lean
counterpart may cite it from `@[hol]`. The scanner accepts every
`val NAME =` line and cannot distinguish a proved binding from an arbitrary ML
value, so it does not enforce theorem status: source review is responsible for
never tagging a non-theorem value, and the reference checker only verifies that
the cited name occurs in one of the two syntactic forms.

| HOL script | Lean counterpart |
| --- | --- |
| `panLangScript.sml` | `Flapjack/Pancake/PanLang.lean` (exact `mlstring`-named syntax over the faithful carriers in `Flapjack/Pancake/PanLang/Shape.lean`, `Flapjack/Pancake/PanLang/Exp.lean` and `Flapjack/Pancake/PanLang/Prog.lean` and `Flapjack/Pancake/PanLang/Decl.lean` (`fun_decl`, `decl`, `struct_info`, byte-ranged production roundtrips and the MlString-keyed struct-context pass-boundary bridge), and follow-ups) |
| `compiler/backend/word_simpScript.sml` | `Flapjack/Compiler/Backend/WordSimp.lean` |
| `compiler/backend/proofs/wordConvsProofScript.sml` | `Flapjack/Pancake/Proofs/WordConvs/` |
| `compiler/backend/wordLangScript.sml` | `Flapjack/Pancake/WordLang.lean` |
| `compiler/backend/backend_commonScript.sml` | `Flapjack/Compiler/Backend/BackendCommon.lean` |
| `compiler/backend/semantics/wordConvsScript.sml` | `Flapjack/Pancake/WordConvs.lean` |
| `compiler/backend/stackLangScript.sml` | `Flapjack/Compiler/Backend/StackLang.lean`, `Flapjack/Compiler/Encoders/Asm.lean`, `Flapjack/Compiler/Backend/StackLang/Prog.lean`, `Flapjack/Compiler/Backend/StackCarrier.lean`, `Flapjack/Compiler/Backend/MlStringBridge.lean` |
| `basis/pure/mlstringScript.sml` | `Flapjack/Basis/Pure/MlString.lean` (`mlstring = implode string`, `string = char list`; HOL `char` modeled by `HolChar = BitVec 8`, the canonical 256-element carrier); kernel-checked `String`<->`mlstring` bridge and stack-program embedding in `Flapjack/Compiler/Backend/MlStringBridge.lean` |
| `basis/pure/mllistScript.sml` (`sort`) | `Flapjack/Basis/Pure/MlList.lean` (tagged `sort_def`, with an untagged clause-for-clause rendering of HOL `mergesort_tail`) |
| `compiler/backend/word_allocScript.sml` | `Flapjack/Compiler/Backend/WordAlloc/` (`Expressions.lean` exact expression renaming and live sets) |
| `compiler/backend/proofs/word_allocProofScript.sml` | `Flapjack/Compiler/Backend/WordAlloc/Proofs/` (`StrongLocalsRel.lean` live-scoped lookup transport) |
| `compiler/backend/semantics/wordSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/WordSem/` (`State.lean` carriers, `Accessors.lean` state accessors and `word_exp`, `Env.lean` env/stack/cut helpers, `CallHelpers.lean` call/loop helpers, `Alloc.lean` find_code/gc/alloc/assign, `ShMem.lean` sh_mem_*/share_inst, `Inst.lean` inst_def, `Evaluate.lean` evaluate_def, `EvaluateClock.lean` clock lemmas, `EvaluateInd.lean` rebound evaluate_ind/evaluate_def, `Semantics.lean` semantics_def); the older call-aware executable analogue `Flapjack/WordSemantics.lean` is not a port |
| `compiler/backend/semantics/wordPropsScript.sml` | `Flapjack/Compiler/Backend/Semantics/WordSem/EnvListSupport.lean` (`env_to_list_lookup_equiv`, over the exact `wordSemEnvToList` result and Spt lookup carriers); `Flapjack/Compiler/Backend/Semantics/WordSem/Props/` (`EvaluateAddClock.lean` clock-constancy lemmas and `evaluate_add_clock`) |
| `compiler/backend/semantics/stackPropsScript.sml` | `Flapjack/Compiler/Backend/StackProps.lean` (recursive `stack_asm_ok` clauses and `addr_ok`, linked to the `asm_config` predicates) |
| `compiler/backend/semantics/stackSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/StackSem/State.lean` (exact state/result carriers and canonical finite-support state roundtrip), `StackSem/StateOps.lean` (memory/register/clock primitives), `StackSem/Control.lean` (code lookup and clock clamp/bound), `StackSem/Bitmap.lean` (polymorphic bitmap filter/map and length theorems), `StackSem/WordBitmap.lean` (word bit length and bitmap decoding), `StackSem/StackCodec.lean` (descriptor and recursive stack codecs; evaluator remains open) |
| `compiler/encoders/asm/asmScript.sml` | `Flapjack/Compiler/Encoders/Asm.lean` (asm_config validity predicates: `reg_ok`, `fp_reg_ok`, `reg_imm_ok`, `offset_ok`, `arith_ok`, `fp_ok`, `cmp_ok`, `inst_ok`; exact carriers `reg_imm`, `addr`, `inst`, `arith`, `fp`, `binop`, `cmp`, `memop`, `asm`) |
| `compiler/backend/labLangScript.sml` | `Flapjack/Compiler/Backend/LabLang.lean` (generic HOL `lab`, `line`, and `sec` syntax) |
| `compiler/backend/lab_to_targetScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`cbw_to_asm` carrier boundary only; target encoding remains open) |
| `compiler/backend/semantics/labPropsScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`line_ok_pre`, `sec_ok_pre`, and `all_enc_ok_pre`; asm/config carrier bridge remains explicit) |
| `compiler/backend/semantics/labPropsScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`line_ok_pre`, `sec_ok_pre`, and `all_enc_ok_pre`; asm/config carrier bridge remains explicit) |
| `compiler/backend/semantics/labSemScript.sml` | `Flapjack/Compiler/Backend/LabSem.lean` (`is_Label`) |
| `semantics/astScript.sml` | `Flapjack/AstHOL.lean` (exact `ast$shift` carrier; the remaining `ast` declarations are an open inventory item) |
| `compiler/backend/stack_namesScript.sml` | `Flapjack/Compiler/Backend/StackNames.lean` |
| `compiler/backend/riscv/riscv_configScript.sml` | `Flapjack/Compiler/Backend/RiscVConfig/Names.lean` |
| `compiler/backend/stackLangScript.sml` (shared-word `prog`) | `Flapjack/Compiler/Backend/StackCarrier.lean` |
| `compiler/backend/stack_removeScript.sml` | `Flapjack/Compiler/Backend/StackRemove.lean` (`max_stack_alloc`, `word_offset`, `store_list`, `store_length`, `stack_err_lab`, `halt_inst`; also the tagged stackLang instruction overloads `left_shift_inst`/`right_shift_inst`/`const_inst`/`load_inst`/`store_inst` over the exact `HolProg` carrier) |
| `compiler/backend/proofs/stack_removeProofScript.sml` | `Flapjack/Compiler/Backend/StackRemove.lean` (`is_SOME_Word`, `read_mem`/`LENGTH_read_mem`, `addresses`/`IN_addresses`; `names_ok` Prop-shaped tag) |
| `compiler/backend/stack_allocScript.sml` | `Flapjack/Compiler/Backend/StackAlloc.lean` (`next_lab`; executable pass counterpart remains `Flapjack/StackAlloc.lean`) |
| `compiler/backend/stack_to_labScript.sml` | `Flapjack/Compiler/Backend/StackToLab.lean` (`flatten` and `prog_to_section`; `compile` remains open) |
| `compiler/backend/reg_alloc/parmoveScript.sml` | `Flapjack/Compiler/Backend/Parmove.lean` |
| `compiler/backend/word_to_stackScript.sml` | `Flapjack/Compiler/Backend/WordToStack.lean`, `Flapjack/Compiler/Backend/WordToStackRegFormat.lean` |
| `compiler/backend/proofs/word_to_stackProofScript.sml` | `Flapjack/Compiler/Backend/WordToStack/Proofs/` (theorem groups, including `StackSize.lean`) |
| `panStaticScript.sml` | `Flapjack/Pancake/PanStatic.lean` |
| `pan_simpScript.sml` | `Flapjack/Pancake/PanSimp.lean` |
| `pan_structsScript.sml` | `Flapjack/Pancake/PanStructs.lean` |
| `proofs/pan_structsProofScript.sml` | `Flapjack/Pancake/Proofs/PanStructs.lean` |
| `pan_globalsScript.sml` | `Flapjack/Pancake/PanGlobals.lean` |
| `proofs/pan_globalsProofScript.sml` | `Flapjack/Pancake/Proofs/PanGlobals.lean`, `PanGlobals/ShapeInfrastructure.lean` |
| `proofs/pan_to_crepProofScript.sml` | `Flapjack/Pancake/Proofs/PanToCrep.lean`, `PanToCrep/CompileExpVmax.lean`, `PanToCrep/CompileProgParams.lean`, `PanToCrep/Primop.lean` |
| `pan_to_crepScript.sml` | `Flapjack/Pancake/PanToCrep.lean`, `PanToCrep/Compile.lean`, `PanToCrep/CompileProg.lean` |
| `crepLangScript.sml` | `Flapjack/Pancake/CrepLang.lean`, `Flapjack/Pancake/CrepLang/Exp.lean` (exact width-indexed `CrepExpHOL`), `Flapjack/Pancake/CrepLang/Prog.lean` (exact width-indexed `CrepProgHOL`) |
| `crep_arithScript.sml` | `Flapjack/Pancake/CrepArith.lean` |
| `crep_inlineScript.sml` | `Flapjack/Pancake/CrepInline.lean`, `CrepInline/Pass.lean` |
| `crep_to_loopScript.sml` | `Flapjack/Pancake/CrepToLoop.lean`, `CrepToLoop/Optimise.lean` |
| `proofs/crep_to_loopProofScript.sml` | `Flapjack/Pancake/CrepToLoop/StateRel.lean` (proof relations and exact `mem_lookup_fromalist_some` port) |
| `misc/miscScript.sml` (`spt`/`num_set`) | `Flapjack/Misc/Sptree.lean` (exact `spt` inductive carrier + tagged `num_set` abbrev; `Spt` itself untagged because HOL/src is outside cakeml) |
| `loopLangScript.sml` | `Flapjack/Pancake/LoopLang.lean` (exact exp/loop_arith/prog carriers, now over the exact `unit spt`-backed `NumSet`; executable `LoopProg` bridge tracked by .18.5.17.1.1) |
| `loop_callScript.sml` | `Flapjack/Pancake/LoopCall.lean`, `LoopCall/IsLoad.lean` |
| `proofs/loop_callProofScript.sml` | `Flapjack/Pancake/Proofs/LoopCall/CompileCorrect.lean` (`labels_in_def`, `compile_correct`) |
| `loop_liveScript.sml` | `Flapjack/Pancake/LoopLive.lean`, `LoopLive/Fixedpoint.lean` |
| `proofs/loop_liveProofScript.sml` | `Flapjack/Pancake/Proofs/LoopLive/CompileCorrect.lean` (`compile_correct` and its case pieces), `LoopLive/Optimise.lean` (`mark_correct`, `comp_correct`, `optimise_correct`) |
| `loop_to_wordScript.sml` | `Flapjack/Pancake/LoopToWord.lean` |
| `semantics/panSemScript.sml` | `Flapjack/PanBst.lean`, `Flapjack/PanValueFfiClockSemantics.lean`, `Flapjack/Pancake/Semantics/PanSem.lean`, `PanSem/Primop.lean`, `PanSem/ValueHOL.lean`, `PanSem/MemLoadHOL.lean`, `PanSemStateEval.lean`, `PanSem/Semantics.lean` (exact `semantics_def` over `evaluateHOLFiniteState`) |
| `semantics/pan_commonPropsScript.sml` | `Flapjack/Pancake/Semantics/PanCommonProps.lean` |
| `pan_commonScript.sml` | `Flapjack/Pancake/PanCommon.lean` |
| `misc/miscScript.sml` (`app_list`/`append`) | `Flapjack/Misc/AppList.lean` |
| `misc/miscScript.sml` (`good_dimindex`) | `Flapjack/Misc/GoodDimindex.lean` (exact `good_dimindex` predicate) |
| `semantics/panPropsScript.sml` | `Flapjack/Pancake/Semantics/PanProps.lean`, `PanProps/EvalInvariant.lean`, `PanProps/MemByteArray.lean` (exact `write_bytearray_update_byte` / `read_write_bytearray_lemma`), `PanProps/LocalisedExpSimps.lean`, `PanProps/NamelessExpSimps.lean`, `PanProps/EvaluateAddClockIoEventsMono.lean` |
| `semantics/crepSemScript.sml` | `Flapjack/Pancake/Semantics/CrepSem.lean`, `CrepSem/Eval.lean`, `CrepSem/TotalEval.lean`, `CrepSem/Primop.lean`, `CrepSem/LookupCode.lean` |
| `semantics/crepPropsScript.sml` | `Flapjack/Pancake/Semantics/CrepProps.lean` |
| `semantics/loopSemScript.sml` | `Flapjack/Pancake/Semantics/LoopSem.lean`; exact width-indexed `state` carrier + production bridge in `Flapjack/Pancake/Semantics/LoopSemState.lean` (untagged pending exact sub-carriers) |
| `semantics/ffi/ffiScript.sml` | `Flapjack/Ffi.lean` (production FFI state/events), `Flapjack/FfiHOL.lean` (exact ffi_outcome/oracle_result/shmem_op/ffiname/oracle/oracle_function/io_event/final_event/ffi_state/ffi_result carriers + call_FFI) |
| `semantics/fpSemScript.sml` | `Flapjack/FpSemHOL.lean` (tagged `fpfma_def`, over the untagged HOL `binary_ieee`/`machine_ieee` renderings in `Flapjack/Misc/BinaryIeee*.lean` and `MachineIeee.lean`) |
| `semantics/proofs/semanticsPropsScript.sml` | `Flapjack/SemanticsProps.lean` (structural behavior and `implements'` analogue; HOL `llist` representation bridge remains open) |
| `proofs/pan_simpProofScript.sml` | `Flapjack/Pancake/Proofs/PanSimp.lean`, `PanSimp/Evaluate.lean` |
| `proofs/pan_to_wordProofScript.sml` | `Flapjack/Pancake/Proofs/PanToWord.lean` |

Placement under `Proofs` does not imply that a whole pass correctness theorem
has been established. For declaration-level provenance, use
`scripts/check-hol-refs.py --mapping`; CI validates the review inventory with
`scripts/check_hol_theorem_map.py`. For untagged port candidates, use
`scripts/next-hol-port.py`. Track individual gaps and progress in
[GitHub issues](https://github.com/pirapira/flapjack/issues), not in this
layout guide.
| compiler/backend/reg_alloc/reg_allocScript.sml | Flapjack/Compiler/Backend/RegAlloc.lean |
| compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml | Flapjack/Compiler/Backend/RegAlloc/Proofs.lean |

The pinned external `hol4/src/coretypes/optionScript.sml` counterpart is
`Flapjack/Misc/Option.lean`.

The pinned external `hol4/src/coalgebras/llistScript.sml` counterpart is
`Flapjack/Misc/LList.lean`; `lprefix_lubScript.sml` chain and least-upper-bound
declarations remain in `Flapjack/Misc/LprefixLub.lean`.
