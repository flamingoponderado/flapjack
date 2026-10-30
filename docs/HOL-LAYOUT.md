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
| `compiler/backend/backend_passesScript.sml` | `Flapjack/Compiler/Backend/BackendPasses/Frontend.lean`, `BackendPasses/Closure.lean`, `BackendPasses/Bvi.lean`, `BackendPasses/Data.lean`, `BackendPasses/Word.lean`, `BackendPasses/WordOptimise.lean` and `BackendPasses/Stack.lean` (explorer snapshots through lab filtering) |
| `compiler/backend/presLangScript.sml` | `Flapjack/Compiler/Backend/PresLang/Config.lean`, `PresLang/Source.lean`, `PresLang/Flat.lean`, `PresLang/Clos.lean`, `PresLang/Bvl.lean`, `PresLang/Bvi.lean`, `PresLang/Data.lean`, `PresLang/Asm.lean`, `PresLang/Lab.lean`, `PresLang/Word.lean` and `PresLang/Stack.lean` (explorer display; representation review and explorer wiring remain open) |
| `semantics/tokensScript.sml` | `Flapjack/CakeParser/Tokens.lean` |
| `semantics/lexer_funScript.sml` | `Flapjack/CakeParser/Lexer.lean` |
| `compiler/inference/infer_tScript.sml` | `Flapjack/Compiler/Inference/InferT.lean` and `Flapjack/Compiler/Inference/InferT/Display.lean` (inference types and rendering; source review pending) |
| `compiler/inference/inferScript.sml` | `Flapjack/Compiler/Inference/Infer.lean`, `Flapjack/Compiler/Inference/Infer/Core.lean`, and `Flapjack/Compiler/Inference/Infer/TypesOutput.lean` (bounded inference and combined type-output infrastructure; source correspondence remains open) |
| `compiler/parsing/lexer_implScript.sml` | `Flapjack/CakeParser/LexerImpl.lean` |
| `semantics/gramScript.sml` | `Flapjack/CakeParser/Grammar.lean` |
| `compiler/parsing/pegexec_cml_foScript.sml` | `Flapjack/CakeParser/PegChecks.lean` and `Flapjack/CakeParser/PegActions.lean` |
| `compiler/parsing/fromSexpScript.sml` | `Flapjack/CakeParser/FromSexp.lean` and `Flapjack/CakeParser/FromSexp/Operators.lean`, `Ast.lean` (untagged bounded AST decoders used by the S-expression executable input; source correspondence review remains open) |
| `HOL/examples/formal-languages/context-free/simpleSexpPEGScript.sml` | `Flapjack/CakeParser/Sexp.lean` (untagged direct, bounded parser; PEG equivalence and CakeML AST conversion remain open) |
| `pancake/pan_to_targetScript.sml` | `Flapjack/Pancake/PanToTarget.lean` |
| `pancake/proofs/pan_to_targetProofScript.sml` | `Flapjack/Pancake/Proofs/PanToTarget.lean` and its `PanToTarget/` submodules |
| `panLangScript.sml` | `Flapjack/Pancake/PanLang.lean` (exact `mlstring`-named syntax over the faithful carriers in `Flapjack/Pancake/PanLang/Shape.lean`, `Flapjack/Pancake/PanLang/Exp.lean` and `Flapjack/Pancake/PanLang/Prog.lean` and `Flapjack/Pancake/PanLang/Decl.lean` (`fun_decl`, `decl`, `struct_info`, byte-ranged production roundtrips and the MlString-keyed struct-context pass-boundary bridge), and follow-ups) |
| `compiler/backend/word_simpScript.sml` | `Flapjack/Compiler/Backend/WordSimp.lean` |
| `compiler/backend/proofs/word_simpProofScript.sml` | `Flapjack/Compiler/Backend/WordSimp/Proofs/` (`GcWordConst.lean` `is_gc_word_const`) |
| `compiler/backend/proofs/wordConvsProofScript.sml` | `Flapjack/Pancake/Proofs/WordConvs/` |
| `compiler/backend/wordLangScript.sml` | `Flapjack/Pancake/WordLang.lean` |
| `compiler/backend/backendScript.sml` | `Flapjack/Compiler/Backend/Backend.lean`, `Flapjack/Compiler/Backend/Backend/PrimSrcConfig.lean` (`prim_src_config_def`, `prim_src_config_eq`) |
| `compiler/backend/backend_commonScript.sml` | `Flapjack/Compiler/Backend/BackendCommon.lean` and its `BackendCommon/BvlStubs.lean` submodule (`BackendCommon/BoolTags.lean`: Boolean tags; `BackendCommon/ConstructorTags.lean`: list and exception tags) |
| `compiler/backend/proofs/word_depthProofScript.sml` | `Flapjack/Compiler/Backend/WordDepthProof/` (`Helpers.lean` lines 12-146 helper lemmas; `CallGraphLemma.lean` `max_depth_call_graph_lemma` assembled from the per-case `CallGraphLemma/*` pieces; `CallGraph.lean` `max_depth_call_graph`, `max_depth_Call_NONE`) |
| `compiler/backend/flatLangScript.sml` | `Flapjack/Compiler/Backend/FlatLang.lean` (`op`, `ctor_id`, `type_id`, `type_group_id`, `pat`, `pat_bindings_def`, `exp`, `bool_id_def`, `Bool_def`, `SmartIf_def`; the script has no `dec` datatype) |
| `compiler/backend/source_letScript.sml` | `Flapjack/Compiler/Backend/SourceLet.lean` (source `Let`/`Letrec` lifting; pending statement review) |
| `compiler/backend/proofs/source_letProofScript.sml` | `Flapjack/Compiler/Backend/SourceLet/Proofs.lean`, `SourceLet/Proofs/Evaluate.lean`, `SourceLet/Proofs/Repeated.lean`, `SourceLet/Proofs/Correct.lean`, and `SourceLet/Proofs/Semantics.lean` (clocked evaluation and observable semantics preservation; oracle-adjustment theorem and correspondence review remain open) |
| `compiler/backend/proofs/source_to_sourceProofScript.sml` | `Flapjack/Compiler/Backend/SourceToSource/Proofs.lean` (observable semantics preservation; oracle-adjustment theorem and correspondence review remain open) |
| `compiler/backend/source_to_sourceScript.sml` | `Flapjack/Compiler/Backend/SourceToSource.lean` (source pass driver; pending statement review) |
| `compiler/backend/proofs/clos_to_bvlProofScript.sml` | `Flapjack/Compiler/Backend/ClosToBvl/Proofs/ClosureArguments.lean` (closure argument accumulation and arity helpers), `ClosToBvl/Proofs/Integer.lean` and `ClosToBvl/Proofs/Word.lean` (integer and selected word primitive agreement; full relation and pass correctness remain open). |
| `compiler/backend/clos_to_bvlScript.sml` | `Flapjack/Compiler/Backend/ClosToBvl/Config.lean`, `ClosToBvl/Constants.lean`, `ClosToBvl/Layout.lean`, `ClosToBvl/Sort.lean`, `ClosToBvl/Names.lean`, `ClosToBvl/ExtractName.lean`, `ClosToBvl/Compile.lean`, `ClosToBvl/SourceCompile.lean`, `ClosToBvl/SourceExps.lean`, `ClosToBvl/Proofs/SourceCompile.lean`, `ClosToBvl/Proofs/ExpsEquivalence.lean`, `ClosToBvl/Stubs.lean`, `ClosToBvl/Prepared.lean` and `ClosToBvl/Proofs/Total.lean` (checked expression lowering and the wrapper with optional optimizations disabled are proved to succeed; checked conversion equals the source singleton and list forms and original compile_exps/program forms; pass semantic correctness remains open). `SourceToFlat/ToBvi.lean` and `SourceToFlat/ToData.lean` compose the restricted checked passes. |
| `compiler/backend/bvl_jumpScript.sml` | `Flapjack/Compiler/Backend/BvlJump.lean` (statement review remains open) |
| `compiler/backend/db_varsScript.sml` | `Flapjack/Compiler/Backend/DbVars.lean` (statement review remains open) |
| `compiler/backend/clos_annotateScript.sml` | `Flapjack/Compiler/Backend/ClosAnnotate/Free.lean` and `ClosAnnotate/Shift.lean` (statement review remains open) |
| `compiler/backend/flat_elimScript.sml` | `Flapjack/Compiler/Backend/FlatElim/Analysis.lean`, `FlatElim/Reachability.lean` and `FlatElim/Proofs/Reachability.lean` (analyses, removal criterion and total closure with a proved sufficient bound; exact whole-pass correspondence remains open, declarations pending statement review); `SourceToFlat/Eliminate.lean` composes the pass with program compilation |
| `compiler/backend/flat_patternScript.sml` | `Flapjack/Compiler/Backend/FlatPattern/Config.lean`, `FlatPattern/Names.lean`, `FlatPattern/Encode.lean`, `FlatPattern/Decode.lean`, `FlatPattern/BindingsTotal.lean`, `FlatPattern/NaiveTotal.lean`, `FlatPattern/Patterns.lean`, `FlatPattern/CompileTotal.lean` (total pattern branch and expression compilation; declarations pending statement review) |
| `compiler/backend/proofs/flat_patternProofScript.sml` | `Flapjack/Compiler/Backend/FlatPattern/Proofs/` (pattern compiler proof components, global-initialization invariants, and installation relation) |
| `compiler/backend/flat_to_closScript.sml` | `Flapjack/Compiler/Backend/FlatToClos/Helpers.lean`, `FlatToClos/Arith.lean`, `FlatToClos/CopyByte.lean`, `FlatToClos/Op.lean`, `FlatToClos/Compile.lean` (expression, declaration, program and incremental lowering; statement review remains open) |
| `compiler/backend/proofs/flat_to_closProofScript.sml` | `Flapjack/Compiler/Backend/FlatToClos/Proofs/` (proof-side relations, operator and evaluator simulations, global-write, closure-safety and pre-MTI and complete closure syntax preservation for expression lowering and their composition with source-to-flat, executable initialization, and source-to-closure observational composition through interpreter attachment; HOL correspondence of the relations and evaluators remains pending). |
| `compiler/backend/proofs/clos_interpProofScript.sml` | `Flapjack/Compiler/Backend/ClosInterp/Proofs/Globals.lean` (global-write and closure-safety preservation for interpreter insertion), `ClosInterp/Proofs/NoMti.lean` (pre-MTI syntax preservation for interpreter insertion), and other `ClosInterp/Proofs/` modules for interpreter and insertion simulations. |
| `compiler/backend/clos_interpScript.sml` | `Flapjack/Compiler/Backend/ClosInterp/Interpreter.lean`, `ClosInterp/Optimise.lean` (interpreter attachment, runtime expression and incremental optimization; statement review remains open) |
| `compiler/backend/clos_numberScript.sml` | `Flapjack/Compiler/Backend/ClosNumber.lean` (closure location numbering and incremental wrapper; statement review remains open) |
| `compiler/backend/clos_fvsScript.sml` | `Flapjack/Compiler/Backend/ClosFvs.lean` and `ClosFvs/Proofs/Total.lean` (free-variable cleanup with a proved sufficient traversal bound; HOL correspondence remains open) |
| `compiler/backend/clos_callScript.sml` | `Flapjack/Compiler/Backend/ClosCall.lean` and `ClosCall/Proofs/` (free-variable analysis and direct-call conversion with proved sufficient traversal bounds; HOL correspondence remains open) |
| `compiler/backend/clos_ticksScript.sml` | `Flapjack/Compiler/Backend/ClosTicks.lean` and `ClosTicks/Proofs/Total.lean` (tick removal with a proved sufficient traversal bound; HOL correspondence remains open) |
| `compiler/backend/clos_letopScript.sml` | `Flapjack/Compiler/Backend/ClosLetop.lean` and `ClosLetop/Proofs/Total.lean` (let-operation cleanup with a proved sufficient traversal bound; HOL correspondence remains open) |
| `compiler/backend/pattern_matching/pattern_commonScript.sml` | `Flapjack/Compiler/Backend/PatternCommon.lean` (position and match-result carriers) |
| `compiler/backend/pattern_matching/pattern_semanticsScript.sml` | `Flapjack/Compiler/Backend/PatternSemantics.lean` (pattern and decision-tree carriers; semantics remains open) |
| `compiler/backend/pattern_matching/pattern_compScript.sml` | `Flapjack/Compiler/Backend/PatternComp/Decision.lean` (row rearrangement, decision-tree construction and `comp`; statement review remains open) |
| `compiler/backend/pattern_matching/pattern_exhScript.sml` | `Flapjack/Compiler/Backend/PatternExh/Matrix.lean`, `PatternExh/Weights.lean`, `PatternExh/Measures.lean`, `PatternExh/Exhaustive.lean` (matrix transformations, measures and total exhaustiveness recursion; statement review remains open) |
| `compiler/backend/proofs/source_evalProofScript.sml` | `Flapjack/Compiler/Backend/SourceEval/Proofs.lean` and `Flapjack/Compiler/Backend/SourceEval/Proofs/` (compiler instance and source Eval oracle operations) |
| `compiler/backend/source_to_flatScript.sml` | `Flapjack/Compiler/Backend/SourceToFlat/Config.lean` (carriers `var_name`, `environment`, stores, `next_indices`, `config`), `SourceToFlat/Helpers.lean` (`compile_var` .. `simple_dlet`, lines 46-340 except `compile_exp`), `SourceToFlat/CompileExp.lean` (mutual `compile_exp_def`), `SourceToFlat/CompileDecs.lean` (`compile_decs_def`, `empty_config_def`), `SourceToFlat/CompileProg.lean` (program and incremental compilation before flat elimination and pattern compilation; pending statement review), `SourceToFlat/ToClos.lean` (bounded composition through closure lowering, with earlier source pass and later compiler stages still open) |
| `compiler/backend/proofs/source_to_flatProofScript.sml` | `Flapjack/Compiler/Backend/SourceToFlat/Proofs/CompileExp.lean` (expression-list length prerequisite), `CompileGlobals.lean` (expression global-initialization invariant), `CompileDecGlobals.lean` (declaration and program global-initialization invariants), `BindingCount.lean` (declaration binding counts and counter growth), `BindingGlobals.lean` (allocated global bags and distinct initialization), `GlobalOracle.lean` (incremental oracle global ordering), `CompileFlatGlobals.lean` (complete and incremental pass safety), `SourceToFlat/Proofs/BindLocals.lean` (local-binding definition, namespace composition and pattern binding), `SourceToFlat/Proofs/GlobalEnv.lean` and `GlobalEnvConditions.lean` (global environment carrier and constructor-map assumptions), and `SourceToFlat/Proofs/ValueRel.lean`, `ValueRelCases.lean`, `Equality.lean`, `ListConversion.lean`, `PrimitiveType.lean` and `PrimitiveTest.lean` (untagged factored relation, inversion and equality simulation infrastructure, pending full HOL correspondence review); `SourceToFlat/Proofs/PatternStamps.lean` contains constructor-map prerequisites, `SourceToFlat/Proofs/PatternRows.lean` contains pattern-binding preservation and untagged row-selection infrastructure, `SourceToFlat/Proofs/EvaluateMatch.lean` composes row selection with evaluator and body simulations, `SourceToFlat/Proofs/EvaluateApply.lean` composes operand evaluation with primitive operations, and `StateRel.lean`, `StoreUpdate.lean`, `MemoryOps.lean`, `ThunkRel.lean`, `PatternRel.lean`, `PatternSimulation.lean`, `GlobalLookup.lean`, `EvaluateCases.lean` and `EvaluateControl.lean` contain untagged state, store-update, memory-operation, thunk, pattern and expression-composition simulations over the factored relations. `SourceToFlat/Proofs/CompileSemantics.lean` composes the factored program simulation with elimination and pattern compilation; the factored relations and complete pass theorem still require HOL correspondence review. |
| `compiler/backend/semantics/flatSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/FlatSem.lean` (value, local environment, install configuration and state carriers), `FlatSem/Operations.lean` (value equality and closure application), `FlatSem/Conversions.lean` (list and string conversions), `FlatSem/Primitives.lean` (primitive type checks and literal projection), `FlatSem/Test.lean` (primitive comparisons), `FlatSem/PatternMatch.lean` (pattern and row matching), `FlatSem/Eval.lean` (clock and dynamic-compilation helpers), `FlatSem/Thunk.lean` (thunk inspection and updates), `FlatSem/Apply.lean` with `ApplyFlat.lean`, `ApplyMemory.lean`, `ApplyData.lean`, `ApplyCopy.lean` and `ApplyNumeric.lean` (assembled, untagged primitive application; source numeric and carrier review remains open), `FlatSem/Evaluate.lean` (untagged fuel-bounded evaluator), `FlatSem/EvaluateExact.lean` with `Measure.lean` (untagged well-founded clocked evaluator and termination infrastructure), and `FlatSem/ApplyClock.lean` and `FlatSem/EvaluateClock.lean` (untagged clock preservation for primitive operations and the complete clocked evaluator, proved by explicit induction). Full HOL source and carrier review and evaluator correspondence remain open. |
| `compiler/backend/semantics/closSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/ClosSem.lean` (value and reference carriers, global lookup, list conversions and equality), `ClosSem/State.lean` (untagged state and clock infrastructure), `ClosSem/Int.lean` and `ClosSem/Word.lean` (untagged numeric operations), `ClosSem/ApplyBasic.lean`, `ClosSem/ApplyMemory.lean`, `ClosSem/Apply.lean` and `ClosSem/ApplyClock.lean` (untagged primitive dispatcher and clock invariant), `ClosSem/Call.lean` (untagged closure application and code lookup), `ClosSem/Thunk.lean` (untagged thunk operations), `ClosSem/Install.lean` (untagged dynamic installation), and `ClosSem/EvaluateFuel.lean`, `EvaluateExact.lean`, `EvaluateClock.lean` and `Measure.lean` (untagged bounded and clocked unbounded evaluators and complete evaluator clock bounds). Complete source, type and carrier review remains pending. |
| `compiler/backend/semantics/bvlSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/BvlSem/Value.lean` and `BvlSem/Int.lean`, `BvlSem/Word.lean`, `BvlSem/Equality.lean`, `BvlSem/State.lean`, `BvlSem/Call.lean`, `BvlSem/Thunk.lean`, `BvlSem/Build.lean`, `BvlSem/ApplyBasic.lean`, `BvlSem/ApplyMemory.lean`, `BvlSem/Conversions.lean`, `BvlSem/MemoryChoice.lean`, `BvlSem/Apply.lean`, `BvlSem/ApplyClock.lean`, `BvlSem/ApplyCode.lean`, `BvlSem/Evaluate.lean`, `BvlSem/EvaluateClock.lean`, `BvlSem/EvaluateLength.lean` and `BvlSem/EvaluateHOL.lean` (value and reference-cell carriers, list encodings, integer, word and equality operations, state, code lookup, thunk inspection, source-shaped constant construction, primitive application with code-frame properties, and clocked evaluation with clock bounds and successful-result length; finite-map product-result qualification remains open). |
| `compiler/backend/semantics/bvlPropsScript.sml` | `Flapjack/Compiler/Backend/Semantics/BvlProps/EvaluateLength.lean`, `BvlProps/EvaluateList.lean`, `BvlProps/EvaluateClockShift.lean`, `BvlProps/EvaluateEvents.lean`, `BvlProps/EvaluateEventsClock.lean`, `BvlProps/ApplyError.lean`, `BvlProps/ApplyClock.lean`, `BvlProps/ApplyCode.lean`, `BvlProps/ApplyEvents.lean` and `BvlProps/FindCode.lean` (reviewed result-length, list-sequencing, clock extension, evaluator and primitive event-prefix, primitive-error, primitive clock and code replacement, and code-lookup properties; remaining BVL evaluator properties are open). |
| `compiler/backend/semantics/closPropsScript.sml` | `Flapjack/Compiler/Backend/Semantics/ClosProps/Evaluate.lean` (untagged singleton and error sequencing properties; full append theorem and source correspondence remain open), `ClosProps/Globals.lean` (global-write bags and closure safety), `ClosProps/NoMti.lean` (pre-multi-argument syntax invariant), `ClosProps/Syntactic.lean` (application and function-annotation predicates), and `ClosProps/NoMtiSyntactic.lean` (relationships among the predicates). |
| `compiler/backend/semantics/flatPropsScript.sml` | `Flapjack/Compiler/Backend/FlatProps/` (flat evaluator and simulation properties, including `NoMat.lean` for flat-to-closure lowering; correspondence review remains pending). |
| `compiler/backend/bvl_to_bviScript.sml` | `Flapjack/Compiler/Backend/BvlToBvi.lean` and its `BvlToBvi/Config.lean`, `BvlToBvi/Analysis.lean`, `BvlToBvi/CompileOp.lean`, `BvlToBvi/Stubs.lean`, `BvlToBvi/Names.lean`, `BvlToBvi/Compile.lean` and `BvlToBvi/Proofs/Total.lean` submodules (expression conversion with a proved sufficient traversal bound; full compiler and HOL correspondence remain open) |
| `compiler/backend/bvl_inlineScript.sml` | `Flapjack/Compiler/Backend/BvlInline.lean`, `BvlInline/RemoveTicks.lean` and `BvlInline/Proofs/` (inlining, cache analysis, tick removal, let-operation reduction and handler processing with proved sufficient traversal bounds; total tick removal is source-reviewed and connected to the executed bounded traversal; other HOL correspondences remain open) |
| `compiler/backend/proofs/bvl_inlineProofScript.sml` | `Flapjack/Compiler/Backend/BvlInline/Proofs/StateRel.lean` and `BvlInline/Proofs/ApplySimulation.lean` (tick-removal state relation and non-install primitive simulation; complete installation simulation and pass-correctness theorems remain open). |
| `compiler/backend/bvl_handleScript.sml` | `Flapjack/Compiler/Backend/BvlHandle.lean` and `BvlHandle/Proofs/` (handler simplification, live-variable compilation and sequence splitting with proved sufficient traversal bounds; HOL correspondence remains open) |
| `compiler/backend/bvl_constScript.sml` | `Flapjack/Compiler/Backend/BvlConst.lean` and `BvlConst/Proofs/Total.lean` (constant propagation with a proved sufficient traversal bound; HOL correspondence remains open) |
| `compiler/backend/clos_mtiScript.sml` | `Flapjack/Compiler/Backend/ClosMti.lean` and `ClosMti/Proofs/` (argument collection and multi-argument traversal with a proved sufficient structural bound; HOL correspondence remains open) |
| `compiler/backend/bvi_inlineScript.sml` | `Flapjack/Compiler/Backend/BviInline.lean` and `BviInline/Proofs/Total.lean` (wrapper inlining and tick removal with proved sufficient traversal bounds; HOL correspondence remains open) |
| `compiler/backend/bvi_tmcScript.sml` | `Flapjack/Compiler/Backend/BviTmc.lean` and `BviTmc/Proofs/` (purity, constructor extraction and TMC conversion with proved sufficient traversal bounds; HOL correspondence and pass correctness remain open) |
| `compiler/backend/bvi_tailrecScript.sml` | `Flapjack/Compiler/Backend/BviTailrec.lean`, `BviTailrec/Analysis.lean`, `BviTailrec/Rewrite.lean` and `BviTailrec/Proofs/` (recursion and type analysis, scans and rewriting with proved sufficient traversal bounds; HOL correspondence and pass correctness remain open) |
| `compiler/backend/bvi_to_dataScript.sml` | `Flapjack/Compiler/Backend/BviToData/Assign.lean`, `BviToData/Compile.lean`, `BviToData/Optimise.lean` and `BviToData/Proofs/Total.lean` (expression traversal with a proved sufficient structural bound; full compiler and HOL correspondence remain open) |
| `compiler/backend/data_liveScript.sml` | `Flapjack/Compiler/Backend/DataLive.lean` (statement review remains open) |
| `compiler/backend/data_simpScript.sml` | `Flapjack/Compiler/Backend/DataSimp.lean` (statement review remains open) |
| `compiler/backend/data_spaceScript.sml` | `Flapjack/Compiler/Backend/DataSpace/Requirements.lean` and `DataSpace/Compile.lean` (statement review remains open) |
| `compiler/backend/dataLangScript.sml` | `Flapjack/Compiler/Backend/DataLang/Syntax.lean` (syntax and allocation classifications; statement review remains open) |
| `compiler/backend/bvi_letScript.sml` | `Flapjack/Compiler/Backend/BviLet/Helpers.lean`, `BviLet/Compile.lean` and `BviLet/Proofs/Total.lean` (optimizer with a proved sufficient structural bound; HOL correspondence remains open) |
| `compiler/backend/semantics/wordConvsScript.sml` | `Flapjack/Pancake/WordConvs.lean` |
| `compiler/backend/stackLangScript.sml` | `Flapjack/Compiler/Backend/StackLang.lean`, `Flapjack/Compiler/Encoders/Asm.lean`, `Flapjack/Compiler/Backend/StackLang/Prog.lean`, `Flapjack/Compiler/Backend/StackLang/Overloads.lean` (`While`/`move`/arithmetic overloads, `list_Seq`, `gc_stub_location`), `Flapjack/Compiler/Backend/StackCarrier.lean`, `Flapjack/Compiler/Backend/MlStringBridge.lean` |
| `basis/pure/mlstringScript.sml` | `Flapjack/Basis/Pure/MlString.lean` (`mlstring = implode string`, `string = char list`; HOL `char` modeled by `HolChar = BitVec 8`, the canonical 256-element carrier; `concat_def`); kernel-checked `String`<->`mlstring` bridge and stack-program embedding in `Flapjack/Compiler/Backend/MlStringBridge.lean` |
| `basis/pure/mllistScript.sml` (`sort`) | `Flapjack/Basis/Pure/MlList.lean` (tagged `sort_def`, with an untagged clause-for-clause rendering of HOL `mergesort_tail`) |
| `compiler/backend/word_allocScript.sml` | `Flapjack/Compiler/Backend/WordAlloc/` (`Expressions.lean` exact expression renaming and live sets) |
| `compiler/backend/word_removeScript.sml` | `Flapjack/Compiler/Backend/WordRemove.lean` |
| `compiler/backend/word_unreachScript.sml` | `Flapjack/Compiler/Backend/WordUnreach.lean` |
| `compiler/backend/word_copyScript.sml` | `Flapjack/Compiler/Backend/WordCopy.lean` |
| `compiler/backend/word_to_wordScript.sml` | `Flapjack/Compiler/Backend/WordToWord/` (`Config.lean` config and `next_n_oracle`; `Compile.lean` `compile_single`, `full_compile_single` and `compile`) |
| `compiler/backend/proofs/word_to_wordProofScript.sml` | `Flapjack/Compiler/Backend/WordToWord/Proofs/` (`CodeRel.lean` `code_rel` and its helpers; `CompileSingle.lean` `FST_compile_single` and `compile_single_lem`; `CompileSingleCorrect/` the `compile_single_correct` case pieces and assembly; `CompileWordToWord.lean` `compile_word_to_word_thm`) |
| `misc/miscScript.sml` (`anub`) | `Flapjack/Misc/Anub.lean` |
| `compiler/backend/data_to_wordScript.sml` | `Flapjack/Compiler/Backend/DataToWord/` (`Config.lean`, `Variables.lean`, `Header.lean`, `Locations.lean`, `WordOp.lean`, `Control.lean`, `Stubs.lean`, `Names.lean` and pointer-layout helpers; partial conversion, full compiler and statement review remain open) |
| `compiler/backend/word_bignumScript.sml` | `Flapjack/Compiler/Backend/WordBignum/` (source-reviewed expression translation, code-construction helpers and total mini compiler, used with a captured polymorphic mini-program; the shallow-to-deep generator and semantic correctness remain open) |
| `compiler/backend/proofs/word_gcFunctionsScript.sml` | `Flapjack/Compiler/Backend/WordGcFunctions.lean` (copying, generational and partial GC definitions and `word_gc_fun`); `WordGcFunctions/Roots.lean` (root `EVERY2`/`LENGTH` theorems) |
| `compiler/backend/proofs/word_allocProofScript.sml` | `Flapjack/Compiler/Backend/WordAlloc/Proofs/` (`StrongLocalsRel.lean` live-scoped lookup transport) |
| `compiler/backend/proofs/word_unreachProofScript.sml` | `Flapjack/Compiler/Backend/WordUnreach/Proofs.lean` |
| `compiler/backend/proofs/word_instProofScript.sml` | `Flapjack/Compiler/Backend/WordInst/Proofs/` (`PullExp.lean` pull_exp/optimize_consts/flatten_exp group, `InstSelect.lean` inst_select_exp_thm/inst_select_thm/inst_select_Loop_helper, `ThreeToTwo.lean` three_to_two_reg family) |
| `compiler/backend/proofs/word_removeProofScript.sml` | `Flapjack/Compiler/Backend/WordRemove/Proofs/` (`CompileState.lean` compile_state group, `Correct.lean` word_remove_correct) |
| `compiler/backend/proofs/word_copyProofScript.sml` | `Flapjack/Compiler/Backend/WordCopy/Proofs/` (`Invariant.lean` CPstate_inv group, `Models.lean` CPstate_models group, `Move.lean` copy_prop_move and invariant preservation, `Store.lean` move/store models and expression congruences, `Inst.lean` copy_prop_inst semantics, `Correct.lean` copy_prop_correct and evaluate_copy_prop) |
| `compiler/backend/word_cseScript.sml` | `Flapjack/Compiler/Backend/WordCse/` (`Knowledge.lean`, `RegisterData.lean`, `InstructionKeys.lean`, `RegisterUses.lean`, `Canonical*.lean`, `FactProducers.lean`, `Join.lean` and `Production*.lean` definitions and clause bodies; `Transform.lean` `word_cseInst`, `word_cse`, `word_common_subexp_elim` and `Seqs`) |
| `compiler/backend/proofs/word_cseProofScript.sml` | `Flapjack/Compiler/Backend/WordCse/Proofs/` (`ListOrder.lean` listCmp laws, `IntersectionInvariant.lean` `invariant_bm_inter_eq`, `IntersectionAccumulator.lean` `bm_inter_eq_acc_thm` and `lookup_bm_inter_eq`, `KnowledgeLemmas.lean` the listCmp-map and `register_read(s)` lemmas, `WfDataPreservation.lean` the `wf_data` preservation section, `DataInvTransport.lean` the `data_inv` transport lemmas, `DataInvUpdates.lean` the `data_inv` knowledge-update lemmas, `FactInsert.lean` the fact-producer correctness group, `MoveLemmas.lean` the move and clock lemmas, `CompCorrect.lean` with `CompCorrect/` cases `comp_correct` and `word_common_subexp_elim_correct`, `Conventions.lean` the syntactic-convention section) |
| `compiler/backend/semantics/wordSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/WordSem/` (`State.lean` carriers, `Accessors.lean` state accessors and `word_exp`, `Env.lean` env/stack/cut helpers, `CallHelpers.lean` call/loop helpers, `Alloc.lean` find_code/gc/alloc/assign, `ShMem.lean` sh_mem_*/share_inst, `Inst.lean` inst_def, `Evaluate.lean` evaluate_def, `EvaluateClock.lean` clock lemmas, `EvaluateInd.lean` rebound evaluate_ind/evaluate_def, `Semantics.lean` semantics_def); the older call-aware executable analogue `Flapjack/WordSemantics.lean` is not a port |
| `compiler/backend/semantics/wordPropsScript.sml` | `Flapjack/Compiler/Backend/Semantics/WordSem/EnvListSupport.lean` (`env_to_list_lookup_equiv`, over the exact `wordSemEnvToList` result and Spt lookup carriers); `Flapjack/Compiler/Backend/Semantics/WordSem/Props/` (`EvaluateAddClock.lean` clock-constancy lemmas and `evaluate_add_clock`, `EvaluateDecClock.lean` `evaluate_dec_clock`, `LocalsRel.lean` locals_rel family through `locals_rel_evaluate_thm`, `StateConst.lean` the `*_const`/`*_with_const` state-constancy group, `CodeOnlyGrows.lean` `evaluate_code_only_grows` and `evaluate_NONE_stack_size_const`) |
| `compiler/backend/semantics/stackPropsScript.sml` | `Flapjack/Compiler/Backend/StackProps.lean` (recursive `stack_asm_ok` clauses and `addr_ok`, linked to the `asm_config` predicates; `StackProps/EvaluateAddClock.lean` and `StackProps/EvaluateConsts.lean` prove `evaluate_add_clock` and `evaluate_consts` over the exact StackSem evaluator; `StackProps/CallArgs.lean` `call_args_def`) |
| `compiler/backend/semantics/backendPropsScript.sml` | `Flapjack/Compiler/Backend/BackendProps.lean` and `Flapjack/Compiler/Backend/BackendProps/` (label restrictions, set support, and pure compiler/oracle operations) |
| `compiler/backend/semantics/stackSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/StackSem/State.lean` (exact state/result carriers and canonical finite-support state roundtrip), `StackSem/StateOps.lean` (memory/register/clock primitives), `StackSem/Control.lean` (code lookup and clock clamp/bound), `StackSem/Bitmap.lean` (polymorphic bitmap filter/map and length theorems), `StackSem/WordBitmap.lean` (word bit length and bitmap decoding), `StackSem/StackCodec.lean` (descriptor and recursive stack codecs), `StackSem/Evaluate.lean` (assembled total evaluator), `StackSem/EvaluateDef.lean` (`evaluate` and the 34-clause `evaluate_def`), `StackSem/Semantics.lean` (observational `semantics_def`) |
| `compiler/encoders/asm/asmScript.sml` | `Flapjack/Compiler/Encoders/Asm.lean` (asm_config validity predicates: `reg_ok`, `fp_reg_ok`, `reg_imm_ok`, `offset_ok`, `arith_ok`, `fp_ok`, `cmp_ok`, `inst_ok`; exact carriers `reg_imm`, `addr`, `inst`, `arith`, `fp`, `binop`, `cmp`, `memop`, `asm`) |
| `compiler/encoders/asm/asmSemScript.sml` | `Flapjack/Compiler/Encoders/AsmSem/` (`State.lean` asm_state, `Arithmetic.lean` register/arith updates, `FpUpdates.lean` fp_upd, `Memory.lean` addr/read_mem_word/write_mem_word, `MemOps.lean` mem_load/mem_store/mem_op, `Step.lean` inst/jump_to_offset/asm/asm_step) |
| `compiler/encoders/asm/asmPropsScript.sml` | `Flapjack/Compiler/Encoders/AsmProps/` (`Target.lean` target carrier and target_state_rel, `Encoding.lean` enc_ok/target_ok, `Interference.lean`, `Assertions.lean` asserts/asserts2, `PcCoverage.lean` all_pcs, `Memory.lean` memory-word invariants, `EncoderCorrect.lean` encoder_correct) |
| `compiler/backend/labLangScript.sml` | `Flapjack/Compiler/Backend/LabLang.lean` (generic HOL `lab`, `line`, and `sec` syntax) |
| `compiler/backend/lab_to_targetScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`cbw_to_asm` carrier boundary only; target encoding remains open), `Flapjack/Compiler/Backend/LabToTarget/` (exact encoding/labels/positions/second-pass/padding/remove-labels/shmem-info and the `config`/`compile_lab`/`compile` entry) |
| `compiler/backend/lab_filterScript.sml` | `Flapjack/Compiler/Backend/LabFilter.lean` |
| `misc/miscScript.sml` (`list_subset`) | `Flapjack/Misc/ListSubset.lean` |
| `compiler/backend/proofs/lab_filterProofScript.sml` | `Flapjack/Compiler/Backend/LabFilter/Proofs.lean` (submodules in `LabFilter/Proofs/`) |
| `compiler/backend/proofs/lab_to_targetProofScript.sml` | `Flapjack/Compiler/Backend/LabToTarget/` (code similarity and structural preservation; `ShareMemDomain.lean` share_mem_domain_code_rel, `ShareMemState.lean` share_mem_state_rel) |
| `compiler/backend/proofs/backendProofScript.sml` | `Flapjack/Compiler/Backend/BackendProof/` (`MachineInit.lean`, `WordToStackSfs.lean`, `CompileLab.lean`, `ConfigOk.lean`, and `ReadLimits.lean`) |
| `compiler/backend/proofs/data_to_wordProofScript.sml` | `Flapjack/Compiler/Backend/DataToWord/Proofs/` (`OptionLe.lean`; `Gc/` for the gc section) |
| `compiler/backend/semantics/labPropsScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`line_ok_pre`, `sec_ok_pre`, and `all_enc_ok_pre`; asm/config carrier bridge remains explicit) |
| `compiler/backend/semantics/labPropsScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`line_ok_pre`, `sec_ok_pre`, and `all_enc_ok_pre`; asm/config carrier bridge remains explicit) |
| `compiler/backend/semantics/labSemScript.sml` | `Flapjack/Compiler/Backend/LabSem.lean` (`is_Label`) |
| `semantics/astScript.sml` | `Flapjack/AstHOL.lean` (exact `ast$shift`, `opb`), `Flapjack/AstHOL/BackendOperators.lean` (`word_size`, `thunk_mode`, `thunk_op`, `test`), `Flapjack/AstHOL/LitOp.lean` (`lit`, `arith`, name abbreviations, `prim_type`, `op`, `op_class`, `getOpClass_def`, `lop`), `Flapjack/AstHOL/Syntax.lean` (`ast_t`, `pat`, `exp`, `type_def`, `dec`, `pat_bindings_def`, `every_exp_def`) |
| `semantics/gramScript.sml` | `Flapjack/CakeParser/Grammar.lean`, `Flapjack/CakeParser/CfgGrammarCore.lean`, and `Flapjack/CakeParser/CfgGrammar.lean` (operator classes and grammar patterns generated from pinned HOL capture). `CfgValidation.lean` and `CfgLocation.lean` prove Flapjack's executable checks agree with generic grammar and location validity; full grammar and PEG correspondence remain open. |
| `semantics/typeSystemScript.sml` | `Flapjack/TypeSystemHOL.lean` and `Flapjack/TypeSystemHOL/Environments.lean`, `Flapjack/TypeSystemHOL/TypeNames.lean`, and `Flapjack/TypeSystemHOL/Patterns.lean`, `Flapjack/TypeSystemHOL/Operators.lean` and `Flapjack/TypeSystemHOL/Expressions.lean`, `Flapjack/TypeSystemHOL/Values.lean`, and `Flapjack/TypeSystemHOL/Declarations.lean` (type carrier, environments, pattern and operator typing; expression and declaration encodings and source review remain open) |
| `HOL/examples/formal-languages/context-free/grammarScript.sml` | `Flapjack/Misc/Grammar.lean` (generic parse trees, grammar and validity; CakeML grammar correspondence remains open) |
| `HOL/examples/formal-languages/context-free/locationScript.sml` | `Flapjack/Misc/Location.lean` and `Flapjack/Misc/Location/Merge.lean` (source positions and location merging) |
| `semantics/semanticsScript.sml` | `Flapjack/SemanticsHOL.lean` and `Flapjack/SemanticsHOL/Typed.lean` (clock-indexed behavior, source state and post-parse semantics; original parser relation and source initialization remain open) |
| `semantics/semanticPrimitivesScript.sml` | `Flapjack/SemanticPrimitivesHOL.lean` and its `PatternMatch`, `Operations`, `Conversions`, `Thunk`, `EvalState`, `Concrete`, `Eval`, `Control`, `Array`, `Primitives`, `Compare`, `Test`, `Apply`, and `ApplyNumeric` submodules (source values, evaluator state, pattern matching, primitive helpers, a source application dispatcher pending complete review, and proof-side dynamic Eval; statement review pending) |
| `semantics/proofs/semanticPrimitivesPropsScript.sml` | `Flapjack/SemanticPrimitivesProps/` (store-entry relation; correspondence review pending) |
| `semantics/evaluateScript.sml` | `Flapjack/EvaluateHOL.lean` and its `Definition`, `Measure`, `Clock`, and `ClockFull` submodules (clock and result helpers and the mutually recursive evaluator; full source and carrier review pending) |
| `semantics/namespaceScript.sml` | `Flapjack/NamespaceHOL.lean` (`alist`, `namespace`, `id` and every namespace operation of lines 14-117) |
| `semantics/primTypesScript.sml` | `Flapjack/PrimTypesHOL.lean` and `Flapjack/PrimTypesHOL/Types.lean` (primitive declaration program, semantic initialization and declarative type environment; source and carrier review pending) |
| `compiler/backend/stack_namesScript.sml` | `Flapjack/Compiler/Backend/StackNames.lean` |
| `compiler/backend/proofs/stack_namesProofScript.sml` | `Flapjack/Compiler/Backend/StackNames/` (`NamesOk.lean` names_ok lemmas, `AsmAdmissibility/` stack_asm_ok, `Proofs/RenameState.lean` rename_state group over the MAP_KEYS rendering in `Flapjack/FiniteMap/MapKeys.lean`, `Proofs/CompCorrect.lean` comp_correct, `Proofs/CompileSemantics.lean` compile_semantics(_alt), `Proofs/MakeInit.lean` make_init_def/make_init_semantics, `Proofs/LabelsCallArgs.lean` stack_names_lab_pres/stack_names_call_args) |
| `compiler/backend/riscv/export_riscvScript.sml` | `Flapjack/RiscV/CakeArtifactFormat.lean` and `Flapjack/RiscV/ArtifactFormat.lean` (Flapjack formatting infrastructure; returning and non-returning outputs tested against the pinned HOL exporter, source correspondence remains pending) |
| `compiler/backend/riscv/riscv_configScript.sml` | `Flapjack/Compiler/Backend/RiscVConfig/Names.lean` (submodules in `RiscVConfig/`, e.g. `BackendConfig.lean`) |
| `compiler/compilerScript.sml` | `Flapjack/Compiler/Compiler.lean` (`pancake_backend_conf_def`; the GC-free RISC-V `backend_config_ok` corollary is untagged in `Flapjack/Compiler/Backend/RiscVConfig/PancakeConfigOk.lean`) |
| `compiler/backend/riscv/proofs/riscv_configProofScript.sml` | `Flapjack/Compiler/Backend/RiscVConfig/Proofs.lean` |
| `compiler/backend/mips/mips_configScript.sml` | `Flapjack/Compiler/Backend/Mips32Config/Names.lean` (`mips_names_def` only; the MIPS32 backend configuration, its proofs and the MIPS32 target are Flapjack-specific, see `docs/MIPS32.md`) |
| `compiler/encoders/arm8/arm8_targetScript.sml` | `Flapjack/Compiler/Encoders/Arm8/Target.lean` (`arm8_ast`/`arm8_enc` for the emitted instruction subset), `Flapjack/Compiler/Encoders/Arm8/Encode.lean` (instruction encodings and `EncodeBitMask`), `Flapjack/Compiler/Encoders/Arm8/Configuration.lean`; see `docs/ARM8.md` |
| `HOL/examples/l3-machine-code/arm8/model/arm8Script.sml` | `Flapjack/Compiler/Encoders/Arm8/Encode.lean` (`ShiftType` and `MoveWideOp` L3 datatype ports); the remaining machine model is Flapjack-specific, see `docs/ARM8.md` |
| `compiler/backend/arm8/arm8_configScript.sml` | `Flapjack/Compiler/Backend/Arm8Config/Names.lean` (`arm8_names_def`) and `Flapjack/Compiler/Backend/Arm8Config/BackendConfig.lean` (Flapjack-specific full configuration) |
| `compiler/backend/arm8/export_arm8Script.sml` | `Flapjack/Arm8/NativeCLIAdapter.lean` (Pancake `ret = F`, `pk = T` assembly frame) |
| `compiler/encoders/arm8/proofs/arm8_targetProofScript.sml` | `Flapjack/Compiler/Encoders/Arm8/TargetProof.lean` (structural length lemmas only; `arm8_encoder_correct` is not ported) and `Flapjack/Compiler/Encoders/Arm8/Machine/` (Flapjack-specific closed ARMv8 machine model with `arm8EncoderCorrect`; its decoder/executor are not ports of `arm8Script.sml`, unlike the `ShiftType`/`MoveWideOp` types above) |
| `compiler/backend/stackLangScript.sml` (shared-word `prog`) | `Flapjack/Compiler/Backend/StackCarrier.lean` |
| `compiler/backend/stack_removeScript.sml` | `Flapjack/Compiler/Backend/StackRemove.lean` (`max_stack_alloc`, `word_offset`, `store_list`, `store_length`, `stack_err_lab`, `halt_inst`; also the tagged stackLang instruction overloads `left_shift_inst`/`right_shift_inst`/`const_inst`/`load_inst`/`store_inst` over the exact `HolProg` carrier) |
| `compiler/backend/proofs/stack_removeProofScript.sml` | `Flapjack/Compiler/Backend/StackRemove.lean` (`is_SOME_Word`, `read_mem`/`LENGTH_read_mem`, `addresses`/`IN_addresses`; `names_ok` Prop-shaped tag); full native code relation in `Flapjack/Compiler/Backend/StackRemove/Proofs/CodeRelation.lean` |
| `HOL/examples/machine-code/hoare-triple/set_sepScript.sml` | `Flapjack/Misc/SetSep.lean` (generic paired function graph and heap predicates) |
| `compiler/backend/proofs/stack_allocProofScript.sml` | `Flapjack/Compiler/Backend/StackAlloc/Proofs/` (`WordLemmas.lean` word/bit-length lemmas, `Bitmap.lean` bitmap list lemmas and `enc_dec_stack`, `GcBitmaps.lean` proof-side GC definitions, `Unroll.lean` bitmap-collector unrolling theorems, `Submap.lean` SUBMAP lemmas, `CodeThm/` GC code simulation theorems) |
| `compiler/backend/stack_allocScript.sml` | `Flapjack/Compiler/Backend/StackAlloc.lean` (generic `next_lab`; executable pass counterpart remains `Flapjack/StackAlloc.lean`); `StackAlloc/GcCode.lean` (GC stub code); `StackAlloc/Compile.lean` (`next_lab`, `comp`, `prog_comp`, `stubs`, `compile` over `HolProg`) |
| `compiler/backend/stack_to_labScript.sml` | `Flapjack/Compiler/Backend/StackToLab.lean`, `Flapjack/Compiler/Backend/StackToLab/Native.lean` (`flatten`, `prog_to_section`), `Flapjack/Compiler/Backend/StackToLab/Compile.lean` (`is_gen_gc`, `config`, `compile`, `compile_no_stubs`) |
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
| `pan_to_wordScript.sml` | `Flapjack/Pancake/PanToWord.lean` |
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
| `proofs/loop_to_wordProofScript.sml` | `Flapjack/Pancake/Proofs/LoopToWord/` (`EveryInstOkLess.lean`: `loop_inst_ok_def` and the `every_inst_ok_less` section, lines 2285-2380; other sections in sibling modules) |
| `loop_to_wordScript.sml` | `Flapjack/Pancake/LoopToWord.lean` |
| `semantics/panSemScript.sml` | `Flapjack/PanBst.lean`, `Flapjack/PanValueFfiClockSemantics.lean`, `Flapjack/Pancake/Semantics/PanSem.lean`, `PanSem/Primop.lean`, `PanSem/ValueHOL.lean`, `PanSem/MemLoadHOL.lean`, `PanSemStateEval.lean`, `PanSem/Semantics.lean` (exact `semantics_def` over `evaluateHOLFiniteState`) |
| `semantics/pan_commonPropsScript.sml` | `Flapjack/Pancake/Semantics/PanCommonProps.lean` |
| `pan_commonScript.sml` | `Flapjack/Pancake/PanCommon.lean` |
| `misc/miscScript.sml` (`app_list`/`append`) | `Flapjack/Misc/AppList.lean` |
| `misc/miscScript.sml` (`good_dimindex`) | `Flapjack/Misc/GoodDimindex.lean` (exact `good_dimindex` predicate) |
| `misc/miscScript.sml` (`fun2set_disjoint_union`) | `Flapjack/Misc/Fun2SetUnion.lean` |
| `misc/miscScript.sml` (`UPDATE_LIST`/`=++`, `APPLY_UPDATE_LIST_ALOOKUP`) | `Flapjack/Misc/UpdateList.lean` |
| `misc/miscScript.sml` (`MOD_SUB_LEMMA`, `IMP_MULT_DIV_LESS`, `DIV_LESS_DIV`) | `Flapjack/Misc/DivModLemmas.lean` |
| `misc/miscScript.sml` (`DISJOINT_INTER`) | `Flapjack/Misc/DisjointInter.lean` |
| `misc/miscScript.sml` (`WORD_LS_IMP`) | `Flapjack/Misc/WordLsImp.lean` |
| `compiler/backend/proofs/data_to_word_gcProofScript.sml` | `Flapjack/Compiler/Backend/DataToWord/Proofs/Gc/` (`WordLemmas.lean` opening word lemmas: `lsr_lsl`; `InitStoreOk.lean`, `GcFunOk.lean`, `GcFunConstOk.lean`) |
| `semantics/panPropsScript.sml` | `Flapjack/Pancake/Semantics/PanProps.lean`, `PanProps/EvalInvariant.lean`, `PanProps/MemByteArray.lean` (exact `write_bytearray_update_byte` / `read_write_bytearray_lemma`), `PanProps/LocalisedExpSimps.lean`, `PanProps/NamelessExpSimps.lean`, `PanProps/EvaluateAddClockIoEventsMono.lean` |
| `semantics/crepSemScript.sml` | `Flapjack/Pancake/Semantics/CrepSem.lean`, `CrepSem/Eval.lean`, `CrepSem/TotalEval.lean`, `CrepSem/Primop.lean`, `CrepSem/LookupCode.lean` |
| `semantics/crepPropsScript.sml` | `Flapjack/Pancake/Semantics/CrepProps.lean` |
| `semantics/loopSemScript.sml` | `Flapjack/Pancake/Semantics/LoopSem.lean`; exact width-indexed `state` carrier + production bridge in `Flapjack/Pancake/Semantics/LoopSemState.lean` (untagged pending exact sub-carriers) |
| `semantics/ffi/ffiScript.sml` | `Flapjack/Ffi.lean` (production FFI state/events), `Flapjack/FfiHOL.lean` (exact ffi_outcome/oracle_result/shmem_op/ffiname/oracle/oracle_function/io_event/final_event/ffi_state/ffi_result carriers + call_FFI) |
| `semantics/fpSemScript.sml` | `Flapjack/FpSemHOL.lean` (tagged `fpfma_def`, over the HOL `binary_ieee`/`machine_ieee` renderings in `Flapjack/Misc/BinaryIeee*.lean` and `Flapjack/Misc/MachineIeee*.lean`) |
| `semantics/proofs/evaluatePropsScript.sml` | `Flapjack/EvaluateProps.lean`, `Flapjack/EvaluateProps/Declarations.lean` (declaration head and append equations), `Flapjack/EvaluateProps/DoApp.lean`, `Flapjack/EvaluateProps/EvaluateFfi.lean`, `Flapjack/EvaluateProps/EvaluateFfiFull.lean`, `Flapjack/EvaluateProps/ClockIo.lean`, `Flapjack/EvaluateProps/ClockIoBind.lean`, `Flapjack/EvaluateProps/PrimitiveLength.lean`, `Flapjack/EvaluateProps/Length.lean` (untagged successful expression and match result lengths), `Flapjack/EvaluateProps/ClockIoSafe.lean`, `Flapjack/EvaluateProps/ClockIoCases.lean`, `Flapjack/EvaluateProps/ClockIoDecs.lean`, `Flapjack/EvaluateProps/ClockIoExpr.lean`, `Flapjack/EvaluateProps/ClockIoApp.lean`, `Flapjack/EvaluateProps/ClockIoFull.lean`, and `Flapjack/EvaluateProps/ClockIoConsequences.lean` (FFI call relation, evaluator trace monotonicity, and clock-I/O invariant; source and carrier review pending) |
| `semantics/proofs/semanticsPropsScript.sml` | `Flapjack/SemanticsProps.lean` (structural behavior and `implements'` analogue; HOL `llist` representation bridge remains open), `Flapjack/SemanticsProps/Clock.lean`, `Flapjack/SemanticsProps/Determinism.lean`, and `Flapjack/SemanticsProps/Typed.lean` (clocked trace chain, source behavior totality, determinism and a post-parse singleton property; source and carrier review pending) |
| `proofs/pan_simpProofScript.sml` | `Flapjack/Pancake/Proofs/PanSimp.lean`, `PanSimp/Evaluate.lean` |
| `proofs/pan_to_wordProofScript.sml` | `Flapjack/Pancake/Proofs/PanToWord.lean` (submodules in `Pancake/Proofs/PanToWord/`, e.g. `EveryInstOkLess.lean` for the `inst_ok_less` section) |

Placement under `Proofs` does not imply that a whole pass correctness theorem
has been established. For declaration-level provenance, use
`scripts/check-hol-refs.py --mapping`; CI validates the review inventory with
`scripts/check_hol_theorem_map.py`. For untagged port candidates, use
`scripts/next-hol-port.py`. Track individual gaps and progress in
[GitHub issues](https://github.com/pirapira/flapjack/issues), not in this
layout guide.
| compiler/backend/reg_alloc/reg_allocScript.sml | Flapjack/Compiler/Backend/RegAlloc.lean |
| compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml | Flapjack/Compiler/Backend/RegAlloc/Proofs.lean |
| compiler/backend/reg_alloc/linear_scanScript.sml | Flapjack/Compiler/Backend/LinearScan.lean |
| compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml | Flapjack/Compiler/Backend/LinearScan/Proofs.lean |
| translator/monadic/monad_base/ml_monadBaseScript.sml | Flapjack/Translator/Monadic/MonadBase.lean (fixed arrays in `MonadBase/Arrays.lean`) |
| `misc/miscScript.sml` (`the`) | `Flapjack/Misc/MiscThe.lean` |
| `misc/miscScript.sml` (`LLOOKUP` optional indexing and list-update laws) | `Flapjack/Misc/ListLookup.lean` |

The pinned external `hol4/src/coretypes/optionScript.sml` counterpart is
`Flapjack/Misc/Option.lean`.

The pinned external `hol4/src/coalgebras/llistScript.sml` counterpart is
`Flapjack/Misc/LList.lean`; `lprefix_lubScript.sml` chain and least-upper-bound
declarations remain in `Flapjack/Misc/LprefixLub.lean`.

The pinned external `HOL/src/n-bit/byteScript.sml` counterpart is
`Flapjack/Byte.lean` (byte extraction and arbitrary-count word serialization).

The pinned external `HOL/examples/formal-languages/context-free/locationScript.sml` counterpart is
`Flapjack/Misc/Location.lean` (`locn`, `locs`, `default_loc`, `start_locs`, `unknown_loc`).

The pinned external `HOL/examples/machine-code/hoare-triple/addressScript.sml` counterpart is
`Flapjack/Misc/Address.lean` (`word_arith_lemma2`).

The pinned external `HOL/src/n-bit/alignmentScript.sml` counterpart is
`Flapjack/Misc/Alignment.lean` (`align`, `aligned`, `byte_align`, `byte_aligned`, `aligned_add_sub`, and
`wordsScript.sml`'s `word_slice`), with production bridges in `Flapjack/Misc/Alignment/Production.lean`.

The pinned external `HOL/examples/l3-machine-code/riscv/model/riscvScript.sml` (the L3-generated
RISC-V model) counterpart is `Flapjack/RiscV/L3/` (`Types.lean`: every `Construct`/`Record`
datatype and the `riscv_state` record; `Defs.lean`: the selected complete
FP/state equations and their source dependency closure; `Support.lean`:
library-rendering infrastructure sharing the canonical `Flapjack.holArb`).
The full original dependency export is reproduced by
`scripts/l3/regenerate-export.sh` from the pinned HOL. Generator self-consistency
checks are distinct from source review and the finite original HOL probes.

The pinned external `HOL/src/pred_set/src/pred_setScript.sml` counterpart is
`Flapjack/Misc/PredSet.lean` (the left inverse `LINV_OPT`/`LINV`, sets as predicates).

The pinned external `HOL/src/num/extra_theories/logrootScript.sml` counterpart is
`Flapjack/Misc/Logroot.lean` (the specified `LOG`, rendered by Hilbert choice like HOL's
`new_specification`), and `HOL/src/num/extra_theories/bitScript.sml`'s is `Flapjack/Misc/Bit.lean`
(`LOG2`).

The pinned external `hol4/src/finite_maps/sptreeScript.sml` counterpart is
`Flapjack/Misc/Sptree.lean` with submodules under `Flapjack/Misc/Sptree/` (for example
`Map.lean` for `map_def`/`lookup_map` and `InterEq.lean` for `inter_eq_def`).

The pinned external `HOL/src/sort/mergesortScript.sml` counterpart is
`Flapjack/Misc/Mergesort.lean` (the non-tail `sort2`/`sort3`/`merge`/`mergesortN`, their
sortedness, and the tail-recursive correctness lemmas over the untagged tail rendering in
`Flapjack/Basis/Pure/MlList.lean`).

The pinned external `HOL/src/floating-point/binary_ieeeScript.sml` counterpart is
`Flapjack/Misc/BinaryIeee.lean` with its rendering family `BinaryIeeeRound.lean`,
`BinaryIeeeArith.lean`, `BinaryIeeeConvert.lean` and `BinaryIeeeSqrt.lean`; the
arbitrary-real (Mathlib `ℝ`) ports of its real-argument declarations are in
`Flapjack/Misc/BinaryIeeeSqrt/RealCarrier.lean`. `HOL/src/floating-point/machine_ieeeScript.sml`,
including the declarations `machine_ieeeLib` generates at its fp32/fp64 encoding calls,
maps to `Flapjack/Misc/MachineIeee.lean` with submodules `Arith.lean`, `Convert.lean`,
`ConvertInt.lean`, `ConvertReal.lean` and `SqrtReal.lean` under `Flapjack/Misc/MachineIeee/`.


### Computed finite-map result observations

`(fmap_as_finite_support_result_observations := [Producer, ...])` records
only the canonical finite-support representation of explicitly named imported
map producers used in a tagged declaration's type. Each producer must return
`HolFiniteMapExact`, carry the standalone result qualifier, have its checked
same-module lookup witness, and have a source-reviewed result manifest record.
The observer has its own `reviewed_fmap_as_finite_support_result_observations`
record with exactly the same producer list and a complete source comparison.
Producer acceptance does not establish observer acceptance. The checker rejects
unused, ambiguous, shadowed, unqualified, unreviewed, non-map, and unwitnessed
producers. This narrow qualifier cannot combine with other representations and
permits no changed quantifiers, hypotheses, evaluator, or conclusion. The
syntactic checks and kernel witnesses do not prove cross-language equivalence;
the complete observer still requires manual HOL source comparison.

The pinned `HOL/src/monad/more_monads/state_transformerScript.sml` iteration counterpart is `Flapjack/Misc/StateTransformer.lean` (`FOR_def`).

`Flapjack/Misc/Words/Replicate.lean` is the `word_replicate_def` group counterpart of pinned `HOL/src/n-bit/wordsScript.sml`.

Pinned `HOL/src/list/src/numposrepScript.sml` digit conversion maps to `Flapjack/Misc/Numposrep.lean`; `HOL/src/string/ASCIInumbersScript.sml` character conversion maps to `Flapjack/Misc/ASCIInumbers.lean`; wordsScript `w2s_def`/`word_to_hex_string_def` map to `Flapjack/Misc/Words/Formatting.lean`.

The riscvScript MMU exception group counterpart is `Flapjack/RiscV/L3/Defs/MMU/Exception.lean`; `Nonempty` records HOL type variables intrinsic nonempty kind, as in the reviewed HD/EL/THE/LINV counterparts.

The primary counterpart of `cakeml/compiler/encoders/riscv/riscv_targetScript.sml`
is `Flapjack/Compiler/Encoders/RiscV/Target.lean`. Its native RISC-V instruction
carrier and Encode body are in the original L3 model counterpart under
`Flapjack/RiscV/L3/`; the exact assembly carrier is in
`Flapjack/Compiler/Encoders/Asm.lean`.
