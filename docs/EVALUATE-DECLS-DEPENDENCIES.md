# Dependency inventory: `evaluateDecls` (source declaration evaluator)

Beads: `flapjack-pxn.18.3.6.1` (direct dependency inventory) and
`flapjack-pxn.18.3.6` (transitive dependency audit).
Scope: the **direct** production calls and datatypes reachable from production
`evaluateDecls`, paired with their HOL definitions, plus the HOL-defined calls
traced one layer deep. This is a review-frontier triage, not a proof: it records
what is tagged `reviewed_exact`, what is unreviewed (and thus a *possible*
mismatch until clause-by-clause evidence exists), a representation refinement,
or a confirmed mismatch, and links a child bead for every remaining node. A
classification of "unreviewed" does **not** assert exactness — it only means no
review has been done yet.

## Root

| Lean | HOL | Status |
| --- | --- | --- |
| `Flapjack.evaluateDecls` (`Flapjack/Pancake/Semantics/PanSem.lean:2914`) | `evaluate_decls_def` (`cakeml/pancake/semantics/panSemScript.sml:813`) | production analogue, **not an exact port and untagged**: generic `Decl α`, `PanSemDeclarationState`, String/`InfoMap` carriers, production `evalPanValueExp` and `isWfShape` |
| `PanSemStateFiniteExact.evaluateDeclsHOLFinite` (`Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean:1616`) | `evaluate_decls_def` (`panSemScript.sml:813`) | separate exact finite-support port, tagged with `fmap_as_finite_support := [locals, globals, code, eshapes]`; production does not textually call it |

The production definition has analogous `Name`, `Decl`, `Function`, and
`ExnDecl` branches, but matching branch names do not establish a port. HOL uses
the exact `panSem$state`, `DeclHOL` over `MlString` names, finite maps, and
`eval` over the HOL value/state carriers. Production uses generic `Decl α`, a
split `PanSemDeclarationState` with String-keyed association-list `InfoMap`s,
the production expression evaluator, and Bool shape comparison. A separate
kernel-checked finite-support definition carries the `evaluate_decls_def` tag.
There is now a conditional semantic bridge,
`PanSemEntryState.evaluateDecls_agree` (`PanSem/EntryState.lean:197`), between
the production evaluator and that exact evaluator. It is for fixed
`Word 64`, byte-ranged production declarations mapped through `declToHOL`, and
an initial `PanSemDeclEntryRel` state. That relation requires
`PanSemStateRelExec`, its ranged companion, and the canonical production
memory-access and bytes-per-word settings. The result relates both failure
and success; on success it preserves the corresponding entry-state relation.
Its source-level consumer is `panSemRunEntryCake_agree`
(`PanSem/EntryState.lean:492`), which composes declaration correspondence
with exact/production entry-call agreement and additionally assumes the
initial code and exception-shape maps are byte-ranged.
The theorem is a correspondence proof, not textual routing of the production
body through `evaluateDeclsHOLFinite`, and it does not establish an
unconditional result for arbitrary `String` names, `Decl α`, or `InfoMap`
states. The route/bridge slice `flapjack-pxn.18.3.6.10` is recorded closed;
the parent audit remains open for remaining dependency reviews and explicit
representation limits.

The remaining limits are tracked rather than silently accepted: the generic
`Exp α` production datatype does not itself encode HOL's width-indexed word
payload (`flapjack-pxn.18.3.5.3.1`), and generic `[BEq]` helper APIs do not
establish HOL key equality without lawfulness (`flapjack-pxn.18.5.5.19`). The
conditional theorem above does not remove either carrier/side-condition
boundary for arbitrary production inputs. Keep the evaluator and its generic
dependencies untagged unless a specific exact statement and carrier review
justifies a tag.

2026-09-28 refresh: production `evaluateDecls` is at line 2914 and the exact
finite-support definition is at line 1616. Source review of
`PanSemEntryState.evaluateDecls_agree` confirmed the premise-limited bridge
above. It does not make the generic String/`InfoMap` production definition an
exact HOL declaration or justify an unconditional production-routing claim.
The direct dependencies below describe the production function unless
explicitly marked as proof-side exact infrastructure.

2026-09-26 refresh: the earlier root row incorrectly called the String-backed
production `evaluateDecls` exact/tagged. The corrected classification above
distinguishes it from `evaluateDeclsHOLFinite`. The direct dependencies below
describe the production function unless explicitly marked as proof-side exact
infrastructure.

## Direct dependencies

| Dependency | Lean (file:line) | HOL counterpart | Classification | Bead |
| --- | --- | --- | --- | --- |
| `evalPanValueExp` (production) | `Flapjack/PanValues.lean:1470` | `eval_def` (`panSemScript.sml:209`) | **reviewed, not exact** (pure/value subset follows `eval_def`; production struct/memory/Op path and projected state differ as detailed in `.18.3.6.2`). An exact finite-support `evalHOLFinite`/`evalHOLExact` port exists separately; its use is bridged only under the explicit premises of `evaluateDecls_agree`, while the production body is not routed through that definition | `.18.3.6.2`, `.18.3.6.9`; conditional bridge `.18.3.6.10` |
| `isWfShape` (production) | `Flapjack/Pancake/PanStatic.lean:140` | `is_wf_shape_def` (`panLangScript.sml:139`) | production String/`StructContext` predicate remains distinct from exact `isWfShapeHOL`; do not infer production use from the proof-side port. StructInfo fields and name equality differ; see `.18.3.6.3` and the exact Shape carrier bead | `.18.3.6.7`; production route `.18.3.6.10` |
| `panValueShape` | `Flapjack/PanValues.lean:530` | `shape_of_def` (`panSemScript.sml:80`) | **exact in content**: unused `context` parameter, but proved equal to the tagged `panSemShapeOf` by `panValueShape_eq_panSemShapeOf_tagged` (`PanSem.lean:63`); kept untagged (extra parameter) | `.18.3.6.4` |
| `panShapeMatches` | `Flapjack/PanValues.lean:1123` | HOL `=` on `Shape` (`sh = shape_of res`) | **representation**: structural `Bool` using `==` for `Named`; `panShapeMatches_eq_true` justifies equality under `[LawfulBEq String]`, but production key carrier remains String | `.18.3.6.4`, conditional bridge `.18.3.6.10` |
| `lookupInfo` | `Flapjack/Pancake/PanLang.lean:126` | `alist$ALOOKUP` / `FLOOKUP` | **exact in content under lawful keys**: key-polymorphic first-match lookup; `==` reflects HOL `=` under `[LawfulBEq κ]` (equals core `List.lookup`, `lookupInfo_eq_lookup`). Untagged because the HOL source (`alistTheory`) is HOL stdlib outside the cakeml submodule and the def quantifies `[BEq κ]`; tagged `ALOOKUP_MAP3`/`ALOOKUP_MAP4` ports exist | `.18.3.6.5` |
| `panSemDeclUpdateGlobal` | `Flapjack/Pancake/Semantics/PanSem.lean:2813` | `globals |+ (v,res)` (`FUPDATE` on a finite map) | **exact in content**: `panSemDeclUpdateGlobal_eq_FUPDATE` proves it equals the repo `FUPDATE` on the finite-map view (`VarName → Option (PanValue α)`) under `[LawfulBEq String]`. Untagged (HOL `finite_mapTheory` is stdlib; repo `FUPDATE` quantifies `[BEq α]`) | `.18.3.6.5` (+ key-equality gap `.18.5.5.19`) |
| `panSemDeclUpdateInfo` | `Flapjack/Pancake/Semantics/PanSem.lean:2800` | `code |+ ...` / `eshapes |+ ...` (sptree update) | **representation-refined**: association list (with duplicate removal) vs finite map; `lookupInfo_panSemDeclUpdateInfo` proves lookups after the update agree with `FUPDATE` of `fun k => lookupInfo k entries`; untagged (stdlib source + `[BEq String]`) | `.18.3.6.5` (+ key-equality gap `.18.5.5.19`) |
| `Decl` | `Flapjack/Pancake/PanLang.lean:425` | `panLang$decl` datatype | datatype | existing `.18.3.5.5` |
| `Shape` | `Flapjack/Pancake/PanLang.lean:71` | `panLang$shape` datatype | datatype | existing `.18.3.5.2` |
| `Exp` (inside `.decl`) | `Flapjack/Pancake/PanLang.lean:272` | `panLang$exp` datatype | datatype | existing `.18.3.5.3` |
| `Prog` (inside `.function`) | `Flapjack/Pancake/PanLang.lean:381` | `panLang$prog` datatype | datatype | existing `.18.3.5.4` |
| production word/value carriers | `Flapjack/PanValues.lean:48` | `word_lab` / `v` (`panSemScript.sml:17,22`) | production `PanValue.word` carries generic `α`, unlike HOL `Val (Word w)`; exact `HolWordLab`/`ValueHOL` carriers exist in the PanSem counterpart, but their existence does not prove the production codec for every constructor | `.18.3.6.8`; production bridge `.18.3.6.10` |
| `PanSemDeclarationState` | `Flapjack/Pancake/Semantics/PanSem.lean:262` | `panSem$state` record | production representation: split state with String-keyed `InfoMap` `code`/`eshapes`; not the exact `MlString` finite-map state. Conditional correspondence is `evaluateDecls_agree` in `PanSem/EntryState.lean`; arbitrary states are not covered | `.18.3.6.10` |
| `PanSemFunctionEntry` | `Flapjack/Pancake/Semantics/PanSem.lean:250` | `(params,(body,return))` tuple in the `code` map | representation: named record vs tuple | note (below) |

## One-layer frontier of HOL-defined calls

- `eval_def` (`panSemScript.sml:209`) — production `evalPanValueExp` was
  reviewed in `.18.3.6.2` and is not statement-exact (memory/struct clusters
  and the state projection differ). An exact finite-support `evalHOLFinite`
  port exists under `.18.3.6.9`; `evaluateDecls_agree` supplies a conditional
  whole-declaration correspondence under the bridge premises recorded above,
  but production execution is not routed through that exact definition. HOL
  `eval` calls:
  `OPT_MMAP` (Lean carrier `List.mapM`; tagged `optMmapEqSome` in
  `Flapjack/Pancake/Semantics/PanCommonProps.lean`), `shape_of` (tagged
  `panSemShapeOf`), `ALOOKUP` (`lookupInfo`, `.18.3.6.5`), `UNZIP`, `EVERY`,
  `LENGTH`, `EL`, and itself recursively on subexpressions. Its `NStruct` case
  additionally checks `field_names' = field_names` and
  `EVERY (\(s,v). s = shape_of v) (ZIP ...)`.
- `is_wf_shape_def` (`panLangScript.sml:139`) — reviewed in `.18.3.6.3`:
  production `isWfShape` clauses align, but it is not statement-exact (carrier
  plus `lookupInfo` equality); the exact HOL-shaped Shape-level port is tracked
  by `.18.3.6.7`. It calls `EVERY` and `ALOOKUP` (`lookupInfo`).
- `shape_of_def` (`panSemScript.sml:80`) — tagged exact as `panSemShapeOf`; the
  behavior used by `evaluateDecls` also flows through `panValueShape`
  (`panValueShape_eq_panSemShapeOf_tagged` proves it equal to the tagged port) and
  the untagged `panShapeMatches` Bool rendering of HOL shape equality
  (`.18.3.6.4`).
- `FLOOKUP`/`FUPDATE` on `code`, `eshapes`, `globals` — reviewed in
  `.18.3.6.5`: `panSemDeclUpdateGlobal_eq_FUPDATE` shows the `globals` update is
  the repo `FUPDATE`, and `lookupInfo_panSemDeclUpdateInfo` shows the assoc-list
  `code`/`eshapes` update agrees with `FUPDATE` on the finite-map view. The
  remaining key-equality gap (`=` vs `[BEq]`) is tracked by
  `flapjack-pxn.18.5.5.19`.

## Representation notes (terminal unless a child bead is listed)

- `PanSemDeclarationState` splits HOL `panSem$state` into a `runtime`
  (`structs`/`globals`/`memory`/…) plus `code`, `eshapes`, `memoryAccess`,
  `contracts`, `memoryHandler`. This is the production state shape used by the
  tracer/runtime; the source-field projections are reviewed as part of the
  `evaluateDecls` port but the record layout itself is a documented refinement,
  not an exact HOL datatype.
- `PanSemFunctionEntry` names the tuple stored in HOL's `code` map; the
  `code`/`eshapes` maps are association lists (`InfoMap`) rather than HOL
  `num_map`/finite maps.
- External primitives reachable through `eval` (word ops, `PanCmp`, shifts,
  `AndOp`/`OrOp`/`HXor`) are the assumed typeclass operations; they are leaves
  of this review and are not re-audited here.

## Child beads (parent `flapjack-pxn.18.3.6`)

- `.18.3.6.2` — cluster review of the production expression evaluator against HOL `eval_def`: pure/value clusters match (direct HOL rows), memory (`Load`/`Load32`/`LoadByte`) and struct (`NStruct`/`NField`) plus `Op` clusters and the state projection differ, so no exact tag; faithful port tracked by `.18.3.6.9`.
- `.18.3.6.9` — port the exact HOL-shaped `eval_def` expression evaluator (HOL state projection, `ALOOKUP`/`UNZIP`/`EVERY` struct clauses, and the `memaddrs`/`be`/byte-width memory codec) so an exact tag can be attached.
- `.18.3.6.3` — reviewed the production `Shape` predicate against HOL `is_wf_shape_def`: clauses align, but not statement-exact (carrier/equality); exact port tracked by `.18.3.6.7`.
- `.18.3.6.7` — port the exact HOL-shaped `is_wf_shape_def` Shape-level predicate over `StructContextHOL`.
- `.18.3.6.4` — aligned `evaluateDecls` shape comparison with the tagged `panSemShapeOf`: added the proved equality `panValueShape_eq_panSemShapeOf_tagged` (unused-context twin) and documented `panShapeMatches` as the untagged Bool rendering of HOL shape equality (lawful-String caveat).
- `.18.3.6.5` — reviewed the finite-map lookup/update helpers: `lookupInfo` is exact content under `[LawfulBEq κ]` (equals `List.lookup`); `panSemDeclUpdateGlobal_eq_FUPDATE` proves `panSemDeclUpdateGlobal` is the repo `FUPDATE`; `lookupInfo_panSemDeclUpdateInfo` proves the assoc-list `code`/`eshapes` update agrees with `FUPDATE` on the finite-map view. All untagged (HOL sources are stdlib; `[BEq]` vs `=` gap tracked by `.18.5.5.19`).
- `.18.3.6.6` — reviewed the value datatype: `PanValue` corresponds to HOL `v` (not `word_lab`) and is not statement-exact (first constructor stores `α` rather than `'a word_lab`); `PanWordLab` is the exact `word_lab` counterpart but is untagged for placement reasons; exact port tracked by `.18.3.6.8`.
- `.18.3.6.8` — port the exact HOL `word_lab`/`v` datatypes (or prove a representation equivalence) so an exact Datatype tag can be attached in a `panSemScript.sml` counterpart file.
- `.18.3.6.10` — **closed with a conditional bridge**: `PanSemEntryState.evaluateDecls_agree` relates the String/`InfoMap` production evaluator to `evaluateDeclsHOLFinite` for fixed Word64, byte-ranged declarations, and an initial `PanSemDeclEntryRel` state. It covers failure and success and relates successful states. It does not route the production body through the exact evaluator or cover arbitrary production carriers/states. The production definition therefore remains untagged.

Datatype reviews for `Decl`, `Shape`, `Exp`, `prog` are owned by the existing
`flapjack-pxn.18.3.5.2`–`.18.3.5.5` beads.

2026-09-28 source refresh: production `evaluateDecls` remains the generic
String/`InfoMap` path at `PanSem.lean:2914`; its `Name` clause is a no-op, its
`Decl` branch calls `evalPanValueExp`, `panValueShape`, and `panShapeMatches`,
and its function/exception branches call production `isWfShape` and
`lookupInfo`. The tagged `evaluateDeclsHOLFinite` at
`StateExactFiniteMap.lean:1616` uses `DeclHOL`, `MlString`, `evalHOLFinite`,
`shapeOfHOLExact`, `isWfShapeExactHOL`, and exact finite maps. The untagged
`PanSemEntryState.evaluateDecls_agree` theorem establishes correspondence only
under its byte-range, state-relation, memory-access, and word-size premises; it
adds no tag and does not establish a textual production call route or an
unconditional equivalence for arbitrary production carriers.

Coverage review: all 17 named outputs in `pan_evaluate_decls_probe.out` now have
`#guard`s against `evaluateDeclsHOLFinite` in
`Flapjack/Test/PanSemEvaluateDeclsFiniteParity.lean`. Besides the prior empty,
Name, successful/failing Decl, Function, and Exn rows, this includes local
preservation, left-to-right global visibility, empty-locals evaluation,
function-code replacement, bad return shape, duplicate-exception failure, and
an in-domain byte load in a declaration initializer. The byte-load row starts
with empty locals/globals, clock 20, little-endian mode, memory `0 ↦ Word 1w`,
and domain `{0w}`; `Decl One "g" (LoadByte (Const 0w))` yields both
`SOME (ValWord 1w)` for global `g` and the unchanged `Word 1w` memory cell.
The separate production parity module remains a comparison of the production
String/InfoMap evaluator and does not turn the conditional theorem into a
textual route through the exact evaluator.
