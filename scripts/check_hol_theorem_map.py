#!/usr/bin/env python3
"""Check the reviewed inventory for HOL-tagged declarations and Proofs theorems.

The inventory records citation metadata and the current statement-review state.
This gate checks coverage and consistency; it is not a cross-prover equivalence
checker. In particular, ``pending_statement_review`` is an explicit open review
state, not a claim that the Lean statement is equivalent to HOL.
"""

from __future__ import annotations

import argparse
from functools import lru_cache
import json
import re
import runpy
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
PROOFS_DIR = ROOT / "Flapjack" / "Pancake" / "Proofs"
DEFAULT_MANIFEST = ROOT / "docs" / "HOL-THEOREM-MAP.json"
PENDING_REVIEW_NOTE_ALLOWLIST_PATH = (
    ROOT / "scripts" / "pending-review-note-allowlist.json"
)
PENDING_REVIEW_NOTE_ALLOWLIST_DATA = json.loads(
    PENDING_REVIEW_NOTE_ALLOWLIST_PATH.read_text()
)
PENDING_REVIEW_NOTE_ALLOWLIST_ISSUE = PENDING_REVIEW_NOTE_ALLOWLIST_DATA["bead"]
PENDING_REVIEW_NOTE_ALLOWLIST = {
    tuple(entry) for entry in PENDING_REVIEW_NOTE_ALLOWLIST_DATA["entries"]
}
COORDINATOR_PENDING_NOTE = re.compile(
    r"\b(?:coordinator|integration|external\s+PR)\b[^.;]{0,40}?"
    r"\b(?:acceptance|review)\b[^.;]{0,20}?\b(?:pending|required)\b"
    r"|\bcoordinator\s+(?:is\s+)?(?:pending|required)\b"
    r"|\bpending\s+(?:coordinator|integration)\s+(?:acceptance|review)\b"
    r"|\b(?:acceptance|review)\s+pending\s+coordinator\b"
    r"|\b(?:fleet\s+merge|merge)\s+acceptance\b"
    r"|\bacceptance\s+separate\b"
    r"|\b(?:coordinator|fleet)\s+acceptance\s+tracked\b",
    re.IGNORECASE,
)
REFS = runpy.run_path(str(ROOT / "scripts" / "check-hol-refs.py"))
HOL_ATTRIBUTE_SITES = REFS["hol_attribute_sites"]
FIND_LEAN_DECL = REFS["find_lean_decl"]

THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma)\s+([^\s:({\[]+)"
)
DATA_DECLARATION_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|abbrev|opaque|structure|inductive|class)\s+([^\s:({\[]+)"
)


def reviewed_note_pending_error(
    key: tuple[str, str], status: str, reviewer: Any
) -> str | None:
    """Reject pending coordinator review notes on reviewed entries, except the tracked legacy set."""
    if (
        not isinstance(status, str)
        or not status.startswith("reviewed_")
        or not isinstance(reviewer, str)
        or not COORDINATOR_PENDING_NOTE.search(reviewer)
        or key in PENDING_REVIEW_NOTE_ALLOWLIST
    ):
        return None
    return (
        f"{key[0]}:{key[1]}: reviewed statement status cannot retain a "
        "coordinator review/acceptance pending or required note; the only "
        f"temporary legacy exceptions are enumerated for {PENDING_REVIEW_NOTE_ALLOWLIST_ISSUE}"
    )


# HOL definition candidates whose Lean declarations were withdrawn from
# @[hol] because their carrier or statement shape differs. Keep this explicit
# inventory small and source-reviewed; a mismatch row is not generated merely
# because an arbitrary Lean def happens to mention a HOL name.
WITHDRAWN_HOL_DECLARATIONS = {
    ("Flapjack/Pancake/Proofs/PanGlobals.lean", "goodResHOL"): (
        "cakeml/pancake/proofs/pan_globalsProofScript.sml",
        "good_res_def",
        "flapjack-ds8 (bead flapjack-ikjm.2): HOL good_res_def classifies the word-parametrized "
        "panSem$result; the Lean declaration fixes the carrier to the width-indexed inductive "
        "PanSemResultExact width.  The required (words_as_type_indexed_bitvec) qualifier cannot be "
        "validated for an inductive carrier, so the @[hol] tag was withdrawn pending a checker "
        "extension for reviewed width-indexed inductive carriers."
    ),
    ("Flapjack/Pancake/PanLang.lean", "Exp"): (
        "cakeml/pancake/panLangScript.sml",
        "exp",
        "flapjack-luna-b (bead flapjack-p0l9, 2026-09-28): HOL exp at "
        "panLangScript.sml:53-69 indexes Const by the target word type, but "
        "production Exp (alpha : Type u) stores an arbitrary alpha. The "
        "executed compiler specializes it to Exp (BitVec width), which does "
        "not make this generic declaration width-indexed. The exact "
        "constructor-for-constructor port is ExpHOL width in "
        "PanLang/Exp.lean (reviewed_exact); expToHOL_expOfHOL is unconditional "
        "and expOfHOL_expToHOL is proved for ExpByteRanged production values. "
        "This checked codec is the representation refinement for the width "
        "specialization; the reverse direction's String/MlString and "
        "Shape/ShapeHOL bounds remain explicit, not silently identified. "
        "Keep production Exp untagged. Exact compiler routing and other "
        "String-backed syntax fields remain tracked by "
        "flapjack-pxn.18.3.5.8."
    ),
    ("Flapjack/Compiler/Encoders/Asm.lean", "asmRegOk"): (
        "cakeml/compiler/encoders/asm/asmScript.sml",
        "reg_ok_def",
        "flapjack-ds8 (bead flapjack-4ac.6): HOL reg_ok_def uses a positive-dimensional word type; "
        "the Lean declaration quantifies width : Nat with no [NeZero width] binder, so BitVec 0 "
        "is admitted.  The HOL tag was withdrawn pending a faithful width-restricted restatement."
    ),
    ("Flapjack/Compiler/Encoders/Asm.lean", "asmRegImmOk"): (
        "cakeml/compiler/encoders/asm/asmScript.sml",
        "reg_imm_ok_def",
        "flapjack-ds8 (bead flapjack-4ac.6): HOL reg_imm_ok_def uses a positive-dimensional word type; "
        "the Lean declaration quantifies width : Nat with no [NeZero width] binder, so BitVec 0 "
        "is admitted.  The HOL tag was withdrawn pending a faithful width-restricted restatement."
    ),
    ("Flapjack/Compiler/Encoders/Asm.lean", "asmArithOk"): (
        "cakeml/compiler/encoders/asm/asmScript.sml",
        "arith_ok_def",
        "flapjack-ds8 (bead flapjack-4ac.6): HOL arith_ok_def uses a positive-dimensional word type; "
        "the Lean declaration quantifies width : Nat with no [NeZero width] binder, so BitVec 0 "
        "is admitted.  The HOL tag was withdrawn pending a faithful width-restricted restatement."
    ),
    ("Flapjack/Compiler/Encoders/Asm.lean", "asmFpOk"): (
        "cakeml/compiler/encoders/asm/asmScript.sml",
        "fp_ok_def",
        "flapjack-ds8 (bead flapjack-4ac.6): HOL fp_ok_def uses a positive-dimensional word type; "
        "the Lean declaration quantifies width : Nat with no [NeZero width] binder, so BitVec 0 "
        "is admitted.  The HOL tag was withdrawn pending a faithful width-restricted restatement."
    ),
    ("Flapjack/Compiler/Encoders/Asm.lean", "asmCmpOk"): (
        "cakeml/compiler/encoders/asm/asmScript.sml",
        "cmp_ok_def",
        "flapjack-ds8 (bead flapjack-4ac.6): HOL cmp_ok_def uses a positive-dimensional word type; "
        "the Lean declaration quantifies width : Nat with no [NeZero width] binder, so BitVec 0 "
        "is admitted.  The HOL tag was withdrawn pending a faithful width-restricted restatement."
    ),
    ("Flapjack/Compiler/Encoders/Asm.lean", "asmInstOk"): (
        "cakeml/compiler/encoders/asm/asmScript.sml",
        "inst_ok_def",
        "flapjack-ds8 (bead flapjack-4ac.6): HOL inst_ok_def uses a positive-dimensional word type; "
        "the Lean declaration quantifies width : Nat with no [NeZero width] binder, so BitVec 0 "
        "is admitted.  The HOL tag was withdrawn pending a faithful width-restricted restatement."
    ),
    ("Flapjack/Compiler/Encoders/Asm.lean", "asmOk"): (
        "cakeml/compiler/encoders/asm/asmScript.sml",
        "asm_ok_def",
        "flapjack-ds8 (bead flapjack-4ac.6): HOL asm_ok_def uses a positive-dimensional word type; "
        "the Lean declaration quantifies width : Nat with no [NeZero width] binder, so BitVec 0 "
        "is admitted.  The HOL tag was withdrawn pending a faithful width-restricted restatement."
    ),
    ("Flapjack/Compiler/Backend/StackProps.lean", "asmAddrOk"): (
        "cakeml/compiler/backend/semantics/stackPropsScript.sml",
        "addr_ok_def",
        "flapjack-ds8 (bead flapjack-4ac.6): HOL addr_ok_def uses a positive-dimensional word type; "
        "the Lean declaration quantifies width : Nat with no [NeZero width] binder, so BitVec 0 "
        "is admitted.  The HOL tag was withdrawn pending a faithful width-restricted restatement."
    ),
    ("Flapjack/Pancake/Semantics/PanSem.lean", "panEmptyLocals"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "empty_locals_def",
        "Codex (source comparison with panSemScript.sml:436-438: HOL updates the "
        "finite mlstring-keyed locals map to FEMPTY; panEmptyLocals uses the "
        "production String-keyed unrestricted lookup-function state. "
        "emptyLocalsHOLExact in PanSem/StateExact.lean improves the name and "
        "value carriers but its untouched map fields still admit infinite support. "
        "Direct HOL rows empty_locals/empty_locals_globals/empty_locals_clock are "
        "in pan_empty_locals_probe.out and sampled by PanSemEmptyLocalsHOLParity. "
        "No exact finite-map bridge; tag remains withdrawn pending "
        "flapjack-pxn.18.3.7.1.3.1.1.2."
    ),
    ("Flapjack/Pancake/Semantics/PanSem/EvalExact.lean", "evalHOLExact"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "eval_def",
        "Codex and flapjack-ds6 (source comparison, bead flapjack-dlc.120, with "
        "panSemScript.sml:209-283: all fifteen clauses Const, Var Local/Global, "
        "RStruct, RField, NStruct, NField, Load/Load32/LoadByte, Op/Panop, Cmp, "
        "Shift, BaseAddr/TopAddr/BytesInWord and every used subcarrier "
        "(MlS/ExpHOL/ValueHOL/ShapeHOL/StructContextExact, HolWordLab memory, "
        "memaddrs as a Prop for HOL 'a word set, [NeZero width] for HOL's positive "
        "dimindex) were compared one by one and match. The blocking mismatch is "
        "the state carrier: HOL panSem$state.locals/globals are finite maps "
        "varname |-> 'a v, while PanSemStateExact.locals/globals are unrestricted "
        "MlS -> Option _ functions, a strict superset admitting infinite support; "
        "the evaluator is faithful only on the finite-support subcarrier. Direct "
        "HOL rows are in pan_eval_probe.out, reproduced by "
        "Flapjack/Test/PanSemEvalExactParity.lean. Tag remains withdrawn pending "
        "the exact finite-map state carrier flapjack-pxn.18.3.7.1.3.1.1.2 (audit "
        "flapjack-pxn.18.3.7.1.3.1.2)."
    ),
    ("Flapjack/Pancake/PanLang/Exp.lean", "globalVarExpHOL"): (
        "cakeml/pancake/panLangScript.sml",
        "global_var_exp_def",
        "flapjack-ds6 (source comparison, bead flapjack-4ac.1.39): HOL "
        "global_var_exp_def (panLangScript.sml:278-291) is a partially specified "
        "recursive function: the exported theorem states exactly thirteen clauses, "
        "and the generated global_var_exp_def_primitive stores `| Load32 v => ARB | "
        "BaseAddr => ARB | TopAddr => ARB | BytesInWord => ARB`. A total Lean "
        "function must choose values for those four constructors, so globalVarExpHOL "
        "(exact ExpHOL/MlS carrier, the thirteen specified clauses verbatim, plus "
        "`load32` recursion and `[]` for the three nullary address constructors, "
        "matching production expGlobalVars) extends HOL's specification and cannot "
        "be an exact port. Direct HOL-EVAL rows global_var/nested_global are in "
        "pan_lang_var_exp_probe.out and replayed in Flapjack/Test/"
        "PanLangVarExpParity.lean. The tag is withheld; ARB/partial rendering is "
        "tracked by the child bead of flapjack-4ac.1.39."
    ),
    ("Flapjack/Pancake/Semantics/CrepSem.lean", "resVarW"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "res_var_def",
        "Codex (source comparison with crepSemScript.sml:163-166: the delete/update "
        "equations and Nat keys match; PanWordLab (BitVec width) is the single-Word "
        "word_lab carrier at positive width. However FiniteMap Nat _ is the raw "
        "unrestricted Nat-to-Option function and admits infinite support, unlike HOL "
        "num |-> word_lab. Direct HOL rows res_var_delete_hit/res_var_update_hit "
        "are in crep_res_var_probe.out and sampled by FiniteMapParity. No exact "
        "finite-support carrier; tag remains withdrawn pending "
        "flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
}
# An untagged documented mismatch may be a definition-like declaration or a
# theorem/lemma whose carrier or statement shape differs from HOL's.
DEFINITION_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|abbrev|opaque|theorem|lemma)\s+([^\s:({\[]+)"
)
DOCUMENTED_MISMATCHES = {
    ("Flapjack/Pancake/PanToCrep/MakeVmapHOL.lean", "panToCrepMakeVmapHOLExact"): (
        "cakeml/pancake/pan_to_crepScript.sml",
        "make_vmap_def",
        "Tag withdrawn (task 149): the typed capture make_vmap_def_typed in "
        "scripts/hol-probes/pan_to_crep_typed_probe.out gives params :(\u03b1 # shape) list "
        "and result \u03b1 |-> shape # num list, so HOL's variable-name type \u03b1 is generic, "
        "while this definition fixes it to MlS. Generalising the key would need "
        "[BEq \u03b1] [LawfulBEq \u03b1] for HolFiniteMapExact.updateList, whereas the accepted "
        "rendering of HOL equality on a generic key type is [DecidableEq \u03b1]; the "
        "definition is the \u03b1 = MlS instance. A faithful port needs a key-generic "
        "finite-map update that follows the DecidableEq convention."
    ),
    ("Flapjack/Compiler/Backend/Semantics/TargetSem/EncodedBytes.lean", "encodedBytesInMemHOL"): (
        "cakeml/compiler/backend/semantics/targetSemScript.sml",
        "encoded_bytes_in_mem_def",
        "Tag withdrawn (task 149): the typed capture encoded_bytes_in_mem_def_typed in "
        "scripts/hol-probes/target_sem_typed_probe.out gives c : \u03b1 asm_config and pc : \u03b2 word, "
        "so HOL's instruction type \u03b1 is independent of the word dimension. Lean's AsmConfigExact "
        "fixes encode : HolAsm width \u2192 List (BitVec 8), so the definition is the \u03b1 = HolAsm width "
        "instance; a faithful port needs an asm-config carrier generic in its instruction type."
    ),
    ("Flapjack/CakeParser/PegActions.lean", "evalUnary"): (
        "cakeml/compiler/parsing/pegexec_cml_foScript.sml",
        "eval_unary_def",
        "Tag withdrawn (task 147): HOL `eval_unary_def` applies `eval_unary` to `(\u03b1, MMLnonT, locs) parsetree list` with the terminal type `\u03b1` generic, while Lean's `ParseTree` fixes the terminal type to CakeML's `Token`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the terminal type."
    ),
    ("Flapjack/CakeParser/PegActions.lean", "mkLinfix"): (
        "cakeml/compiler/parsing/pegexec_cml_foScript.sml",
        "mk_linfix_fo_def",
        "Tag withdrawn (task 147): HOL `mk_linfix_fo_def` is generic in the terminal type `\u03b1` and the rule-index type `\u03b2` of `(\u03b1, \u03b2, locs) parsetree` and `\u03b2 + num`, while Lean's `ParseTree`/`Rule` fix them to `Token` and `Sum Nonterminal Nat`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in both type parameters."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "tokcheck"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "tokcheck_def",
        "Tag withdrawn (task 147): HOL `tokcheck_def` is `\u2200(pt :(\u03b1, \u03b2, \u03b3) parsetree) (tok :\u03b1)`, generic in the terminal type `\u03b1`, the nonterminal type `\u03b2` and the location type `\u03b3`; Lean fixes them to `Token`, `Nonterminal` and `Locs`. `pt.token == some tok` implements HOL's `OPTION_BIND (destLf pt) destTOK = SOME tok`, but a specialised instance is not an exact port; a faithful port needs a generic parsetree and terminal carrier."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeUQTyop"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_UQTyop_def",
        "Tag withdrawn (task 147): HOL `ptree_UQTyop_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeTyvarN"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_TyvarN_def",
        "Tag withdrawn (task 147): HOL `ptree_TyvarN_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeTyop"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_Tyop_def",
        "Tag withdrawn (task 147): HOL `ptree_Tyop_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeV"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_V_def",
        "Tag withdrawn (task 147): HOL `ptree_V_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeFQV"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_FQV_def",
        "Tag withdrawn (task 147): HOL `ptree_FQV_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeUQConstructorName"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_UQConstructorName_def",
        "Tag withdrawn (task 147): HOL `ptree_UQConstructorName_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeConstructorName"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_ConstructorName_def",
        "Tag withdrawn (task 147): HOL `ptree_ConstructorName_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeOpID"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_OpID_def",
        "Tag withdrawn (task 147): HOL `ptree_OpID_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeEliteral"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_Eliteral_def",
        "Tag withdrawn (task 147): HOL `ptree_Eliteral_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeOp"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_Op_def",
        "Tag withdrawn (task 147): HOL `ptree_Op_def` is generic in the identifier name type `\u03b1` (its result is `(\u03b1, mlstring) id option`) and the location type `\u03b2`, while Lean fixes them to `MlString` and `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs generic name and location carriers."
    ),
    ("Flapjack/CakeParser/PtreeConversion.lean", "ptreeStructName"): (
        "cakeml/semantics/cmlPtreeConversionScript.sml",
        "ptree_StructName_def",
        "Tag withdrawn (task 147): HOL `ptree_StructName_def` takes `(token, MMLnonT, \u03b1) parsetree` with the location type `\u03b1` generic, while Lean's `ParseTree` fixes the location payload to CakeML's `Locs`. The clauses are HOL's, but a specialised instance is not an exact port; a faithful port needs a parsetree carrier generic in the location type."
    ),
    ("Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean", "isValidValueSimps2HOLFinite"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "is_valid_value_simps2",
        "codewhale source comparison (2026-11-11; bead flapjack-4ac.3.30/.3.38/.3.39): tag withdrawn. "
        "HOL is_valid_value_simps2 keeps the candidate value width (vl :γ v) and the replacement FFI host "
        "(ffi :δ ffi_state) independent of the state's (α,'ffi), so the `s with ffi := ffi` equation relates "
        "states of different carriers. PanSemStateFiniteExact fixes the FFI host at σ and the candidate value at "
        "width, so the Lean statement specialises both. The eight equations are HOL's, but the interface is not "
        "the source shape; a faithful port needs a state carrier polymorphic in the FFI host."
    ),
    ("Flapjack/Compiler/Backend/ClosFvs/Source.lean", "compile"): ("cakeml/compiler/backend/clos_fvsScript.sml", "compile_def", "The executable uses removeList; compileSource is the source-shaped definition and compileSource_eq_compile proves agreement."),
    ("Flapjack/Compiler/Backend/ClosFvs/Source.lean", "compileInc"): ("cakeml/compiler/backend/clos_fvsScript.sml", "compile_inc_def", "The executable uses compile; compileIncSource is the source-shaped definition and compileIncSource_eq_compileInc proves agreement."),
    ("Flapjack/Compiler/Backend/ClosKnown/Compile.lean", "knownCompileInc"): ("cakeml/compiler/backend/clos_knownScript.sml", "known_compile_inc_def", "The executable uses the total traversals; knownCompileIncSource is the source-shaped definition and knownCompileIncSource_eq proves agreement."),
    ("Flapjack/Compiler/Backend/ClosLetop/Source.lean", "compileInc"): ("cakeml/compiler/backend/clos_letopScript.sml", "compile_inc_def", "The executable uses compileList; compileIncSource is the source-shaped definition and compileIncSource_eq_compileInc proves agreement."),
    ("Flapjack/Compiler/Backend/ClosTicks/Source.lean", "compileInc"): ("cakeml/compiler/backend/clos_ticksScript.sml", "compile_inc_def", "The executable uses removeList; compileIncSource is the source-shaped definition and compileIncSource_eq_compileInc proves agreement."),
    ("Flapjack/Compiler/Backend/ClosKnown/Compile.lean", "compile"): ("cakeml/compiler/backend/clos_knownScript.sml", "compile_def", "The executable uses singleton-derived traversals; compileSource is the source-shaped definition and compileSource_eq_compile proves agreement."),
    ("Flapjack/Compiler/Backend/ClosToBvl/ExtractName.lean", "extractName"): ("cakeml/compiler/backend/clos_to_bvlScript.sml", "extract_name_def", "The executable pattern match follows extract_name_pmatch; HOL's original definition uses option choice and agrees by extractNameSource_eq_extractName."),
    ("Flapjack/Compiler/Backend/ClosAnnotate/Shift.lean", "compile"): ("cakeml/compiler/backend/clos_annotateScript.sml", "compile_def", "The executable uses annotateSing, whereas HOL's original definition takes the head of the separate list-shaped annotate. The source definition agrees by compileSource_eq_compile."),
    ("Flapjack/Compiler/Backend/ClosAnnotate/Shift.lean", "compileInc"): ("cakeml/compiler/backend/clos_annotateScript.sml", "compile_inc_def", "The executable uses annotateList and optimized compile, whereas HOL uses its separate source annotate and compile. The source definition agrees by compileIncSource_eq_compileInc."),
    ("Flapjack/Misc/Sptree.lean", "sptDomain"): ("hol4/src/finite_maps/sptreeScript.sml", "domain_def", "HOL defines domain with recursive set clauses; the Lean lookup predicate is extensionally characterized by its membership lemmas, but is not the source definition. The source-shaped definition and set representation remain open."),
    ("Flapjack/Compiler/Backend/PatternSemantics/Semantics.lean", "isSibling"): ("cakeml/compiler/backend/pattern_matching/pattern_semanticsScript.sml", "is_sibling_def", "The executed operation specializes HOL's polymorphic element type to Nat pairs. isSiblingHOL is the unrestricted port, and isSibling_eq_HOL checks agreement at this specialization."),
    ('Flapjack/Compiler/Backend/PatternExh/Matrix.lean', 'ctorInter'): ('cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml', 'ctor_inter_def', 'HOL infers an arbitrary element type; the executed ctorInter specializes it to Ctor and is not tagged as the generic source declaration. ctorInterHOL is the unrestricted HOL-shaped port; a kernel-checked equality connects its Ctor specialization to the executed operation.'),
    ('Flapjack/Compiler/Backend/PatternExh/Matrix.lean', 'ctorKeep'): ('cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml', 'ctor_keep_def', 'HOL infers an arbitrary element type; the executed ctorKeep specializes it to Ctor and is not tagged as the generic source declaration. ctorKeepHOL is the unrestricted HOL-shaped port; a kernel-checked equality connects its Ctor specialization to the executed operation.'),
    ('Flapjack/Compiler/Backend/PatternExh/Matrix.lean', 'ctorNub'): ('cakeml/compiler/backend/pattern_matching/pattern_exhScript.sml', 'ctor_nub_def', 'HOL infers an arbitrary element type; the executed ctorNub specializes it to Ctor and is not tagged as the generic source declaration. ctorNubHOL is the unrestricted HOL-shaped port; a kernel-checked equality connects its Ctor specialization to the executed operation.'),
    ('Flapjack/Pancake/Semantics/PanSem/ValueHOL.lean', 'shapeOfHOLExact'): ('cakeml/pancake/semantics/panSemScript.sml', 'shape_of_def', 'HOL-shaped word-indexed definition retained for faithful proofs; the required word qualifier is blocked until the checker supports the nested ValueHOL to HolWordLab to BitVec carrier.'),
    ('Flapjack/Pancake/CrepToLoop.lean', 'rtVars'): ('cakeml/pancake/crep_to_loopScript.sml', 'rt_vars_def', 'Raw function map admits infinite support, unlike HOL finite maps; retained for faithful finite-map lookup proofs.'),
    ('Flapjack/Pancake/CrepToLoop/StateRel.lean', 'makeVmapHOL'): ('cakeml/pancake/crep_to_loopScript.sml', 'make_vmap_def', 'Raw function map admits infinite support, unlike HOL finite maps; retained for faithful finite-map lookup proofs.'),
    ('Flapjack/Pancake/Semantics/PanCommonProps.lean', 'ctxtMax'): ('cakeml/pancake/semantics/pan_commonPropsScript.sml', 'ctxt_max_def', 'Raw function maps admit infinite support and Boolean equality adds assumptions absent from HOL; retained for faithful finite-map lookup proofs.'),
    ('Flapjack/Pancake/Semantics/PanCommonProps.lean', 'noOverlap'): ('cakeml/pancake/semantics/pan_commonPropsScript.sml', 'no_overlap_def', 'Raw function maps admit infinite support and Boolean equality adds assumptions absent from HOL; retained for faithful finite-map lookup proofs.'),
    ('Flapjack/Pancake/Semantics/PanCommonProps.lean', 'fmEmptyZipAlist'): ('cakeml/pancake/semantics/pan_commonPropsScript.sml', 'fm_empty_zip_alist', 'Raw function maps admit infinite support and Boolean equality adds assumptions absent from HOL; retained for faithful finite-map lookup proofs.'),
    ('Flapjack/Pancake/Semantics/PanCommonProps.lean', 'fmEmptyZipFlookup'): ('cakeml/pancake/semantics/pan_commonPropsScript.sml', 'fm_empty_zip_flookup', 'Raw function maps admit infinite support and Boolean equality adds assumptions absent from HOL; retained for faithful finite-map lookup proofs.'),
    ('Flapjack/FiniteMap/Basic.lean', 'opt_mmap_some_eq_zip_flookup'): ('cakeml/pancake/semantics/pan_commonPropsScript.sml', 'opt_mmap_some_eq_zip_flookup', 'Raw function maps admit infinite support and Boolean equality adds assumptions absent from HOL; retained for faithful finite-map lookup proofs.'),
    ('Flapjack/FiniteMap/Basic.lean', 'opt_mmap_disj_zip_flookup'): ('cakeml/pancake/semantics/pan_commonPropsScript.sml', 'opt_mmap_disj_zip_flookup', 'Raw function maps admit infinite support and Boolean equality adds assumptions absent from HOL; retained for faithful finite-map lookup proofs.'),
    ('Flapjack/Pancake/Semantics/PanCommonProps.lean', 'updateEqZipFlookupHOL'): ('cakeml/pancake/semantics/pan_commonPropsScript.sml', 'update_eq_zip_flookup', 'Raw function maps admit infinite support and Boolean equality adds assumptions absent from HOL; retained for faithful finite-map lookup proofs.'),
    ("Flapjack/Pancake/Proofs/CrepInline/UnreachElimProgSize.lean", "unreachElimProgSize"): (
        "cakeml/pancake/proofs/crep_inlineProofScript.sml", "unreach_elim_prog_size",
        "flapjack-ds10 (source comparison, 2026-09-30; bead flapjack-pxn.18.5.5.50; documented_mismatch). HOL unreach_elim_prog_size (crep_inlineProofScript.sml:1730-1733), elaborated type in scripts/hol-probes/crep_inline_prog_size_type_probe.out, is forall (p q : 'a crepLang$prog) (r : early_exit option) (f : 'a -> num). unreach_elim p = (q,r) ==> prog_size f q <= prog_size f p, where 'a is the same bare HOL type index that indexes 'a word. The untagged Lean declaration quantifies an independent {alpha : Type} (f : alpha -> Nat), an extra type quantifier: it is implied by each HOL instance only because prog_size never applies f, which does not license replacing the bare index carrier. A BitVec-width-domain rendering was attempted and rejected by coordinator review (words_as_type_indexed_bitvec licenses HOL word values, not arbitrary bare alpha; checker-green is not review acceptance). Faithful translation/review of the bare index carrier, or a reviewed size-family translation removing the irrelevant function uniformly, remains open."
    ),

    ("Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean", "evalCrepSemHOLProgExact_seq_fixClockFree"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "evaluate_def",
        "Coordinator review PR #1168: the local fix-clock-free Seq equation is valid, but "
        "whole-evaluator agreement between evalCrepSemHOLProgExact and HOL evaluate has not "
        "been reviewed across Call, domain stamping, and FFI. Tag withdrawn pending that review.",
    ),
    ("Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean", "evalCrepSemHOLProgExact_while_fixClockFree"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "evaluate_def",
        "Coordinator review PR #1168: the local fix-clock-free While equation is valid, but "
        "whole-evaluator agreement between evalCrepSemHOLProgExact and HOL evaluate has not "
        "been reviewed across Call, domain stamping, and FFI. Tag withdrawn pending that review.",
    ),
    ("Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean", "evalCrepSemHOLProgExact_skip"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "evaluate_def",
        "Coordinator review HOLD (flapjack-l60u, PR #1167): the local Skip equation is valid, "
        "but full agreement between evalCrepSemHOLProgExact and HOL evaluate across every "
        "constructor, including FFI, has not been source-reviewed. Tag withdrawn pending "
        "that evaluator review.",
    ),
    ("Flapjack/Pancake/Proofs/PanSimp.lean", "collectPanValueStructs_panSimpDecls"): (
        "cakeml/pancake/proofs/pan_simpProofScript.sml",
        "decs_stcnames_compile_prog",
        "flapjack-ds8 (bead flapjack-4ac.8): production String-keyed Prog/Decl carriers; "
        "HOL states it over the exact mlstring-keyed panLang syntax. Tag withdrawn; exact port "
        "tracked by flapjack-4ac.8 (blocked by flapjack-4ac.8.1).",
    ),
    ("Flapjack/Pancake/Semantics/PanSem/StateExactFiniteMap.lean", "evaluateDeclsHOLFinite_functions"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "evaluate_decls_functions",
        "flapjack-ds10 (beads flapjack-4ac.4.86/4ac.4.84, coordinator HOLD 2026-09-26T16:46Z): a "
        "panProps-sourced theorem tagged in the PanSem module; the @[hol] tag was withdrawn pending "
        "relocation to the PanProps counterpart with a kernel codec to the canonical tagged evaluator. "
        "Tracked by flapjack-lqws."
    ),
    ("Flapjack/Pancake/Semantics/CrepSem/Eval.lean", "evalCrepHolExp"): (
        "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
        "eval_nested_decs_seq_res_var_eq",
        "flapjack-luna-b (source comparison, 2026-09-26; bead flapjack-4ac.5.19; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL "
        "eval_nested_decs_seq_res_var_eq (pan_to_crepProofScript.sml:596-620) "
        "implicitly universally quantifies es, ns, t, ev, p. Its four premises "
        "are MAP (eval t) es = MAP SOME ev; LENGTH ns = LENGTH es; "
        "distinct_lists ns (FLAT (MAP var_cexp es)); ALL_DISTINCT ns. Its exact "
        "conclusion evaluates nested_decs ns es p in t and equates that with "
        "evaluation of p after installing ZIP (ns,ev), then restores original "
        "locals with FOLDL res_var over ZIP (ns, MAP (FLOOKUP t.locals) ns). "
        "nestedDecsHOL ports only syntax. evalCrepHolExp is over production "
        "CrepExp/CrepHolState, so this expression evaluator cannot state the "
        "theorem and no @[hol] tag is claimed. The faithful statement is the "
        "tagged evalNestedDecsSeqResVarEqHOL over CrepProgHOL/CrepExpHOL/"
        "CrepSemHOLState with evalCrepSemHOLProgExact; the restricted production "
        "evalCrepClockProg has been retired."
    ),
    ("Flapjack/Pancake/Semantics/PanSemStateEval.lean", "holValueWord"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "theValWord_def",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.7; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL theValWord_def "
        "(panSemScript.sml:42) is the partial inverse theValWord (ValWord w) = w "
        "over the exact v/word_lab carrier, unspecified on other constructors. "
        "holValueWord (PanSemStateEval.lean:1362) totalizes to 0 on non-word "
        "inputs and is over the String-backed HolValue width (word carrier "
        "HolWordLab). Not statement-exact; tag withheld. HOL's unspecified "
        "branch needs separate review (flapjack-yaq); positive-width carrier "
        "work remains flapjack-0lj.5 (umbrella flapjack-pxn.18.3.5.8). "
    ),
    ("Flapjack/PanObservationalSemantics.lean", "panSemantics"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "semantics_def",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.52; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL semantics_def "
        "(panSemScript.sml:785-812) is the concrete semantics s start: with "
        "prog = Call NONE start [], Fail when some clock yields a forbidden "
        "result, else Terminate the first FinalFFI/Return run's outcome and "
        "io_events, else Diverge the build_lprefix_lub of per-clock io_events. "
        "The Lean analogue panSemantics (PanObservationalSemantics.lean:104, via "
        "panSemanticsWithLub) has the same fail/success/diverge structure and "
        "existential-clock shape (panHasForbiddenRun/panHasSuccessfulRun) but is "
        "abstracted over a PanSemanticsHooks record exposing evaluate : Nat -> "
        "Option (PanValueFfiClockResult alpha sigma) instead of fixing the "
        "concrete Call/evaluate, and uses PanValueFfiClockResult/FfiState rather "
        "than HOL's result x panSem$state. Hook parameterization and the result "
        "carrier are differences beyond names_as_string. The concrete faithful "
        "port depends on the exact panSem evaluate and is tracked by "
        "flapjack-pxn.18.4.4 / flapjack-pxn.18.4.3 and flapjack-pxn.18.3.6.9. "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/ClockExact.lean", "fixClockHOLExact_IMP_LESS_EQ"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "fix_clock_IMP_LESS_EQ",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.35; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL fix_clock_IMP_LESS_EQ "
        "(panSemScript.sml:451-457) states over panSem$state, whose locals/globals/"
        "code/eshapes are finite maps, that a fix_clock step cannot raise the clock. "
        "fixClockHOLExact_IMP_LESS_EQ (ClockExact.lean:47) keeps the same quantifiers "
        "and conclusion but the carrier PanSemStateExact uses unrestricted functions "
        "in place of those finite-map fields, a strict superset admitting infinite "
        "support. Exact finite-support replacement over PanSemStateFiniteExact tracked "
        "by flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean", "kvar_simps"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "kvar_simps",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.30; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL kvar_simps (panSemScript.sml:422-429) "
        "is the four set_kvar/lookup_kvar simp equations over panSem$state with finite-map "
        "locals/globals. The Lean kvar_simps (StateSimpExact.lean:44) keeps the four "
        "equations but its PanSemStateExact carrier exposes unrestricted lookup functions "
        "instead of HOL finite maps. Exact finite-support replacement tracked by "
        "flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean", "is_valid_value_simps"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "is_valid_value_simps",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.38; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL is_valid_value_simps "
        "(panSemScript.sml:476-487) gives the Local/Global FLOOKUP clauses of "
        "is_valid_value over panSem$state finite maps. is_valid_value_simps "
        "(StateSimpExact.lean:55) matches the two clauses but its PanSemStateExact "
        "carrier reads arbitrary functions rather than HOL finite-map fields. Exact "
        "finite-support replacement tracked by flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/StateSimpExact.lean", "is_valid_value_simps2"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "is_valid_value_simps2",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.39; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL is_valid_value_simps2 "
        "(panSemScript.sml:489-500) is the eight clock/ffi/code/memory update-invariance "
        "equations for is_valid_value and lookup_kvar over panSem$state. "
        "is_valid_value_simps2 (StateSimpExact.lean:70) keeps the equations but binds "
        "whole statern with function-typed code/memory in place of HOL finite maps. "
        "Exact finite-support replacement tracked by flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/StateDefsExact.lean", "kvar_defs"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "kvar_defs",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.40; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL kvar_defs (panSemScript.sml:502-503) "
        "is LIST_CONJ of set_var/set_global/set_kvar/is_valid_value/lookup_kvar over "
        "panSem$state finite maps. kvar_defs (StateDefsExact.lean:51) spells out the same "
        "five accessor equations as a nested conjunction, but its PanSemStateExact map "
        "fields are unrestricted functions rather than HOL finite maps. Exact "
        "finite-support replacement tracked by flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/IsValidValueExact.lean", "isValidValueHOLExact"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "is_valid_value_def",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.37; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL is_valid_value (panSemScript.sml:469-475) "
        "compares shape_of value with the looked-up shape in panSem$state finite maps. "
        "isValidValueHOLExact (IsValidValueExact.lean:85) matches the body and uses exact "
        "ShapeHOL/ValueHOL, but its PanSemStateExact argument admits arbitrary lookup "
        "functions instead of HOL finite-map fields. Exact finite-support replacement "
        "tracked by flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/LocalUpdatesExact.lean", "resVarHOLExact"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "res_var_def",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.41; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL res_var (panSemScript.sml:505-508) "
        "performs \\\\ n or |+ (n,v) on the finite-map locals. resVarHOLExact "
        "(LocalUpdatesExact.lean:72) reproduces the delete/update behavior pointwise, but "
        "its MlS -> Option function input is not HOL's finite-map carrier. Exact "
        "finite-support replacement tracked by flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/DecCallExact.lean", "lookupCodeHOLExact"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "lookup_code_def",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.36; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL lookup_code (panSemScript.sml:458-467) "
        "FLOOKUP s the code finite map and builds FEMPTY |++ ZIP arguments. "
        "lookupCodeHOLExact (DecCallExact.lean:39) retains the lookup and argument checks "
        "and the same return triple, but its code is an unrestricted function rather than "
        "a HOL finite map. Exact finite-support replacement tracked by "
        "flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/ShMemExact.lean", "shMemLoadHOLExact"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "sh_mem_load_def",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.42; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL sh_mem_load (panSemScript.sml:510-527) "
        "calls call_FFI on s.ffi and updates set_kvar/empty_locals over panSem$state "
        "finite maps. shMemLoadHOLExact (ShMemExact.lean:51) keeps the same branches "
        "and returns but its PanSemStateExact input admits arbitrary function-valued "
        "map fields. Exact finite-support replacement tracked by "
        "flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/Semantics/PanSem/ShMemExact.lean", "shMemStoreHOLExact"): (
        "cakeml/pancake/semantics/panSemScript.sml",
        "sh_mem_store_def",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.3.43; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL sh_mem_store "
        "(panSemScript.sml:529-547) calls call_FFI with word_to_bytes and updates the "
        "ffi field over panSem$state finite maps. shMemStoreHOLExact (ShMemExact.lean:79) "
        "keeps the same branches and returns but its PanSemStateExact input admits "
        "arbitrary function-valued map fields. Exact finite-support replacement tracked "
        "by flapjack-pxn.18.3.7.1.3.1.1.2.5 (parent .2.3). "
    ),
    ("Flapjack/Pancake/PanLang.lean", "length_withShape_eq_shape"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "length_with_shape_eq_shape",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.24; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL length_with_shape_eq_shape "
        "(panPropsScript.sml:265-267) is over the mlstring-named shape and an "
        "arbitrary value list. length_withShape_eq_shape (PanLang.lean:554) uses "
        "the production Shape carrier and Shape.shapeSize. Exact ShapeHOL route "
        "tracked by flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/Pancake/PanLang.lean", "all_distinct_withShape"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "all_distinct_with_shape",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.26; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL all_distinct_with_shape "
        "(panPropsScript.sml:286-289) is over the mlstring-named shape. "
        "all_distinct_withShape (PanLang.lean:581) uses the production Shape "
        "carrier. Exact ShapeHOL route tracked by flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/Pancake/PanLang.lean", "mem_of_withShape_mem"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "el_mem_with_shape",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.27; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL el_mem_with_shape "
        "(panPropsScript.sml:307-310) is over the mlstring-named shape. "
        "mem_of_withShape_mem (PanLang.lean:616) uses the production Shape "
        "carrier. Exact ShapeHOL route tracked by flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/Pancake/PanLang.lean", "mem_withShape_length"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "mem_with_shape_length",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.28; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL mem_with_shape_length "
        "(panPropsScript.sml:328-331) is over the mlstring-named shape. "
        "mem_withShape_length (PanLang.lean:606) uses the production Shape "
        "carrier. Exact ShapeHOL route tracked by flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/Pancake/PanLang.lean", "withShape_getElem_eq_take_drop"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "with_shape_el_take_drop_eq",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.29; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL with_shape_el_take_drop_eq "
        "(panPropsScript.sml:341-344) is over the mlstring-named shape. "
        "withShape_getElem_eq_take_drop (PanLang.lean:644) uses the production "
        "Shape carrier and Shape.shapeSize. Exact ShapeHOL route tracked by "
        "flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/Pancake/PanLang.lean", "listDisjoint_withShape_getElem"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "all_distinct_with_shape_distinct",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.30; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL all_distinct_with_shape_distinct "
        "(panPropsScript.sml:357-408) concludes DISJOINT (set x) (set y) for two MEM "
        "components of with_shape sh ns over the mlstring-named shape. "
        "listDisjoint_withShape_getElem (PanLang.lean:955) selects the components by two "
        "distinct indices and concludes element-level ListDisjoint over the production "
        "Shape carrier. Exact ShapeHOL route tracked by flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/Pancake/PanLang.lean", "listDisjoint_withShape_getElem_lt"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "all_distinct_disjoint_with_shape",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.31; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL all_distinct_disjoint_with_shape "
        "(panPropsScript.sml:409-451) concludes DISJOINT (set (EL n ...)) (set (EL n' ...)) "
        "over the mlstring-named shape. listDisjoint_withShape_getElem_lt "
        "(PanLang.lean:921) is the strictly increasing n < n' case concluding "
        "element-level ListDisjoint over the production Shape carrier. Exact ShapeHOL "
        "route tracked by flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/Pancake/PanLang.lean", "listDisjoint_of_mem_zip_withShape"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "all_distinct_mem_zip_disjoint_with_shape",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.32; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL all_distinct_mem_zip_disjoint_with_shape "
        "(panPropsScript.sml:452-...) reads ZIP (l,ZIP (sh,with_shape sh ns)) members and "
        "concludes DISJOINT (set xs) (set ys) over the mlstring-named shape. "
        "listDisjoint_of_mem_zip_withShape (PanLang.lean:988) reads the aligned triples by "
        "an indexed getElem helper and concludes element-level ListDisjoint over the "
        "production Shape carrier. Exact ShapeHOL route tracked by flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/Pancake/PanLang.lean", "withShape_getElem_getElem"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "el_el_with_shape",
        "flapjack-ds5 (source comparison, 2026-09-25; bead flapjack-4ac.4.36; "
        "FLAPJACK-SPECIFIC, documented_mismatch). HOL el_el_with_shape "
        "(panPropsScript.sml:568-583) keeps the EVERY is_wf_shape_nil shs hypothesis. "
        "withShape_getElem_getElem (PanLang.lean:1340) states the same indexed equality "
        "but drops that hypothesis (Shape.shapeSize is total) and uses the production "
        "Shape carrier and Shape.shapeSize. Exact ShapeHOL route tracked by "
        "flapjack-pxn.18.3.5.8. "
    ),
    ("Flapjack/PanLocalised.lean", "localisedProg"): (
        "cakeml/pancake/semantics/panPropsScript.sml",
        "localised_prog_def",
        "flapjack-ds4 (source comparison, bead flapjack-4ac.4.74; FLAPJACK-SPECIFIC, "
        "documented_mismatch). HOL panProps$localised_prog (panPropsScript.sml:1380-1406) "
        "is polymorphic over the 'a prog carrier whose identifiers are mlstring; this "
        "definition is over the production Prog α carrier (PanLang.lean:316) whose "
        "FunName/ExceptionId/StructName are Lean String. The @[hol] tag was withdrawn for "
        "the carrier mismatch. Exact MlString/width-indexed port: localisedProgHOL over "
        "ProgHOL width in Flapjack/Pancake/Semantics/PanProps.lean. Faithful replacement "
        "depends on flapjack-pxn.18.3.5.8 (MlString carriers). "
    ),
    ("Flapjack/Pancake/Proofs/PanToCrep.lean", "globalsLookup"): (
        "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
        "globals_lookup_def",
        "flapjack-ds5 (source comparison with pan_to_crepProofScript.sml:435-438: "
        "the OPT_MMAP/FLOOKUP/GENLIST n2w/size_of_shape(shape_of v) algorithm "
        "matches clause-for-clause, but HOL inputs are panSem$value/crepSem$state "
        "while the Lean statement uses production PanValue α with String "
        "struct/field names, untagged panSemShapeOf/Shape.shapeSize instead of "
        "HOL shape_of/size_of_shape, and CrepRuntimeState α σ, only a production "
        "projection of the HOL state. names_as_string cannot authorize the "
        "value/shape/state carriers, and no NameRanged witness is statable for an "
        "Option (List (PanWordLab α)) output. Keep @[hol] withheld; exact-carrier "
        "work flapjack-pxn.18.3.5.8.8.)"
    ),
    ("Flapjack/Pancake/Proofs/PanToCrep.lean", "ctxtFc"): (
        "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
        "ctxt_fc_def",
        "flapjack-ds5 (source comparison with pan_to_crepProofScript.sml:25-30: "
        "the vars/funcs/eids/vmax construction via FUPDATE_LIST/ZIP/withShape/"
        "MAX_LIST matches, but every finite map is keyed by FunName/VarName/"
        "ExceptionId = String while HOL keys by funname/varname/eid = mlstring. "
        "names_as_string cannot authorize keyed-map carriers and no NameRanged "
        "premise exists. Keep @[hol] withheld pending exact-carrier work "
        "flapjack-pxn.18.3.5.8.)"
    ),
    ("Flapjack/Pancake/Proofs/PanToCrep.lean", "codeRel"): (
        "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
        "code_rel_def",
        "flapjack-ds5 (source comparison with pan_to_crepProofScript.sml:32-43: "
        "the source-FLOOKUP/localised_prog/ctxt_fc/compile shape matches, but "
        "Lean is generic over the global value type α with String identifiers "
        "and production finite maps while HOL is word-indexed with funname/"
        "varname/eid = mlstring. The carrier difference is beyond name "
        "representation. Keep @[hol] withheld pending exact-carrier work "
        "flapjack-pxn.18.3.5.8.)"
    ),
    ("Flapjack/Pancake/Proofs/PanToCrep.lean", "stateRel"): (
        "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
        "state_rel_def",
        "flapjack-ds5 (source comparison with pan_to_crepProofScript.sml:45-69: "
        "the conjunct layout matches, but Lean uses production PanSemState α "
        "(FfiState σ)/CrepRuntimeState α σ, reconstructs an optional target "
        "memory with PanValue.word/panTheWord (a source structure cell is not "
        "recoverable), fixes s.structs = [] and s.globals = FEMPTY, and keys "
        "globals by VarName = String, while HOL uses total word_lab memory and "
        "varname/eid = mlstring. Beyond name representation; keep @[hol] "
        "withheld pending exact-carrier work flapjack-pxn.18.3.5.8 and the "
        "state-carrier dependency flapjack-pxn.18.3.7.1.3.)"
    ),
    ("Flapjack/Pancake/Proofs/PanToCrep.lean", "localsRel"): (
        "cakeml/pancake/proofs/pan_to_crepProofScript.sml",
        "locals_rel_def",
        "flapjack-ds5 (source comparison with pan_to_crepProofScript.sml:71: "
        "the context-wf/live-variable-recovery/flattened-value/shape-wf clause "
        "layout matches, but Lean uses production PanToCrepProofContext α, "
        "FiniteMap String (PanValue α) source locals and FiniteMap Nat "
        "(PanWordLab α) target locals, while HOL keys by varname/eid = mlstring "
        "and uses word_lab. Beyond name representation; keep @[hol] withheld "
        "pending exact-carrier work flapjack-pxn.18.3.5.8.)"
    ),
    ("Flapjack/Pancake/Semantics/CrepSem.lean", "setCrepHolGlobalsW"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "set_globals_def",
        "Codex (source comparison with crepSemScript.sml:61-63: the BitVec 5 "
        "global key and PanWordLab word_lab cell, plus the FUPDATE body, match. "
        "The quantified whole-state carrier CrepHolState (BitVec width) still "
        "uses unrestricted Nat-to-Option locals and FunName-to-Option code "
        "functions, unlike HOL finite maps. Keep the tag withdrawn pending "
        "finite-support state carrier flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Semantics/CrepSem.lean", "setCrepHolVarW"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "set_var_def",
        "Codex (source comparison with crepSemScript.sml:55-57: the clause "
        "`set_var v w s = s with locals := s.locals |+ (v,w)` matches the "
        "FUPDATE on the Nat key, and PanWordLab (BitVec width) is the single-Word "
        "word_lab carrier at positive width. However the quantified whole-state "
        "carrier CrepHolState (BitVec width) stores locals/code as unrestricted "
        "Nat-to-Option and FunName-to-Option functions that admit infinite "
        "support, a strict superset of HOL's finite maps. names_as_string cannot "
        "authorize that carrier (the key is not an mlstring), and no NameRanged "
        "byte witness applies to a state result. Direct HOL rows set_var_hit / "
        "set_var_keeps_other / set_var_fields_preserved are in "
        "crep_local_updates_probe.out and sampled by the localBase examples in "
        "Flapjack/Test/CrepGlobalShapeParity.lean:227-269. No exact "
        "finite-support carrier; tag remains withdrawn pending "
        "flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Semantics/CrepSem.lean", "decCrepHolClockW"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "dec_clock_def",
        "Codex (source comparison with crepSemScript.sml:145-148: the clause "
        "`dec_clock s = s with clock := s.clock - 1` matches the Lean clock "
        "decrement, and [NeZero width] excludes the invalid zero word dimension. "
        "However the quantified whole-state carrier CrepHolState (BitVec width) "
        "stores locals/globals/code as unrestricted Nat-to-Option, "
        "BitVec-5-to-Option and FunName-to-Option functions that admit infinite "
        "support, a strict superset of HOL's finite maps (crepSemScript.sml:20-31). "
        "names_as_string cannot authorize that carrier and no NameRanged byte "
        "witness applies to a state result. Direct HOL rows dec_clock_clock / "
        "dec_clock_globals / dec_clock_be / dec_clock_top are in "
        "crep_dec_clock_simp_probe.out and sampled by "
        "Flapjack/Test/CrepGlobalShapeParity.lean:288-289. No exact "
        "finite-support carrier; tag remains withdrawn pending "
        "flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Semantics/CrepSem.lean", "emptyCrepHolLocalsW"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "empty_locals_def",
        "Codex (source comparison with crepSemScript.sml:71-74: the clause "
        "`empty_locals s = s with <| locals := FEMPTY |>` matches the Lean "
        "pointwise locals-clearing step. However the quantified whole-state "
        "carrier CrepHolState (BitVec width) stores locals/globals/code as "
        "unrestricted Nat-to-Option, BitVec-5-to-Option and FunName-to-Option "
        "functions that admit infinite support, a strict superset of HOL's finite "
        "maps (crepSemScript.sml:20-31). names_as_string cannot authorize that "
        "carrier and no NameRanged byte witness applies to a state result. Direct "
        "HOL rows empty_locals_locals / empty_locals_clock / empty_locals_memory "
        "are in crep_dec_clock_simp_probe.out, and empty_locals_none / "
        "empty_locals_fields_preserved in crep_local_updates_probe.out; sampled by "
        "Flapjack/Test/CrepGlobalShapeParity.lean:284-285. No exact "
        "finite-support carrier; tag remains withdrawn pending "
        "flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Semantics/CrepSem.lean", "fixCrepHolClock_IMP_LESS_EQW"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "fix_clock_IMP_LESS_EQ",
        "Codex (source comparison with crepSemScript.sml:155-160: the bound "
        "`fix_clock s x = (res,s1) ==> s1.clock <= s.clock` matches the Lean "
        "inequality, with HOL's pair variable and implicit res/s1 exposed as the "
        "explicit step/result/newState binders. However the quantified whole-state "
        "carrier CrepHolState (BitVec width) stores locals/globals/code as "
        "unrestricted Nat-to-Option, BitVec-5-to-Option and FunName-to-Option "
        "functions that admit infinite support, a strict superset of HOL's finite "
        "maps (crepSemScript.sml:20-31). names_as_string cannot authorize that "
        "carrier and no NameRanged byte witness applies to a clock inequality. "
        "Direct HOL rows fix_clock_clamps / fix_clock_keeps_lower are in "
        "crep_fix_clock_probe.out and sampled by "
        "Flapjack/Test/CrepGlobalShapeParity.lean:307-312. No exact "
        "finite-support carrier; tag remains withdrawn pending "
        "flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Semantics/CrepSem.lean", "fixCrepHolClockW"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "fix_clock_def",
        "flapjack-ds4 (source comparison with crepSemScript.sml:150-152: the "
        "clause `fix_clock old_s (res, new_s) = (res, new_s with clock := if "
        "old_s.clock < new_s.clock then old_s.clock else new_s.clock)` matches the "
        "Lean clamp clause for clause, with HOL's result/state pair exposed as the "
        "explicit `step` binder. However the quantified whole-state carrier "
        "CrepHolState (BitVec width) stores locals/globals/code as unrestricted "
        "Nat-to-Option, BitVec-5-to-Option and FunName-to-Option functions that "
        "admit infinite support, a strict superset of HOL's finite maps "
        "(crepSemScript.sml:20-31). names_as_string cannot authorize that carrier "
        "and no NameRanged byte witness applies to a state result. Direct HOL rows "
        "fix_clock_clamps / fix_clock_keeps_lower are in crep_fix_clock_probe.out "
        "and the clamp is sampled by "
        "Flapjack/Test/CrepGlobalShapeParity.lean:292-296. On the CrepSemHOLState "
        "finite-support carrier the set_var/set_globals/upd_locals/empty_locals/"
        "res_var bridges exist, but there is still no fix_clock bridge. Tag remains "
        "withdrawn pending flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Proofs/CrepInline.lean", "foldl_res_var_zip_lookup_var_hol"): (
        "cakeml/pancake/proofs/crep_inlineProofScript.sml",
        "FOLDL_res_var_ZIP_lookup_var",
        "flapjack-ds4 (source comparison, bead flapjack-pxn.18.5.5.19): "
        "FLAPJACK-SPECIFIC / not an exact HOL port. DecidableEq encodes HOL equality and "
        "removes the [BEq]/[LawfulBEq] side conditions, but the statement quantifies the raw "
        "function carrier FiniteMap alpha beta := alpha -> Option beta "
        "(Flapjack/FiniteMap/Basic.lean:19), which admits infinite-support inhabitants whereas "
        "HOL alpha |-> beta is finite-support. Tag withdrawn; faithful port over "
        "HolFiniteMapExact (Flapjack/Pancake/Semantics/CrepSem/HOLState.lean) tracked by bead "
        "flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Proofs/CrepInline.lean", "res_var_commutes_strong_hol"): (
        "cakeml/pancake/proofs/crep_inlineProofScript.sml",
        "res_var_commutes_strong",
        "flapjack-ds4 (source comparison, bead flapjack-pxn.18.5.5.19): "
        "FLAPJACK-SPECIFIC / not an exact HOL port. DecidableEq removes the BEq side condition, "
        "but resVarHOL quantifies the raw function carrier FiniteMap, which admits infinite "
        "support whereas HOL res_var ranges over finite maps. Tag withdrawn; faithful port over "
        "HolFiniteMapExact tracked by bead flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Proofs/CrepInline.lean", "res_var_foldl_commutes_strong_hol"): (
        "cakeml/pancake/proofs/crep_inlineProofScript.sml",
        "res_var_foldl_commutes_strong",
        "flapjack-ds4 (source comparison, bead flapjack-pxn.18.5.5.19): "
        "FLAPJACK-SPECIFIC / not an exact HOL port. DecidableEq removes the BEq side condition, "
        "but resVarHOL/List.foldl quantify the raw function carrier FiniteMap, which admits "
        "infinite support whereas HOL res_var/foldl range over finite maps. Tag withdrawn; "
        "faithful port over HolFiniteMapExact tracked by bead flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Proofs/CrepInline.lean", "flookup_res_var_is_mem_zip_eq_hol"): (
        "cakeml/pancake/proofs/crep_inlineProofScript.sml",
        "flookup_res_var_is_mem_zip_eq",
        "flapjack-ds4 (source comparison, bead flapjack-pxn.18.5.5.19): "
        "FLAPJACK-SPECIFIC / not an exact HOL port. DecidableEq removes the BEq side condition, "
        "but resVarHOL/FLOOKUP quantify the raw function carrier FiniteMap, which admits infinite "
        "support whereas HOL res_var/FLOOKUP range over finite maps. Tag withdrawn; faithful port "
        "over HolFiniteMapExact tracked by bead flapjack-pxn.18.3.7.1.3.1.1.3.1."
    ),
    ("Flapjack/Pancake/Semantics/CrepSem/HOLState.lean", "resVarEq"): (
        "cakeml/pancake/semantics/crepSemScript.sml",
        "res_var_def",
        "flapjack-ds4 (source comparison, bead flapjack-pxn.18.3.7.1.3.1.1.3.1): "
        "HOL equality port uses DecidableEq with no BEq side condition and the carrier "
        "is finite-support, but the declaration's carrier is HolFiniteMapExact itself "
        "(no owning structure field), so the field-based fmap_as_finite_support qualifier "
        "does not directly apply; exact tagging route tracked by bead "
        "flapjack-pxn.18.3.7.1.3.1.1.2.4. Helper and executable bridge remain valid."
    ),
    ("Flapjack/Pancake/PanToCrep.lean", "compileExp"): (
        "cakeml/pancake/pan_to_crepScript.sml",
        "compile_exp_def",
        "flapjack-luna-b (source comparison, bead flapjack-4ac.2.5; "
        "pan_to_crepScript.sml:39-108): clauses are structurally aligned, but "
        "compileExp ranges over production Exp α with generic Const α, String-backed "
        "names, production Shape/CrepExp α, and InfoMap-backed CompileContext. HOL "
        "uses word-indexed ExpHOL/CrepExpHOL, ShapeHOL/MlString names, and finite-map "
        "context; the generic [BEq α]/[OfNat α 0]/[Add α] carrier is not a positive-width "
        "HOL word. Lean also reads arbitrary context.bytesInWord for Load/BytesInWord "
        "while HOL uses fixed word-width-derived bytes_in_word. Nearby "
        "PanToCrepHOLContext still has String keys and production Shape/generic α too. "
        "No @[hol] tag is claimed. Exact carrier/compiler replacement is "
        "flapjack-4ac.2.5.1, dependent on flapjack-pxn.18.3.5.8; because compileExp "
        "feeds the executed compiler, replacement must connect the production path "
        "or record a measured exception."
    ),
}

# Flapjack-specific theorems that support exact HOL ports but are deliberately
# not ports of standalone HOL declarations. Most proof helpers live under
# Proofs/ and are inventoried automatically; counterpart-side witnesses and
# induction helpers belong beside their semantic definitions instead.
INFRASTRUCTURE_THEOREMS = {
    ("Flapjack/RiscV/NativeBackendOutput.lean", "fromWord_runtimeImage"):
        "Flapjack full backend output composition infrastructure; no independent HOL declaration.",

    ('Flapjack/Pancake/Proofs/PanToTarget/AssemblyGoodCodeSource.lean', 'panToTargetGoodCodeSource'): 'Flapjack-specific unnamed stageA2 original top-proof1376-1428: original backendConfigOk/goodDimindex/nonag32/distinctfunctionnames/pancakeGoodCodeHOL hypotheses only; computes both actual WordToWord and WordToStack intermediate tuples internally with no compileeq/hinst/targetrun/desiredgoodCode premise. Applies full source instruction validity and accepted backend admissibility/labels chain. Final top still identifies this exact lab program with fullcompile result and assembles remaining semantic/resource stages; no named HOL port or wholecompiler completion claimed.',
    ('Flapjack/Pancake/Proofs/PanToTarget/AssemblyGoodCodeSource.lean', 'panToTargetGoodCodeFromSource'): 'Flapjack-specific intermediate original top-proof A2 factoring1376-1428, no separately named HOL declaration: derives full PanToWord instruction invariant and both zerooffsets from original pancakeGoodCodeHOL/backendConfigOk/goodDimindex, then applies accepted panToTargetGoodCode at actual WordToWord/WordToStack intermediate equations. Final top assembly still supplies these equations from full compile equation; no target-run or desired-goodCode premise; full semantic theorem remains open.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'expr_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'exprs_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'nested_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'seqs_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'assigns_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'vars_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'zeros_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'globals_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'handler_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'stores_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'compile_valid'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileValidity.lean', 'holFmapAsFiniteSupportWitness'): 'Flapjack-specific internal expression/list/nested-declaration/sequence/assignment/generated-global/handler/store and native induction proof factoring, or canonical context representation witness, for the separately tagged full original PanToCrep compile validity in the same module. No standalone HOL declaration or completed port claim; all original source hypotheses are discharged by the final theorem.',

    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepTableValidity.lean', 'functions_valid'): 'Flapjack-specific internal function-projection membership factoring for the separately tagged full original compiler table validity theorem; no separate HOL declaration or completed port claim.',
    ("Flapjack/Compiler/Backend/WordAlloc/ProductionNativeCopyMemoryGuard.lean", "nativeCopyInstructionMemoryGuard"):
        "Flapjack runtime memory-domain invariant of native copy instructions; no separate HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepInlineTableValidity.lean', 'filter_lookup'): 'Flapjack-specific internal key-filter lookup and native wrapper proof factoring for the separately tagged full original every_inst_w_inline in the same module; no standalone HOL declaration or completed port claim.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepInlineTableValidity.lean', 'inline_top_valid'): 'Flapjack-specific internal key-filter lookup and native wrapper proof factoring for the separately tagged full original every_inst_w_inline in the same module; no standalone HOL declaration or completed port claim.',

    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileExpValidity.lean', 'holFmapAsFiniteSupportWitness'): 'Flapjack-specific canonical imported context toBroad/ofBroad roundtrip witness for the finite-support qualifier of the full original theorem in the same module; no separate HOL declaration.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileExpValidity.lean', 'compileList_length'): 'Flapjack-specific internal list-length or mutual-induction proof factoring for the separately tagged full original expression compiler validity theorem in the same module; no standalone HOL declaration or completed port claim.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileExpValidity.lean', 'heads_length'): 'Flapjack-specific internal list-length or mutual-induction proof factoring for the separately tagged full original expression compiler validity theorem in the same module; no standalone HOL declaration or completed port claim.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepCompileExpValidity.lean', 'compile_valid'): 'Flapjack-specific internal list-length or mutual-induction proof factoring for the separately tagged full original expression compiler validity theorem in the same module; no standalone HOL declaration or completed port claim.',

    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'everyInstOk_nestedDecsCodec'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'everyInstOkLess_storeGlobalsCodec'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'everyInstOkLess_storesCodec'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'everyInstOkLess_loadShapeCodec'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'everyInstOkLess_cexpHeadsCodec'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'everyInstOkLess_compFieldCodec'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'binaryExpNative_iff'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'binaryListNative_iff'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanToCrepValidity.lean', 'binaryProgNative_iff'): 'Flapjack-specific internal Boolean proof factoring/codec equivalence for the separately tagged full original native Crep validity statements in the same module. No standalone HOL declaration or completed port claim; unconditional constructor-for-constructor codec correspondence supplies shared literal crepEveryExpHOL predicate and membership EVERY without additional premises.',

    ('Flapjack/Pancake/Proofs/PanToWord/PanSimpValidity.lean', 'binary_append'): 'Flapjack-specific Boolean factoring for the four original PanSimp validity theorem ports in this module; no independent HOL declaration. List append fold, smart-sequence/tail-call support and Bool equality recursion assemble the separately tagged full original iff/implication results without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanSimpValidity.lean', 'binary_seqCallRet'): 'Flapjack-specific Boolean factoring for the four original PanSimp validity theorem ports in this module; no independent HOL declaration. List append fold, smart-sequence/tail-call support and Bool equality recursion assemble the separately tagged full original iff/implication results without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanSimpValidity.lean', 'binary_smartSeq'): 'Flapjack-specific Boolean factoring for the four original PanSimp validity theorem ports in this module; no independent HOL declaration. List append fold, smart-sequence/tail-call support and Bool equality recursion assemble the separately tagged full original iff/implication results without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanSimpValidity.lean', 'panBinary_retToTail_eq'): 'Flapjack-specific Boolean factoring for the four original PanSimp validity theorem ports in this module; no independent HOL declaration. List append fold, smart-sequence/tail-call support and Bool equality recursion assemble the separately tagged full original iff/implication results without additional premises.',
    ('Flapjack/Pancake/Proofs/PanToWord/PanSimpValidity.lean', 'panBinary_seqAssoc_eq'): 'Flapjack-specific Boolean factoring for the four original PanSimp validity theorem ports in this module; no independent HOL declaration. List append fold, smart-sequence/tail-call support and Bool equality recursion assemble the separately tagged full original iff/implication results without additional premises.',

    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCallReturn.lean', 'returningRefreshArguments'): ('Flapjack-specific returning Call preparation factoring of original8298-8410, no standalone HOL declaration. Actual source getVars/paired-cut guards and original SSA/map/frame derive first native rename NONE/new SSA/frame plus argument reads through original SSA map (the actual compiler uses original map), then convention Move2*(i+1), rereads, preserved new stack SSA/frame and mapped paired-cut image domains/scoped relations/injections. No target-run or desired post-relation premise. Existing original-lookup preservation, physical ignore updates, get/set and cut lemmas discharge obligations. Full returning Call/callee/stack/return/exception-handler and fullSSA remain open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCallReturn.lean', 'returningPrepareArguments'): ('Flapjack-specific returning Call preparation factoring of original8298-8410, no standalone HOL declaration. Actual source getVars/paired-cut guards and original SSA/map/frame derive first native rename NONE/new SSA/frame plus argument reads through original SSA map (the actual compiler uses original map), then convention Move2*(i+1), rereads, preserved new stack SSA/frame and mapped paired-cut image domains/scoped relations/injections. No target-run or desired post-relation premise. Existing original-lookup preservation, physical ignore updates, get/set and cut lemmas discharge obligations. Full returning Call/callee/stack/return/exception-handler and fullSSA remain open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCallReturn.lean', 'returningCalleeTransport'): ('Flapjack-specific inline factoring of original returning Call8422-8477, no standalone HOL declaration. Actual mapped paired-cut domains/injections, second-cut value relation and matching handler labels derive a source root permutation, complete callee-entry state equality after stack replacement and value-equal stacks; existing total evaluateStackSwap supplies result-sensitive body transport. No target evaluation or desired callee equality premise. Full returning Call return/exception restoration and full SSA remain open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCallReturn.lean', 'returningRestoreRegisters'): ('Flapjack-specific inline returning Call continuation factoring of original8550-8575, no standalone HOL declaration. Internal restored cut SSA, source cut domain, original map validity/frame and return-value length derive preservation under actual physical registers2*(i+1) insertion and actual retMov NONE/newSSA/frame via original rename preservation. No target evaluation or desired output SSA premise. Pop-environment cut SSA derivation, continuation/exception assembly and fullSSA remain open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCallReturn.lean', 'returningPopCutRelation'): ('Flapjack-specific inline returning Call8477-8550 factoring, no standalone HOL declaration. Actual callee key/value stack facts and pushed root-map correspondence derive successful source/target pops, complete wordStateEqRel, popped cut domain and all value lookup transport using native pushEnvPopEnvSKeyEq/popEnvFrame/keyMapImplies/allocLocalsRel. Internal actual cut domain/scoped lookup relation plus map-domain and source-bound facts reconstruct all restricted SSA conjuncts. No desired popped-local relation/output SSA or target evaluation premise. Continuation/exception full returning Call and fullSSA assembly remain open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCut.lean', 'cutLocalsRelation'): ('Flapjack-specific inline returning Call8477-8550 factoring, no standalone HOL declaration. Actual callee key/value stack facts and pushed root-map correspondence derive successful source/target pops, complete wordStateEqRel, popped cut domain and all value lookup transport using native pushEnvPopEnvSKeyEq/popEnvFrame/keyMapImplies/allocLocalsRel. Internal actual cut domain/scoped lookup relation plus map-domain and source-bound facts reconstruct all restricted SSA conjuncts. No desired popped-local relation/output SSA or target evaluation premise. Continuation/exception full returning Call and fullSSA assembly remain open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCallReturn.lean', 'returningRestoreRegistersRead'): ('Flapjack-specific inline returning Call8575-8610 factoring, no standalone HOL declaration. Existing actual retMov preservation plus duplicate-free physical convention writes derive successful return-register rereads; actual listNextVarRename producer and Move copy derive NONE/source-setVars versus target-setVars SSA/frame from internal cut SSA/map/nonphysical/bounds and native Call return Nodup/length guards. No target continuation run or desired output relation premise. Counter class/bounds are internal original producer facts to be discharged in full case. Full continuation/exception assembly and fullSSA remain open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCallReturn.lean', 'returningBindResults'): ('Flapjack-specific inline returning Call8575-8610 factoring, no standalone HOL declaration. Existing actual retMov preservation plus duplicate-free physical convention writes derive successful return-register rereads; actual listNextVarRename producer and Move copy derive NONE/source-setVars versus target-setVars SSA/frame from internal cut SSA/map/nonphysical/bounds and native Call return Nodup/length guards. No target continuation run or desired output relation premise. Counter class/bounds are internal original producer facts to be discharged in full case. Full continuation/exception assembly and fullSSA remain open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCallReturn.lean', 'returningNoHandlerException'): ('Flapjack-specific inline no-handler returning Call8660-8692 factoring, no standalone HOL declaration. Actual source callee Exception and total evaluateStackSwap prove LASTN cannot select the new NONE-handler frame, so it enters the identical original common stack. Native key/value equality reconstructs identical outer-handler locals/tail stack and actual target evaluate equals the complete original returned state. Internal pre-run callee stack-replacement equality comes from calleeSwap, never a target run or output-state premise. Full returning Call constructor with original six premises and return/handler IHs remains open on flapjack-sola-callreturn.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticAlloc.lean', 'allocNonErrorShape'): ('Flapjack-specific exhaustive actual alloc branch factoring from original Alloc9558-9606, no standalone HOL declaration. Excluding actual Error derives NONE or actual NotEnoughSpace with flush-empty locals; no target outcome or desired locals premise. Used to discharge full SSA result-sensitive failure branch. Full six-premise Alloc case is assembled in ssaCcTransCorrectAlloc; full SSA remains open.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticAlloc.lean', 'allocCollectorTransport'): ('Flapjack-specific internal factoring of original Alloc9410-9558, no standalone HOL declaration. Existing actual native allocSim chooses the source permutation and proves result/frame equality from intermediate original scoped-cut relations and injectivity. Normal return derives full union-cut scoped locals and domain via allocNormalLocalsDomain; no target-run/result or desired post-relation premise. Depends on delivered flapjack-sola-alloc.2. Full six-premise SSA Alloc assembly remains open on flapjack-sola-alloc.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticAlloc.lean', 'allocRestoreLocals'): ('Flapjack-specific internal factoring of original Alloc9478-9606, no standalone HOL declaration. Intermediate collector domain/scoped-local relation, original map validity and source-name bounds derive restricted SSA relation and actual final listNextVarRenameMove NONE/full SSA/frame. No target-run or desired final SSA premise. Collector transport and full six-premise Alloc case are assembled in ssaCcTransCorrectAlloc; full SSA remains open.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticAlloc.lean', 'allocRefreshCutNames'): ('Flapjack-specific factoring of original Alloc9333-9410 preparation, no standalone HOL declaration. Successful source count/paired-cut inputs are actual evaluator branch guards. Native initial rename/count Move runs, preserved SSA/frame, successful mapped paired cuts with full image domains, restricted strong relations and inherited injections are conclusions; no targetrun or collector result assumed. Original tagged cutEnvsLemma/renameMovePreserve/Distinct discharge the obligations. Internal prerequisite only, not full Alloc correctness; GC/permutation/restoration/full six-premise Alloc case are assembled in ssaCcTransCorrectAlloc; full SSA remains open.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticAlloc.lean', 'allocNormalLocalsDomain'): ('Flapjack-specific internal factoring of original Alloc9460-9480, no standalone HOL declaration. Actual alloc NONE return derives collector/pop success and post-locals domain equal union of original paired-cut names through native gcSKeyEq and pushEnvPopEnvSKeyEq. No target-run or desired-domain premise. Full six-premise Alloc case is assembled in ssaCcTransCorrectAlloc; full SSA remains open.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticAlloc.lean', 'allocPrepareArguments'): ('Flapjack-specific factoring of original Alloc9333-9410 preparation, no standalone HOL declaration. Successful source count/paired-cut inputs are actual evaluator branch guards. Native initial rename/count Move runs, preserved SSA/frame, successful mapped paired cuts with full image domains, restricted strong relations and inherited injections are conclusions; no targetrun or collector result assumed. Original tagged cutEnvsLemma/renameMovePreserve/Distinct discharge the obligations. Internal prerequisite only, not full Alloc correctness; GC/permutation/restoration/full six-premise Alloc case are assembled in ssaCcTransCorrectAlloc; full SSA remains open.'),
    ("Flapjack/Compiler/Backend/WordAlloc/Proofs/SSAReconcileEmpty.lean", "evaluateSSAReconcileEmpty"): (
        'Flapjack-specific empty-moves branch factoring; the extra compiler-filter guard is derived inside evaluateSSAReconcile, not an independent HOL theorem. Full original evaluate_ssa_reconcile is separately tagged and assembled in SSAReconcile.lean. Useful helper retained without a HOL tag; this classification is not an additional completed port.'
    ),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticInstall.lean', 'installCallbacksAligned'): ('Flapjack-specific factoring of original Install9710-9858 callback transport, no standalone HOL declaration. Source/target argument and cut success are internal alignment facts derived by preparation; original shared frame yields identical actual compile callback, buffer flush, oracle/config check and code union branches. Total evaluator result/frame and successful source-pointer versus target-pointer Loc local shapes are conclusions, no targetrun/result or post-frame premise. Failure cases retained. Infrastructure prerequisite only; full six-premise Install simulation is assembled in ssaCcTransCorrectInstall; full SSA remains open.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticInstall.lean', 'installResultLocals'): ('Flapjack-specific factoring of original Install9800-9858 post-result algebra/restoration, no standalone HOL declaration. Actual callback local shapes, source cut environment domain/strong matching and original map bounds are intermediate branch facts. Fresh SSA insertion/physical2 nonalias, actual pointer-copy/final native rename execution and final SSA/frame are proved conclusions. No targetrun or desired final locals hypothesis. This is an independent prerequisite of full six-premise Install simulation, not an additional completed HOL port; callback branch and full case are assembled in ssaCcTransCorrectInstall; full SSA remains open.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticInstall.lean', 'installRestoreResult'): ('Flapjack-specific factoring of original Install9800-9858 post-result algebra/restoration, no standalone HOL declaration. Actual callback local shapes, source cut environment domain/strong matching and original map bounds are intermediate branch facts. Fresh SSA insertion/physical2 nonalias, actual pointer-copy/final native rename execution and final SSA/frame are proved conclusions. No targetrun or desired final locals hypothesis. This is an independent prerequisite of full six-premise Install simulation, not an additional completed HOL port; callback branch and full case are assembled in ssaCcTransCorrectInstall; full SSA remains open.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticCut.lean', 'refreshCutNames'): ('Flapjack-specific factoring of original Install9710-9800 preparation, no standalone HOL declaration. Successful source argument/cut guards are evaluator branch facts; actual native rename/scratch execution, preserved data arguments and mapped-cut relation are conclusions, never final correctness premises. Useful dependency of full Install case, not an additional completed HOL theorem port; full six-premise Install simulation and callback/post-rename assembly are assembled in ssaCcTransCorrectInstall; full SSA remains open.'),
    ('Flapjack/Compiler/Backend/WordAlloc/Proofs/SSASemanticInstall.lean', 'installPrepareArguments'): ('Flapjack-specific factoring of original Install9710-9800 preparation, no standalone HOL declaration. Successful source argument/cut guards are evaluator branch facts; actual native rename/scratch execution, preserved data arguments and mapped-cut relation are conclusions, never final correctness premises. Useful dependency of full Install case, not an additional completed HOL theorem port; full six-premise Install simulation and callback/post-rename assembly are assembled in ssaCcTransCorrectInstall; full SSA remains open.'),
    ("Flapjack/Pancake/Semantics/CrepSem/EvaluateIndWhile.lean", "evalCrepSemHOLProgExact_inductWhile"): (
        "Flapjack-specific well-founded clock/sizeOf induction interface, no standalone "
        "HOL declaration. Derives guarded While body and plain-state NONE/Continue0 "
        "reentry IHs using evaluator clock monotonicity; other constructors retain "
        "the induction step. This is not the full HOL evaluate_ind port. Consumed by "
        "CrepInline/WhileInduction.lean assembleWhile without an extra correctness premise."
    ),
    ("Flapjack/Pancake/Proofs/CrepInline.lean", "holFmapAsFiniteSupportWitness"): (
        "Same-module canonical finite-support roundtrip witness for the exact "
        "CrepInline relation qualifiers. It reuses CrepSemHOLState's reviewed "
        "toBroad/ofBroad witness and has no standalone HOL declaration."
    ),
    ("Flapjack/Pancake/Proofs/CrepArith/SimpProgCorrect.lean", "holFmapAsFiniteSupportWitness"): (
        "Same-module canonical finite-support roundtrip witness for the tagged "
        "simp_prog_correct leaf cases. It reuses CrepSemHOLState's reviewed "
        "toBroad/ofBroad witness and has no standalone HOL declaration."
    ),
    ("Flapjack/Pancake/Proofs/CrepArith/SimpProgCorrect.lean", "crepSimpMapcsHOL_emptyLocals"): (
        "Flapjack-only commuting law for the local simp_prog_correct mapcs "
        "rendering and exact emptyLocals; HOL has no standalone declaration."
    ),
    ("Flapjack/Pancake/Proofs/CrepArith/SimpProgCorrect.lean", "crepSimpMapcsHOL_decClock"): (
        "Flapjack-only commuting law for the local simp_prog_correct mapcs "
        "rendering and exact decClock; HOL has no standalone declaration."
    ),
    ("Flapjack/Pancake/Proofs/CrepArith/SimpProgCorrectStoreGlob.lean", "holFmapAsFiniteSupportWitness"): (
        "Same-module canonical finite-support roundtrip witness for the tagged "
        "simp_prog_correct StoreGlob case. It reuses CrepSemHOLState's reviewed "
        "toBroad/ofBroad witness and has no standalone HOL declaration."
    ),
    ("Flapjack/Pancake/Proofs/CrepArith/SimpProgCorrectStoreGlob.lean", "crepSimpMapcsHOL_setGlobals"): (
        "Flapjack-only commuting law for the local simp_prog_correct mapcs "
        "rendering and exact setGlobals; HOL has no standalone declaration."
    ),
    ("Flapjack/Pancake/Proofs/CrepArith/SimpProgCorrectStore32.lean", "holFmapAsFiniteSupportWitness"): (
        "Same-module canonical finite-support roundtrip witness for the tagged "
        "simp_prog_correct Store32 case. It reuses CrepSemHOLState's reviewed "
        "toBroad/ofBroad witness and has no standalone HOL declaration."
    ),
    ("Flapjack/Pancake/Proofs/CrepArith/SimpProgCorrectStore32.lean", "crepSimpMapcsHOL_setMemory"): (
        "Flapjack-only commuting law for the local simp_prog_correct mapcs "
        "rendering and exact memory update; HOL has no standalone declaration."
    ),
    ("Flapjack/Pancake/Proofs/PanToCrep/StateRelFiniteSupport.lean", "panWriteBytearrayWord8HOL_domainCongr"): (
        "Flapjack-specific support for the ExtCall returned-byte state relation. "
        "This congruence handles distinct DecidablePred instances after equality "
        "of their domains; it has no standalone HOL declaration and is not a port."
    ),
    ("Flapjack/Pancake/Proofs/PanToCrep/StateRelFiniteSupport.lean", "panToCrepStateRelFiniteExact_writeBytearray"): (
        "Flapjack-specific support for the ExtCall returned-byte state relation. "
        "This helper preserves the exact state relation across equal bytearray writes; "
        "it has no standalone HOL declaration and is not a port."
    ),
    ("Flapjack/Pancake/Semantics/CrepProps/MemLoadFlatRel.lean", "holFmapAsFiniteSupportWitness"): (
        "Same-module canonical finite-support witness required by the qualified "
        "mem_load_flat_rel port. This witness restates the CrepSemHOLState / "
        "CrepSemBroadState roundtrip and is not a standalone HOL theorem."
    ),
    ("Flapjack/Pancake/Semantics/CrepProps/MemLoadFlatRel.lean", "memLoadHOLExact_flatRead_mutual"): (
        "Flapjack-specific mutual evaluator-induction helper for the strided "
        "mem_load_flat_rel analogue. HOL has no standalone declaration with "
        "this helper statement; its list cases are part of mem_loads_flat_rel."
    ),
    ("Flapjack/Pancake/PanLang/Exp.lean", "expOfHOL_expToHOL_nStruct"): (
        "Flapjack-only constructor refinement for panLang exp NStruct "
        "(panLangScript.sml:53-69): states the exact production-to-ExpHOL-to-"
        "production roundtrip under the byte-range premises required to convert "
        "String structure/field names to HOL mlstring. It specializes the codec, "
        "is not a separately declared HOL theorem, and does not tag production "
        "Exp or claim arbitrary String correspondence. The direct HOL constructor "
        "observation and ordered field payload are replayed in "
        "pan_lang_exp_probe.out by PanLangExpHOLParity."
    ),

    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'compileProgAsmWithReason_toOption'):
        "Flapjack-only located-failure sibling agreement for the allocator-"
        "parametric artifact compiler: the with-reason function succeeds "
        "exactly when the reviewed compileProgAsmWith succeeds, with the same "
        "tuple. No separately named HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'compileProgAsmFastWithReason_toOption'):
        "Flapjack-only located-failure sibling agreement for the ordinary "
        "artifact compiler: the with-reason function succeeds exactly when the "
        "reviewed compileProgAsmFast succeeds, with the same tuple. No "
        "separately named HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'fromStackChecked_ok_agrees'):
        "Flapjack-only checked-from_stack agreement: when the driver-side "
        "encoding guard accepts the stack_to_lab output (register ranges and "
        "unsupported instruction shapes), the checked sibling returns exactly "
        "the reviewed from_stack tuple. No separately named HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'compileProgAsmWithChecked_ok_agrees'):
        "Flapjack-only checked-pipeline agreement: when the word-to-stack and "
        "encoding guards accept, the checked allocator-parametric artifact "
        "pipeline returns exactly the reviewed compileProgAsmWith tuple. No "
        "separately named HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'compileProgAsmFastChecked_ok_agrees'):
        "Flapjack-only checked-pipeline agreement for the ordinary artifact "
        "compiler: the checked function returns exactly the reviewed "
        "compileProgAsmFast tuple on success. No separately named HOL "
        "declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'fromStack_names_eq'):
        "Flapjack-only names-table agreement for from_stack: the named call "
        "differs from the empty-names call only in the recorded symbol table "
        "(attach_bitmaps), so bytes, bitmaps and every other configuration "
        "field agree. No separately named HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'fromStack_ln_eq_names'):
        "Flapjack-only reverse names-table agreement for from_stack: the "
        "empty-names call is the named call with the symbol table reset to "
        "NOTFOUND. No separately named HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'compileProgAsmWith_names_eq_fst'):
        "Flapjack-only artifact agreement: the named artifact pipeline is the "
        "compile_prog_max mirror with the real symbol table recorded. No "
        "separately named HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileDefinitions.lean',
     'compileProgAsmWith_fst_names_eq'):
        "Flapjack-only reverse artifact agreement: the compile_prog_max mirror "
        "is the named artifact pipeline with the symbol table reset to "
        "NOTFOUND. No separately named HOL declaration.",
    ('Flapjack/Pancake/Proofs/PanToTarget/ExecutableCompileProgMaxAsmWith.lean',
     'compileProgAsmFast_symbols_eq_fst'):
        "Flapjack-only artifact agreement for the executable allocator: the "
        "named driver artifact is the compile_prog_max mirror with the real "
        "symbol table recorded. No separately named HOL declaration.",
}
VALID_STATUSES = {
    "reviewed_exact",
    "reviewed_nested_list_rel_as_mutual",
    "reviewed_fmap_as_finite_support_nested_list_rel_as_mutual",
    "reviewed_list_as_array",
    "reviewed_names_as_string",
    "reviewed_list_as_array_names_as_string",
    "reviewed_fmap_as_finite_support",
    "reviewed_fmap_as_finite_support_function",
    "reviewed_fmap_as_finite_support_function_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_tuple_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_heterogeneous_function",
    "reviewed_fmap_as_finite_support_heterogeneous_function_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_result",
    "reviewed_fmap_as_finite_support_result_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_result_observations",
    "reviewed_fmap_as_finite_support_parameter_observations",
    "reviewed_fmap_as_finite_support_parameter_predicate_domain",
    "reviewed_fmap_as_finite_support_parameters",
    "reviewed_fmap_as_finite_support_parameters_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_existentials",
    "reviewed_fmap_as_finite_support_existentials_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_relation_existentials_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_relation_existentials",
    "reviewed_fmap_as_finite_support_relation",
    "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_equalities",
    "reviewed_fmap_as_finite_support_equality",
    "reviewed_fmap_as_finite_support_equality_words_as_type_indexed_bitvec",
    "reviewed_words_as_type_indexed_bitvec",
    "reviewed_word_dimension_as_width",
    "reviewed_word_dimensions_as_widths",
    "reviewed_reals_as_rational_cuts",
    "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec",
    "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec",
    "pending_statement_review",
    "documented_mismatch",
    "no_hol_reference_pending_classification",
}
FIELDS = {
    "hol_path",
    "hol_name",
    "lean_path",
    "lean_name",
    "statement_status",
    "reviewer",
}


_NORMAL_TOKEN_RE = re.compile(r'/-|--|"')
_BLOCK_TOKEN_RE = re.compile(r"/-|-/")
_STRING_TOKEN_RE = re.compile(r'[\\"]')
_NON_NEWLINE_RE = re.compile(r"[^\n]")


def _blank(segment: str) -> str:
    """Replace every character except newlines by a space."""
    return _NON_NEWLINE_RE.sub(" ", segment)


def strip_comments(text: str) -> str:
    """Remove Lean line and nested block comments, preserving line boundaries.

    Comment characters become spaces and newlines are kept, so offsets and line
    numbers are unchanged. String literals (with backslash escapes) are copied
    verbatim; a comment opener inside one is not a comment. This scans token to
    token with compiled patterns instead of character by character.
    """
    result: list[str] = []
    index = 0
    length = len(text)
    while index < length:
        match = _NORMAL_TOKEN_RE.search(text, index)
        if match is None:
            result.append(text[index:])
            break
        token_start = match.start()
        result.append(text[index:token_start])
        token = match.group()
        if token == '"':
            # Copy the string literal through its closing quote.
            position = token_start + 1
            while True:
                found = _STRING_TOKEN_RE.search(text, position)
                if found is None:
                    position = length
                    break
                if found.group() == "\\":
                    position = found.start() + 2
                    continue
                position = found.end()
                break
            result.append(text[token_start:min(position, length)])
            index = position
        elif token == "--":
            newline = text.find("\n", token_start)
            stop = length if newline < 0 else newline
            result.append(" " * (stop - token_start))
            index = stop
        else:
            depth = 1
            position = token_start + 2
            while depth:
                found = _BLOCK_TOKEN_RE.search(text, position)
                if found is None:
                    position = length
                    break
                depth += 1 if found.group() == "/-" else -1
                position = found.end()
            result.append(_blank(text[token_start:position]))
            index = position
    return "".join(result)


@lru_cache(maxsize=None)
def _stripped_source_cached(path: str, size: int, mtime_ns: int) -> str:
    return strip_comments(Path(path).read_text(encoding="utf-8"))


def stripped_source(path: Path) -> str:
    """Comment-stripped text of a Lean file, cached per (path, size, mtime)."""
    stat = path.stat()
    return _stripped_source_cached(str(path), stat.st_size, stat.st_mtime_ns)


def lean_definition_exists(root: Path, lean_path: str, lean_name: str) -> bool:
    """Check that a registered untagged mismatch names a Lean declaration."""
    source = stripped_source(root / lean_path)
    return any(
        (match := DATA_DECLARATION_RE.match(line)) and match.group(1) == lean_name
        for line in source.splitlines()
    ) or any(
        (match := THEOREM_RE.match(line)) and match.group(1) == lean_name
        for line in source.splitlines()
    )


def lean_theorem_exists(root: Path, lean_path: str, lean_name: str) -> bool:
    """Check a theorem helper in any counterpart module, including Semantics/."""
    source = stripped_source(root / lean_path)
    return any(
        (match := THEOREM_RE.match(line)) and match.group(1) == lean_name
        for line in source.splitlines()
    )


def proof_theorem_declarations(root: Path = ROOT) -> set[tuple[str, str]]:
    """Return file/name pairs for theorem and lemma declarations under Proofs.

    ``#check`` commands and theorem names in comments are deliberately ignored.
    """
    declarations: set[tuple[str, str]] = set()
    proofs = root / "Flapjack" / "Pancake" / "Proofs"
    for path in sorted(proofs.rglob("*.lean")):
        source = stripped_source(path)
        rel = path.relative_to(root).as_posix()
        for line in source.splitlines():
            match = THEOREM_RE.match(line)
            if match:
                declarations.add((rel, match.group(1)))
    return declarations


def data_declarations(root: Path = ROOT) -> set[tuple[str, str]]:
    """Return data/definition declaration names outside the Proofs inventory."""
    declarations: set[tuple[str, str]] = set()
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        source = stripped_source(path)
        rel = path.relative_to(root).as_posix()
        for line in source.splitlines():
            match = DATA_DECLARATION_RE.match(line)
            if match:
                declarations.add((rel, match.group(1)))
    return declarations


def tagged_declarations(
    root: Path = ROOT,
) -> dict[tuple[str, str], tuple]:
    """Return Lean file/name to HOL file/name for every active ``@[hol]``."""
    tagged: dict[tuple[str, str], tuple] = {}
    for path in REFS["lean_files"]():
        rel = path.relative_to(root).as_posix()
        lines = path.read_text(encoding="utf-8").splitlines()
        for (line, hol_path, hol_name, _hol_line, list_fields,
             names_fields, boundary_fields, fmap_fields, fmap_result,
             fmap_relation, fmap_equalities, words_bitvec,
             fmap_parameters, fmap_existentials, dimension_width,
             fmap_function_positions,
             fmap_heterogeneous_function_positions, reals_cuts,
             fmap_equality, result_observations, dimension_widths, fmap_tuple, nested_list_rel,
             predicate_domain) in HOL_ATTRIBUTE_SITES(
                 lines, include_fmap_existentials=True,
                 include_word_dimension_width=True,
                 include_fmap_function=True,
                 include_fmap_heterogeneous_function=True,
                 include_reals_as_rational_cuts=True,
                 include_fmap_as_finite_support_equality=True,
                 include_result_observations=True,
                 include_word_dimensions_widths=True,
                 include_fmap_tuple=True,
                 include_nested_list_rel=True,
                 include_predicate_domain=True,
             ):
            lean_name = FIND_LEAN_DECL(lines, line - 1)
            key = (rel, lean_name)
            # Source-line disambiguation is checked against the HOL script by
            # check-hol-refs.py. The inventory keys the declaration by its
            # stable HOL file/name pair, not by an editable source line.
            value = (hol_path, hol_name, list_fields, names_fields,
                     boundary_fields, fmap_fields, fmap_result, fmap_relation,
                     fmap_equalities, words_bitvec, fmap_parameters,
                     fmap_existentials, dimension_width, fmap_function_positions,
                     fmap_heterogeneous_function_positions, reals_cuts, fmap_equality, result_observations, dimension_widths, fmap_tuple, nested_list_rel, predicate_domain)
            if key in tagged and tagged[key] != value:
                raise ValueError(f"conflicting @[hol] references for {rel}:{lean_name}")
            tagged[key] = value
    return tagged


def build_inventory(root: Path = ROOT) -> list[dict[str, Any]]:
    """Build a review inventory template without claiming statement review."""
    tagged = tagged_declarations(root)
    inventory: dict[tuple[str, str], dict[str, Any]] = {}
    for (lean_path, lean_name), (
        hol_path, hol_name, list_fields, names_fields, boundary_fields, fmap_fields,
        fmap_result, fmap_relation, fmap_equalities, words_bitvec, fmap_parameters,
        fmap_existentials, dimension_width,
        fmap_function_positions, fmap_heterogeneous_function_positions, reals_cuts,
        fmap_equality, result_observations, dimension_widths, fmap_tuple, nested_list_rel, predicate_domain,
    ) in tagged.items():
        entry = {
            "hol_path": hol_path,
            "hol_name": hol_name,
            "lean_path": lean_path,
            "lean_name": lean_name,
            "statement_status": "pending_statement_review",
            "reviewer": "Codex (reference inventory)",
        }
        if list_fields:
            entry["list_as_array"] = list(list_fields)
        if names_fields:
            entry["names_as_string"] = list(names_fields)
        if boundary_fields:
            entry["names_as_string_boundary"] = list(boundary_fields)
        if fmap_fields:
            entry["fmap_as_finite_support"] = list(fmap_fields)
        if fmap_result:
            entry["fmap_as_finite_support_result"] = True
        if fmap_function_positions:
            entry["fmap_as_finite_support_function"] = list(fmap_function_positions)
        if fmap_tuple:
            entry["fmap_as_finite_support_tuple"] = list(fmap_tuple)
        if nested_list_rel:
            entry["nested_list_rel_as_mutual"] = list(nested_list_rel)
        if fmap_heterogeneous_function_positions:
            entry["fmap_as_finite_support_heterogeneous_function"] = list(
                fmap_heterogeneous_function_positions
            )
        if result_observations:
            entry["fmap_as_finite_support_result_observations"] = list(result_observations)
        if fmap_parameters:
            entry["fmap_as_finite_support_parameters"] = list(fmap_parameters)
        if predicate_domain:
            entry["fmap_as_finite_support_parameter_predicate_domain"] = list(predicate_domain)
        if fmap_existentials:
            entry["fmap_as_finite_support_existentials"] = list(fmap_existentials)
        if fmap_relation:
            entry["fmap_as_finite_support_relation"] = [
                f"{carrier}.{field}" if field else carrier
                for carrier, field in fmap_relation
            ]
        if fmap_equalities:
            entry["fmap_as_finite_support_equalities"] = True
        if words_bitvec:
            entry["words_as_type_indexed_bitvec"] = True
        if dimension_widths:
            entry["word_dimensions_as_widths"] = list(dimension_widths)
        if dimension_width:
            entry["word_dimension_as_width"] = dimension_width
        if reals_cuts:
            entry["reals_as_rational_cuts"] = True
        if fmap_equality:
            entry["fmap_as_finite_support_equality"] = True
        inventory[(lean_path, lean_name)] = entry

    for lean_path, lean_name in proof_theorem_declarations(root):
        inventory.setdefault(
            (lean_path, lean_name),
            {
                "hol_path": None,
                "hol_name": None,
                "lean_path": lean_path,
                "lean_name": lean_name,
                "statement_status": "no_hol_reference_pending_classification",
                "reviewer": "Codex (proof inventory)",
            },
        )

    for (lean_path, lean_name), (hol_path, hol_name, reviewer) in DOCUMENTED_MISMATCHES.items():
        if not lean_definition_exists(root, lean_path, lean_name):
            raise ValueError(f"documented mismatch is not a current declaration: {lean_path}:{lean_name}")
        inventory[(lean_path, lean_name)] = {
            "hol_path": hol_path,
            "hol_name": hol_name,
            "lean_path": lean_path,
            "lean_name": lean_name,
            "statement_status": "documented_mismatch",
            "reviewer": reviewer,
        }

    for (lean_path, lean_name), reviewer in INFRASTRUCTURE_THEOREMS.items():
        if not lean_theorem_exists(root, lean_path, lean_name):
            raise ValueError(f"infrastructure theorem is not a current theorem: {lean_path}:{lean_name}")
        inventory[(lean_path, lean_name)] = {
            "hol_path": None,
            "hol_name": None,
            "lean_path": lean_path,
            "lean_name": lean_name,
            "statement_status": "no_hol_reference_pending_classification",
            "reviewer": reviewer,
        }

    # These source/theorem pairs were checked against their HOL declaration
    # statements in the active review task, not merely copied from attributes.
    reviewed_exact = {
        ("Flapjack/Misc/FindIndex.lean", "findIndex"),
        ("Flapjack/Compiler/Backend/LabToTarget/Positions.lean", "findPos"),
        ("Flapjack/Compiler/Backend/LabToTarget/Positions.lean", "getFfiIndex"),
        ("Flapjack/Compiler/Backend/LabToTarget/Padding.lean", "padBytes"),
        ("Flapjack/Compiler/Backend/LabToTarget/ShmemInfo.lean", "ShmemInfoNum"),
        ("Flapjack/Compiler/Backend/LabToTarget/ShmemInfo.lean", "listAddIfFresh"),
        ("Flapjack/Compiler/Backend/LabToTarget/ShmemInfo.lean", "getMemopInfo"),
        ("Flapjack/Misc/ListSubset.lean", "listSubset"),
        ("Flapjack/Compiler/Backend/LabToTarget/Compile.lean", "Config"),
        ("Flapjack/Misc/LList.lean", "lprefixAntisymHOL"),
        ("Flapjack/Misc/LList.lean", "lprefixTransHOL"),
        ("Flapjack/Misc/LList.lean", "prefixesLprefixTotalHOL"),
        ("Flapjack/Compiler/Backend/RegAlloc.lean", "isStackVar"),
        ("Flapjack/Compiler/Backend/RegAlloc.lean", "isPhyVar"),
        ("Flapjack/Compiler/Backend/RegAlloc.lean", "isAllocVar"),
        ("Flapjack/Compiler/Backend/RegAlloc.lean", "conventionPartitions"),
        ("Flapjack/Misc/LprefixLub.lean", "equivLprefixChain"),
        ("Flapjack/Misc/LprefixLub.lean", "lprefixRel"),
        ("Flapjack/Misc/LprefixLub.lean", "lprefix_lub_is_chain"),
        ("Flapjack/Misc/LprefixLub.lean", "equivLprefixChain_thm"),
        ("Flapjack/Misc/LprefixLub.lean", "equiv_lprefix_chain_thm2"),
        ("Flapjack/Misc/LprefixLub.lean", "lprefix_rel_lnth"),
        ("Flapjack/Misc/LprefixLub.lean", "IMP_equiv_lprefix_chain"),
        ("Flapjack/Misc/LprefixLub.lean", "lprefix_lub_equiv_chain2"),
        ("Flapjack/Misc/LprefixLub.lean", "IMP_build_lprefix_lub_EQ"),
        ("Flapjack/Misc/LprefixLub.lean", "llistShorter"),
        ("Flapjack/Misc/LprefixLub.lean", "llistShorter_fromList"),
        ("Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean", "CrepResultHOLExact"),
        ("Flapjack/Pancake/Semantics/CrepSem/EvaluateHOL.lean", "exitLoopCrepResult"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "genlist_less_than"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "genlist_not_in"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "genlist_all_distinct"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "moreThenNotMaxList"),
        ("Flapjack/Pancake/Proofs/CrepInline.lean", "max_list_genlist_add_suc_val"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "map_pick_up_first"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "tuple_4_o"),
        ("Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean", "convertResHOL"),
        ("Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean", "convertResHOL_eqCase1"),
        ("Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean", "isContResHOL"),
        ("Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean", "isContResHOL_eqDisj"),
        ("Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean", "resVsHOL"),
        ("Flapjack/Pancake/Proofs/PanStructs/CompileCorrect.lean", "everyConvertVEq"),
        ("Flapjack/Pancake/Proofs/PanStructs/StructInfosOkExact.lean",
         "structInfosOkHOLExact_lookup_fields_nodup"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "numCasesLemma"),
        ("Flapjack/Pancake/PanGlobals.lean", "fpermName"),
        ("Flapjack/Pancake/PanGlobals.lean", "resortDeclsHOL"),
        ("Flapjack/Pancake/PanGlobals.lean", "decShapesHOL"),
        ("Flapjack/Pancake/PanGlobals.lean", "freshNameMlS"),
        ("Flapjack/Pancake/PanGlobals.lean", "newMainNameHOL"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fpermName_cancel"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "fpermName_cong"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "EVERY_fperm_decsHOL"),
        ("Flapjack/Pancake/Proofs/PanGlobals.lean", "FILTER_decs_fperm_decsHOL"),
        ("Flapjack/Pancake/Proofs/PanToCrep.lean", "mod_eq_of_lt_eq"),
        ("Flapjack/Pancake/Proofs/PanToCrep.lean", "option_ne_none_iff_exists"),
        ("Flapjack/Pancake/Proofs/PanToCrep.lean", "prod_mk_pair_eq_id"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "isDeclHOL"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "isFunctionHOL"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "isNameHOL"),
        ("Flapjack/Pancake/PanLang/Shape.lean", "memImpShapeSizeHOL"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "functionsHOL_append"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "functionsHOL_filter_isFunction"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "functionsHOL_filter_isDecl"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "isWfShapeValueHOLExact"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "isWfShapeValueHOLExact_shapeOfHOLExact"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "panPrimopHOLExact_isWfShapeValueHOLExact"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "isWfShapeValueHOLExact_nil_step1"),
        ("Flapjack/Pancake/Semantics/PanProps.lean",
         "isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "isWfShapeValueHOLExact_drop"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "memLoadHOLExact_isWfShapeValueHOLExact"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "memLoadHOLExact_shape_eq"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "memLoadHOLExact_some_shapeOf_eq"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "everyExpHOL"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "expsOfHOL"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "localisedExpHOL"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "namelessExpHOL"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "localisedProgHOL"),
        ("Flapjack/Pancake/Semantics/PanProps.lean", "optMmapEqSomeHelper"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "exceptionsHOL"),
        ("Flapjack/Pancake/PanLang/Exp.lean", "varExpHOL"),
        ("Flapjack/Pancake/PanLang/Exp.lean", "globalVarExpHOL_spec"),
        ("Flapjack/Pancake/PanLang/Exp.lean", "memImpExpSizeHOL"),
        ("Flapjack/Pancake/PanToCrep/Compile.lean", "crepVarsHOL"),
        ("Flapjack/Pancake/PanToCrep/Compile.lean", "loadMemOpHOL"),
        ("Flapjack/Pancake/Semantics/PanProps/LocalisedExpSimps.lean", "localisedExpSimpsHOL"),
        ("Flapjack/Pancake/Semantics/PanProps/NamelessExpSimps.lean", "namelessExpSimpsHOL"),
        ("Flapjack/Misc/GoodDimindex.lean", "goodDimindex"),
        ("Flapjack/Pancake/Semantics/PanProps/MemByteArray.lean", "readWriteBytearrayLemma"),
        ("Flapjack/Pancake/Semantics/PanSem/MemLoad32Alt.lean", "panMemLoad32HOL_eq_alt"),
        ("Flapjack/Pancake/Semantics/PanSem/MemStore32Alt.lean", "panMemStore32HOL_eq_alt"),
        ("Flapjack/Pancake/Semantics/PanSem/ValueHOL.lean", "valWordHOL"),
        ("Flapjack/Pancake/PanLang.lean", "Index"),
        ("Flapjack/Pancake/PanLang.lean", "Stcname"),
        ("Flapjack/Pancake/PanLang.lean", "Fldname"),
        ("Flapjack/Pancake/PanLang.lean", "Varname"),
        ("Flapjack/Pancake/PanLang.lean", "Funname"),
        ("Flapjack/Pancake/PanLang.lean", "Eid"),
        ("Flapjack/Pancake/PanLang.lean", "Decname"),
        ("Flapjack/Pancake/PanToCrep/Compile.lean", "storeMemOpHOL"),
        ("Flapjack/Pancake/PanLang/Prog.lean", "expIdsHOL"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "sizeOfEidsHOL"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "isWfFldsExactHOL"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "isWfCtxtExactHOL"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "sizeOfShapeWithContextHOL"),
        ("Flapjack/Pancake/PanLang/Decl.lean", "inlinableHOL"),
        ("Flapjack/Pancake/PanLang/Prog.lean", "funIdsHOL"),
        ("Flapjack/Pancake/PanLang/Prog.lean", "tailCallHOL"),
        ("Flapjack/Pancake/PanLang/Prog.lean", "assignCallHOL"),
        ("Flapjack/Pancake/PanLang/Prog.lean", "standAloneCallHOL"),
        ("Flapjack/Pancake/PanLang/Prog.lean", "freeVarIdsHOL"),
        ("Flapjack/Pancake/PanLang/Prog.lean", "nestedSeqHOL"),
        ("Flapjack/Pancake/PanLang/Exp.lean", "shapeValHOL"),
        ("Flapjack/Pancake/PanLang/Exp.lean", "shapeValsHOL"),
        ("Flapjack/Pancake/PanLang/Shape.lean", "sizeOfShapeHOL"),
        ("Flapjack/Pancake/PanLang/Shape.lean", "shapeToStrHOL"),
        ("Flapjack/Pancake/PanLang/Shape.lean", "withShapeHOL"),
        ("Flapjack/AstHOL.lean", "Shift"),
        ("Flapjack/Pancake/PanLang.lean", "PanLangShift"),
        ("Flapjack/FfiHOL.lean", "HolFfiOutcome"),
        ("Flapjack/FfiHOL.lean", "HolOracleResult"),
        ("Flapjack/FfiHOL.lean", "HolShmemOp"),
        ("Flapjack/FfiHOL.lean", "HolFfiName"),
        ("Flapjack/FfiHOL.lean", "HolOracleFunction"),
        ("Flapjack/FfiHOL.lean", "HolOracle"),
        ("Flapjack/FfiHOL.lean", "HolIoEvent"),
        ("Flapjack/FfiHOL.lean", "HolFinalEvent"),
        ("Flapjack/FfiHOL.lean", "HolFfiState"),
        ("Flapjack/FfiHOL.lean", "initialHolFfiState"),
        ("Flapjack/FfiHOL.lean", "HolFfiResult"),
        ("Flapjack/FfiHOL.lean", "callFFIHOL"),
        ("Flapjack/Compiler/Backend/RegAlloc.lean", "isStackVar"),
        ("Flapjack/Compiler/Backend/RegAlloc.lean", "isPhyVar"),
        ("Flapjack/Compiler/Backend/RegAlloc.lean", "isAllocVar"),
        ("Flapjack/Compiler/Backend/RegAlloc.lean", "conventionPartitions"),
        ("Flapjack/Compiler/Backend/StackRemove.lean", "leftShiftInst"),
        ("Flapjack/Compiler/Backend/StackRemove.lean", "rightShiftInst"),
        ("Flapjack/Compiler/Backend/StackRemove.lean", "constInst"),
        ("Flapjack/Compiler/Backend/StackRemove.lean", "loadInst"),
        ("Flapjack/Compiler/Backend/StackRemove.lean", "storeInst"),
        ("Flapjack/Compiler/Backend/StackRemove.lean", "haltInst"),
        ("Flapjack/Pancake/PanStructs.lean", "afindi"),
        ("Flapjack/Misc/Sptree.lean", "NumSet"),
        ("Flapjack/Pancake/WordConvs.lean", "distinctTarRegExact"),
        ("Flapjack/Pancake/WordConvs.lean", "twoRegInstExact"),
        ("Flapjack/Pancake/WordConvs.lean", "instArgConventionExact"),
        ("Flapjack/Pancake/WordConvs.lean", "instOkLessExact"),
        ("Flapjack/Pancake/Semantics/CrepProps.lean", "crepExpsOfHOL"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmOffsetOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmRegOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmFpRegOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmRegImmOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmFpOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmCmpOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmArithOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmInstOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "asmOkExact"),
        ("Flapjack/Compiler/Backend/StackProps.lean", "asmAddrOkExact"),
        ("Flapjack/Compiler/Encoders/Asm.lean", "AsmConfigExact"),
        ("Flapjack/Pancake/Proofs/PanSimp.lean", "mapSndFEq"),
        ("Flapjack/Pancake/Proofs/PanSimp.lean", "expIdsHOL_retToTailHOL_eq"),
        ("Flapjack/Pancake/Proofs/PanSimp.lean", "expIdsHOL_seqAssocHOL_eq"),
        ("Flapjack/Pancake/Proofs/PanSimp.lean", "expIdsHOL_panSimpCompileHOL_eq"),
        ("Flapjack/Pancake/Proofs/PanSimp.lean", "functionsHOL_panSimpDeclsHOL_eq"),
        ("Flapjack/Pancake/Proofs/PanSimp.lean", "sizeOfEidsHOL_panSimpDeclsHOL_eq"),
        ("Flapjack/Pancake/Proofs/PanSimp.lean", "firstCompileProgAllDistinctHOL"),
        ("Flapjack/Pancake/Proofs/PanSimp.lean", "decsStcnamesHOLExact_panSimpDeclsHOL_eq"),
        ("Flapjack/Pancake/PanSimp.lean", "smartSeqHOL"),
        ("Flapjack/Pancake/PanSimp.lean", "seqCallRetHOL"),
        ("Flapjack/Pancake/PanSimp.lean", "seqAssocHOL"),
        ("Flapjack/Pancake/PanSimp.lean", "retToTailHOL"),
        ("Flapjack/Pancake/PanSimp.lean", "panSimpCompileHOL"),
        ("Flapjack/Pancake/PanSimp.lean", "panSimpDeclsHOL"),
        ("Flapjack/Pancake/CrepToLoop/Proofs/Primop.lean", "crepPrimopLoopPrimopHOL"),
        ("Flapjack/Pancake/LoopToWord.lean", "findVarHOL"),
        ("Flapjack/Pancake/LoopToWord.lean", "toNumSetHOL"),
        ("Flapjack/Pancake/LoopToWord.lean", "fromNumSetHOL"),
        ("Flapjack/Pancake/LoopToWord.lean", "mkNewCutsetHOL"),
        ("Flapjack/Compiler/Backend/WordAlloc/Proofs/CutEnvLemma.lean", "cutEnvLemma"),
        ("Flapjack/Compiler/Backend/WordAlloc/ReadsExp.lean", "getReadsExpHOL"),
    }
    for key in reviewed_exact:
        # A source comparison cannot claim an exact HOL port after its tag is
        # withdrawn. Keep the untagged proof in the classification queue.
        if key in inventory and inventory[key]["hol_name"] is not None:
            inventory[key]["statement_status"] = "reviewed_exact"
            inventory[key]["reviewer"] = "Codex (source comparison)"

    for key, (hol_path, hol_name, reviewer) in WITHDRAWN_HOL_DECLARATIONS.items():
        inventory[key] = {
            "hol_path": hol_path,
            "hol_name": hol_name,
            "lean_path": key[0],
            "lean_name": key[1],
            "statement_status": "documented_mismatch",
            "reviewer": reviewer,
        }

    return [inventory[key] for key in sorted(inventory)]


def validate_inventory(
    records: list[dict[str, Any]],
    proof_declarations: set[tuple[str, str]],
    tagged: dict[
        tuple[str, str],
        tuple[str, str, tuple[str, ...], tuple[str, ...], tuple[str, ...]],
    ],
    data_declarations_: set[tuple[str, str]] | None = None,
) -> list[str]:
    errors: list[str] = []
    by_key: dict[tuple[str, str], dict[str, Any]] = {}
    for index, record in enumerate(records, start=1):
        missing_fields = FIELDS - record.keys()
        if missing_fields:
            errors.append(f"record {index}: missing fields {sorted(missing_fields)}")
            continue
        key = (record["lean_path"], record["lean_name"])
        if key in by_key:
            errors.append(f"duplicate manifest entry: {key[0]}:{key[1]}")
            continue
        by_key[key] = record
        status = record["statement_status"]
        if status not in VALID_STATUSES:
            errors.append(f"{key[0]}:{key[1]}: invalid statement_status {status!r}")
        reviewer = record["reviewer"]
        if not isinstance(reviewer, str) or not reviewer.strip():
            errors.append(f"{key[0]}:{key[1]}: reviewer metadata is required")
        else:
            pending_note_error = reviewed_note_pending_error(key, status, reviewer)
            if pending_note_error:
                errors.append(pending_note_error)

        hol_path, hol_name = record["hol_path"], record["hol_name"]
        tag = tagged.get(key)
        if tag is not None and len(tag) < 8:
            tag = tag + ((),) * (8 - len(tag))
        list_fields = tag[2] if tag is not None else ()
        names_fields = tag[3] if tag is not None else ()
        boundary_fields = tag[4] if tag is not None else ()
        fmap_fields = tag[5] if tag is not None else ()
        fmap_result = bool(tag[6]) if tag is not None else False
        fmap_relation = tag[7] if tag is not None else ()
        fmap_equalities = bool(tag[8]) if tag is not None and len(tag) > 8 else False
        words_bitvec = bool(tag[9]) if tag is not None and len(tag) > 9 else False
        fmap_parameters = tag[10] if tag is not None and len(tag) > 10 else ()
        fmap_existentials = tag[11] if tag is not None and len(tag) > 11 else ()
        dimension_width = tag[12] if tag is not None and len(tag) > 12 else None
        fmap_function_positions = tag[13] if tag is not None and len(tag) > 13 else ()
        fmap_heterogeneous_function_positions = (
            tag[14] if tag is not None and len(tag) > 14 else ()
        )
        reals_cuts = bool(tag[15]) if tag is not None and len(tag) > 15 else False
        fmap_equality = bool(tag[16]) if tag is not None and len(tag) > 16 else False
        result_observations = tag[17] if tag is not None and len(tag) > 17 else ()
        dimension_widths = tag[18] if tag is not None and len(tag) > 18 else ()
        fmap_tuple = tag[19] if tag is not None and len(tag) > 19 else ()
        nested_list_rel = tag[20] if tag is not None and len(tag) > 20 else ()
        predicate_domain = tag[21] if tag is not None and len(tag) > 21 else ()
        predicate_status = "reviewed_fmap_as_finite_support_parameter_predicate_domain"
        if tuple(record.get("fmap_as_finite_support_parameter_predicate_domain", ())) != predicate_domain:
            errors.append(f"{key[0]}:{key[1]}: predicate-domain binders do not match @[hol] tag")
        if bool(predicate_domain) != (status == predicate_status):
            errors.append(f"{key[0]}:{key[1]}: predicate-domain qualifier requires its reviewed status")
        if predicate_domain:
            if predicate_domain != ("code1", "rel"):
                errors.append(f"{key[0]}:{key[1]}: predicate-domain qualifier requires [code1, rel]")
            allowed_predicate_sites = {
                ("cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml", "eval_sim_def",
                 "Flapjack/Compiler/Backend/ClosToBvl/Proofs/EvalSim.lean", "evalSim"),
                ("cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml", "IMP_semantics_eq",
                 "Flapjack/Compiler/Backend/ClosToBvl/Proofs/EvalSim.lean", "impSemanticsEq"),
            }
            if (hol_path, hol_name, key[0], key[1]) not in allowed_predicate_sites:
                errors.append(f"{key[0]}:{key[1]}: predicate-domain qualifier is restricted to the reviewed simulation declarations")
            if any(tag[2:21]):
                errors.append(f"{key[0]}:{key[1]}: predicate-domain qualifier cannot combine with other representation qualifiers")
            if (not isinstance(reviewer, str) or "source" not in reviewer.lower() or
                    any(name not in reviewer for name in predicate_domain)):
                errors.append(f"{key[0]}:{key[1]}: predicate-domain review must name the source and both binders")
        if tuple(record.get("nested_list_rel_as_mutual", ())) != nested_list_rel:
            errors.append(f"{key[0]}:{key[1]}: nested-list relation qualifier does not match @[hol] tag")
        nested_combined_status = "reviewed_fmap_as_finite_support_nested_list_rel_as_mutual"
        expected_nested_status = nested_combined_status if fmap_fields else "reviewed_nested_list_rel_as_mutual"
        if bool(nested_list_rel) != (status in {"reviewed_nested_list_rel_as_mutual", nested_combined_status}):
            errors.append(f"{key[0]}:{key[1]}: nested-list relation requires its reviewed status")
        if nested_list_rel and status != expected_nested_status:
            errors.append(f"{key[0]}:{key[1]}: nested-list relation and finite-map qualifiers require matching combined status")
        if status == nested_combined_status and tuple(fmap_fields) != ("refs", "code"):
            errors.append(f"{key[0]}:{key[1]}: combined nested-list qualifier requires refs and code fields")
        if nested_list_rel and (not isinstance(reviewer, str) or "functionsRel_iff" not in reviewer or
                                "nested_list_rel_as_mutual" not in reviewer or "source" not in reviewer.lower()):
            errors.append(f"{key[0]}:{key[1]}: nested-list relation review must cite qualifier, source and functionsRel_iff")
        tuple_status = "reviewed_fmap_as_finite_support_tuple_words_as_type_indexed_bitvec"
        if tuple(record.get("fmap_as_finite_support_tuple", ())) != fmap_tuple:
            errors.append(f"{key[0]}:{key[1]}: tuple-map positions do not match @[hol] tag")
        if bool(fmap_tuple) != (status == tuple_status) or (fmap_tuple and not words_bitvec):
            errors.append(f"{key[0]}:{key[1]}: tuple maps require their combined reviewed status and word qualifier")
        if fmap_tuple and (not isinstance(reviewer, str) or
                           any(pos not in reviewer for pos in fmap_tuple) or
                           "source" not in reviewer.lower()):
            errors.append(f"{key[0]}:{key[1]}: tuple-map review must name the source and both positions")
        manifest_observations = tuple(record.get("fmap_as_finite_support_result_observations", ()))
        observation_status = "reviewed_fmap_as_finite_support_result_observations"
        combined_observation_status = "reviewed_fmap_as_finite_support_parameter_observations"
        if manifest_observations != result_observations:
            errors.append(f"{key[0]}:{key[1]}: manifest result observation producers do not match @[hol] tag")
        if bool(result_observations) != (status in {observation_status, combined_observation_status}):
            errors.append(f"{key[0]}:{key[1]}: result observations require matching reviewed result-observation status")
        if result_observations:
            if any(value for index, value in enumerate(tag[2:17], start=2)
                   if not (status == combined_observation_status and index == 10)):
                errors.append(f"{key[0]}:{key[1]}: result observations cannot combine with other representation qualifiers")
            if not isinstance(reviewer, str) or not reviewer.strip():
                errors.append(f"{key[0]}:{key[1]}: result observations require source-comparison note")
        if status == combined_observation_status:
            if not fmap_parameters or not result_observations:
                errors.append(f"{key[0]}:{key[1]}: combined parameter observations require both lists")
            if not isinstance(reviewer, str) or "source" not in reviewer.lower() or any(
                    name not in reviewer for name in (*fmap_parameters, *result_observations)):
                errors.append(f"{key[0]}:{key[1]}: combined observation review must name source, parameters and producers")
        manifest_list_fields = tuple(record.get("list_as_array", ()))
        manifest_names_fields = tuple(record.get("names_as_string", ()))
        manifest_boundary_fields = tuple(record.get("names_as_string_boundary", ()))
        manifest_fmap_fields = tuple(record.get("fmap_as_finite_support", ()))
        manifest_fmap_result = bool(record.get("fmap_as_finite_support_result", False))
        manifest_fmap_function = tuple(record.get("fmap_as_finite_support_function", ()))
        manifest_fmap_heterogeneous_function = tuple(
            record.get("fmap_as_finite_support_heterogeneous_function", ())
        )
        manifest_fmap_parameters = tuple(record.get("fmap_as_finite_support_parameters", ()))
        manifest_fmap_existentials = tuple(record.get("fmap_as_finite_support_existentials", ()))
        manifest_fmap_relation = tuple(record.get("fmap_as_finite_support_relation", ()))
        manifest_fmap_equalities = bool(record.get("fmap_as_finite_support_equalities", False))
        manifest_fmap_equality = bool(record.get("fmap_as_finite_support_equality", False))
        tag_fmap_relation = tuple(
            f"{carrier}.{field}" if field else carrier
            for carrier, field in fmap_relation
        )
        if manifest_list_fields != list_fields:
            errors.append(
                f"{key[0]}:{key[1]}: manifest list_as_array fields do not match its @[hol] tag"
            )
        if manifest_names_fields != names_fields:
            errors.append(
                f"{key[0]}:{key[1]}: manifest names_as_string fields do not match its @[hol] tag"
            )
        if manifest_boundary_fields != boundary_fields:
            errors.append(
                f"{key[0]}:{key[1]}: manifest names_as_string_boundary fields do not match its @[hol] tag"
            )
        if manifest_fmap_fields != fmap_fields:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support fields do not match its @[hol] tag"
            )
        if manifest_fmap_result != fmap_result:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support_result does not match its @[hol] tag"
            )
        if manifest_fmap_function != fmap_function_positions:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support_function positions do not match its @[hol] tag"
            )
        if manifest_fmap_heterogeneous_function != fmap_heterogeneous_function_positions:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support_heterogeneous_function positions do not match its @[hol] tag"
            )
        if manifest_fmap_parameters != fmap_parameters:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support_parameters do not match its @[hol] tag"
            )
        if manifest_fmap_existentials != fmap_existentials:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support_existentials do not match its @[hol] tag"
            )
        if manifest_fmap_relation != tag_fmap_relation:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support_relation entries do not match its @[hol] tag"
            )
        if manifest_fmap_equalities != fmap_equalities:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support_equalities does not match its @[hol] tag"
            )
        if manifest_fmap_equality != fmap_equality:
            errors.append(
                f"{key[0]}:{key[1]}: manifest fmap_as_finite_support_equality does not match its @[hol] tag"
            )
        if fmap_equality and (
            fmap_fields or fmap_result or fmap_relation or fmap_equalities
            or fmap_parameters or fmap_existentials or fmap_function_positions
            or fmap_heterogeneous_function_positions
        ):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_equality (single map "
                "equality) is mutually exclusive with other finite-map qualifiers"
            )
        combined_equality_words_status = (
            "reviewed_fmap_as_finite_support_equality_words_as_type_indexed_bitvec"
        )
        if fmap_equality and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_equality @[hol] tag cannot have "
                "reviewed_exact status; use reviewed_fmap_as_finite_support_equality after source comparison"
            )
        if fmap_equality and words_bitvec and status != combined_equality_words_status:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_equality combined with "
                "words_as_type_indexed_bitvec requires the combined review status "
                "reviewed_fmap_as_finite_support_equality_words_as_type_indexed_bitvec"
            )
        if (
            fmap_equality
            and not words_bitvec
            and status != "reviewed_fmap_as_finite_support_equality"
        ):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_equality @[hol] tag needs a reviewed "
                "source classification (reviewed_fmap_as_finite_support_equality)"
            )
        if not fmap_equality and status in {
            "reviewed_fmap_as_finite_support_equality",
            combined_equality_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_equality needs a "
                "fmap_as_finite_support_equality @[hol] tag"
            )
        if fmap_equality:
            equality_reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in equality_reviewer_text or "fmap_as_finite_support_equality" not in equality_reviewer_text:
                errors.append(
                    f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_equality requires a "
                    "source-comparison note naming the qualifier"
                )
        manifest_words_bitvec = bool(record.get("words_as_type_indexed_bitvec", False))
        if manifest_words_bitvec != words_bitvec:
            errors.append(
                f"{key[0]}:{key[1]}: manifest words_as_type_indexed_bitvec does not match its @[hol] tag"
            )
        manifest_dimension_width = record.get("word_dimension_as_width")
        if manifest_dimension_width != dimension_width:
            errors.append(
                f"{key[0]}:{key[1]}: manifest word_dimension_as_width does not match its @[hol] tag"
            )
        if dimension_width:
            if words_bitvec:
                errors.append(
                    f"{key[0]}:{key[1]}: word_dimension_as_width is mutually exclusive with words_as_type_indexed_bitvec"
                )
            if status == "reviewed_exact":
                errors.append(
                    f"{key[0]}:{key[1]}: word_dimension_as_width @[hol] tag cannot have reviewed_exact status"
                )
            if status != "reviewed_word_dimension_as_width":
                errors.append(
                    f"{key[0]}:{key[1]}: word_dimension_as_width needs reviewed_word_dimension_as_width status"
                )
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text or dimension_width.lower() not in reviewer_text:
                errors.append(
                    f"{key[0]}:{key[1]}: reviewed_word_dimension_as_width requires a source-comparison note naming `{dimension_width}`"
                )
        elif status == "reviewed_word_dimension_as_width":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_word_dimension_as_width needs a matching @[hol] qualifier"
            )
        manifest_dimensions = tuple(record.get("word_dimensions_as_widths", ()))
        if manifest_dimensions != dimension_widths:
            errors.append(f"{key[0]}:{key[1]}: manifest word_dimensions_as_widths does not match its @[hol] tag")
        if dimension_widths:
            if len(dimension_widths) != 2 or len(set(dimension_widths)) != 2:
                errors.append(f"{key[0]}:{key[1]}: word_dimensions_as_widths requires exactly two distinct dimensions")
            if (dimension_width or words_bitvec or list_fields or names_fields or boundary_fields
                    or fmap_fields or fmap_result or fmap_relation or fmap_equalities or fmap_equality
                    or fmap_parameters or fmap_existentials or fmap_function_positions
                    or fmap_heterogeneous_function_positions or result_observations):
                errors.append(f"{key[0]}:{key[1]}: word_dimensions_as_widths conflicts with other representation qualifiers except reals_as_rational_cuts")
            if status != "reviewed_word_dimensions_as_widths":
                errors.append(f"{key[0]}:{key[1]}: word_dimensions_as_widths needs reviewed_word_dimensions_as_widths status, never reviewed_exact")
            note = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in note or "word_dimensions_as_widths" not in note or any(name.lower() not in note for name in dimension_widths):
                errors.append(f"{key[0]}:{key[1]}: word_dimensions_as_widths requires a source-comparison note naming both dimensions")
        elif status == "reviewed_word_dimensions_as_widths":
            errors.append(f"{key[0]}:{key[1]}: reviewed_word_dimensions_as_widths needs a matching @[hol] qualifier")
        if bool(record.get("reals_as_rational_cuts", False)) != reals_cuts:
            errors.append(
                f"{key[0]}:{key[1]}: manifest reals_as_rational_cuts does not match its @[hol] tag"
            )
        other_qualified = bool(
            list_fields or names_fields or boundary_fields or fmap_fields or fmap_result
            or fmap_relation or fmap_equalities or words_bitvec or fmap_parameters
            or fmap_existentials or dimension_width or dimension_widths or fmap_function_positions
        )
        if reals_cuts:
            if status == "reviewed_exact":
                errors.append(
                    f"{key[0]}:{key[1]}: reals_as_rational_cuts @[hol] tag cannot have reviewed_exact status"
                )
            if not other_qualified and status != "reviewed_reals_as_rational_cuts":
                errors.append(
                    f"{key[0]}:{key[1]}: reals_as_rational_cuts alone needs "
                    "reviewed_reals_as_rational_cuts status"
                )
            if other_qualified and status == "reviewed_reals_as_rational_cuts":
                errors.append(
                    f"{key[0]}:{key[1]}: reals_as_rational_cuts with other qualifiers keeps "
                    "the status those qualifiers require"
                )
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if ("source" not in reviewer_text or "reals_as_rational_cuts" not in reviewer_text
                    or "soundness" not in reviewer_text):
                errors.append(
                    f"{key[0]}:{key[1]}: reals_as_rational_cuts requires a source-comparison "
                    "note naming the qualifier and docs/SOUNDNESS.md item 8"
                )
        elif status == "reviewed_reals_as_rational_cuts":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_reals_as_rational_cuts needs a matching @[hol] qualifier"
            )
        if record.get("inherits_reals_as_rational_cuts", False):
            if reals_cuts:
                errors.append(
                    f"{key[0]}:{key[1]}: a reals_as_rational_cuts-qualified declaration "
                    "does not also record an inherited assumption"
                )
            if tag is None:
                errors.append(
                    f"{key[0]}:{key[1]}: inherits_reals_as_rational_cuts is only for tagged declarations"
                )
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "inherit" not in reviewer_text or "reals_as_rational_cuts" not in reviewer_text:
                errors.append(
                    f"{key[0]}:{key[1]}: inherits_reals_as_rational_cuts requires a note "
                    "naming the inherited reals_as_rational_cuts assumption"
                )
        combined_words_status = (
            "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec"
        )
        combined_function_words_status = (
            "reviewed_fmap_as_finite_support_function_words_as_type_indexed_bitvec"
        )
        heterogeneous_function_status = (
            "reviewed_fmap_as_finite_support_heterogeneous_function"
        )
        combined_heterogeneous_function_words_status = (
            "reviewed_fmap_as_finite_support_heterogeneous_function_words_as_type_indexed_bitvec"
        )
        combined_relation_words_status = (
            "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec"
        )
        combined_parameter_words_status = (
            "reviewed_fmap_as_finite_support_parameters_words_as_type_indexed_bitvec"
        )
        combined_existential_words_status = (
            "reviewed_fmap_as_finite_support_existentials_words_as_type_indexed_bitvec"
        )
        # Both map translations retain their separate witness and review rules.
        combined_relation_existential_status = (
            "reviewed_fmap_as_finite_support_relation_existentials"
        )
        combined_relation_existential_words_status = (
            "reviewed_fmap_as_finite_support_relation_existentials_words_as_type_indexed_bitvec"
        )
        if words_bitvec and fmap_fields and status != combined_words_status:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support combined with "
                "words_as_type_indexed_bitvec requires the combined review status "
                "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec"
            )
        if words_bitvec and fmap_function_positions and status != combined_function_words_status:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_function combined with "
                "words_as_type_indexed_bitvec requires the combined review status "
                "reviewed_fmap_as_finite_support_function_words_as_type_indexed_bitvec"
            )
        if (words_bitvec and fmap_heterogeneous_function_positions
                and status != combined_heterogeneous_function_words_status):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_heterogeneous_function "
                "combined with words_as_type_indexed_bitvec requires the combined review status "
                "reviewed_fmap_as_finite_support_heterogeneous_function_words_as_type_indexed_bitvec"
            )
        if words_bitvec and fmap_relation and status not in {
            combined_relation_words_status,
            combined_relation_existential_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_relation combined with "
                "words_as_type_indexed_bitvec requires the combined review status "
                "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec"
            )
        if words_bitvec and fmap_parameters and status != combined_parameter_words_status:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_parameters combined with "
                "words_as_type_indexed_bitvec requires the combined review status "
                "reviewed_fmap_as_finite_support_parameters_words_as_type_indexed_bitvec"
            )
        if words_bitvec and fmap_existentials and status not in {
            combined_existential_words_status,
            combined_relation_existential_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_existentials combined with "
                "words_as_type_indexed_bitvec requires the combined review status "
                "reviewed_fmap_as_finite_support_existentials_words_as_type_indexed_bitvec"
            )
        if status == combined_words_status and not (words_bitvec and fmap_fields):
            errors.append(
                f"{key[0]}:{key[1]}: "
                "reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec needs "
                "both the fmap_as_finite_support and words_as_type_indexed_bitvec @[hol] qualifiers"
            )
        if status == combined_function_words_status and not (
            words_bitvec and fmap_function_positions
        ):
            errors.append(
                f"{key[0]}:{key[1]}: "
                "reviewed_fmap_as_finite_support_function_words_as_type_indexed_bitvec needs "
                "both fmap_as_finite_support_function and words_as_type_indexed_bitvec qualifiers"
            )
        if status == combined_heterogeneous_function_words_status and not (
            words_bitvec and fmap_heterogeneous_function_positions
        ):
            errors.append(
                f"{key[0]}:{key[1]}: {status} needs both "
                "fmap_as_finite_support_heterogeneous_function and "
                "words_as_type_indexed_bitvec qualifiers"
            )
        if status == combined_relation_words_status and not (
            words_bitvec and fmap_relation
        ):
            errors.append(
                f"{key[0]}:{key[1]}: "
                "reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec needs "
                "both the fmap_as_finite_support_relation and words_as_type_indexed_bitvec @[hol] qualifiers"
            )
        if status == combined_parameter_words_status and not (
            words_bitvec and fmap_parameters
        ):
            errors.append(
                f"{key[0]}:{key[1]}: "
                "reviewed_fmap_as_finite_support_parameters_words_as_type_indexed_bitvec needs "
                "both the fmap_as_finite_support_parameters and words_as_type_indexed_bitvec qualifiers"
            )
        if status == combined_existential_words_status and not (
            words_bitvec and fmap_existentials
        ):
            errors.append(
                f"{key[0]}:{key[1]}: "
                "reviewed_fmap_as_finite_support_existentials_words_as_type_indexed_bitvec needs "
                "both the fmap_as_finite_support_existentials and words_as_type_indexed_bitvec qualifiers"
            )
        if status == combined_relation_existential_words_status and not (
            words_bitvec and fmap_existentials and fmap_relation
        ):
            errors.append(
                f"{key[0]}:{key[1]}: "
                "reviewed_fmap_as_finite_support_relation_existentials_words_as_type_indexed_bitvec needs "
                "the fmap_as_finite_support_relation, fmap_as_finite_support_existentials, and "
                "words_as_type_indexed_bitvec qualifiers"
            )
        if words_bitvec and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: words_as_type_indexed_bitvec @[hol] tag cannot have "
                "reviewed_exact status; use reviewed_words_as_type_indexed_bitvec after source comparison"
            )
        if words_bitvec and status not in {
            "reviewed_words_as_type_indexed_bitvec",
            "reviewed_fmap_as_finite_support_tuple_words_as_type_indexed_bitvec",
            combined_words_status,
            "reviewed_fmap_as_finite_support_function_words_as_type_indexed_bitvec",
            "reviewed_fmap_as_finite_support_result_words_as_type_indexed_bitvec",
            combined_heterogeneous_function_words_status,
            combined_relation_words_status,
            combined_parameter_words_status,
            combined_existential_words_status,
            combined_relation_existential_words_status,
            combined_equality_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: words_as_type_indexed_bitvec @[hol] tag needs a reviewed "
                "source classification (reviewed_words_as_type_indexed_bitvec, or the combined "
                "status alongside fmap_as_finite_support / fmap_as_finite_support_relation)"
            )
        if not words_bitvec and status == "reviewed_words_as_type_indexed_bitvec":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_words_as_type_indexed_bitvec needs a "
                "words_as_type_indexed_bitvec @[hol] tag"
            )
        if fmap_relation and (fmap_fields or fmap_result or fmap_parameters):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_relation (multi-carrier) is mutually "
                "exclusive with fmap_as_finite_support, fmap_as_finite_support_result, and fmap_as_finite_support_parameters"
            )
        if fmap_parameters and (fmap_fields or fmap_result or fmap_relation or fmap_equalities):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_parameters is mutually exclusive with other finite-map qualifiers"
            )
        if fmap_parameters and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_parameters @[hol] tag cannot have reviewed_exact status"
            )
        if fmap_parameters and status not in {
            "reviewed_fmap_as_finite_support_parameters",
            combined_parameter_words_status,
            combined_observation_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_parameters needs reviewed_fmap_as_finite_support_parameters status"
            )
        if not fmap_parameters and status in {
            "reviewed_fmap_as_finite_support_parameters",
            combined_parameter_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_parameters needs the matching @[hol] qualifier"
            )
        if fmap_parameters:
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text:
                errors.append(
                    f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_parameters requires a source-comparison note"
                )
        if status == combined_relation_existential_status and not (fmap_relation and fmap_existentials):
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_relation_existentials "
                "needs both relation and existential qualifiers"
            )
        if fmap_existentials and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_existentials @[hol] tag cannot have "
                "reviewed_exact status; use reviewed_fmap_as_finite_support_existentials after source comparison"
            )
        if fmap_existentials and status not in {
            "reviewed_fmap_as_finite_support_existentials",
            combined_existential_words_status,
            combined_relation_existential_status,
            combined_relation_existential_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_existentials @[hol] tag needs a reviewed "
                "source classification (reviewed_fmap_as_finite_support_existentials, or the combined "
                "status with words_as_type_indexed_bitvec)"
            )
        if not fmap_existentials and status in {
            "reviewed_fmap_as_finite_support_existentials",
            combined_existential_words_status,
            combined_relation_existential_status,
            combined_relation_existential_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_existentials needs a "
                "fmap_as_finite_support_existentials @[hol] tag"
            )
        if fmap_existentials:
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text or any(
                binder.lower() not in reviewer_text for binder in fmap_existentials
            ):
                errors.append(
                    f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_existentials requires "
                    "a source-comparison note naming every existential binder"
                )
        if fmap_relation and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_relation @[hol] tag cannot have "
                "reviewed_exact status; use reviewed_fmap_as_finite_support_relation after source comparison"
            )
        if fmap_relation and status not in {
            "reviewed_fmap_as_finite_support_relation",
            combined_relation_words_status,
            combined_relation_existential_status,
            combined_relation_existential_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_relation @[hol] tag needs a reviewed "
                "source classification (reviewed_fmap_as_finite_support_relation, or the combined "
                "status with words_as_type_indexed_bitvec)"
            )
        if not fmap_relation and status == "reviewed_fmap_as_finite_support_relation":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_relation needs a "
                "fmap_as_finite_support_relation @[hol] tag"
            )
        if fmap_relation:
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text:
                errors.append(
                    f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_relation requires a "
                    "source-comparison note in the reviewer field"
                )
        if fmap_result and (fmap_fields or fmap_parameters):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_result (standalone carrier) and "
                "fmap_as_finite_support (structure fields) are mutually exclusive"
            )
        if fmap_result and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_result @[hol] tag cannot have "
                "reviewed_exact status; use reviewed_fmap_as_finite_support_result after source comparison"
            )
        result_words_status = "reviewed_fmap_as_finite_support_result_words_as_type_indexed_bitvec"
        if status == result_words_status and not (fmap_result and words_bitvec):
            errors.append(
                f"{key[0]}:{key[1]}: {result_words_status} needs both "
                "fmap_as_finite_support_result and words_as_type_indexed_bitvec qualifiers"
            )
        if fmap_result and status not in {"reviewed_fmap_as_finite_support_result", result_words_status}:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_result @[hol] tag needs a reviewed "
                "source classification (reviewed_fmap_as_finite_support_result)"
            )
        if not fmap_result and status in {"reviewed_fmap_as_finite_support_result", result_words_status}:
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_result needs a "
                "fmap_as_finite_support_result @[hol] tag"
            )
        if fmap_result:
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text:
                errors.append(
                    f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_result requires a "
                    "source-comparison note in the reviewer field"
                )
        if fmap_equalities and (fmap_fields or fmap_result or fmap_relation or fmap_parameters or fmap_equality):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_equalities (theorem-level map "
                "equalities) is mutually exclusive with the field/result/relation qualifiers"
            )
        if fmap_equalities and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_equalities @[hol] tag cannot have "
                "reviewed_exact status; use reviewed_fmap_as_finite_support_equalities after source comparison"
            )
        if fmap_equalities and status != "reviewed_fmap_as_finite_support_equalities":
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_equalities @[hol] tag needs a reviewed "
                "source classification (reviewed_fmap_as_finite_support_equalities)"
            )
        if not fmap_equalities and status == "reviewed_fmap_as_finite_support_equalities":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_equalities needs a "
                "fmap_as_finite_support_equalities @[hol] tag"
            )
        if fmap_equalities:
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text:
                errors.append(
                    f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support_equalities requires a "
                    "source-comparison note in the reviewer field"
                )
        if fmap_function_positions and (
            fmap_fields or fmap_result or fmap_parameters or fmap_existentials
            or fmap_relation or fmap_equalities or fmap_equality
        ):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_function is mutually "
                "exclusive with other finite-map qualifiers"
            )
        if fmap_heterogeneous_function_positions and (
            fmap_fields or fmap_result or fmap_parameters or fmap_existentials
            or fmap_relation or fmap_equalities or fmap_function_positions or fmap_equality
        ):
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support_heterogeneous_function is "
                "mutually exclusive with other finite-map qualifiers"
            )
        if not set(boundary_fields) <= set(names_fields):
            errors.append(
                f"{key[0]}:{key[1]}: names_as_string_boundary must be a subset of names_as_string"
            )
        if list_fields and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: qualified @[hol] tag cannot have reviewed_exact status; "
                "use reviewed_list_as_array after source comparison"
            )
        if not list_fields and status == "reviewed_list_as_array":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_list_as_array needs a qualified @[hol] tag"
            )
        if names_fields and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: names_as_string @[hol] tag cannot have reviewed_exact status; "
                "use reviewed_names_as_string after source comparison"
            )
        if names_fields and status not in {
            "reviewed_names_as_string",
            "reviewed_list_as_array_names_as_string",
        }:
            errors.append(
                f"{key[0]}:{key[1]}: names_as_string @[hol] tag needs a reviewed "
                "source classification"
            )
        if not names_fields and status == "reviewed_names_as_string":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_names_as_string needs a names_as_string @[hol] tag"
            )
        if fmap_fields and status == "reviewed_exact":
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support @[hol] tag cannot have reviewed_exact "
                "status; use reviewed_fmap_as_finite_support after source comparison"
            )
        function_fmap_status = "reviewed_fmap_as_finite_support_function"
        if fmap_function_positions:
            expected_function_status = (
                combined_function_words_status if words_bitvec else function_fmap_status
            )
            if status != expected_function_status:
                errors.append(
                    f"{key[0]}:{key[1]}: fmap_as_finite_support_function needs "
                    f"{expected_function_status} after source comparison"
                )
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text or any(
                position.lower() not in reviewer_text
                for position in fmap_function_positions
            ):
                errors.append(
                    f"{key[0]}:{key[1]}: {status} needs a source-review note that "
                    "names every nested finite-map function position"
                )
        elif status in {function_fmap_status, combined_function_words_status}:
            errors.append(
                f"{key[0]}:{key[1]}: {status} needs a matching "
                "fmap_as_finite_support_function @[hol] tag"
            )
        if fmap_heterogeneous_function_positions:
            expected_heterogeneous_status = (
                combined_heterogeneous_function_words_status
                if words_bitvec else heterogeneous_function_status
            )
            if status != expected_heterogeneous_status:
                errors.append(
                    f"{key[0]}:{key[1]}: fmap_as_finite_support_heterogeneous_function "
                    f"needs {expected_heterogeneous_status} after source comparison"
                )
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text or any(
                position.lower() not in reviewer_text
                for position in fmap_heterogeneous_function_positions
            ):
                errors.append(
                    f"{key[0]}:{key[1]}: {status} needs a source-review note that names "
                    "every heterogeneous nested finite-map position"
                )
        elif status in {
            heterogeneous_function_status,
            combined_heterogeneous_function_words_status,
        }:
            errors.append(
                f"{key[0]}:{key[1]}: {status} needs a matching "
                "fmap_as_finite_support_heterogeneous_function @[hol] tag"
            )
        if fmap_fields and status not in {"reviewed_fmap_as_finite_support", combined_words_status,
                                          combined_relation_words_status, nested_combined_status}:
            errors.append(
                f"{key[0]}:{key[1]}: fmap_as_finite_support @[hol] tag needs a reviewed "
                "source classification (reviewed_fmap_as_finite_support, or the combined "
                "status with words_as_type_indexed_bitvec)"
            )
        if not fmap_fields and status == "reviewed_fmap_as_finite_support":
            errors.append(
                f"{key[0]}:{key[1]}: reviewed_fmap_as_finite_support needs a "
                "fmap_as_finite_support @[hol] tag"
            )
        if list_fields and names_fields:
            if status == "reviewed_list_as_array" or status == "reviewed_names_as_string":
                errors.append(
                    f"{key[0]}:{key[1]}: combined qualifiers require "
                    "reviewed_list_as_array_names_as_string"
                )
        elif status == "reviewed_list_as_array_names_as_string":
            errors.append(
                f"{key[0]}:{key[1]}: combined review status requires both qualifiers"
            )
        if status in {
            "reviewed_names_as_string",
            "reviewed_list_as_array_names_as_string",
        }:
            reviewer_text = reviewer.lower() if isinstance(reviewer, str) else ""
            if "source" not in reviewer_text or any(
                field not in reviewer_text for field in names_fields
            ):
                errors.append(
                    f"{key[0]}:{key[1]}: {status} needs a source-review note that "
                    "names every names_as_string field"
                )
            for identifier in names_fields:
                classification = (
                    "byte-observable" if identifier in boundary_fields
                    else "equality/map-key-only"
                )
                if f"{identifier}: {classification}" not in reviewer_text:
                    errors.append(
                        f"{key[0]}:{key[1]}: source-review note must classify "
                        f"{identifier} as {classification}"
                    )
        if (hol_path is None) != (hol_name is None):
            errors.append(f"{key[0]}:{key[1]}: HOL path and name must both be set or null")
        elif status == "documented_mismatch":
            if hol_path is None:
                errors.append(f"{key[0]}:{key[1]}: documented mismatch needs its HOL candidate")
            elif not isinstance(hol_path, str) or not isinstance(hol_name, str):
                errors.append(f"{key[0]}:{key[1]}: HOL path/name must be strings")
            if key in tagged:
                errors.append(f"{key[0]}:{key[1]}: documented mismatch must not carry an @[hol] tag")
            if (key not in proof_declarations
                    and key not in WITHDRAWN_HOL_DECLARATIONS
                    and key not in DOCUMENTED_MISMATCHES):
                errors.append(f"{key[0]}:{key[1]}: untagged HOL mismatch is not source-reviewed")
            if key in WITHDRAWN_HOL_DECLARATIONS and hol_path is not None:
                expected_path, expected_name, _reviewer = WITHDRAWN_HOL_DECLARATIONS[key]
                if (hol_path, hol_name) != (expected_path, expected_name):
                    errors.append(f"{key[0]}:{key[1]}: withdrawn declaration HOL candidate differs from source review")
            if key in DOCUMENTED_MISMATCHES and hol_path is not None:
                expected_path, expected_name, _reviewer = DOCUMENTED_MISMATCHES[key]
                if (hol_path, hol_name) != (expected_path, expected_name):
                    errors.append(f"{key[0]}:{key[1]}: documented mismatch HOL candidate differs from source review")
        elif hol_path is not None:
            if not isinstance(hol_path, str) or not isinstance(hol_name, str):
                errors.append(f"{key[0]}:{key[1]}: HOL path/name must be strings")
            elif tag is None or tag[:2] != (hol_path, hol_name):
                errors.append(
                    f"{key[0]}:{key[1]}: manifest HOL reference does not match its @[hol] tag"
                )
            if status == "no_hol_reference_pending_classification":
                errors.append(f"{key[0]}:{key[1]}: tagged entry cannot have no-HOL status")
        elif status != "no_hol_reference_pending_classification":
            errors.append(f"{key[0]}:{key[1]}: null HOL reference needs no-HOL status")

    for key, reference in tagged.items():
        record = by_key.get(key)
        if record is None:
            errors.append(f"tagged declaration missing from manifest: {key[0]}:{key[1]}")
        elif (record["hol_path"], record["hol_name"]) != reference:
            # The detailed mismatch was already reported above.
            pass

    for key in proof_declarations:
        if key not in by_key:
            errors.append(f"Proofs theorem missing from manifest: {key[0]}:{key[1]}")

    documented_mismatch_keys = set(DOCUMENTED_MISMATCHES)
    infrastructure_theorem_keys = set(INFRASTRUCTURE_THEOREMS)
    for key in by_key:
        if key not in tagged and key not in proof_declarations and not (
            key in WITHDRAWN_HOL_DECLARATIONS
            and (data_declarations_ is None or key in data_declarations_)
        ) and key not in documented_mismatch_keys and key not in infrastructure_theorem_keys:
            errors.append(f"manifest entry is not a current declaration: {key[0]}:{key[1]}")
    return errors


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--bootstrap",
        action="store_true",
        help="write an initial inventory template and exit (will not overwrite)",
    )
    args = parser.parse_args(argv)

    if args.bootstrap:
        if args.manifest.exists():
            print(f"error: refusing to overwrite {args.manifest}", file=sys.stderr)
            return 1
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(
            json.dumps(build_inventory(), indent=2) + "\n", encoding="utf-8"
        )
        print(f"wrote {args.manifest.relative_to(ROOT)}")
        return 0

    try:
        records = json.loads(args.manifest.read_text(encoding="utf-8"))
        if not isinstance(records, list):
            raise ValueError("manifest root must be a JSON array")
        errors = validate_inventory(
            records,
            proof_theorem_declarations(),
            tagged_declarations(),
            data_declarations(),
        )
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        return 1
    print(
        f"HOL theorem inventory checked: {len(records)} declarations; "
        f"all {len(proof_theorem_declarations())} Proofs theorems/lemmas are mapped"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
