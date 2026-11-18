#!/usr/bin/env python3
"""Generate the CakeML-to-Lean port progress dashboard (dashboard.html).

This script reads the same authoritative sources the port's tooling uses and
emits a single self-contained HTML file that can be opened offline:

  * ``docs/HOL-THEOREM-MAP.json``  -- the reviewed HOL<->Lean declaration map
      (every ``@[hol]``-tagged declaration plus pending-classification and
      documented-mismatch entries; see ``docs/HOL-LAYOUT.md``).
  * ``.hol-index/``                 -- the CakeML/HOL source index built by
      ``scripts/index-hol.py``: declaration kinds, per-script totals, and the
      HOL theory dependency graph (``theory-deps.txt``) used for dependency
      ordering.  The index is regenerated automatically when it is stale.
  * the ``Flapjack`` tree itself     -- scanned for ``@[hol ...]`` tags so the
      headline theorem/definition counts come straight from the Lean source.

Regenerate with::

    python3 scripts/build-dashboard.py                 # writes dashboard.html
    python3 scripts/build-dashboard.py --out /tmp/x.html

The output is deterministic apart from the generation timestamp.  It is a
developer aid, not part of the Lean build.  Numbers are explained in the page
legend; "reviewed" means a HOL correspondence was source-reviewed, "pending
classification" marks Flapjack-only declarations with no HOL original yet, and
"documented mismatch" marks a known statement difference that stays untagged.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import html
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAP_FILE = ROOT / "docs" / "HOL-THEOREM-MAP.json"
INDEX_DIR = ROOT / ".hol-index"
INDEX_TSV = INDEX_DIR / "hol-index.tsv"
DEPS_TXT = INDEX_DIR / "theory-deps.txt"
SOURCE_SHA = INDEX_DIR / "source.sha"
LEAN_ROOT = ROOT / "Flapjack"

# A reviewed_* status means a source-reviewed HOL correspondence.  The remaining
# statuses are open-work markers, listed separately below.
REVIEWED_PREFIX = "reviewed_"
PENDING_STATUS = "no_hol_reference_pending_classification"
MISMATCH_STATUS = "documented_mismatch"

# Names that signal a headline compiler-correctness / stability theorem.  These
# are the "theorems of correctness" in the narrow sense; the label is a name
# heuristic, not a classification, so the page marks it as such.
CORRECTNESS_TOKENS = (
    "_correct", "correct_thm", "_sound", "soundness", "_sim", "_simulation",
    "simulation", "preserves", "preserve", "_determ", "deterministic",
    "_semantics", "semantics_eq", "refines", "reflexive", "rev_thm",
    "compile_semantics", "observational", "agrees", "agreement",
)

# The compiler-port scope: CakeML source under these submodule-relative prefixes,
# excluding the out-of-scope translator/candle/characteristic trees.  Used to
# measure how much of the in-scope CakeML surface has been ported.
SCOPE_PREFIXES = ("pancake/", "compiler/", "semantics/", "basis/",
                  "examples/l3-machine-code/")
SCOPE_EXCLUDE = ("examples/candle/", "translator/", "characteristic/")

# Curated major-compilation pipeline, ordered CakeML AST -> RISC-V target.  Each
# row is (stage, pass name, HOL proof script [submodule-relative], headline
# semantic-preservation theorem).  The Pipeline view colours each pass by
# whether that headline theorem has been ported (see pipe_status).  This is a
# per-pass heuristic, not a per-theorem review: many passes carry additional
# supporting theorems beyond the one named here.
PIPELINE = [
    ("CakeML (front-end)", "parse", "compiler/proofs/compilerProofScript.sml",
     "parse_prog_correct"),
    ("CakeML (front-end)", "infertype", "compiler/proofs/compilerProofScript.sml",
     "infertype_prog_correct"),
    ("CakeML (front-end)", "compile", "compiler/proofs/compilerProofScript.sml",
     "compile_tap_compile"),
    ("Backend · closure", "flat_to_clos", "compiler/backend/proofs/flat_to_closProofScript.sml",
     "compile_correct"),
    ("Backend · closure", "clos_annotate", "compiler/backend/proofs/clos_annotateProofScript.sml",
     "semantics_annotate"),
    ("Backend · closure", "clos_fvs", "compiler/backend/proofs/clos_fvsProofScript.sml",
     "semantics_compile"),
    ("Backend · closure", "clos_number", "compiler/backend/proofs/clos_numberProofScript.sml",
     "semantics_number"),
    ("Backend · closure", "clos_known", "compiler/backend/proofs/clos_knownProofScript.sml",
     "semantics_compile"),
    ("Backend · closure", "clos_ticks", "compiler/backend/proofs/clos_ticksProofScript.sml",
     "semantics_remove_ticks"),
    ("Backend · closure", "clos_letop", "compiler/backend/proofs/clos_letopProofScript.sml",
     "semantics_let_op"),
    ("Backend · closure", "clos_call", "compiler/backend/proofs/clos_callProofScript.sml",
     "semantics_compile"),
    ("Backend · closure", "clos_interp", "compiler/backend/proofs/clos_interpProofScript.sml",
     "clos_interp_rev_thm"),
    ("Backend · closure", "clos_mti", "compiler/backend/proofs/clos_mtiProofScript.sml",
     "semantics_compile"),
    ("Backend · closure", "clos_to_bvl", "compiler/backend/proofs/clos_to_bvlProofScript.sml",
     "compile_prog_semantics"),
    ("BVL → BVI", "bvl_to_bvi", "compiler/backend/proofs/bvl_to_bviProofScript.sml",
     "compile_prog_semantics"),
    ("BVI optimizer", "bvi_let", "compiler/backend/proofs/bvi_letProofScript.sml",
     "compile_prog_semantics"),
    ("BVI optimizer", "bvi_inline", "compiler/backend/proofs/bvi_inlineProofScript.sml",
     "compile_prog_semantics"),
    ("BVI optimizer", "bvi_tailrec", "compiler/backend/proofs/bvi_tailrecProofScript.sml",
     "compile_prog_semantics"),
    ("BVI optimizer", "bvi_tmc", "compiler/backend/proofs/bvi_tmcProofScript.sml",
     "compile_prog_semantics"),
    ("BVI → Data", "bvi_to_data", "compiler/backend/proofs/bvi_to_dataProofScript.sml",
     "compile_correct"),
    ("Data", "data_live", "compiler/backend/proofs/data_liveProofScript.sml",
     "compile_correct"),
    ("Data", "data_simp", "compiler/backend/proofs/data_simpProofScript.sml",
     "simp_correct"),
    ("Data", "data_space", "compiler/backend/proofs/data_spaceProofScript.sml",
     "compile_correct"),
    ("Data → Word", "data_to_word", "compiler/backend/proofs/data_to_wordProofScript.sml",
     "data_compile_correct"),
    ("Word", "word_to_word", "compiler/backend/proofs/word_to_wordProofScript.sml",
     "word_to_word_compile_semantics"),
    ("Word", "word_alloc", "compiler/backend/proofs/word_allocProofScript.sml",
     "full_ssa_cc_trans_correct"),
    ("Word", "word_copy", "compiler/backend/proofs/word_copyProofScript.sml",
     "copy_prop_correct"),
    ("Word", "word_cse", "compiler/backend/proofs/word_cseProofScript.sml",
     "word_common_subexp_elim_correct"),
    ("Word", "word_remove", "compiler/backend/proofs/word_removeProofScript.sml",
     "word_remove_correct"),
    ("Word → Stack", "word_to_stack", "compiler/backend/proofs/word_to_stackProofScript.sml",
     "word_to_stack_compile_no_install"),
    ("Stack → Lab", "stack_alloc", "compiler/backend/proofs/stack_allocProofScript.sml",
     "make_init_semantics"),
    ("Stack → Lab", "stack_remove", "compiler/backend/proofs/stack_removeProofScript.sml",
     "stack_remove_call_args"),
    ("Stack → Lab", "stack_to_lab", "compiler/backend/proofs/stack_to_labProofScript.sml",
     "stack_to_lab_compile_no_install"),
    ("Lab → target", "lab_to_target", "compiler/backend/proofs/lab_to_targetProofScript.sml",
     "compile_correct"),
    ("Lab → target", "lab_filter", "compiler/backend/proofs/lab_filterProofScript.sml",
     "filter_skip_semantics"),
]

# The end-to-end AST -> RISC-V correctness chain. CakeML's front-end
# (compile_correct) feeds the SAME backend and the SAME RISC-V target encoder,
# so there is one source-to-machine chain. Each link is (hol_script
# [submodule-relative], hol_name, lean_path substring, description). Port status
# is computed by (script, theorem) via pipe_status, so the unported front-end
# (compile_correct) is shown as an open gap, never falsely claimed.
E2E_CHAINS = [
    {
        "label": "CakeML",
        "src_lang": "CakeML source → RISC-V",
        "links": [
            ("compiler/proofs/compilerProofScript.sml", "compile_correct",
             "",
             "CakeML program semantics -> installed target machine code (target-agnostic "
             "machine_sem): parse, type and compile are all handled, for any target config "
             "including RISC-V -- the whole CakeML front-end plus shared backend in one "
             "theorem. NOT YET PORTED to Lean. Click to expand its constituent theorems."),
            ("compiler/encoders/riscv/proofs/riscv_targetProofScript.sml", "riscv_encoder_correct",
             "RiscV/CorrectnessEncoding/",
             "Each target instruction's machine-code encoding matches its RISC-V model "
             "step (26 instruction-family cases)."),
            ("compiler/encoders/riscv/proofs/riscv_targetProofScript.sml", "riscv_target_ok",
             "RiscV/CorrectnessEncoding/TargetOk.lean",
             "Well-formedness of the compiled target program fed to the RISC-V model."),
        ],
    },
]

# The correctness theorems that CakeML's compile_correct composes, in HOL
# composition order (the front-end glue + type soundness, then the backend
# compile_correct' per-pass chain).  Each is (group, hol_script, hol_name);
# group is "Front-end" / "Type soundness" / "Backend pass".  Port status is
# computed by (script, theorem) via pipe_status, so the missing CakeML front-end
# and the four unported backend passes surface as not_ported.
CAKEML_COMPILE_CORRECT = [
    ("Front-end", "compiler/proofs/compilerProofScript.sml", "parse_prog_correct"),
    ("Front-end", "compiler/proofs/compilerProofScript.sml", "infertype_prog_correct"),
    ("Front-end", "compiler/proofs/compilerProofScript.sml", "compile_tap_compile"),
    ("Type soundness", "compiler/proofs/compilerProofScript.sml", "semantics_type_sound"),
    ("Backend pass", "compiler/backend/proofs/flat_to_closProofScript.sml", "compile_correct"),
    ("Backend pass", "compiler/backend/proofs/clos_to_bvlProofScript.sml", "compile_semantics"),
    ("Backend pass", "compiler/backend/proofs/bvl_to_bviProofScript.sml", "compile_prog_semantics"),
    ("Backend pass", "compiler/backend/proofs/bvi_letProofScript.sml", "compile_prog_semantics"),
    ("Backend pass", "compiler/backend/proofs/bvi_inlineProofScript.sml", "compile_prog_semantics"),
    ("Backend pass", "compiler/backend/proofs/bvi_tailrecProofScript.sml", "compile_prog_semantics"),
    ("Backend pass", "compiler/backend/proofs/bvi_tmcProofScript.sml", "compile_prog_semantics"),
    ("Backend pass", "compiler/backend/proofs/bvi_to_dataProofScript.sml", "compile_correct"),
    ("Backend pass", "compiler/backend/proofs/data_liveProofScript.sml", "compile_correct"),
    ("Backend pass", "compiler/backend/proofs/data_simpProofScript.sml", "simp_correct"),
    ("Backend pass", "compiler/backend/proofs/data_spaceProofScript.sml", "compile_correct"),
    ("Backend pass", "compiler/backend/proofs/data_to_wordProofScript.sml", "data_compile_correct"),
    ("Backend pass", "compiler/backend/proofs/word_to_wordProofScript.sml", "word_to_word_compile_semantics"),
    ("Backend pass", "compiler/backend/proofs/word_allocProofScript.sml", "full_ssa_cc_trans_correct"),
    ("Backend pass", "compiler/backend/proofs/word_copyProofScript.sml", "copy_prop_correct"),
    ("Backend pass", "compiler/backend/proofs/word_cseProofScript.sml", "word_common_subexp_elim_correct"),
    ("Backend pass", "compiler/backend/proofs/word_removeProofScript.sml", "word_remove_correct"),
    ("Backend pass", "compiler/backend/proofs/word_to_stackProofScript.sml", "word_to_stack_compile_no_install"),
    ("Backend pass", "compiler/backend/proofs/stack_allocProofScript.sml", "make_init_semantics"),
    ("Backend pass", "compiler/backend/proofs/stack_removeProofScript.sml", "stack_remove_call_args"),
    ("Backend pass", "compiler/backend/proofs/stack_to_labProofScript.sml", "stack_to_lab_compile_no_install"),
    ("Backend pass", "compiler/backend/proofs/lab_to_targetProofScript.sml", "compile_correct"),
]

# --------------------------------------------------------------------------- #
# CakeML compile_correct dependency DAG (richer constituent view)
# --------------------------------------------------------------------------- #
# Built from the real CakeML proof scripts (submodule `cakeml/`), so every node
# is a genuine theorem and every edge is a genuine proof dependency.  Used only
# by the dashboard (a dev aid); if the submodule is missing the view degrades to
# the flat constituent list below.
CAKE = ROOT / "cakeml"

# Verified composition of the top-level theorem, read from
# compiler/proofs/compilerProofScript.sml:
#   compile_correct        = SPEC_ALL compile_correct_lemma
#   compile_correct_lemma  = Q.ISPEC_THEN st mp_tac compile_correct_gen  (+ primSemEnv)
#   compile_correct_gen    composes the front-end, type soundness and the backend
#                          (backendProofTheory.compile_correct').
CAKE_TOP_GLUE = [
    {"t": "compile_correct",        "script": "compiler/proofs/compilerProofScript.sml",
     "kind": "root",   "stage": "CakeML front-end", "group": "Top composition"},
    {"t": "compile_correct_lemma",  "script": "compiler/proofs/compilerProofScript.sml",
     "kind": "glue",   "stage": "CakeML front-end", "group": "Top composition"},
    {"t": "compile_correct_gen",    "script": "compiler/proofs/compilerProofScript.sml",
     "kind": "glue",   "stage": "CakeML front-end", "group": "Top composition"},
    {"t": "prim_sem_env_eq",        "script": "compiler/scheme/proofs/scheme_to_machine_code_correctScript.sml",
     "kind": "helper", "stage": "scheme", "group": "Top composition"},
    {"t": "prim_type_sound_invariants", "script": "compiler/scheme/proofs/scheme_to_machine_code_correctScript.sml",
     "kind": "helper", "stage": "scheme", "group": "Top composition"},
]
CAKE_FRONTEND = ["parse_prog_correct", "infertype_prog_correct", "compile_tap_compile"]
CAKE_TYPESOUND = ["semantics_type_sound"]

# The backend spine: the per-pass headline correctness theorem, in compilation
# order (source -> flat -> clos -> bvl -> bvi -> data -> word -> stack -> lab ->
# target).  Headlines are the real top theorem of each pass's proof script
# (verified against the checked-out CakeML source), so e.g. data_to_word shows
# its genuine `compile_correct` (still unported) rather than only the mapped
# `data_compile_correct`.
CAKE_SPINE = [
    ("Backend · closure", "flat_to_clos", "compiler/backend/proofs/flat_to_closProofScript.sml", "compile_correct"),
    ("Backend · closure", "clos_to_bvl", "compiler/backend/proofs/clos_to_bvlProofScript.sml", "compile_semantics"),
    ("BVL → BVI", "bvl_to_bvi", "compiler/backend/proofs/bvl_to_bviProofScript.sml", "compile_prog_semantics"),
    ("BVI optimizer", "bvi_let", "compiler/backend/proofs/bvi_letProofScript.sml", "compile_thm"),
    ("BVI optimizer", "bvi_inline", "compiler/backend/proofs/bvi_inlineProofScript.sml", "compile_prog_semantics"),
    ("BVI optimizer", "bvi_tailrec", "compiler/backend/proofs/bvi_tailrecProofScript.sml", "compile_prog_semantics"),
    ("BVI optimizer", "bvi_tmc", "compiler/backend/proofs/bvi_tmcProofScript.sml", "compile_prog_semantics"),
    ("BVI → Data", "bvi_to_data", "compiler/backend/proofs/bvi_to_dataProofScript.sml", "compile_correct"),
    ("Data", "data_live", "compiler/backend/proofs/data_liveProofScript.sml", "compile_correct"),
    ("Data", "data_simp", "compiler/backend/proofs/data_simpProofScript.sml", "simp_correct"),
    ("Data", "data_space", "compiler/backend/proofs/data_spaceProofScript.sml", "compile_correct"),
    ("Data → Word", "data_to_word", "compiler/backend/proofs/data_to_wordProofScript.sml", "compile_correct"),
    ("Word", "word_to_word", "compiler/backend/proofs/word_to_wordProofScript.sml", "word_to_word_compile_semantics"),
    ("Word", "word_alloc", "compiler/backend/proofs/word_allocProofScript.sml", "full_ssa_cc_trans_correct"),
    ("Word", "word_copy", "compiler/backend/proofs/word_copyProofScript.sml", "copy_prop_correct"),
    ("Word", "word_cse", "compiler/backend/proofs/word_cseProofScript.sml", "word_common_subexp_elim_correct"),
    ("Word", "word_remove", "compiler/backend/proofs/word_removeProofScript.sml", "word_remove_correct"),
    ("Word → Stack", "word_to_stack", "compiler/backend/proofs/word_to_stackProofScript.sml", "word_to_stack_compile_no_install"),
    ("Stack → Lab", "stack_alloc", "compiler/backend/proofs/stack_allocProofScript.sml", "make_init_semantics"),
    ("Stack → Lab", "stack_remove", "compiler/backend/proofs/stack_removeProofScript.sml", "stack_remove_call_args"),
    ("Stack → Lab", "stack_to_lab", "compiler/backend/proofs/stack_to_labProofScript.sml", "stack_to_lab_compile_no_install"),
    ("Lab → target", "lab_to_target", "compiler/backend/proofs/lab_to_targetProofScript.sml", "compile_correct"),
]

# Token words that are tactics / sort / boilerplate, never theorem dependencies.
_CAKE_TAC = set(
    """metis_tac fs srw_tac gen_tac strip_tac disch_then drule rw_tac Cases_on Cases qexists_tac
    qmatch_goalsub_abbrev_tac qpat_x_assum unabbrev_all_tac rename1 sg THEN1 CONV_TAC simpCases simp
    every_case_tac pairarg_tac rveq res_tac old_drule qspec_then mp_tac instPairs boolTheory std_ss
    PULL_EXISTS FORALL_PROD EXISTS_PROD SKOLEM_THM EXTENSION domain_lookup lookup_map spt_eq eq_shape_map
    QED Proof DEP_REWRITE_TAC impl_tac DISCH_THM CONJUNCTS SIMP_RULE REWRITE_RULE Q.INST Q.ISPEC""".split()
)

_proof_cache: dict[str, dict] = {}

def _parse_hol_proof(path: Path) -> dict[str, dict]:
    """Top-level Theorem/Triviality decls in a HOL proof script -> {name: {proof}}.

    The proof body is the tactic text between `Proof` and `QED`; declarations with
    an inline `Q.prove(...)` keep their whole segment (their dependencies are not
    needed here — only the named spine theorems are parsed)."""
    key = str(path)
    if key in _proof_cache:
        return _proof_cache[key]
    decls: dict[str, dict] = {}
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        _proof_cache[key] = decls
        return decls
    starts = [(m.start(), m.group(2)) for m in
              re.finditer(r'(?m)^[ \t]*(Theorem|Triviality)\s+([A-Za-z0-9_]+)\s*[:=]', text)]
    for i, (start, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(text)
        seg = text[start:end]
        pm = re.search(r'\bProof\b(.*?)\bQED\b', seg, re.S)
        decls[name] = {"proof": pm.group(1) if pm else seg}
    _proof_cache[key] = decls
    return decls

def _direct_lemmas(headline: str, script_rel: str) -> list[str]:
    """Theorems declared in the same pass script that `headline`'s proof cites."""
    decls = _parse_hol_proof(CAKE / script_rel)
    if headline not in decls:
        return []
    scope = set(decls)
    out = set()
    for tok in set(re.findall(r'[A-Za-z_][A-Za-z0-9_]*', decls[headline]["proof"])):
        if tok == headline or tok in _CAKE_TAC or tok.endswith("_def"):
            continue
        if tok in scope:                       # a same-script top-level theorem ref
            out.add(tok)
    return sorted(out)


def _git_rev(path: Path) -> str:
    try:
        out = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            capture_output=True, text=True, check=True,
        )
        return out.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def ensure_index() -> None:
    """Regenerate the CakeML/HOL index when missing or stale, like next-hol-port.py.

    Best-effort: if the CakeML submodule or its tooling is unavailable but an
    index already exists, keep using it rather than failing the whole build.
    """
    try:
        if INDEX_TSV.is_file() and SOURCE_SHA.is_file():
            current = _git_rev(ROOT / "cakeml")
            if current != "unknown" and SOURCE_SHA.read_text().strip() == current:
                return
        subprocess.run([sys.executable, str(ROOT / "scripts" / "index-hol.py")],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    except (OSError, subprocess.CalledProcessError):
        pass


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def strip_source_prefix(path: str | None) -> str | None:
    """Normalise a source path cited by a tag/map to its submodule-relative form."""
    if not path:
        return path
    for pre in ("cakeml/", "HOL/", "hol4/"):
        if path.startswith(pre):
            return path[len(pre):]
    return path


# --------------------------------------------------------------------------- #
# Loaders
# --------------------------------------------------------------------------- #

def load_map() -> list[dict]:
    return json.loads(MAP_FILE.read_text(encoding="utf-8"))


def load_index() -> tuple[dict, Counter, dict]:
    """Return ((path,name,start)->(kind,theory), per-script totals, script->theories)."""
    kind_at: dict[tuple[str, str, str], tuple[str, str]] = {}
    totals: Counter = Counter()
    theories_of: dict[str, set[str]] = defaultdict(set)
    if not INDEX_TSV.is_file():
        return kind_at, totals, theories_of
    for line in INDEX_TSV.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        kind, name, loc, theory = line.split("\t")
        src, span = loc.rsplit(":", 1)
        start, end = span.split("-", 1)
        key = (src, name, start)
        kind_at[key] = (kind, theory)
        theories_of[src].add(theory)
        # totals keyed by submodule-relative source path
        totals[src] += 1
    return kind_at, totals, theories_of


def load_deps() -> tuple[list[tuple[str, str]], set[str]]:
    edges: list[tuple[str, str]] = []
    nodes: set[str] = set()
    if not DEPS_TXT.is_file():
        return edges, nodes
    for line in DEPS_TXT.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        a, _, b = line.partition(" -> ")
        a, b = a.strip(), b.strip()
        if a and b:
            edges.append((a, b))
            nodes |= {a, b}
    return edges, nodes


def theory_ranks(edges: list[tuple[str, str]]) -> dict[str, int]:
    """Longest-chain rank over the dependency graph (leaves = 0); cycles broken."""
    deps: dict[str, list[str]] = defaultdict(list)  # node -> theories it depends on
    for a, b in edges:
        deps[a].append(b)
    memo: dict[str, int] = {}

    def rank(n: str, stack: set[str]) -> int:
        if n in memo:
            return memo[n]
        if n in stack:
            return 0  # ignore a cycle back-edge
        stack.add(n)
        r = 0 if not deps[n] else 1 + max(rank(d, stack) for d in deps[n])
        stack.discard(n)
        memo[n] = r
        return r

    for (a, b) in edges:
        rank(a, set())
        rank(b, set())
    return memo


def scan_tags() -> tuple[list[dict], int, int]:
    """Scan Flapjack/*.lean for @[hol] tags; return ([decls], files_with_tags, total_tags).

    Each decl: {path, name, keyword}.  Test files are excluded from the
    headline counts (they are Flapjack's own regression suite, not ported
    source), but the total tag scan still counts them for context.
    """
    decl_re = re.compile(
        r"^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|"
        r"coinductive|inductive|instance|class|axiom|constant|equation|attribute)\b"
    )
    name_re = re.compile(
        r"^\s*(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|"
        r"coinductive|inductive)\s+([A-Za-z_][A-Za-z0-9_]*)"
    )
    decls: list[dict] = []
    files_with_tags = 0
    total_tags = 0
    # Precompute, per line, the declaration keyword it begins (if any).
    for f in sorted(LEAN_ROOT.rglob("*.lean")):
        text = f.read_text(errors="replace")
        lines = text.splitlines()
        n_tags = text.count("@[hol ")
        if not n_tags:
            continue
        total_tags += n_tags
        is_test = "/Test/" in f.as_posix()
        if is_test:
            continue
        files_with_tags += 1
        for i, line in enumerate(lines):
            tag_at = line.find("@[hol ")
            if tag_at < 0:
                continue
            # Case 1: inline attribute, e.g. `@[hol "..."] theorem foo ...`
            after = line[tag_at + len("@[hol "):]
            if "]" in line:
                after = line[line.rfind("]") + 1:]
            m = decl_re.match(after)
            if m:
                nm = name_re.match(after)
                decls.append({"path": rel(f),
                              "name": nm.group(1) if nm else "", "keyword": m.group(1)})
                continue
            # Case 2: attribute on its own line; the declaration follows it,
            # possibly after blank lines, docstrings or other attributes.
            for j in range(i + 1, min(i + 10, len(lines))):
                jm = decl_re.match(lines[j])
                if jm:
                    nm = name_re.match(lines[j])
                    decls.append({"path": rel(f),
                                  "name": nm.group(1) if nm else "", "keyword": jm.group(1)})
                    break
    return decls, files_with_tags, total_tags


# --------------------------------------------------------------------------- #
# Classification helpers
# --------------------------------------------------------------------------- #

def status_category(status: str) -> str:
    if status == PENDING_STATUS:
        return "pending"
    if status == MISMATCH_STATUS:
        return "mismatch"
    if status.startswith(REVIEWED_PREFIX):
        return "reviewed"
    return "other"


def phase_of(lean_path: str) -> str:
    """Coarse compiler-phase grouping derived from the Lean module path."""
    p = lean_path
    if p.startswith("Flapjack/Test/"):
        return "Tests"
    if p.startswith(("Flapjack/CakeParser/", "Flapjack/Parser/")):
        return "Frontend · Parsing & AST"
    if p.startswith("Flapjack/Pancake/"):
        return "Pancake · source IR & semantics"
    if p.startswith("Flapjack/Compiler/Backend/"):
        seg = p.split("/")[3] if len(p.split("/")) > 3 else ""
        if seg.endswith(".lean"):
            seg = seg[:-5]
        if seg == "semantics":
            return "Backend · layer semantics"
        if seg == "proofs":
            return "Backend · pass proofs"
        if seg == "Encoders" or p.startswith("Flapjack/Compiler/Encoders/"):
            return "Backend · ASM encoders"
        return f"Backend · {seg}"
    if p.startswith("Flapjack/Compiler/Encoders/"):
        return "Backend · ASM encoders"
    if p.startswith("Flapjack/Compiler/"):
        return "Compiler · front-end passes"
    if p.startswith("Flapjack/RiscV/"):
        return "Target · RISC-V model"
    if p.startswith("Flapjack/Mips32/"):
        return "Target · MIPS32 (experimental)"
    if p.startswith("Flapjack/Arm8/"):
        return "Target · ARMv8 (experimental)"
    if p.startswith("Flapjack/X64/"):
        return "Target · x86-64 (experimental)"
    if p.startswith("Flapjack/FiniteMap/"):
        return "Basis · finite maps"
    if p.startswith("Flapjack/Basis/"):
        return "Basis · pure library"
    if p.startswith("Flapjack/Misc/"):
        return "Basis · misc utilities"
    return "Pancake · top-level / other"


def is_correctness_name(*names: str) -> bool:
    blob = " ".join("" if n is None else str(n) for n in names).lower()
    return any(tok in blob for tok in CORRECTNESS_TOKENS)


# --------------------------------------------------------------------------- #
# Assembly
# --------------------------------------------------------------------------- #

def build() -> dict:
    ensure_index()
    map_entries = load_map()
    kind_at, script_totals, theories_of = load_index()
    edges, dep_nodes = load_deps()
    ranks = theory_ranks(edges)
    decls, files_tagged, total_tags = scan_tags()

    # Lean-side declaration name -> keyword, for status joins.
    lean_kw = {(d["path"], d["name"]): d["keyword"] for d in decls if d["name"]}

    # Per Lean-module aggregates from the curated map.
    mod: dict[str, dict] = {}

    def module_row(mp: str) -> dict:
        r = mod.get(mp)
        if r is None:
            r = mod[mp] = {
                "path": mp, "scripts": set(), "theories": set(),
                "reviewed": 0, "pending": 0, "mismatch": 0, "total": 0,
                "headline": False,
            }
        return r

    for e in map_entries:
        mp = e.get("lean_path")
        if not mp:
            continue
        row = module_row(mp)
        hp = strip_source_prefix(e.get("hol_path"))
        if hp:
            row["scripts"].add(hp)
            for th in theories_of.get(hp, ()):  # theories_of keyed by raw src
                if th:
                    row["theories"].add(th)
        cat = status_category(e.get("statement_status", ""))
        row[cat] += 1
        row["total"] += 1
        # headline correctness theorems (name heuristic) among reviewed theorems
        if cat == "reviewed" and is_correctness_name(e.get("hol_name", ""), e.get("lean_name", "")):
            row["headline"] = True

    # Lean-module totals from the source scan (authoritative keyword counts).
    scan_by_module: dict[str, Counter] = defaultdict(Counter)
    for d in decls:
        scan_by_module[d["path"]][d["keyword"]] += 1

    # Lean-module -> dependency rank (min theory rank of its source theories).
    def module_rank(row: dict) -> int | None:
        rs = [ranks[t] for t in row["theories"] if t in ranks]
        return min(rs) if rs else None

    # Group modules by phase; order phases by their earliest (min) module rank,
    # then by name; order rows within a phase by rank then path.
    phases: dict[str, list[dict]] = defaultdict(list)
    for mp, row in mod.items():
        row["rank"] = module_rank(row)
        row["scan"] = dict(scan_by_module.get(mp, {}))
        row["ported"] = row["total"]  # curated inventory count
        phases[phase_of(mp)].append(row)

    phase_order = sorted(
        phases, key=lambda ph: (
            0 if ph == "Tests" else 1,
            min((r["rank"] for r in phases[ph] if r["rank"] is not None), default=10**9),
            ph,
        )
    )
    for ph in phases:
        phases[ph].sort(key=lambda r: (r["rank"] if r["rank"] is not None else 10**9, r["path"]))

    # HOL source scripts: dependency-ordered rollup (272 scripts with a port).
    scripts: dict[str, dict] = {}
    for e in map_entries:
        hp = strip_source_prefix(e.get("hol_path"))
        if not hp:
            continue
        s = scripts.get(hp)
        if s is None:
            s = scripts[hp] = {
                "hol_path": hp, "lean_modules": set(), "theories": set(),
                "reviewed": 0, "pending": 0, "mismatch": 0, "total": 0,
            }
        cat = status_category(e.get("statement_status", ""))
        s[cat] += 1
        s["total"] += 1
        lean_mp = e.get("lean_path")
        if lean_mp:
            s["lean_modules"].add(lean_mp)
    for hp, s in scripts.items():
        for th in theories_of.get(hp, ()):
            if th:
                s["theories"].add(th)
        s["rank"] = min([ranks[t] for t in s["theories"] if t in ranks], default=None)
        s["index_total"] = script_totals.get(hp, 0)  # HOL source decl count (best-effort)
        s["ported"] = s["total"]

    script_rows = sorted(
        scripts.values(),
        key=lambda s: (
            s["rank"] if s["rank"] is not None else 10**9,
            s["hol_path"],
        ),
    )

    # --- Port-scope completion: how much of the in-scope CakeML surface is ported
    def in_scope(p: str | None) -> bool:
        if not p:
            return False
        if not any(p.startswith(pre) for pre in SCOPE_PREFIXES):
            return False
        return not any(x in p for x in SCOPE_EXCLUDE)

    # in-scope HOL decl totals from the CakeML index (best-effort denominator)
    scope_totals = {s: n for s, n in script_totals.items() if in_scope(s)}
    # per in-scope script: how many map rows (ported decls) it has
    scope_map_total: dict[str, int] = defaultdict(int)
    for e in map_entries:
        hp = strip_source_prefix(e.get("hol_path"))
        if in_scope(hp):
            scope_map_total[hp] += 1
    scope_ported_scripts = sum(1 for s in scope_totals if scope_map_total.get(s))
    # index decls that sit in scripts that already carry a port (same-unit share)
    scope_decls_in_ported = sum(n for s, n in scope_totals.items()
                                if scope_map_total.get(s))
    scope_total_decls = sum(scope_totals.values())
    scope_unported = sorted(
        ({"hol_path": s, "hol_decls": n}
         for s, n in scope_totals.items() if not scope_map_total.get(s)),
        key=lambda x: (-x["hol_decls"], x["hol_path"]),
    )
    scope = {
        "scope_scripts": len(scope_totals),
        "scope_scripts_ported": scope_ported_scripts,
        "scope_scripts_unported": len(scope_unported),
        "scope_scripts_unported_decls": scope_total_decls - scope_decls_in_ported,
        "scope_decls": scope_total_decls,
        "scope_decls_in_ported": scope_decls_in_ported,
        # map entries covering in-scope scripts (a different unit; shown as context)
        "scope_map_entries": sum(scope_map_total.values()),
        "pct_scripts": round(100 * scope_ported_scripts / len(scope_totals))
        if scope_totals else 0,
        "pct_decls": round(100 * scope_decls_in_ported / scope_total_decls)
        if scope_total_decls else 0,
        "unported_top": scope_unported[:40],          # largest unported scripts
        "unported_all": scope_unported,               # full list for the page
    }

    # --- Pipeline: per-pass headline correctness theorem, coloured by port status
    pipe_idx: dict[tuple[str, str], list[str]] = defaultdict(list)
    pipe_loc: dict[tuple[str, str], tuple[str, str]] = {}  # (script,name)->(lean_path,status)
    for e in map_entries:
        hp = strip_source_prefix(e.get("hol_path"))
        hn = e.get("hol_name")
        if hp and hn:
            pipe_idx[(hp, hn)].append(status_category(e.get("statement_status", "")))
            pipe_loc.setdefault((hp, hn),
                                (e.get("lean_path") or "", e.get("statement_status") or ""))

    def pipe_status(script: str, head: str) -> str:
        st = pipe_idx.get((script, head))
        if not st:
            return "not_ported"
        if "reviewed" in st:
            return "ported"
        if "mismatch" in st:
            return "mismatch"
        return "partial"

    pipeline_rows: list[dict] = []
    pipe_counts: Counter = Counter()
    for stage, passn, script, head in PIPELINE:
        st = pipe_status(script, head)
        pipe_counts[st] += 1
        pipeline_rows.append(
            {"stage": stage, "pass": passn, "script": script,
             "theorem": head, "status": st})

    # --- End-to-end AST -> RISC-V correctness chains (Pancake + CakeML)
    e2e_chains: list[dict] = []
    for ch in E2E_CHAINS:
        links: list[dict] = []
        any_open = False
        for script, name, _ln_sub, desc in ch["links"]:
            st = pipe_status(script, name)
            if st != "ported":
                any_open = True
            lean, map_status = pipe_loc.get((script, name), ("", ""))
            links.append({
                "hol_name": name, "script": script, "lean_path": lean,
                "status": st, "cat": status_category(map_status),
                "n": len(pipe_idx.get((script, name), ())), "desc": desc,
            })
        e2e_chains.append({
            "label": ch["label"], "src_lang": ch["src_lang"],
            "links": links, "any_open": any_open,
        })

    # Expand CakeML's compile_correct into the correctness theorems it composes,
    # as a dependency DAG built from the real proof scripts (see CAKE_* above).
    def _mk(t, script, kind, stage, group):
        return {"name": t, "script": script, "kind": kind, "stage": stage,
                "group": group, "status": pipe_status(script, t),
                "lean": pipe_loc.get((script, t), ("", ""))[0], "children": []}

    root = _mk("compile_correct", "compiler/proofs/compilerProofScript.sml",
               "root", "CakeML front-end", "Top composition")
    lemma = _mk("compile_correct_lemma", "compiler/proofs/compilerProofScript.sml",
                "glue", "CakeML front-end", "Top composition")
    gen = _mk("compile_correct_gen", "compiler/proofs/compilerProofScript.sml",
              "glue", "CakeML front-end", "Top composition")
    helpers = [_mk(x, "compiler/scheme/proofs/scheme_to_machine_code_correctScript.sml",
                   "helper", "scheme", "Top composition")
               for x in ("prim_sem_env_eq", "prim_type_sound_invariants")]
    fe_nodes = [_mk(x, "compiler/proofs/compilerProofScript.sml",
                    "frontend", "CakeML front-end", "Front-end") for x in CAKE_FRONTEND]
    ts_nodes = [_mk(x, "compiler/proofs/compilerProofScript.sml",
                    "typesound", "CakeML front-end", "Type soundness") for x in CAKE_TYPESOUND]

    # Backend spine (compile_correct'): the per-pass chain, each pass with the
    # same-script theorems its headline proof directly cites.
    spine = {"name": "compile_correct'",
             "script": "compiler/backend/proofs/backendProofScript.sml",
             "kind": "spine", "stage": "Backend", "group": "Backend · per-pass chain",
             "status": "spine", "lean": "", "children": []}
    for stage, passn, script, hdr in CAKE_SPINE:
        pnode = _mk(hdr, script, "pass", stage, "Backend pass")
        pnode["pass"] = passn
        for lem in _direct_lemmas(hdr, script):
            pnode["children"].append(_mk(lem, script, "lemma", stage, "Backend pass"))
        spine["children"].append(pnode)

    gen["children"] = fe_nodes + ts_nodes + [spine]
    lemma["children"] = helpers + [gen]
    root["children"] = [lemma]
    cake_dag = root

    def _walk(n):
        yield n
        for c in n["children"]:
            yield from _walk(c)
    all_nodes = list(_walk(cake_dag))
    # Flat view (legacy table + counts); partsTree is the nested DAG render.
    cakeml_parts = [{"group": p["group"], "pass": p.get("pass", p["kind"]), "name": p["name"],
                     "script": p["script"], "status": p["status"], "lean_path": p["lean"]}
                    for p in all_nodes]
    for ch in e2e_chains:
        if ch["label"] != "CakeML":
            continue
        for link in ch["links"]:
            if link["hol_name"] == "compile_correct":
                link["parts"] = cakeml_parts
                link["parts_ported"] = sum(1 for p in cakeml_parts if p["status"] == "ported")
                link["parts_total"] = len(cakeml_parts)
                link["partsTree"] = cake_dag
                link["partsSpineLen"] = len(spine["children"])

    # Headline correctness theorems: reviewed theorem-kind ports with a
    # correctness-statement name.  Join map status with the Lean keyword scan.
    headline: list[dict] = []
    theorem_ports = 0
    theorem_reviewed = 0
    theorem_pending = 0
    theorem_mismatch = 0
    kw_totals = Counter()
    for d in decls:
        kw_totals[d["keyword"]] += 1
    for e in map_entries:
        hp, ln = e.get("hol_name", ""), e.get("lean_name", "")
        if not is_correctness_name(hp, ln):
            continue
        # only the headline-famous ones that are theorems in Lean
        kw = lean_kw.get((e.get("lean_path", ""), ln), "theorem")
        if kw not in ("theorem", "lemma"):
            continue
        cat = status_category(e.get("statement_status", ""))
        headline.append({
            "hol_name": hp, "lean_name": ln,
            "hol_path": e.get("hol_path"), "lean_path": e.get("lean_path"),
            "status": e.get("statement_status", ""), "cat": cat,
            "rank": None,
        })

    # theorem-kind counts (Lean keyword scan, non-test) with status from the map
    theorem_decls = [d for d in decls if d["keyword"] == "theorem"]
    # status per theorem decl via map join
    lean_status = {(e.get("lean_path", ""), e.get("lean_name", "")):
                   status_category(e.get("statement_status", "")) for e in map_entries}
    for d in theorem_decls:
        cat = lean_status.get((d["path"], d["name"]), "tagged_no_map")
        if cat == "reviewed":
            theorem_reviewed += 1
        elif cat == "pending":
            theorem_pending += 1
        elif cat == "mismatch":
            theorem_mismatch += 1
    theorem_total = len(theorem_decls)

    # sort headline by rank then name
    def hrank(h):
        r = mod.get(h["lean_path"], {}).get("rank")
        return (r if r is not None else 10**9, h["hol_path"] or "", h["lean_name"] or "", h["hol_name"] or "")

    headline.sort(key=hrank)
    for _h in headline:  # expose the module rank for the dependency column
        _h["rank"] = mod.get(_h["lean_path"], {}).get("rank")

    # Overall totals
    kind_counter = Counter(d["keyword"] for d in decls)
    reviewed_decls = sum(1 for e in map_entries if status_category(e.get("statement_status", "")) == "reviewed")
    pending_decls = sum(1 for e in map_entries if status_category(e.get("statement_status", "")) == "pending")
    mismatch_decls = sum(1 for e in map_entries if status_category(e.get("statement_status", "")) == "mismatch")

    # per-phase summary
    phase_summary = []
    for ph in phase_order:
        rows = phases[ph]
        ported = sum(r["ported"] for r in rows)
        reviewed = sum(r["reviewed"] for r in rows)
        pending = sum(r["pending"] for r in rows)
        mismatch = sum(r["mismatch"] for r in rows)
        files = sum(1 for r in rows if r["scan"] or r["total"])
        phase_summary.append({
            "phase": ph, "files": files, "ported": ported, "reviewed": reviewed,
            "pending": pending, "mismatch": mismatch,
            "rank": min((r["rank"] for r in rows if r["rank"] is not None), default=None),
        })

    # HOL whole-tree totals for context (not the port denominator).
    hol_tree_theorems = sum(1 for v in kind_at.values() if v and v[0] in ("Theorem", "Triviality"))

    # JSON cannot serialise sets: convert the module/script collection fields.
    for _m in mod.values():
        _m["scripts"] = sorted(_m["scripts"])
        _m["theories"] = sorted(_m["theories"])
    for _s in script_rows:
        _s["lean_modules"] = sorted(_s["lean_modules"])
        _s["theories"] = sorted(_s["theories"])

    return {
        "generated": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "cakeml_commit": _git_rev(ROOT / "cakeml"),
        "source_index_commit": SOURCE_SHA.read_text().strip() if SOURCE_SHA.is_file() else "unknown",
        "totals": {
            "lean_files_total": sum(1 for _ in LEAN_ROOT.rglob("*.lean")),
            "lean_files_nontest": sum(1 for f in LEAN_ROOT.rglob("*.lean") if "/Test/" not in f.as_posix()),
            "lean_files_tagged": files_tagged,
            "tagged_decls": total_tags,
            "tagged_decls_scanned": len(decls),
            "map_entries": len(map_entries),
            "reviewed": reviewed_decls,
            "pending": pending_decls,
            "mismatch": mismatch_decls,
            "theorems_total": theorem_total,
            "theorems_reviewed": theorem_reviewed,
            "theorems_unmatched": theorem_total - theorem_reviewed,
            "theorems_pending": theorem_pending,
            "theorems_mismatch": theorem_mismatch,
            "defs": kind_counter.get("def", 0),
            "inductive": kind_counter.get("inductive", 0) + kind_counter.get("coinductive", 0),
            "structures": kind_counter.get("structure", 0) + kind_counter.get("abbrev", 0),
            "scripts_covered": len(scripts),
            "hol_tree_theorems": hol_tree_theorems,
        },
        "kw_totals": dict(kw_totals),
        "scripts": script_rows,
        "scope": scope,
        "pipeline": pipeline_rows,
        "pipeline_counts": dict(pipe_counts),
        "e2e": e2e_chains,
        "dep_height": (max(ranks.values()) if ranks else 0),
    }


# --------------------------------------------------------------------------- #
# Rendering
# --------------------------------------------------------------------------- #

STATUS_META = {
    "reviewed": {"label": "Reviewed port", "desc": "HOL<->Lean correspondence source-reviewed (reviewed_* status).", "cls": "reviewed"},
    "pending": {"label": "Pending classification", "desc": "Flapjack-only declaration, no HOL original recorded yet (no_hol_reference_pending_classification).", "cls": "pending"},
    "mismatch": {"label": "Documented mismatch", "desc": "Known statement difference; the Lean analogue stays untagged (documented_mismatch).", "cls": "mismatch"},
    "tagged_no_map": {"label": "Tagged", "desc": "Has an @[hol] tag but no map entry.", "cls": "reviewed"},
}


def json_script(data: dict) -> str:
    payload = json.dumps(data, ensure_ascii=False)
    # keep it safe inside a <script> block
    payload = payload.replace("</", "<\\/").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    return payload


HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Flapjack · CakeML→Lean port progress</title>
<style>
:root{
  --bg:#0f1117; --panel:#171a23; --panel2:#1d212c; --line:#2a2f3c;
  --ink:#e7ebf3; --muted:#9aa4b6; --accent:#5aa7ff; --accent2:#7ee0b8;
  --reviewed:#3fb950; --pending:#d29922; --mismatch:#f85149; --chip:#2a2f3c;
  --link:#8bb4ff;
}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);
  font:14px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
a{color:var(--link);text-decoration:none}
a:hover{text-decoration:underline}
header{position:sticky;top:0;z-index:20;background:rgba(15,17,23,.92);
  backdrop-filter:blur(6px);border-bottom:1px solid var(--line)}
.hbar{display:flex;align-items:center;gap:14px;padding:12px 20px;flex-wrap:wrap}
.brand{font-weight:700;font-size:16px;letter-spacing:.2px}
.brand small{color:var(--muted);font-weight:400}
.meta{color:var(--muted);font-size:12px;margin-left:auto;text-align:right;line-height:1.5}
.tabs{display:flex;gap:4px;padding:0 20px;background:var(--panel);border-bottom:1px solid var(--line)}
.tab{padding:10px 16px;color:var(--muted);cursor:pointer;border-bottom:2px solid transparent}
.tab:hover{color:var(--ink)}
.tab.active{color:var(--ink);border-bottom-color:var(--accent)}
main{padding:20px;max-width:1400px;margin:0 auto}
.section{display:none}
.section.active{display:block}
.kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:12px;margin-bottom:18px}
.card{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:14px 16px}
.card .n{font-size:26px;font-weight:700;line-height:1.1}
.card .k{color:var(--muted);font-size:12px;margin-top:4px}
.card .sub{font-size:11px;color:var(--muted);margin-top:6px}
.card.hl .n{color:var(--accent2)}
h2{font-size:15px;margin:22px 0 10px;color:var(--ink);
  display:flex;align-items:center;gap:8px}
h2 .hint{color:var(--muted);font-weight:400;font-size:12px}
.bar{height:10px;background:var(--panel2);border-radius:6px;overflow:hidden;
  display:flex;border:1px solid var(--line)}
.bar i{display:block;height:100%}
.stack{display:flex;height:10px;border-radius:6px;overflow:hidden;border:1px solid var(--line)}
.stack .seg{height:100%}
table{width:100%;border-collapse:collapse;font-size:13px}
th,td{text-align:left;padding:7px 10px;border-bottom:1px solid var(--line);vertical-align:top}
th{color:var(--muted);font-weight:600;font-size:11px;text-transform:uppercase;letter-spacing:.4px;
  position:sticky;top:0;background:var(--panel);cursor:pointer}
tbody tr:hover{background:#1b1f29}
td.num,th.num{text-align:right;font-variant-numeric:tabular-nums}
.mono{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
  font-size:12px;color:#cfe0ff;word-break:break-all}
.chip{display:inline-block;padding:1px 7px;border-radius:999px;font-size:11px;
  border:1px solid var(--chip);color:var(--muted);margin-right:4px;white-space:nowrap}
.chip.r{color:var(--reviewed);border-color:#1d3a26;background:#12241a}
.chip.p{color:var(--pending);border-color:#3a3112;background:#241f0e}
.chip.m{color:var(--mismatch);border-color:#3a1c1c;background:#241212}
.pill{font-size:11px;color:var(--muted);border:1px solid var(--line);
  border-radius:6px;padding:1px 6px}
.grp{margin:8px 0;border:1px solid var(--line);border-radius:10px;overflow:hidden}
.grp>summary{cursor:pointer;padding:10px 14px;background:var(--panel2);
  font-weight:600;display:flex;align-items:center;gap:10px;list-style:none}
.grp>summary::-webkit-details-marker{display:none}
.grp>summary .cnt{color:var(--muted);font-weight:400;font-size:12px;margin-left:auto}
.grp .inner{padding:0 6px 6px}
.controls{display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin:10px 0}
.controls input,.controls select{background:var(--panel);color:var(--ink);
  border:1px solid var(--line);border-radius:8px;padding:7px 10px;font-size:13px}
.controls input{min-width:240px}
.muted{color:var(--muted)}
.note{background:var(--panel);border:1px solid var(--line);border-left:3px solid var(--accent);
  border-radius:8px;padding:12px 14px;color:#cdd6e6;font-size:12.5px;margin:12px 0}
.legend{display:flex;gap:16px;flex-wrap:wrap;margin:8px 0 4px;color:var(--muted);font-size:12px}
.legend span{display:inline-flex;align-items:center;gap:6px}
.dot{width:10px;height:10px;border-radius:3px;display:inline-block}
footer{color:var(--muted);font-size:12px;padding:22px 20px;border-top:1px solid var(--line);max-width:1400px;margin:0 auto}
.kv{display:grid;grid-template-columns:auto 1fr;gap:2px 12px;font-size:12px;color:var(--muted)}
.rk{color:var(--muted);font-variant-numeric:tabular-nums;min-width:2.4em;text-align:right}
.sh{font-size:11px;color:var(--muted)}
.pct{color:var(--muted);font-size:11px;min-width:3.4em;text-align:right;display:inline-block}
.empty{color:var(--muted);padding:14px;text-align:center}
/* pipeline pass badges */
.badge{display:inline-block;padding:1px 9px;border-radius:999px;font-size:11px;
  font-weight:600;white-space:nowrap;border:1px solid transparent}
.badge.ported{color:var(--reviewed);background:#12241a;border-color:#1d3a26}
.badge.partial{color:var(--pending);background:#2a2410;border-color:#3a3112}
.badge.mismatch{color:var(--mismatch);background:#241212;border-color:#3a1c1c}
.badge.not_ported{color:#8b96a8;background:#1c2029;border-color:#333a49}
.badge-dot{width:9px;height:9px;border-radius:50%;display:inline-block;flex:none}
.badge-dot.ported{background:var(--reviewed)}
.badge-dot.partial{background:var(--pending)}
.badge-dot.mismatch{background:var(--mismatch)}
.badge-dot.not_ported{background:#5b6476}
/* scope completion */
.scope-row{display:flex;align-items:center;gap:12px;margin:8px 0}
.scope-row .lbl{min-width:10.5em;font-size:12.5px;color:var(--muted)}
.scope-row .bar{flex:1}
.scope-row .val{min-width:5.5em;font-size:12px;text-align:right;color:var(--muted)}
.e2e{display:flex;flex-direction:column;gap:10px;margin:10px 0}
.e2e .step{display:flex;align-items:flex-start;gap:12px;padding:10px 14px;
  background:var(--panel);border:1px solid var(--line);border-left:3px solid var(--accent2);border-radius:8px}
.e2e .step .idx{font-weight:700;color:var(--accent2);font-variant-numeric:tabular-nums;min-width:1.6em}
.e2e .step .idx.open{color:#5b6476}
.e2e .step .body{flex:1}
.e2e .step .nm{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:12.5px;color:#cfe0ff;word-break:break-all}
.e2e .step .ds{font-size:12px;color:var(--muted);margin-top:2px}
.e2e .arrow{color:var(--muted);text-align:center;font-size:11px;margin:-2px 0}
.e2e .arrow b{color:var(--accent);font-weight:600}
.e2e-grid{display:flex;gap:16px;flex-wrap:wrap;margin:10px 0}
.e2e-col{flex:1 1 100%;min-width:0;background:var(--panel2);border:1px solid var(--line);
  border-radius:10px;padding:12px 14px;display:flex;flex-direction:column}
.e2e-col > .e2e{margin:8px 0 0}
.e2e-head{display:flex;align-items:center;gap:8px;flex-wrap:wrap;font-size:13.5px}
.e2e-head b{color:var(--ink);font-size:14.5px}
.e2e-head .muted{font-size:12px}
.parts{margin-top:8px;border:1px solid var(--line);border-radius:8px;overflow:hidden}
.parts>summary{cursor:pointer;padding:6px 10px;background:var(--panel2);font-size:12px;
  color:var(--muted);list-style:none;display:flex;align-items:center;gap:6px}
.parts>summary::-webkit-details-marker{display:none}
.parts>summary .cnt{margin-left:auto;color:var(--muted);font-variant-numeric:tabular-nums}
.parts .inner{padding:4px 8px 8px}
.parts-t{width:100%;border-collapse:collapse;font-size:12px}
.parts-t th{text-align:left;color:var(--muted);font-size:10px;text-transform:uppercase;
  letter-spacing:.3px;padding:3px 6px;border-bottom:1px solid var(--line)}
.parts-t td{padding:3px 6px;border-bottom:1px solid var(--line);vertical-align:middle}
.parts-t tr:last-child td{border-bottom:none}
/* compile_correct dependency DAG */
.dk-node{margin:2px 0}
.dk-node>.dk-h{display:flex;align-items:center;gap:7px;flex-wrap:wrap;padding:2px 0}
.dk-kids{margin-left:14px;padding-left:12px;border-left:1px solid var(--line)}
.dk-dot{width:8px;height:8px;border-radius:50%;flex:none;background:#5b6476}
.dk-dot.dot-p{background:var(--reviewed)}
.dk-dot.dot-s{background:var(--accent2)}
.dk-name{font-weight:600;color:var(--ink)}
.dk-pass{font-size:10px;color:var(--accent);font-weight:600}
.dk-stage{font-size:10.5px;color:var(--muted)}
.dk-lean{font-size:10px;color:var(--muted)}
.dk-node .mono{font-size:12px}
.dk-spine{display:flex;flex-wrap:wrap;align-items:flex-start;gap:4px;margin:8px 0 4px}
.dk-spine-lbl{width:100%;font-size:10.5px;color:var(--muted);margin-bottom:4px}
.dk-arrow{color:var(--muted);align-self:center;padding:4px 0;font-size:14px}
.dk-pcard{border:1px solid var(--line);border-radius:7px;padding:5px 8px;background:var(--panel);min-width:150px;max-width:200px;display:flex;flex-direction:column;gap:4px}
.dk-pcard-h{display:flex;align-items:center;gap:6px;flex-wrap:wrap}
.dk-pcard .dk-name{font-size:11.5px}
.dk-pcard .dk-stage{flex-basis:100%}
.dk-lemmas{display:flex;flex-direction:column;gap:2px;border-top:1px solid var(--line);padding-top:4px}
.dk-lem{display:flex;align-items:center;gap:6px;font-size:10.5px;color:var(--ink)}
.dk-lem .mono{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:1}
.parts-t td.g{color:var(--muted);white-space:nowrap}
</style>
</head>
<body>
<header>
  <div class="hbar">
    <div class="brand">Flapjack <small>CakeML → Lean port · progress dashboard</small></div>
    <div class="meta" id="meta"></div>
  </div>
  <div class="tabs" id="tabs">
    <div class="tab active" data-s="overview">Overview</div>
    <div class="tab" data-s="pipeline">Pipeline</div>
  </div>
</header>
<main>
  <div class="section active" id="overview"></div>
  <div class="section" id="pipeline"></div>
  <div class="section" id="scripts"></div>
</main>
<footer id="footer"></footer>
<script id="data" type="application/json">__DATA__</script>
<script>
"use strict";
const DATA = JSON.parse(document.getElementById("data").textContent);
const STATUS_LABEL={reviewed:'Reviewed port',pending:'Pending classification',mismatch:'Documented mismatch'};
const $ = (s,el=document)=>el.querySelector(s);
const $$ = (s,el=document)=>[...el.querySelectorAll(s)];

function esc(s){return (s==null?"":String(s)).replace(/[&<>]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;'}[c]));}
function chips(m){
  const out=[];
  if(m.reviewed) out.push(`<span class="chip r">${m.reviewed} reviewed</span>`);
  if(m.pending)  out.push(`<span class="chip p">${m.pending} pending</span>`);
  if(m.mismatch) out.push(`<span class="chip m">${m.mismatch} mismatch</span>`);
  return out.join("")||`<span class="chip">0</span>`;
}
function bar(reviewed,pending,mismatch,total){
  if(!total) return `<span class="pct">—</span>`;
  const r=100*reviewed/total,p=pending/total*100,m=mismatch/total*100;
  return `<span class="stack" title="${reviewed} reviewed / ${pending} pending / ${mismatch} mismatch">
    <i class="seg" style="width:${r}%;background:var(--reviewed)"></i>
    <i class="seg" style="width:${p}%;background:var(--pending)"></i>
    <i class="seg" style="width:${m}%;background:var(--mismatch)"></i></span>`;
}
function setTab(name){
  const sec=$(".section#"+CSS.escape(name));
  if(!sec) return;
  $$(".tab").forEach(t=>t.classList.toggle("active",t.dataset.s===name));
  $$(".section").forEach(s=>s.classList.toggle("active",s.id===name));
  history.replaceState(null,"","#"+name);
}
$$(".tab").forEach(t=>t.addEventListener("click",()=>setTab(t.dataset.s)));

// ---------- meta / footer ----------
$("#meta").innerHTML =
  `CakeML @ <b>${esc(DATA.cakeml_commit.slice(0,12))}</b> · index ${DATA.source_index_commit.slice(0,8)}<br>generated ${esc(DATA.generated)}`;

// ---------- overview ----------
function renderOverview(){
  const t=DATA.totals;
  const card=(n,k,sub,hl)=>`<div class="card ${hl?'hl':''}"><div class="n">${n}</div><div class="k">${k}</div>${sub?`<div class="sub">${sub}</div>`:''}</div>`;
  const reviewedPct = t.map_entries? Math.round(100*t.reviewed/t.map_entries):0;
  $("#overview").innerHTML = `
    <div class="kpis">
      ${card(t.lean_files_tagged,'Lean files ported',`of ${t.lean_files_nontest} non-test modules carry an <span class="mono">@[hol]</span> tag`,true)}
      ${card(t.theorems_total.toLocaleString(),'Ported theorems',`${t.theorems_reviewed.toLocaleString()} with a reviewed map entry · ${t.theorems_unmatched.toLocaleString()} tagged but not yet mapped`)}
      ${card(t.tagged_decls_scanned.toLocaleString(),'Tagged declarations',`${t.defs.toLocaleString()} defs · ${t.inductive+t.structures} inductive/struct/abbrev`)}
      ${card(t.scripts_covered,'HOL source scripts',`mapped to Lean modules, dependency-ordered`)}
      ${card(t.map_entries.toLocaleString(),'Curated map entries',`${reviewedPct}% reviewed · ${t.pending.toLocaleString()} pending · ${t.mismatch} mismatch`)}
      ${card(t.hol_tree_theorems.toLocaleString(),'HOL tree theorems',`whole CakeML/HOL tree (context, not the port denominator)`)}
    </div>
    <div class="note"><b>How to read this.</b> Every number comes from the port's own tooling:
      the <span class="mono">@[hol]</span> tags in <span class="mono">Flapjack/</span> source and the
      reviewed <span class="mono">docs/HOL-THEOREM-MAP.json</span> inventory, cross-checked against the
      <span class="mono">.hol-index/</span> CakeML source index. <b>Reviewed</b> means a reviewer source-compared the
      HOL and Lean declarations; <b>pending classification</b> is Flapjack-only work awaiting a HOL original;
      <b>documented mismatch</b> is a known statement difference kept untagged. None of these establish
      cross-language equivalence on their own — see <span class="mono">docs/SOUNDNESS.md</span>.</div>
    ${scopeHtml()}
    ${e2eHtml()}
    <div class="note">Dependency order uses the HOL theory graph (<span class="mono">.hol-index/theory-deps.txt</span>):
      a layer's rank is the depth of its source theory in the original proof's dependency tree, so rows near the top
      are prerequisites for rows below. The CakeML/HOL index totals are best-effort and are not used as a port denominator.</div>`;
}

// ---------- port scope completion + end-to-end chain (rendered in overview) ----------
function sstack(a,b){const t=a+b||1;return `<span class="stack" title="${a} ported / ${b} unported">
    <i class="seg" style="width:${100*a/t}%;background:var(--reviewed)"></i>
    <i class="seg" style="width:${100*b/t}%;background:#5b6476"></i></span>`;}
function scopeHtml(){
  const s=DATA.scope||{};
  if(!s.scope_scripts) return '';
  const unpd=s.unported_all||[];
  const top=(s.unported_top||unpd).map(u=>`<tr data-q="${esc(u.hol_path)}"><td class="mono sh">${esc(u.hol_path)}</td><td class="num sh">${u.hol_decls}</td></tr>`).join("");
  const unpdDecls=s.scope_scripts_unported_decls??0;
  return `
    <h2>Port scope completion <span class="hint">how much of the in-scope CakeML surface is ported</span></h2>
    <div class="kpis">
      ${card(s.scope_scripts_ported+' / '+s.scope_scripts,'In-scope scripts ported',`${s.scope_scripts_unported} of ${s.scope_scripts} in-scope CakeML scripts still have no port`,true)}
      ${card(s.pct_decls+'%','Source decls in ported scripts',`share of the ${s.scope_decls.toLocaleString()} in-scope CakeML declarations (source index) now inside a ported script`)}
      ${card(s.scope_map_entries.toLocaleString(),'Ported declarations','map entries covering in-scope scripts — a different unit from the source index, shown for context')}
    </div>
    <div class="scope-row"><div class="lbl">Scripts · ported vs unported</div><div class="bar" style="flex:1">${sstack(s.scope_scripts_ported,s.scope_scripts_unported)}</div><div class="val">${s.scope_scripts_ported} ported · ${s.scope_scripts_unported} unported</div></div>
    <div class="scope-row"><div class="lbl">In-scope source declarations</div><div class="bar" style="flex:1">${bar(s.scope_decls_in_ported,s.scope_decls-s.scope_decls_in_ported,0,s.scope_decls)}</div><div class="val">${s.scope_decls_in_ported.toLocaleString()} / ${s.scope_decls.toLocaleString()} · ${s.pct_decls}%</div></div>
    <details class="grp" open><summary>Largest unported in-scope scripts <span class="cnt">${s.scope_scripts_unported} unported · ${unpdDecls.toLocaleString()} source decls</span></summary>
      <div class="inner"><div style="overflow:auto;max-height:60vh">
      <table class="fmap"><thead><tr><th>HOL script</th><th class="num">Est. source decls</th></tr></thead>
      <tbody>${top||'<tr><td colspan="2" class="empty">none</td></tr>'}</tbody></table>
      </div></div></details>
    <div class="note" style="border-left-color:var(--pending)">Scope = CakeML source under <span class="mono">pancake/</span>, <span class="mono">compiler/</span>, <span class="mono">semantics/</span>, <span class="mono">basis/</span>, <span class="mono">examples/l3-machine-code/</span> (excludes the candle translator / characteristic-files trees).
      "Scripts ported" is a clean same-unit count; the source-declaration share uses the CakeML index on both numerator and denominator, but index totals are best-effort and are <b>not</b> a rigorous port denominator.</div>`;
}
function e2eLinkHtml(e){
  const ported=(e.status==='ported');
  const badge=ported?'<span class="badge ported">ported</span>':`<span class="badge not_ported">${esc((e.status||'other').replace('_',' ')||'other')}</span>`;
  const cases=e.n>1?` <span class="muted">(${e.n} cases)</span>`:'';
  const loc=e.lean_path?`<span class="mono sh">${esc(e.lean_path.replace(/^Flapjack\//,''))}</span> · `:'';
  const parts = e.partsTree ? renderDag(e.partsTree, e) : '';
  const idx = e.parts ? '' : `<div class="idx ${ported?'':'open'}">${ported?'✓':'○'}</div>`;
  return `<div class="step">${idx}<div class="body">
      <div class="nm">${esc(e.hol_name)}</div>
      <div class="ds">${esc(e.desc)}</div>
      <div class="ds">${loc}${badge}${cases}</div>${parts}</div></div>`;
}
function e2eHtml(){
  const chains=DATA.e2e||[];
  const cols=chains.map(ch=>{
    const steps=ch.links.map((e,i)=>(i>0?`<div class="arrow">▼ <b>compiled target program</b> ▼</div>`:'')+e2eLinkHtml(e)).join("");
    const openBadge=ch.any_open?' <span class="badge not_ported">front-end not yet ported</span>':'';
    return `<div class="e2e-col"><div class="e2e-head"><b>${esc(ch.label)}</b><span class="muted">${esc(ch.src_lang)}</span>${openBadge}</div><div class="e2e">${steps}</div></div>`;
  }).join("");
  return `
    <h2>End-to-end correctness · CakeML AST → RISC-V <span class="hint">the CakeML compiler's source-to-machine chain, with its unported front-end broken down</span></h2>
    <div class="note" style="border-left-color:var(--accent2)"><b>CakeML</b> <span class="mono">compile_correct</span> (source → installed RISC-V machine code) is <b>not yet ported</b>. <b>Expand it</b> to see the <b>dependency DAG</b> of the theorems it composes, built straight from the CakeML proof scripts: the top composition <span class="mono">compile_correct → compile_correct_lemma → compile_correct_gen</span> feeds the front-end (<span class="mono">parse</span>/<span class="mono">infertype</span>/<span class="mono">compile</span>), type soundness (<span class="mono">semantics_type_sound</span>) and the backend per-pass chain (<span class="mono">compile_correct'</span>, flat → clos → bvl → bvi → data → word → stack → lab → target, each pass's output feeding the next). Nodes are coloured by whether that <i>exact</i> theorem has a reviewed Lean port. Because the DAG uses the real theorems (not just the mapped ones), it exposes precise gaps — e.g. <span class="mono">data_to_word</span>'s own <span class="mono">compile_correct</span> is still open even though its <span class="mono">data_compile_correct</span> is ported. Its backend and RISC-V encoder (<span class="mono">riscv_encoder_correct</span>, <span class="mono">riscv_target_ok</span>) are already reviewed.</div>
    <div class="e2e-grid">${cols}</div>`;
}

// compile_correct dependency DAG (built from the real CakeML proof scripts).
function dkBadge(st){
  if(st==='ported') return '<span class="badge ported">ported</span>';
  if(st==='spine')  return '<span class="badge partial">backend chain</span>';
  return `<span class="badge not_ported">${esc((st||'not_ported').replace(/_/g,' ')||'not ported')}</span>`;
}
function dkDot(n){
  const st=n.status, cls = st==='ported'?'dot-p':st==='spine'?'dot-s':'dot-n';
  const tip = st==='ported'?'reviewed port':st==='spine'?'backend composition chain':'not yet ported';
  return `<span class="dk-dot ${cls}" title="${tip}"></span>`;
}
function dkLemmas(children){
  return `<div class="dk-lemmas">${children.map(c=>`<div class="dk-lem">${dkDot(c)}<span class="mono sh">${esc(c.name)}</span>${dkBadge(c.status)}</div>`).join('')}</div>`;
}
function dkPassCard(p){
  return `<div class="dk-pcard"><div class="dk-pcard-h">${dkDot(p)}<span class="dk-pass">${esc(p.pass||'')}</span><span class="dk-name mono">${esc(p.name)}</span>${dkBadge(p.status)}</div><div class="dk-stage">${esc(p.stage)}</div>${(p.children&&p.children.length)?dkLemmas(p.children):''}</div>`;
}
function dkSpine(passes){
  const lbl='backend <span class="mono">compile_correct\u2019</span> \u2014 per-pass chain (each pass\u2019s output feeds the next)';
  return `<div class="dk-spine"><div class="dk-spine-lbl">${lbl}</div>${passes.map((p,i)=>(i>0?'<div class="dk-arrow">\u2192</div>':'')+dkPassCard(p)).join('')}</div>`;
}
function dkNode(n){
  if(n.kind==='spine') return dkSpine(n.children||[]);
  const label = n.kind==='pass'
    ? `<span class="dk-stage">${esc(n.stage)}</span> <span class="dk-name mono">${esc(n.name)}</span>`
    : `<span class="dk-name mono">${esc(n.name)}</span>`;
  const lean = n.lean?`<div class="dk-lean mono sh">${esc(n.lean.replace(/^Flapjack\//,''))}</div>`:'';
  const kids = (n.children&&n.children.length)
    ? `<div class="dk-kids">${n.children.map(c=>dkNode(c)).join('')}</div>` : '';
  const pc = (n.kind==='pass'&&n.children&&n.children.length)?`<span class="muted">(${n.children.length} lemmas)</span>`:'';
  return `<div class="dk-node dk-${esc(n.kind)}" data-q="${esc((n.name+' '+n.stage+' '+n.group).toLowerCase())}"><div class="dk-h">${dkDot(n)}${label}${dkBadge(n.status)}${pc}${lean}</div>${kids}</div>`;
}
function renderDag(t,e){
  if(!t) return '';
  const total=e.parts_total, ported=e.parts_ported, spine=e.partsSpineLen;
  return `<details class="parts dk-parts"><summary><span class="idx open">\u25CB</span> dependency DAG \u00b7 ${total} theorems that make up compile_correct
      <span class="cnt">${ported} reviewed \u00b7 ${total-ported} gaps \u00b7 ${spine} backend passes \u00b7 read top\u2193, spine left\u2192right</span></summary>
      <div class="inner">${dkNode(t)}</div></details>`;
}

function card(n,k,sub,hl){return `<div class="card ${hl?'hl':''}"><div class="n">${n}</div><div class="k">${k}</div>${sub?`<div class="sub">${sub}</div>`:''}</div>`;}

// ---------- pipeline ----------
function renderPipeline(){
  const pc=DATA.pipeline_counts||{};
  const total=DATA.pipeline.length;
  const ported=pc.ported||0, partial=pc.partial||0, mm=pc.mismatch||0, np=pc.not_ported||0;
  const badge=(st)=>`<span class="badge ${st}">${st.replace('_',' ')}</span>`;
  const rows=DATA.pipeline.map(p=>`<tr data-q="${esc((p.pass+' '+p.theorem+' '+p.script+' '+p.stage).toLowerCase())}" data-st="${p.status}">
      <td class="mono">${esc(p.pass)}</td>
      <td class="mono sh">${esc(p.script)}</td>
      <td class="mono sh">${esc(p.theorem)}</td>
      <td>${badge(p.status)}</td>
    </tr>`).join("");
  $("#pipeline").innerHTML=`
    <div class="kpis">
      ${card(ported,'Passes ported',`of ${total} major compilation passes with a headline correctness theorem`,true)}
      ${card(np+(partial?1:0),'Not yet ported',`${np} passes whose headline theorem is still missing${partial?` · ${partial} partial`:''}${mm?` · ${mm} mismatch`:''}`)}
      ${card(total,'Pipeline passes','one headline theorem per compilation pass')}
      ${card(Math.round(100*ported/total||0)+'%','Pipeline complete','share of passes whose headline theorem is reviewed')}
    </div>
    <div class="note" style="border-left-color:var(--pending)">A coloured badge per pass shows whether that pass's <b>headline</b> semantic-preservation theorem is ported. The theorem named here is one representative result per <span class="mono">&lt;pass&gt;ProofScript.sml</span>; a pass usually carries additional supporting theorems. Matching is by (script, theorem) against <span class="mono">HOL-THEOREM-MAP.json</span> — a per-pass heuristic, not a per-theorem review.</div>
    <div class="controls">
      <input id="psearch" placeholder="filter by pass / theorem / script…">
      <select id="pstatus">${pipeStatusOptions()}</select>
      <span class="muted">${total} passes</span>
    </div>
    <div style="overflow:auto;max-height:74vh">
    <table id="pt"><thead><tr>
      <th>Pass</th><th>HOL proof script</th><th>Headline correctness theorem</th><th>Status</th>
    </tr></thead><tbody>${rows||'<tr><td colspan="4" class="empty">none</td></tr>'}</tbody></table>
    </div>`;
  const filt=()=>{
    const q=($("#psearch").value||'').toLowerCase(), st=$("#pstatus").value;
    $$("#pt tbody tr").forEach(tr=>{
      const hit=(tr.dataset.q||'').includes(q)&&(st==='all'||tr.dataset.st===st);
      tr.style.display=hit?'':'none';
    });
  };
  $("#psearch").addEventListener("input",filt);
  $("#pstatus").addEventListener("change",filt);
}
function pipeStatusOptions(){
  const pc=DATA.pipeline_counts||{};
  let o='<option value="all">all statuses</option>';
  if(pc.ported)o+=`<option value="ported">ported</option>`;
  if(pc.partial)o+=`<option value="partial">partial</option>`;
  if(pc.mismatch)o+=`<option value="mismatch">mismatch</option>`;
  if(pc.not_ported)o+=`<option value="not_ported">not ported</option>`;
  return o;
}

// ---------- footer ----------
function renderFooter(){
  $("#footer").innerHTML = `
    <b>Provenance & method.</b>
    <div class="kv" style="margin-top:8px">
      <div>Inventory</div><div><span class="mono">docs/HOL-THEOREM-MAP.json</span> (15,098 curated entries; CI-checked by <span class="mono">scripts/check-hol-refs.py</span> & <span class="mono">check_hol_ref_export.py</span>)</div>
      <div>Source tags</div><div>direct scan of <span class="mono">@[hol …]</span> in <span class="mono">Flapjack/</span> (<span class="mono">${DATA.totals.tagged_decls}</span> occurrences)</div>
      <div>Dependency order</div><div>HOL theory graph <span class="mono">.hol-index/theory-deps.txt</span> (longest-chain rank, height ${DATA.dep_height}); ${DATA.scripts.length} ported theories fully covered</div>
      <div>Regenerate</div><div><span class="mono">python3 scripts/build-dashboard.py</span> (auto-refreshes a stale <span class="mono">.hol-index/</span>)</div>
    </div>
    <div class="note" style="margin-top:12px">A ported <span class="mono">@[hol]</span> tag records a reviewed source comparison, not a proof of HOL↔Lean equivalence.
      Statement differences are tracked as <i>documented mismatch</i>; Flapjack-only declarations awaiting a HOL original are <i>pending classification</i>.
      Whole-tree HOL counts are context only — most CakeML/HOL theories (examples, CNF, deflate, …) are outside this Pancake compiler port.</div>
    <div class="muted" style="margin-top:8px">Generated ${esc(DATA.generated)} · CakeML @ ${esc(DATA.cakeml_commit.slice(0,12))}</div>`;
}

renderOverview();
renderPipeline();
renderFooter();
if(location.hash) setTab(location.hash.slice(1));
</script>
</body>
</html>
"""


def render(data: dict) -> str:
    return HTML_TEMPLATE.replace("__DATA__", json_script(data))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, default=ROOT / "dashboard.html",
                    help="output path (default: ./dashboard.html)")
    args = ap.parse_args()
    data = build()
    args.out.write_text(render(data), encoding="utf-8")
    t = data["totals"]
    print(f"wrote {rel(args.out)}")
    print(f"  {t['lean_files_tagged']} ported files · {t['theorems_total']:,} theorems · "
          f"{t['reviewed']:,} reviewed · {t['pending']:,} pending · {t['mismatch']} mismatch")
    print(f"  {t['scripts_covered']} HOL source scripts, dependency-ordered")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
