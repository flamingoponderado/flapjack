"""Reject drift in original HOL universal equation captures."""
from pathlib import Path
EXPECTED = ['nextEval_binders=s::riscv_state;w::rawInstType;fetched::riscv_state;i::instruction;nxt::riscv_state;', 'nextEval_statement=∀s w fetched i nxt.', '  Fetch s = (w,fetched) ∧ DecodeAny w = i ∧ Run i fetched = nxt ∧', '  nxt.exception = NoException ∧ nxt.c_NextFetch nxt.procID = NONE ⇒', '  NextRISCV s = update_pc (nxt.c_PC nxt.procID + Skip nxt) nxt', 'nextEval_hypotheses=0', 'nextEval_proof=T', 'nextBranch_binders=s::riscv_state;w::rawInstType;fetched::riscv_state;i::instruction;nxt::riscv_state;a::word64;', 'nextBranch_statement=∀s w fetched i nxt a.', '  Fetch s = (w,fetched) ∧ DecodeAny w = i ∧ Run i fetched = nxt ∧', '  nxt.exception = NoException ∧', '  nxt.c_NextFetch nxt.procID = SOME (BranchTo a) ⇒', '  NextRISCV s =', '  update_pc a (nxt with c_NextFetch := nxt.c_NextFetch⦇nxt.procID ↦ NONE⦈)', 'nextBranch_hypotheses=0', 'nextBranch_proof=T', 'nextCond_binders=s::riscv_state;w::rawInstType;fetched::riscv_state;i::instruction;nxt::riscv_state;a::word64;b::bool;', 'nextCond_statement=∀s w fetched i nxt a b.', '  Fetch s = (w,fetched) ∧ DecodeAny w = i ∧ Run i fetched = nxt ∧', '  nxt.exception = NoException ∧', '  nxt.c_NextFetch nxt.procID = (if b then SOME (BranchTo a) else NONE) ⇒', '  NextRISCV s =', '  update_pc (if b then a else (nxt.c_PC nxt.procID + Skip nxt))', '    (nxt with c_NextFetch := nxt.c_NextFetch⦇nxt.procID ↦ NONE⦈)', 'nextCond_hypotheses=0', 'nextCond_proof=T']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL equation capture differs from reviewed full statements")

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_next_evaluation_probe.out").read_text())
    print("next_evaluation: exact original HOL types, hypotheses and universal equations PASS")
