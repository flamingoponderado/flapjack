"""Reject drift in original HOL universal equation captures."""
from pathlib import Path
EXPECTED = ['bit10_binders=x0::bool;x1::bool;x2::bool;x3::bool;x4::bool;x5::bool;x6::bool;x7::bool;', 'bit10_statement=∀x0 x1 x2 x3 x4 x5 x6 x7.', '  (word_bit 1 (v2w [x0; x1; x2; x3; x4; x5; x6; x7]) ⇔ x6) ∧', '  (word_bit 0 (v2w [x0; x1; x2; x3; x4; x5; x6; x7]) ⇔ x7)', 'bit10_hypotheses=0', 'bit10_proof=T', 'bit0_binders=w::word64;v::word64;', 'bit0_statement=∀w v.', '  ¬word_bit 0 (0xFFFFFFFFFFFFFFFEw && w) ∧', '  (word_bit 0 ((0xFFFFFFFFFFFFFFFEw && w) + v) ⇔ word_bit 0 v)', 'bit0_hypotheses=0', 'bit0_proof=T', 'v2w0_binders=b3::bool;b2::bool;b1::bool;b0::bool;', 'v2w0_statement=∀b3 b2 b1 b0.', '  v2w [F; F; F; F; T] = 1w ∧ v2w [F; F; F; F; F] = 0w ∧', '  (v2w [T; b3; b2; b1; b0] = 0w ⇔ F) ∧ (v2w [b3; T; b2; b1; b0] = 0w ⇔ F) ∧', '  (v2w [b3; b2; T; b1; b0] = 0w ⇔ F) ∧ (v2w [b3; b2; b1; T; b0] = 0w ⇔ F) ∧', '  (v2w [b3; b2; b1; b0; T] = 0w ⇔ F)', 'v2w0_hypotheses=0', 'v2w0_proof=T', 'bitShift_binders=x::word64;w::word64;', 'bitShift_statement=∀x w. word_bit 0 (x + w ≪ 1) ⇔ word_bit 0 x', 'bitShift_hypotheses=0', 'bitShift_proof=T', 'v2w8_type=:bool list -> word8', 'v2w5_type=:bool list -> word5']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL equation capture differs from reviewed full statements")

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_step_bit_rewrites_probe.out").read_text())
    print("step_bit_rewrites: exact original HOL types, hypotheses and universal equations PASS")
