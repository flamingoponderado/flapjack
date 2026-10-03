"""Reject drift in original HOL universal equation captures."""
from pathlib import Path
EXPECTED = ['DecodeAny_type=:rawInstType -> instruction', 'DecodeAny_hypotheses=0', 'DecodeAny_half_equation=∀h. DecodeAny (Half h) = DecodeRVC h', 'DecodeAny_half_proof=T', 'DecodeAny_word_equation=∀w. DecodeAny (Word w) = Decode w', 'DecodeAny_word_proof=T']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL equation capture differs from reviewed full statements")

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_decode_any_probe.out").read_text())
    print("decode_any: exact original HOL types, hypotheses and universal equations PASS")
