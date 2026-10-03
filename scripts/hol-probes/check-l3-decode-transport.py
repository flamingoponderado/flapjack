"""Reject drift in original HOL universal equation captures."""
from pathlib import Path
EXPECTED = ['decodeWord_binders=w::word32;i::instruction;', 'decodeWord_statement=∀w i. Decode w = i ⇒ DecodeAny (Word w) = i', 'decodeWord_hypotheses=0', 'decodeWord_proof=T', 'decodeHalf_binders=h::word16;i::instruction;', 'decodeHalf_statement=∀h i. DecodeRVC h = i ⇒ DecodeAny (Half h) = i', 'decodeHalf_hypotheses=0', 'decodeHalf_proof=T']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL equation capture differs from reviewed full statements")

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_decode_transport_probe.out").read_text())
    print("decode_transport: exact original HOL types, hypotheses and universal equations PASS")
