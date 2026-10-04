"""Reject drift in original HOL universal equation captures."""
from pathlib import Path
import runpy
ROOT = Path(__file__).resolve().parents[2]
CONTRACTS = runpy.run_path(str(ROOT / "scripts/l3/lean_contracts.py"))
LEAN_PATH = 'Flapjack/RiscV/L3/Step/FetchTheorems.lean'
LEAN_EXPECTED = {
    'fetch16': """theorem fetch16 (s : riscv_state) (xs : List Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF : Bool)
    (h : xs = [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,xA,xB,xC,xD,xE,xF] ∧
      (s.c_MCSR s.procID).mstatus.VM = 0#5 ∧
      s.MEM8 (s.c_PC s.procID + 1#64) = holV2w 8 [x0,x1,x2,x3,x4,x5,x6,x7] ∧
      s.MEM8 (s.c_PC s.procID) = holV2w 8 [x8,x9,xA,xB,xC,xD,xE,xF] ∧
      ¬(xE = true ∧ xF = true)) :
    Fetch s = (.Half (holV2w 16 xs),
      {s with c_Skip := holUpdate s.procID 2#64 s.c_Skip})""",
    'fetch32': """theorem fetch32 (s : riscv_state) (xs : List Bool) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 yA yB yC yD yE yF : Bool)
    (h : xs = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,yA,yB,yC,yD,yE,yF,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,xA,xB,xC,xD,xE,xF] ∧
      (s.c_MCSR s.procID).mstatus.VM = 0#5 ∧
      s.MEM8 (s.c_PC s.procID + 3#64) = holV2w 8 [y0,y1,y2,y3,y4,y5,y6,y7] ∧
      s.MEM8 (s.c_PC s.procID + 2#64) = holV2w 8 [y8,y9,yA,yB,yC,yD,yE,yF] ∧
      s.MEM8 (s.c_PC s.procID + 1#64) = holV2w 8 [x0,x1,x2,x3,x4,x5,x6,x7] ∧
      s.MEM8 (s.c_PC s.procID) = holV2w 8 [x8,x9,xA,xB,xC,xD,xE,xF] ∧
      xE = true ∧ xF = true) :
    Fetch s = (.Word (holV2w 32 xs),
      {s with c_Skip := holUpdate s.procID 4#64 s.c_Skip})""",
}
EXPECTED = ['Fetch16_binders=s::riscv_state;xs::bool list;x0::bool;x1::bool;x2::bool;x3::bool;x4::bool;x5::bool;x6::bool;x7::bool;x8::bool;x9::bool;xA::bool;xB::bool;xC::bool;xD::bool;xE::bool;xF::bool;', 'Fetch16_statement=∀s xs x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF.', '  xs = [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; xA; xB; xC; xD; xE; xF] ∧', '  (s.c_MCSR s.procID).mstatus.VM = 0w ∧', '  s.MEM8 (s.c_PC s.procID + 1w) = v2w [x0; x1; x2; x3; x4; x5; x6; x7] ∧', '  s.MEM8 (s.c_PC s.procID) = v2w [x8; x9; xA; xB; xC; xD; xE; xF] ∧', '  ¬(xE ∧ xF) ⇒', '  Fetch s = (Half (v2w xs),s with c_Skip := s.c_Skip⦇s.procID ↦ 2w⦈)', 'Fetch16_hypotheses=0', 'Fetch16_proof=T', 'Fetch32_binders=s::riscv_state;xs::bool list;x0::bool;x1::bool;x2::bool;x3::bool;x4::bool;x5::bool;x6::bool;x7::bool;x8::bool;x9::bool;xA::bool;xB::bool;xC::bool;xD::bool;xE::bool;xF::bool;y0::bool;y1::bool;y2::bool;y3::bool;y4::bool;y5::bool;y6::bool;y7::bool;y8::bool;y9::bool;yA::bool;yB::bool;yC::bool;yD::bool;yE::bool;yF::bool;', 'Fetch32_statement=∀s xs x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF y0 y1 y2 y3 y4 y5 y6 y7', '    y8 y9 yA yB yC yD yE yF.', '  xs =', '  [y0; y1; y2; y3; y4; y5; y6; y7; y8; y9; yA; yB; yC; yD; yE; yF; x0; x1;', '   x2; x3; x4; x5; x6; x7; x8; x9; xA; xB; xC; xD; xE; xF] ∧', '  (s.c_MCSR s.procID).mstatus.VM = 0w ∧', '  s.MEM8 (s.c_PC s.procID + 3w) = v2w [y0; y1; y2; y3; y4; y5; y6; y7] ∧', '  s.MEM8 (s.c_PC s.procID + 2w) = v2w [y8; y9; yA; yB; yC; yD; yE; yF] ∧', '  s.MEM8 (s.c_PC s.procID + 1w) = v2w [x0; x1; x2; x3; x4; x5; x6; x7] ∧', '  s.MEM8 (s.c_PC s.procID) = v2w [x8; x9; xA; xB; xC; xD; xE; xF] ∧ xE ∧ xF ⇒', '  Fetch s = (Word (v2w xs),s with c_Skip := s.c_Skip⦇s.procID ↦ 4w⦈)', 'Fetch32_hypotheses=0', 'Fetch32_proof=T', 'v2w8_type=:bool list -> word8', 'v2w16_type=:bool list -> word16', 'v2w32_type=:bool list -> word32']

def check_lean(text):
    for name, expected in LEAN_EXPECTED.items():
        CONTRACTS["check_declaration"](text, 'theorem', name, expected, statement=True)

def check(text, lean=None):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL equation capture differs from reviewed full statements")

    check_lean((ROOT / LEAN_PATH).read_text() if lean is None else lean)

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_fetch_theorems_probe.out").read_text())
    print("fetch_theorems: original HOL captures AND reviewed full Lean statements PASS")
