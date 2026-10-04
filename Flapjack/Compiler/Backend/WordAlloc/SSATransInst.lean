import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies
import Flapjack.Compiler.Backend.WordAlloc.SSASetup

/-!
# word_alloc SSA renaming of instructions and expressions

Literal ports of `word_allocScript.sml:129-283`: `ssa_cc_trans_inst` and
`ssa_cc_trans_exp`, over the native `WordLangInst`/`WordLangExpHOL`/
`WordLangProgHOL` carriers with HOL's `'a word` as `BitVec width` (positive
width); `dimindex (:'a) = 64` is `width = 64`. `Move0`/`Move1` are `Move 0`/
`Move 1`; HOL `let (a, b, c) = e in` is a pattern `let`. Clause order follows
HOL, ending in the `Inst x` catchall (Load16/Store16 and the remaining FP
instructions). Proof-side ports: the executed list-state SSA pass is not routed
through them.
-/

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Literal `ssa_cc_trans_inst` (`word_allocScript.sml:129-266`). -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.

def ssaCcTransInst {width : Nat} [NeZero width] :
    WordLangInst (BitVec width) → Spt Nat → Nat →
      WordLangProgHOL (BitVec width) × Spt Nat × Nat
  | .skip, ssa, na => (.skip, ssa, na)
  | .const reg w, ssa, na =>
    let (reg', ssa', na') := nextVarRename reg ssa na
    (.inst (.const reg' w), ssa', na')
  | .arith (.binop bop r1 r2 ri), ssa, na =>
    match ri with
    | .reg r3 =>
      let r3' := optionLookup ssa r3
      let r2' := optionLookup ssa r2
      let (r1', ssa', na') := nextVarRename r1 ssa na
      (.inst (.arith (.binop bop r1' r2' (.reg r3'))), ssa', na')
    | _ =>
      let r2' := optionLookup ssa r2
      let (r1', ssa', na') := nextVarRename r1 ssa na
      (.inst (.arith (.binop bop r1' r2' ri)), ssa', na')
  | .arith (.shift shift r1 r2 ri), ssa, na =>
    match ri with
    | .reg r3 =>
      let r3' := optionLookup ssa r3
      let r2' := optionLookup ssa r2
      let movIn := WordLangProgHOL.move 1 [(8, r3')]
      let (r1', ssa', na') := nextVarRename r1 ssa na
      (.seq movIn (.inst (.arith (.shift shift r1' r2' (.reg 8)))), ssa', na')
    | _ =>
      let r2' := optionLookup ssa r2
      let (r1', ssa', na') := nextVarRename r1 ssa na
      (.inst (.arith (.shift shift r1' r2' ri)), ssa', na')
  | .arith (.div r1 r2 r3), ssa, na =>
    let r2' := optionLookup ssa r2
    let r3' := optionLookup ssa r3
    let (r1', ssa', na') := nextVarRename r1 ssa na
    (.inst (.arith (.div r1' r2' r3')), ssa', na')
  | .arith (.addCarry r1 r2 r3 r4), ssa, na =>
    let r2' := optionLookup ssa r2
    let r3' := optionLookup ssa r3
    let r4' := optionLookup ssa r4
    let (r1', ssa', na') := nextVarRename r1 ssa na
    let movIn := WordLangProgHOL.move 1 [(0, r4')]
    let (r4'', ssa'', na'') := nextVarRename r4 ssa' na'
    let movOut := WordLangProgHOL.move 1 [(r4'', 0)]
    (.seq movIn (.seq (.inst (.arith (.addCarry r1' r2' r3' 0))) movOut), ssa'', na'')
  | .arith (.addOverflow r1 r2 r3 r4), ssa, na =>
    let r2' := optionLookup ssa r2
    let r3' := optionLookup ssa r3
    let (r1', ssa', na') := nextVarRename r1 ssa na
    let (r4'', ssa'', na'') := nextVarRename r4 ssa' na'
    let movOut := WordLangProgHOL.move 1 [(r4'', 0)]
    (.seq (.inst (.arith (.addOverflow r1' r2' r3' 0))) movOut, ssa'', na'')
  | .arith (.subOverflow r1 r2 r3 r4), ssa, na =>
    let r2' := optionLookup ssa r2
    let r3' := optionLookup ssa r3
    let (r1', ssa', na') := nextVarRename r1 ssa na
    let (r4'', ssa'', na'') := nextVarRename r4 ssa' na'
    let movOut := WordLangProgHOL.move 1 [(r4'', 0)]
    (.seq (.inst (.arith (.subOverflow r1' r2' r3' 0))) movOut, ssa'', na'')
  | .arith (.longMul r1 r2 r3 r4), ssa, na =>
    let r3' := optionLookup ssa r3
    let r4' := optionLookup ssa r4
    let movIn := WordLangProgHOL.move 1 [(0, r3'), (4, r4')]
    let (r1', ssa', na') := nextVarRename r1 ssa na
    let (r2', ssa'', na'') := nextVarRename r2 ssa' na'
    let movOut := WordLangProgHOL.move 1 [(r2', 0), (r1', 6)]
    (.seq movIn (.seq (.inst (.arith (.longMul 6 0 0 4))) movOut), ssa'', na'')
  | .arith (.longDiv r1 r2 r3 r4 r5), ssa, na =>
    let r3' := optionLookup ssa r3
    let r4' := optionLookup ssa r4
    let r5' := optionLookup ssa r5
    let movIn := WordLangProgHOL.move 1 [(6, r3'), (0, r4')]
    let (r2', ssa', na') := nextVarRename r2 ssa na
    let (r1', ssa'', na'') := nextVarRename r1 ssa' na'
    let movOut := WordLangProgHOL.move 1 [(r2', 6), (r1', 0)]
    (.seq movIn (.seq (.inst (.arith (.longDiv 0 6 6 0 r5'))) movOut), ssa'', na'')
  | .mem .load r (.addr a w), ssa, na =>
    let a' := optionLookup ssa a
    let (r', ssa', na') := nextVarRename r ssa na
    (.inst (.mem .load r' (.addr a' w)), ssa', na')
  | .mem .store r (.addr a w), ssa, na =>
    let a' := optionLookup ssa a
    let r' := optionLookup ssa r
    (.inst (.mem .store r' (.addr a' w)), ssa, na)
  | .mem .load32 r (.addr a w), ssa, na =>
    let a' := optionLookup ssa a
    let (r', ssa', na') := nextVarRename r ssa na
    (.inst (.mem .load32 r' (.addr a' w)), ssa', na')
  | .mem .store32 r (.addr a w), ssa, na =>
    let a' := optionLookup ssa a
    let r' := optionLookup ssa r
    (.inst (.mem .store32 r' (.addr a' w)), ssa, na)
  | .mem .load8 r (.addr a w), ssa, na =>
    let a' := optionLookup ssa a
    let (r', ssa', na') := nextVarRename r ssa na
    (.inst (.mem .load8 r' (.addr a' w)), ssa', na')
  | .mem .store8 r (.addr a w), ssa, na =>
    let a' := optionLookup ssa a
    let r' := optionLookup ssa r
    (.inst (.mem .store8 r' (.addr a' w)), ssa, na)
  | x, ssa, na => (.inst x, ssa, na)

/-- Literal `ssa_cc_trans_exp` (`word_allocScript.sml:270-283`): rename every
variable through `option_lookup`; constants and store lookups are unchanged. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "ssa_cc_trans_exp_def"
  (words_as_type_indexed_bitvec)]
def ssaCcTransExp {width : Nat} [NeZero width] (t : Spt Nat) :
    WordLangExpHOL (BitVec width) → WordLangExpHOL (BitVec width)
  | .var num => .var (optionLookup t num)
  | .load exp => .load (ssaCcTransExp t exp)
  | .op wop ls => .op wop (ls.attach.map fun ⟨e, _⟩ => ssaCcTransExp t e)
  | .shift sh exp nexp => .shift sh (ssaCcTransExp t exp) (ssaCcTransExp t nexp)
  | expr => expr

/-- The `Op` clause is HOL's `Op wop (MAP (ssa_cc_trans_exp t) ls)`; the
definition's `attach` only supplies the termination evidence. -/
theorem ssaCcTransExp_op {width : Nat} [NeZero width] (t : Spt Nat) (wop : BinOp)
    (ls : List (WordLangExpHOL (BitVec width))) :
    ssaCcTransExp t (.op wop ls) = .op wop (ls.map (ssaCcTransExp t)) := by
  rw [ssaCcTransExp]
  congr 1
  exact List.map_attach_eq_pmap.trans (by simp)

end Flapjack.Compiler.Backend.WordAlloc
