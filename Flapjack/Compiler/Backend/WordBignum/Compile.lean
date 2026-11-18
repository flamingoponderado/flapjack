module

public import Flapjack.Compiler.Backend.WordBignum.Helpers
public import Flapjack.Compiler.Backend.WordBignum.Proofs.Equality

@[expose] public section

/-! Mini-language compilation. The fuelled helpers are Flapjack infrastructure;
the total entry point has the source carrier and source-shaped equations. The
shallow-to-deep generator and cross-language correctness remain open. -/
namespace Flapjack.Compiler.Backend.WordBignum

abbrev CodeEntry (width : Nat) := Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)
abbrev CodeAcc (width : Nat) := Nat × List (CodeEntry width)

/-- Executable first-match cache lookup with a decidable key equality. -/
def hasCompiled {α β : Type} [DecidableEq α] (code : α)
    (cs : Nat × List (α × Nat × β)) : Sum Nat Nat :=
  letI : BEq α := ⟨fun x y => decide (x = y)⟩
  match cs.2.lookup code with
  | some (index, _) => .inl index
  | none => .inr cs.1

/-- Advance the next code index while retaining the arbitrary accumulator payload. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "code_acc_next_def"]
def codeAccNext {α : Type} (cs : Nat × α) : Nat × α := (cs.1 + 1, cs.2)

/-- Add an arbitrary entry to the installed-code list. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "install_def"]
def install {α β : Type} (entry : α) (cs : β × List α) : β × List α :=
  (cs.1, entry :: cs.2)

/-- A computable structural bound on recursive mini-program compilation. -/
def miniBudget : Mini α → Nat
  | .seq a b | .ite _ _ _ a b => 2 + miniBudget a + miniBudget b
  | .loop _ _ body | .loopBody body => 2 + miniBudget body
  | _ => 2

/-- Compile a mini-program while threading labels, temporary registers, and
the installed-code accumulator. -/
def compileFuel {width : Nat} [NeZero width] : Nat → Nat → Nat → Nat → CodeAcc width →
    Mini (BitVec width) → Option (WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width)
  | 0, _, _, _, _, _ => none
  | fuel + 1, n, l, i, cs, code => do
    match code with
    | .skip => pure (.skip, l, i, cs)
    | .continue => pure (.call none (some n) [0] none, l, i, cs)
    | .recurse save _ =>
      let cuts : WordLangCutsetsHOL := (.ls (), sptListInsert (save.map (· + 2)) .ln)
      pure (loadRegs save (.call (some ([1], cuts, saveRegs save, n, l)) (some n) [] none),
        l + 1, i, cs)
    | .loop _ _ body =>
      match hasCompiled body cs with
      | .inl existing =>
        pure (.call (some ([i], (.ls (), .ln), .skip, n, l)) (some existing) [] none,
          l + 1, i + 1, cs)
      | .inr index =>
        let (newCode, _, _, cs) ← compileFuel fuel index 2 1 (codeAccNext cs) body
        pure (.call (some ([i], (.ls (), .ln), .skip, n, l)) (some index) [] none,
          l + 1, i + 1, install (body, index, newCode) cs)
    | .loopBody body => compileFuel fuel n l i cs body
    | .seq a b =>
      let (a, l, i, cs) ← compileFuel fuel n l i cs a
      let (b, l, i, cs) ← compileFuel fuel n l i cs b
      pure (.seq a b, l, i, cs)
    | .ite op r arg a b =>
      let (a, l, i, cs) ← compileFuel fuel n l i cs a
      let (b, l, i, cs) ← compileFuel fuel n l i cs b
      match arg with
      | .reg r2 => pure (seqTemp i r (seqTemp (i + 1) r2 (.ite op i (.reg (i + 1)) a b)),
          l, i + 2, cs)
      | .imm w => pure (seqTemp i r (.ite op i (.imm w) a b), l, i + 1, cs)
    | .assign j e =>
      pure (.seq (.assign i (compileExp e)) (.set (.temp (BitVec.ofNat 5 j)) (.var i)),
        l, i + 1, cs)
    | .delete _ => pure (.skip, l, i, cs)
    | .swap =>
      pure (.seq (.assign i (.lookup tempIn1))
        (.seq (.set tempIn1 (.lookup tempIn2)) (.set tempIn2 (.var i))), l, i + 1, cs)
    | .store r1 r2 =>
      pure (seqTemp i r1 (seqIndex (i + 1) r2 .out (.store (.var (i + 1)) i)), l, i + 2, cs)
    | .load r1 r2 arr =>
      pure (seqIndex i r2 arr (.seq (.assign (i + 1) (.load (.var i)))
        (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 1)))), l, i + 2, cs)
    | .add r0 r1 r2 r3 r4 =>
      pure (seqTempImm (i + 4) r4 (seqTempImm (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 4))))))), l, i + 5, cs)
    | .sub r0 r1 r2 r3 r4 =>
      pure (seqTempImm (i + 4) r4 (seqTempImmNot (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 4))))))), l, i + 5, cs)
    | .mul r0 r1 r2 r3 =>
      pure (seqTemp (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.longMul i (i + 1) (i + 2) (i + 3))))
          (.seq (.set (.temp (BitVec.ofNat 5 r1)) (.var i))
            (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))))), l, i + 4, cs)
    | .div r0 r1 r2 r3 r4 =>
      pure (seqTemp (i + 4) r4 (seqTemp (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (divCode n l i (i + 1) (i + 2) (i + 3) (i + 4))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var i))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 1))))))), l + 1, i + 5, cs)

/-- Total mini compilation with a structural bound. The default is unreachable:
`compileFuel_succeeds` proves the structural traversal always returns a result.
The source-shaped equations are checked in `Proofs/CompileEquations`. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
def compile {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (code : MiniHOL width) : WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width :=
  (compileFuel (miniBudget code + 1) n l i cs code).getD (.skip, l, i, cs)

end Flapjack.Compiler.Backend.WordBignum
