import Flapjack.Compiler.Backend.WordBignum.Helpers
import Flapjack.Compiler.Backend.WordBignum.Equality

/-! Fuel-bounded mini-language compilation. The fuel parameter and generic
mini carrier differ from HOL's total compiler, so these infrastructure
definitions are not tagged as source ports. The captured mini-program is used
by the production compiler; the shallow-to-deep generator and cross-language
correctness remain open. -/
namespace Flapjack.Compiler.Backend.WordBignum

abbrev CodeEntry (width : Nat) := Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width)
abbrev CodeAcc (width : Nat) := Nat × List (CodeEntry width)

/-- Find the first structurally equal mini-program in the installed code. -/
def lookupCode {width : Nat} (code : Mini (BitVec width)) : List (CodeEntry width) → Option Nat
  | [] => none
  | (body, index, _) :: rest => if miniEq code body then some index else lookupCode code rest

/-- A successful source-style code lookup returns an existing index; otherwise
the accumulator's next index is available for compilation. -/
def hasCompiled {width : Nat} (code : Mini (BitVec width)) (cs : CodeAcc width) : Sum Nat Nat :=
  match lookupCode code cs.2 with
  | some index => .inl index
  | none => .inr cs.1

def codeAccNext {width : Nat} (cs : CodeAcc width) : CodeAcc width := (cs.1 + 1, cs.2)
def install {width : Nat} (entry : CodeEntry width) (cs : CodeAcc width) : CodeAcc width :=
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

/-- Preserve an initial result and retry exhausted structural recursion. -/
def compileBounded {width : Nat} [NeZero width] (fuel n l i : Nat) (cs : CodeAcc width)
    (code : Mini (BitVec width)) :
    Option (WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width) :=
  match compileFuel fuel n l i cs code with
  | some result => some result
  | none => compileFuel (max fuel (miniBudget code + 1)) n l i cs code

/-- Total mini compilation with a structural bound. The default is unreachable:
`compileFuel_succeeds` proves the structural traversal always returns a result. -/
def compile {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (code : MiniHOL width) : WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width :=
  (compileFuel (miniBudget code + 1) n l i cs code).getD (.skip, l, i, cs)

end Flapjack.Compiler.Backend.WordBignum
