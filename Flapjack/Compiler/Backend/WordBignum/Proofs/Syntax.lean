module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.WordArith

@[expose] public section

/-! The bignum generator's syntax well-formedness predicates, ported from
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. HOL states these as
`bool`-valued definitions; Lean states the same clauses as propositions, with
`EVERY` read as membership and `ALL_DISTINCT` as `List.Nodup`. -/
namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

/-- Every register mentioned by a word-language expression is below the
generator's register bound, and expressions have the source's shapes. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "exp_ok_def"
  (words_as_type_indexed_bitvec)]
def expOk {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → Prop
  | .const _ => True
  | .var i => i < 25
  | .op _ [x, y] => expOk x ∧ expOk y
  | .shift _ e _ => expOk e
  | _ => False

/-- Every register named by a mini-program is below the generator's register
bound. `LoopBody` is rejected at this level because the loop body is checked by
the enclosing `Loop`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "syntax_ok_aux_def"
  (words_as_type_indexed_bitvec)]
def syntaxOkAux {width : Nat} [NeZero width] : Mini (BitVec width) → Prop
  | .loop _ _ body => syntaxOkAux body
  | .loopBody _ => False
  | .seq p1 p2 => syntaxOkAux p1 ∧ syntaxOkAux p2
  | .assign t1 e => t1 < 25 ∧ expOk e
  | .load t1 t2 _ => t1 < 25 ∧ t2 < 25
  | .store t1 t2 => t1 < 25 ∧ t2 < 25
  | .ite _ t2 t3 p1 p2 =>
      t2 < 25 ∧ (∀ r, t3 = .reg r → r < 25) ∧ syntaxOkAux p1 ∧ syntaxOkAux p2
  | .add n1 n2 n3 n4 n5 =>
      n1 < 25 ∧ n2 < 25 ∧ n3 < 25 ∧ (∀ r, n4 = .reg r → r < 25) ∧
        (∀ r, n5 = .reg r → r < 25)
  | .sub n1 n2 n3 n4 n5 =>
      n1 < 25 ∧ n2 < 25 ∧ n3 < 25 ∧ (∀ r, n4 = .reg r → r < 25) ∧
        (∀ r, n5 = .reg r → r < 25)
  | .mul n1 n2 n3 n4 => n1 < 25 ∧ n2 < 25 ∧ n3 < 25 ∧ n4 < 25
  | .div n1 n2 n3 n4 n5 => n1 < 25 ∧ n2 < 25 ∧ n3 < 25 ∧ n4 < 25 ∧ n5 < 25
  | .recurse saveRegs _ => (∀ n ∈ saveRegs, n < 25) ∧ saveRegs.Nodup
  | _ => True

/-- A whole mini-program is well formed: a `LoopBody` is checked through the
auxiliary predicate, every other program shape through the same predicate. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "syntax_ok_def"
  (words_as_type_indexed_bitvec)]
def syntaxOk {width : Nat} [NeZero width] : Mini (BitVec width) → Prop
  | .loopBody body => syntaxOkAux body
  | p => syntaxOkAux p

end Flapjack.Compiler.Backend.WordBignum
