import Flapjack.Pancake.WordLang

/-! Expression translation used by the word-level bignum generator. The
production compiler still uses the pinned 64-bit generated stubs; the rest of
the generic generator and its integration remain open. -/
namespace Flapjack.Compiler.Backend.WordBignum

/-- Translate source mini-program expressions into word-language expressions.
Operations with an arity other than two, loads, and store lookups use the
source's zero-constant fallback. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "compile_exp_def"
  (words_as_type_indexed_bitvec)]
def compileExp {width : Nat} [NeZero width] :
    WordLangExpHOL (BitVec width) → WordLangExpHOL (BitVec width)
  | .op op [x, y] => .op op [compileExp x, compileExp y]
  | .var n => .lookup (.temp (BitVec.ofNat 5 n))
  | .const w => .const w
  | .shift sh x y => .shift sh (compileExp x) (compileExp y)
  | _ => .const 0
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega

end Flapjack.Compiler.Backend.WordBignum
