import Flapjack.Pancake.WordLang

namespace Flapjack.Compiler.Backend.WordSimp

/-- HOL's left-Skip elimination over the exact WordLang carrier.
Pattern matching implements the source's `p1 = Skip` test without comparing
irrelevant function-backed payloads of other constructors. Production still uses
the distinct broad `WordProg` carrier; routing is tracked on .15.1.6. -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "SmartSeq_def"
  (words_as_type_indexed_bitvec)]
def smartSeqHOL {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match first with
  | .skip => second
  | _ => .seq first second

end Flapjack.Compiler.Backend.WordSimp
