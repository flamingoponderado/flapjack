import Flapjack.Pancake.WordLang

namespace Flapjack.WordAlloc

/-- Exact HOL `get_reads_exp_def` (`word_allocScript.sml`), clause by clause
over the exact polymorphic `wordLang$exp` carrier `WordLangExpHOL α`. `Var`
yields its singleton read list, `Load` recurses into its address, `Op` flattens
the read lists of its argument expressions in order (`FLAT (MAP ...)`), and
`Shift` concatenates the left operand's reads before the right operand's. HOL's
final catch-all covers `Const` and `Lookup`, both returning the empty list.
Duplicate reads and their order are preserved; no set normalization is
performed. This proof-side port does not replace the executed caller yet. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_reads_exp_def"]
def getReadsExpHOL {α : Type} : WordLangExpHOL α → List Nat
  | .var name => [name]
  | .load address => getReadsExpHOL address
  | .op _ args => (args.map getReadsExpHOL).flatten
  | .shift _ left right => getReadsExpHOL left ++ getReadsExpHOL right
  | _ => []
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

end Flapjack.WordAlloc
