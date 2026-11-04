import Flapjack.Compiler.Backend.WordCse.ProductionGet

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

@[hol "cakeml/compiler/backend/word_cseScript.sml" "dest_Var_def"
  (words_as_type_indexed_bitvec)]
def destVar {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → Option Nat
  | .var register => some register
  | _ => none

/-- Full original Set clause extraction (source557-573). This is untagged
Flapjack assembly infrastructure: HOL has no standalone Set-clause declaration.
The tagged recursive `wordCse` (`Transform.lean`) uses it as its `Set` clause;
semantic correctness (`word_cseProof` `comp_correct`) is not part of this module. -/
def setClause {width : Nat} [NeZero width] (data : Knowledge)
    (store : WordStoreHOL) (expression : WordLangExpHOL (BitVec width)) :
    Knowledge × WordLangProgHOL (BitVec width) :=
  if store = .currHeap then (emptyData, .set store expression)
  else
    let facts := data.getsMem.filter (fun entry => decide (entry.1 ≠ store))
    match destVar expression with
    | none => ({ data with getsMem := facts }, .set store expression)
    | some source =>
        if source % 2 = 0 then ({ data with getsMem := facts }, .set store expression)
        else
          ({ data with
              getsMem := (store, canonicalRegs data source) :: facts,
              toCanonical := sptInsert source
                ((sptLookup source data.toCanonical).getD source) data.toCanonical }, .set store expression)

end Flapjack.Compiler.Backend.WordCse
