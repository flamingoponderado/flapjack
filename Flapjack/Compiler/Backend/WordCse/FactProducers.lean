import Flapjack.Compiler.Backend.WordCse.RegisterData
import Flapjack.Compiler.Backend.WordCse.InstructionKeys
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Misc.BalancedMap.Insert

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack

/-! Literal fact producers over the original balanced-tree, sparse-tree and
full native program carriers. These native definitions do not replace the
executed Std.TreeMap transitions; their invariant-dependent correspondence
and the complete CSE simulation remain separate open work. -/

@[hol "cakeml/compiler/backend/word_cseScript.sml" "add_to_data_aux_def"
  (words_as_type_indexed_bitvec)]
def addToDataAux {width : Nat} [NeZero width] (data : Knowledge)
    (destination : Nat) (key : List Nat) (original : WordLangProgHOL (BitVec width)) :
    Knowledge × WordLangProgHOL (BitVec width) :=
  match Misc.BalancedMap.lookup listCmp key data.instrsMem with
  | some previous =>
      let current := (sptLookup previous data.toLatest).getD previous
      if destination % 2 = 0 then (data, .move 0 [(destination, current)])
      else
        ({ data with
            toCanonical := sptInsert destination previous data.toCanonical,
            toLatest := sptInsert previous destination data.toLatest }, .move 0 [(destination, current)])
  | none =>
      if destination % 2 = 0 then (data, original)
      else
        ({ data with
            instrsMem := Misc.BalancedMap.insert listCmp key destination data.instrsMem,
            toCanonical := sptInsert destination destination data.toCanonical,
            toLatest := sptInsert destination destination data.toLatest }, original)

@[hol "cakeml/compiler/backend/word_cseScript.sml" "add_to_load_aux_def"
  (words_as_type_indexed_bitvec)]
def addToLoadAux {width : Nat} [NeZero width] (data : Knowledge)
    (destination : Nat) (key : List Nat) (original : WordLangProgHOL (BitVec width)) :
    Knowledge × WordLangProgHOL (BitVec width) :=
  match Misc.BalancedMap.lookup listCmp key data.loadsMem with
  | some previous =>
      let current := (sptLookup previous data.toLatest).getD previous
      if destination % 2 = 0 then (data, .move 0 [(destination, current)])
      else
        ({ data with
            toCanonical := sptInsert destination previous data.toCanonical,
            toLatest := sptInsert previous destination data.toLatest }, .move 0 [(destination, current)])
  | none =>
      if destination % 2 = 0 then (data, original)
      else
        ({ data with
            loadsMem := Misc.BalancedMap.insert listCmp key destination data.loadsMem,
            toCanonical := sptInsert destination destination data.toCanonical,
            toLatest := sptInsert destination destination data.toLatest }, original)

/-- Original constant rematerialization for arbitrary destination parity:
source callers guard odd registers, but this definition has no such premise.
Both branches emit the original Const rather than extending a holder lifetime. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "add_to_data_const_def"
  (words_as_type_indexed_bitvec)]
def addToDataConst {width : Nat} [NeZero width] (data : Knowledge)
    (destination : Nat) (word : BitVec width) : Knowledge × WordLangProgHOL (BitVec width) :=
  let key := instToNumList (.const destination word)
  match Misc.BalancedMap.lookup listCmp key data.instrsMem with
  | some previous =>
      ({ data with
          toCanonical := sptInsert destination previous data.toCanonical,
          toLatest := sptInsert previous destination data.toLatest }, .inst (.const destination word))
  | none =>
      ({ data with
          instrsMem := Misc.BalancedMap.insert listCmp key destination data.instrsMem,
          toCanonical := sptInsert destination destination data.toCanonical,
          toLatest := sptInsert destination destination data.toLatest }, .inst (.const destination word))

end Flapjack.Compiler.Backend.WordCse
