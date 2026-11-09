module

public import Flapjack.Compiler.Backend.WordCse.ProductionStoreErase
public import Flapjack.Compiler.Backend.WordCse.ProductionRegisterData
public import Flapjack.Pancake.LoopToWord

@[expose] public section

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack RiscV

/-- Clause extraction for the full original Get equation (source545-556).
Flapjack assembly infrastructure, with no standalone HOL declaration: the
tagged recursive `wordCse` (`Transform.lean`) uses it as its `Get` clause.
All four original branches retain the complete native program and store
carriers. Semantic correctness (`word_cseProof` `comp_correct`) is not part of
this module. -/
def getClause {width : Nat} [NeZero width] (data : Knowledge)
    (destination : Nat) (store : WordStoreHOL) :
    Knowledge × WordLangProgHOL (BitVec width) :=
  let data := invalidateData data destination
  match data.getsMem.lookup store with
  | none =>
      if destination % 2 = 0 then (data, .get destination store)
      else
        ({ data with
            getsMem := (store, destination) :: data.getsMem,
            toCanonical := sptInsert destination destination data.toCanonical,
            toLatest := sptInsert destination destination data.toLatest }, .get destination store)
  | some previous =>
      let source := (sptLookup previous data.toLatest).getD previous
      if destination % 2 = 0 then (data, .move 1 [(destination, source)])
      else
        ({ data with
            toCanonical := sptInsert destination previous data.toCanonical,
            toLatest := sptInsert previous destination data.toLatest }, .move 1 [(destination, source)])

end Flapjack.Compiler.Backend.WordCse
