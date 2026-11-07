import Flapjack.Compiler.Backend.WordCse.FactProducers
import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
import Flapjack.Misc.BalancedMap.InsertCorrect
import Flapjack.Misc.BalancedMap.LookupSemantics
import Flapjack.Compiler.Backend.WordCse.ProductionRegisterData
import Flapjack.Pancake.LoopToWord

namespace Flapjack.Test.WordCseProductionFactAuxParity
open Flapjack RiscV Compiler.Backend.WordCse
private abbrev Observation := List (Option Nat) × List (Option Nat) × List (Option Nat) ×
    List (Option Nat) × List (Option Nat) × (Nat × Nat × List (Nat × Nat))
private def nativeData (mode : Nat) : Knowledge :=
  let table := Misc.BalancedMap.insert listCmp (if mode = 0 then [99] else [42])
    (if mode = 0 then 9 else 3) Misc.BalancedMap.empty
  { toCanonical := sptFromAList [(3,3),(9,9)]
    toLatest := sptFromAList (if mode = 2 then [(3,5),(9,9)] else [(9,9)])
    getsMem := [(.currHeap,9)]
    instrsMem := table, loadsMem := table }
private def nativeObservation (destination : Nat)
    (output : Knowledge × WordLangProgHOL (BitVec 64)) : Observation :=
  let data := output.1
  ([destination,3,9].map (fun k => sptLookup k data.toCanonical),
   [3,destination,9].map (fun k => sptLookup k data.toLatest),
   [WordStore.currHeap,WordStore.nextFree].map (fun s => data.getsMem.lookup s),
   [[42],[99]].map (fun k => Misc.BalancedMap.lookup listCmp k data.instrsMem),
   [[42],[99]].map (fun k => Misc.BalancedMap.lookup listCmp k data.loadsMem),
   match output.2 with
   | .move priority moves => (0,priority,moves)
   | .tick => (1,0,[])
   | _ => (2,0,[]))
private def nativeRun (load : Bool) (mode destination : Nat) :=
  if load then addToLoadAux (nativeData mode) destination [42] (.tick : WordLangProgHOL (BitVec 64))
  else addToDataAux (nativeData mode) destination [42] (.tick : WordLangProgHOL (BitVec 64))
-- Each expected tuple is a complete original HOL aux_data/aux_load EVAL row.
private def fixtures : List (Bool × Nat × Nat × Observation) := [
  (false,0,2,([none,some 3,some 9],[none,none,some 9],[some 9,none],[none,some 9],[none,some 9],(1,0,[]))),
  (false,0,7,([some 7,some 3,some 9],[none,some 7,some 9],[some 9,none],[some 7,some 9],[none,some 9],(1,0,[]))),
  (false,1,2,([none,some 3,some 9],[none,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(2,3)]))),
  (false,1,7,([some 3,some 3,some 9],[some 7,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(7,3)]))),
  (false,2,2,([none,some 3,some 9],[some 5,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(2,5)]))),
  (false,2,7,([some 3,some 3,some 9],[some 7,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(7,5)]))),
  (true,0,2,([none,some 3,some 9],[none,none,some 9],[some 9,none],[none,some 9],[none,some 9],(1,0,[]))),
  (true,0,7,([some 7,some 3,some 9],[none,some 7,some 9],[some 9,none],[none,some 9],[some 7,some 9],(1,0,[]))),
  (true,1,2,([none,some 3,some 9],[none,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(2,3)]))),
  (true,1,7,([some 3,some 3,some 9],[some 7,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(7,3)]))),
  (true,2,2,([none,some 3,some 9],[some 5,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(2,5)]))),
  (true,2,7,([some 3,some 3,some 9],[some 7,none,some 9],[some 9,none],[some 3,none],[some 3,none],(0,0,[(7,5)])))]

example : fixtures.all (fun (load,mode,destination,expected) =>
    nativeObservation destination (nativeRun load mode destination) == expected) = true := by decide +kernel

end Flapjack.Test.WordCseProductionFactAuxParity
