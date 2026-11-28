module

public import Flapjack.Compiler.Backend.Backend
public import Flapjack.AstHOL.Syntax
public import Flapjack.Compiler.Backend.FlatLang
public import Flapjack.Compiler.Backend.ClosLang.Syntax
public import Flapjack.Compiler.Backend.Bvl.Syntax
public import Flapjack.Compiler.Backend.Bvi.Syntax
public import Flapjack.Compiler.Backend.DataLang.Syntax
public import Flapjack.Pancake.WordLang
public import Flapjack.Compiler.Backend.StackLang.Prog
public import Flapjack.Compiler.Backend.LabLang.HOL

@[expose] public section

/-! Backend program-record carriers and helpers from `backendScript.sml`. -/
namespace Flapjack.Compiler.Backend.Backend
open Flapjack

/-- Exact HOL `backend_progs` at a fixed word width: every retained program
uses its reviewed carrier, and the single word dimension is `BitVec width`. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "backend_progs"
  (words_as_type_indexed_bitvec)]
structure BackendProgs (width : Nat) [NeZero width] where
  envId : Nat × Nat
  sourceProg : List AstHOL.Dec
  flatProg : List FlatLang.Exp
  closProg : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)
  bvlProg : List (Nat × Nat × Bvl.Exp)
  bviProg : List (Nat × Nat × Bvi.Exp)
  dataProg : List (Nat × Nat × DataLang.Prog)
  wordProg : List (Nat × Nat × WordLangProgHOL (BitVec width))
  stackProg : List (Nat × StackLang.HolProg width)
  curBm : List (BitVec width)
  labProg : List (LabLang.SecHOL width)
  targetProg : Option (List (BitVec 8) × List (BitVec width))

/-- Original `keep_progs_def`: keep the program list only when the flag is set. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "keep_progs_def"]
def keepProgs {α : Type} (k : Bool) (ps : List α) : List α := if k then ps else []

/-- Original `empty_progs_def`: the all-empty backend program record. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "empty_progs_def"
  (words_as_type_indexed_bitvec)]
def emptyProgs (width : Nat) [NeZero width] : BackendProgs width :=
  { envId := (0, 0)
    sourceProg := []
    flatProg := []
    closProg := ([], [])
    bvlProg := []
    bviProg := []
    dataProg := []
    wordProg := []
    stackProg := []
    curBm := []
    labProg := []
    targetProg := some ([], []) }

/-- Original `set_oracle_def`: replace the word-to-word colour oracle. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "set_oracle_def"]
def setOracle (c : Config) (oracle : List (Option (Spt Nat))) : Config :=
  { c with wordToWordConf := { c.wordToWordConf with colOracle := oracle } }

end Flapjack.Compiler.Backend.Backend
