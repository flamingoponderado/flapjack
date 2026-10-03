import Flapjack.Compiler.Backend.SourceToFlat.Config
import Flapjack.Compiler.Backend.ClosToBvl.Config
import Flapjack.Compiler.Backend.BvlToBvi.Config
import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.WordToWord.Config
import Flapjack.Compiler.Backend.WordToStack.NativeConfig
import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Backend.PresLang.Config
import Flapjack.Misc.LookupAny

namespace Flapjack.Compiler.Backend.Backend
open Flapjack Flapjack.Basis.Pure.MlString

/-- Complete original backend configuration. Every retained frontend/backend
field uses its reviewed concrete carrier; symbols and exported names are native
byte-backed MlStrings and all source lists and sptrees retain their constructors.
This datatype carries no type-indexed word or arbitrary placeholder field. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "config"]
structure Config where
  sourceConf : SourceToFlat.Config
  closConf : ClosToBvl.Config
  bvlConf : BvlToBvi.Config
  dataConf : DataToWord.Config
  wordToWordConf : WordToWord.Config
  wordConf : WordToStack.Native.Config
  stackConf : StackToLab.Config
  labConf : LabToTarget.Config
  symbols : List (MlString × Nat × Nat)
  tapConf : PresLang.TapConfig
  exported : List MlString

/-- The complete source attachment operation. HOL independently quantifies the
byte and bitmap payload types: neither payload is inspected. Only labConf and
symbols are updated, preserving every other configuration field. Missing names
use the original literal NOTFOUND through the reviewed lookup_any operation. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "attach_bitmaps_def"]
def attachBitmaps {Bytes Bitmaps : Type} (names : Spt MlString)
    (config : Config) (bitmaps : Bitmaps) :
    Option (Bytes × LabToTarget.Config) → Option (Bytes × Bitmaps × Config)
  | none => none
  | some (bytes, updatedLab) =>
      some (bytes, bitmaps, { config with
        labConf := updatedLab
        symbols := updatedLab.secPosLen.map fun (name, position, length) =>
          (lookupAny name names (ofString "NOTFOUND"), position, length) })

end Flapjack.Compiler.Backend.Backend
