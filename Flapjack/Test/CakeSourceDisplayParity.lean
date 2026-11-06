import Flapjack.Compiler.Backend.PresLang.Source
import Flapjack.CakeParser.Frontend

/-! The expected text is the `original source code` section emitted by the
pinned CakeML compiler with `--explore --exclude_prelude=true`. -/
namespace Flapjack.Test.CakeSourceDisplayParity

open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.PresLang.Source

private def source : String :=
  "datatype t = A | B int; fun f x = case x of A => ~1 | B n => n; val x = f (B 7);"

private def expected : String :=
  "(Dtype (() t ((A ()) (B ((Attup () (Short int)))))))\n\n" ++
  "(Dletrec\n   (f x\n      (Lannot\n         (Mat (Lannot (Var (Short x)))\n" ++
  "            (((Pcon (some (Short A)) ()) (Lannot (Lit (IntLit ~1))))\n" ++
  "               ((Pcon (some (Short B)) ((Pvar n))) (Lannot (Var (Short n)))))))))\n\n" ++
  "(Dlet (Pvar x)\n   (Lannot\n      (App Opapp (Lannot (Var (Short f)))\n" ++
  "         (Lannot (Con (some (Short B)) ((Lit (IntLit 7))))))))\n\n"

private def sourceStage : Option String :=
  match Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000 (ofString source).explode with
  | .success ds => some (String.join (declarations ds))
  | _ => none

#guard sourceStage == some expected

/-! The original prints the literal's byte directly, not its UTF-8 encoding. -/
private def byteStage : Option (List HolChar) :=
  match Flapjack.CakeParser.Frontend.parseSourceFuel 20000 20000
      (ofString "val x = \"\\255\";").explode with
  | .success ds => some (declarationBytes ds)
  | _ => none

private def expectedByteStage : List HolChar :=
  (ofString "(Dlet (Pvar x) (Lannot (Lit (StrLit ").explode ++
  [BitVec.ofNat 8 255] ++ (ofString "))))\n\n").explode

#guard byteStage == some expectedByteStage

end Flapjack.Test.CakeSourceDisplayParity
