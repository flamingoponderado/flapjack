import Flapjack.Compiler.Inference.Infer.Core
import Flapjack.CakeParser.Frontend

/-! HOL declaration inference, including state and environment ordering. -/
namespace Flapjack.Test.CakeInferDeclParity
open Flapjack Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Misc.Location
open Flapjack.Compiler.Inference Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Infer.Core
open Flapjack.Basis.Pure.MlString

private def initial : State := ⟨0, .ln, 15⟩
private def idDec : Dec := .dlet unknownLoc (.pvar (ofString "id"))
  (.fn (ofString "x") (.var (.short (ofString "x"))))

#guard match inferDeclsFuel 100 100 emptyEnv [idDec] initial with
  | .ok (env, s) =>
    nsLookup env.infV (.short (ofString "id")) == some (1, .app [.varDb 0, .varDb 0] 4) &&
    s.nextUvar == 2 && s.nextId == 15 &&
    sptLookup 1 s.subst == some (.app [.uvar 0, .uvar 0] 4)
  | _ => false

private def datatypeDec : Dec := .dtype unknownLoc
  [([], ofString "t", [(ofString "A", []), (ofString "B", [])])]

#guard match inferDeclsFuel 100 100 emptyEnv [datatypeDec] initial with
  | .ok (env, s) => match env.infC, env.infT with
    | .bind [(b, ([], [], 15)), (a, ([], [], 15))] [],
      .bind [(t, ([], .app [] 15))] [] =>
        a == ofString "A" && b == ofString "B" && t == ofString "t" && s.nextId == 16
    | _, _ => false
  | _ => false

#guard match Flapjack.CakeParser.Frontend.parseSourceFuel 500 500
    (ofString "val id = fn x => x;").explode with
  | .success ds => match inferProgramFuel 100 100 ds with
    | .ok env => nsLookup env.infV (.short (ofString "id")) ==
        some (1, .app [.varDb 0, .varDb 0] 4)
    | _ => false
  | _ => false


#guard match nsLookup initConfig.infT (.short (ofString "int")),
    nsLookup initConfig.infT (.short (ofString "list")),
    nsLookup initConfig.infC (.short (ofString "::")) with
  | some ([], .app [] 5), some ([a], .app [.var b] 6),
    some ([c], [.var d, .app [.var e] 6], 6) =>
      [a, b, c, d, e].all (· == ofString "'a")
  | _, _, _ => false

end Flapjack.Test.CakeInferDeclParity
