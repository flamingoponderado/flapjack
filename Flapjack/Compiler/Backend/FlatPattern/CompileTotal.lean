import Flapjack.Compiler.Backend.FlatPattern.Patterns

/-! Total expression traversal for the flat pattern compiler. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString

mutual
/-- Compile all matches in an expression, retaining the source's generated-name
maximum and global-write flag. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_exp_def"]
def compileExp (cfg : Config) : FlatLang.Exp → Nat × Bool × FlatLang.Exp
  | .varLocal t vid => (decNameToNum vid, false, .varLocal t vid)
  | .raise t x =>
      let (i, sg, y) := compileExp cfg x
      (i, sg, .raise t y)
  | .handle t x ps =>
      let (i, sgx, y) := compileExp cfg x
      let (j, sgp, ps2) := compileMatch cfg ps
      let k := max i j + 2
      let name := encNumToName k
      let v := FlatLang.Exp.varLocal t name
      let body := compilePats cfg sgp t k v (.raise t v) ps2
      (k, sgx || sgp, .handle t y [(.pvar name, body)])
  | .con t tag xs =>
      let (i, sg, ys) := compileExps cfg xs
      (i, sg, .con t tag ys)
  | .fn t v x =>
      let (i, sg, y) := compileExp cfg x
      (i, sg, .fn t v y)
  | .app t op xs =>
      let (i, sg, ys) := compileExps cfg xs
      (i, sg || opSetsGlobals op, .app t op ys)
  | .mat t x ps =>
      let (i, sgx, y) := compileExp cfg x
      let (j, sgp, ps2) := compileMatch cfg ps
      let k := max i j + 2
      let name := encNumToName k
      let v := FlatLang.Exp.varLocal t name
      let failure := FlatLang.Exp.raise t (.con t (some (0, none)) [])
      let body := compilePats cfg sgp t k v failure ps2
      (k, sgx || sgp, .let_ t (some name) y body)
  | .let_ t vo x1 x2 =>
      let (i, sg1, y1) := compileExp cfg x1
      let (j, sg2, y2) := compileExp cfg x2
      let k := vo.elim 0 decNameToNum
      (max i (max j k), sg1 || sg2, .let_ t vo y1 y2)
  | .letrec t fs x =>
      let (j, sgfs, fs2) := compileFuns cfg fs
      let (i, sgx, y) := compileExp cfg x
      (max i j, sgfs || sgx, .letrec t fs2 y)
  | .if_ t x1 x2 x3 =>
      let (i, sg1, y1) := compileExp cfg x1
      let (j, sg2, y2) := compileExp cfg x2
      let (k, sg3, y3) := compileExp cfg x3
      (max i (max j k), sg1 || sg2 || sg3, FlatLang.smartIf t y1 y2 y3)
  | e => (0, false, e)

/-- Compile an expression list in order and combine its metadata. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_exp_def"]
def compileExps (cfg : Config) : List FlatLang.Exp → Nat × Bool × List FlatLang.Exp
  | [] => (0, false, [])
  | x :: xs =>
      let (i, sgx, y) := compileExp cfg x
      let (j, sgy, ys) := compileExps cfg xs
      (max i j, sgx || sgy, y :: ys)

/-- Compile pattern branches and account for their bound names. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_exp_def"]
def compileMatch (cfg : Config) : List (FlatLang.Pat × FlatLang.Exp) →
    Nat × Bool × List (FlatLang.Pat × FlatLang.Exp)
  | [] => (0, false, [])
  | (p, x) :: ps =>
      let (i, sgx, y) := compileExp cfg x
      let j := maxDecName (FlatLang.patBindings p)
      let (k, sgp, ps2) := compileMatch cfg ps
      (max i (max j k), sgx || sgp, (p, y) :: ps2)

/-- Compile recursive function bodies and collect their maximum and effect flag.
This helper packages the source's `MAP`, `MAX_LIST` and `EXISTS` operations. -/
def compileFuns (cfg : Config) : List (MlString × MlString × FlatLang.Exp) →
    Nat × Bool × List (MlString × MlString × FlatLang.Exp)
  | [] => (0, false, [])
  | (f, v, e) :: fs =>
      let (i, sg, e') := compileExp cfg e
      let (j, sgfs, fs') := compileFuns cfg fs
      (max i j, sg || sgfs, (f, v, e') :: fs')
end

/-- Compile a single top-level flat declaration. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "compile_dec_def"]
def compileDec (cfg : Config) (e : FlatLang.Exp) : FlatLang.Exp := (compileExp cfg e).2.2

end Flapjack.Compiler.Backend.FlatPattern
