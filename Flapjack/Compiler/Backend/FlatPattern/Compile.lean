import Flapjack.Compiler.Backend.FlatPattern.Patterns

/-! Bounded replay of the flat pattern pass over expressions. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString

mutual
/-- Pattern-compile one expression, reporting exhaustion from the branch
compiler. The original total `compile_exp` remains unported until the
underlying bounded procedures have sufficient-bound proofs. -/
def compileExpFuel (fuel : Nat) (cfg : Config) : FlatLang.Exp → Option (Nat × Bool × FlatLang.Exp)
  | .varLocal t vid => some (decNameToNum vid, false, .varLocal t vid)
  | .raise t x => do
      let (i, sg, y) ← compileExpFuel fuel cfg x
      pure (i, sg, .raise t y)
  | .handle t x ps => do
      let (i, sgx, y) ← compileExpFuel fuel cfg x
      let (j, sgp, ps2) ← compileMatchFuel fuel cfg ps
      let k := max i j + 2
      let name := encNumToName k
      let v := FlatLang.Exp.varLocal t name
      let body ← compilePatsFuel fuel cfg sgp t k v (.raise t v) ps2
      pure (k, sgx || sgp, .handle t y [(.pvar name, body)])
  | .con t tag xs => do
      let (i, sg, ys) ← compileExpsFuel fuel cfg xs
      pure (i, sg, .con t tag ys)
  | .fn t v x => do
      let (i, sg, y) ← compileExpFuel fuel cfg x
      pure (i, sg, .fn t v y)
  | .app t op xs => do
      let (i, sg, ys) ← compileExpsFuel fuel cfg xs
      pure (i, sg || opSetsGlobals op, .app t op ys)
  | .mat t x ps => do
      let (i, sgx, y) ← compileExpFuel fuel cfg x
      let (j, sgp, ps2) ← compileMatchFuel fuel cfg ps
      let k := max i j + 2
      let name := encNumToName k
      let v := FlatLang.Exp.varLocal t name
      let failure := FlatLang.Exp.raise t (.con t (some (0, none)) [])
      let body ← compilePatsFuel fuel cfg sgp t k v failure ps2
      pure (k, sgx || sgp, .let_ t (some name) y body)
  | .let_ t vo x1 x2 => do
      let (i, sg1, y1) ← compileExpFuel fuel cfg x1
      let (j, sg2, y2) ← compileExpFuel fuel cfg x2
      let k := vo.elim 0 decNameToNum
      pure (max i (max j k), sg1 || sg2, .let_ t vo y1 y2)
  | .letrec t fs x => do
      let (j, sgfs, fs2) ← compileFunsFuel fuel cfg fs
      let (i, sgx, y) ← compileExpFuel fuel cfg x
      pure (max i j, sgfs || sgx, .letrec t fs2 y)
  | .if_ t x1 x2 x3 => do
      let (i, sg1, y1) ← compileExpFuel fuel cfg x1
      let (j, sg2, y2) ← compileExpFuel fuel cfg x2
      let (k, sg3, y3) ← compileExpFuel fuel cfg x3
      pure (max i (max j k), sg1 || sg2 || sg3, FlatLang.smartIf t y1 y2 y3)
  | e => some (0, false, e)

/-- Compile an expression list, preserving order and combining metadata. -/
def compileExpsFuel (fuel : Nat) (cfg : Config) : List FlatLang.Exp →
    Option (Nat × Bool × List FlatLang.Exp)
  | [] => some (0, false, [])
  | x :: xs => do
      let (i, sgx, y) ← compileExpFuel fuel cfg x
      let (j, sgy, ys) ← compileExpsFuel fuel cfg xs
      pure (max i j, sgx || sgy, y :: ys)

/-- Compile pattern branches, including generated names bound by each pattern. -/
def compileMatchFuel (fuel : Nat) (cfg : Config) : List (FlatLang.Pat × FlatLang.Exp) →
    Option (Nat × Bool × List (FlatLang.Pat × FlatLang.Exp))
  | [] => some (0, false, [])
  | (p, x) :: ps => do
      let (i, sgx, y) ← compileExpFuel fuel cfg x
      let j := maxDecName (FlatLang.patBindings p)
      let (k, sgp, ps2) ← compileMatchFuel fuel cfg ps
      pure (max i (max j k), sgx || sgp, (p, y) :: ps2)

/-- Compile recursive function bodies and collect their maximum and effect flag. -/
def compileFunsFuel (fuel : Nat) (cfg : Config) : List (MlString × MlString × FlatLang.Exp) →
    Option (Nat × Bool × List (MlString × MlString × FlatLang.Exp))
  | [] => some (0, false, [])
  | (f, v, e) :: fs => do
      let (i, sg, e') ← compileExpFuel fuel cfg e
      let (j, sgfs, fs') ← compileFunsFuel fuel cfg fs
      pure (max i j, sg || sgfs, (f, v, e') :: fs')
end

/-- Bounded counterpart of the source `compile_dec` projection. -/
def compileDecFuel (fuel : Nat) (cfg : Config) (e : FlatLang.Exp) : Option FlatLang.Exp :=
  (compileExpFuel fuel cfg e).map (fun (_, _, exp) => exp)

end Flapjack.Compiler.Backend.FlatPattern
