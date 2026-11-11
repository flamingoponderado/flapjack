module

public import Flapjack.Compiler.Backend.WordBignum.Generate
public import Flapjack.Test.BignumWordOracle

import all Flapjack.Compiler.Backend.WordBignum.Generate
import all Flapjack.Test.BignumWordOracle
public meta import Flapjack.Compiler.Backend.WordBignum.GeneratedMini
public meta import Flapjack.Arm8.NativeSource
public meta import Flapjack.Compiler.Backend.BviLet.SourceList
public meta import Flapjack.Compiler.Backend.BvlConst.SourceCompile
public meta import Flapjack.Compiler.Backend.BvlHandle.SourceCompile
public meta import Flapjack.Compiler.Backend.ClosAnnotate.Shift
public meta import Flapjack.Compiler.Backend.ClosCall.Compile
public meta import Flapjack.Compiler.Backend.ClosFvs.Source
public meta import Flapjack.Compiler.Backend.ClosKnown.Compile
public meta import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
public meta import Flapjack.Compiler.Backend.DataLive
public meta import Flapjack.Compiler.Backend.DataSpace.Compile
public meta import Flapjack.Compiler.Backend.FlatToClos.Compile
public meta import Flapjack.Compiler.Backend.LabToTarget.Compile
public meta import Flapjack.Compiler.Backend.SourceToSource
public meta import Flapjack.Compiler.Backend.StackAlloc.Compile
public meta import Flapjack.Compiler.Backend.StackNames
public meta import Flapjack.Compiler.Backend.StackRawCall
public meta import Flapjack.Compiler.Backend.StackToLab.Compile
public meta import Flapjack.Compiler.Backend.WordBignum.Compile

@[expose] public section

/-! Compare every generated 64-bit stub with the pinned HOL compiler output. -/
namespace Flapjack.Test.WordBignumGenerateParity
open Flapjack.Compiler.Backend.WordBignum

def matchesOriginal : Bool :=
  match generateStubs 64 39 with
  | none => false
  | some entries => BignumWordOracle.matchesCaptured
      (entries.map fun (location, arity, code) => (location, arity, code, 0))

#guard matchesOriginal

end Flapjack.Test.WordBignumGenerateParity
