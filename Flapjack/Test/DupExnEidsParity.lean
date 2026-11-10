module

public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobalsByteRanged
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.Pancake.PanStructs.CompileDeclsExact
public import Flapjack.Pancake.PanToCrep.Compile
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.RiscV.Lab
public import Flapjack.Display

@[expose] public section

namespace Flapjack.Test.DupExnEidsParity

open Flapjack

/-! Direct executable-boundary parity for repeated exception declarations.

The oracle is `scripts/hol-probes/dup_exn_eids_probe.out`, regenerated from
`pan_to_crep$get_eids_from_decls` and `pan_to_crep$compile_to_crep`
(`cakeml/pancake/pan_to_crepScript.sml:356-391`) by
`scripts/hol-probes/dup_exn_eids_probeScript.sml`.

`get_eids_from_decls` numbers every exception declaration in source order and
folds the pairs with `alist_to_fmap`, whose evaluation returns the *first*
binding for a repeated key.  (This differs from `make_vmap`, which uses
`FEMPTY |++` and keeps the later binding.)  A repeated exception name therefore
resolves to the ID of its first declaration.  Flapjack's list-backed
`InfoMap`/`lookupInfo` is also first-binding, so no executable divergence is
present; these checks pin that agreement. -/

/-- Source-shaped exception declarations with a repeated name. -/
def dupExnDecls : List (Decl Nat) :=
  [.exnDecl "E" .one, .exnDecl "E" .one]

/-- A distinct name followed by a repeated one. -/
def mixedExnDecls : List (Decl Nat) :=
  [.exnDecl "A" .one, .exnDecl "E" .one, .exnDecl "E" .one]

/-! Oracle line `mixed_eids_lookup_e=SOME 1w`: the first `E` declaration is at
index 1, so the repeated name keeps ID 1. -/
/-- Minimal program raising the duplicated exception. -/
def dupProbeProgram : Prog Nat := .raise "E" (.const 7)

end Flapjack.Test.DupExnEidsParity
