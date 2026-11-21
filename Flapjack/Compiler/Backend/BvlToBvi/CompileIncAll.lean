module

public import Flapjack.Compiler.Backend.BvlToBvi.Config
public import Flapjack.Compiler.Backend.BvlToBvi.SourceProgram
public import Flapjack.Compiler.Backend.BvlInline.SourceCompile
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteCorrespondence
public import Flapjack.Compiler.Backend.BviTmc.Proofs.RewriteCorrespondence
public import Flapjack.Compiler.Backend.BviInline.Source

@[expose] public section

/-! bvl_to_bviScript.sml: `bvl_to_bvi_compile_inc_all_def`, the incremental
BVL-to-BVI pipeline used by the backend's incremental compiler. -/
namespace Flapjack.Compiler.Backend.BvlToBvi

/-- Exact HOL `bvl_to_bvi_compile_inc_all_def` (`bvl_to_bviScript.sml:586-600`):
run BVL inlining, BVL-to-BVI, tail-recursion, tail-modulo-cons and BVI
inlining incrementally, threading the inline caches and the three fresh-name
counters through the configuration. The passes are the reviewed source-shaped
definitions. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "bvl_to_bvi_compile_inc_all_def"]
def bvlToBviCompileIncAll (c : Config) (p : List (Nat × Nat × Bvl.Exp)) :
    Config × List (Nat × Nat × Bvi.Exp) :=
  let (inl, p) := BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut c.inlines p
  let c := { c with inlines := inl }
  let (nn1, p) := compileIncSource c.nextName1 p
  let c := { c with nextName1 := nn1 }
  let (nn2, p) := BviTailrec.compileProgSource c.doTailrec c.nextName2 p
  let c := { c with nextName2 := nn2 }
  let (nn3, p) := BviTmc.compileProgSource c.doTmc c.nextName3 p
  let c := { c with nextName3 := nn3 }
  let (bviInlines, p) := BviInline.compileIncSource c.bviInlines p
  let c := { c with bviInlines := bviInlines }
  (c, p)

end Flapjack.Compiler.Backend.BvlToBvi
