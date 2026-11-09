module

public import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
public import Flapjack.Pancake.LoopToWord

@[expose] public section

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack assembly partition, not a HOL declaration: native SSA data leaves
without recursive subprograms. Loop-control leaves are covered separately. -/
def ssaDataLeaf {α : Type} : WordLangProgHOL α → Prop
  | .mustTerminate _ | .call _ _ _ _ | .seq _ _ | .ite _ _ _ _ _
  | .loop _ _ _ | .break _ | .continue _ => False
  | _ => True

end Flapjack.Compiler.Backend.WordAlloc
