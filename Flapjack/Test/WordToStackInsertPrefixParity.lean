import Flapjack.Compiler.Backend.WordToStack.Proofs.InsertBitmapPrefix

namespace Flapjack.Test.WordToStackInsertPrefixParity
open Flapjack Flapjack.Compiler.Backend.WordToStack

/-- Same-input regression applications to the actual insertion result.
This test helper has no separate HOL original. -/
private theorem actualPrefix {α : Type} (words : List α) (bs : AppList α × Nat) :
    (appListAppend bs.1).IsPrefix (appListAppend (insertBitmap words bs).1.1) :=
  insertBitmapIsPrefix words bs _ _ rfl

example : (appListAppend (AppList.nil : AppList Nat)).IsPrefix
    (appListAppend (insertBitmap [] (.nil,0)).1.1) := actualPrefix [] (.nil,0)
example : (appListAppend (AppList.list [4,7])).IsPrefix
    (appListAppend (insertBitmap [8,9] (.list [4,7],2)).1.1) := actualPrefix [8,9] (.list [4,7],2)
example : (appListAppend (AppList.append (.list [4]) (.append .nil (.list [7,8])))).IsPrefix
    (appListAppend (insertBitmap [9] (.append (.list [4]) (.append .nil (.list [7,8])),3)).1.1) :=
  actualPrefix [9] (.append (.list [4]) (.append .nil (.list [7,8])),3)
example : (appListAppend (AppList.list [4,7])).IsPrefix
    (appListAppend (insertBitmap [8,9] (.list [4,7],0)).1.1) := actualPrefix [8,9] (.list [4,7],0)
example : (appListAppend (AppList.list [4,7])).IsPrefix
    (appListAppend (insertBitmap [] (.list [4,7],99)).1.1) := actualPrefix [] (.list [4,7],99)
example : (appListAppend (AppList.list [true,false])).IsPrefix
    (appListAppend (insertBitmap [false,true,true] (.list [true,false],0)).1.1) := actualPrefix [false,true,true] (.list [true,false],0)
example : (appListAppend (AppList.list [none,some 1])).IsPrefix
    (appListAppend (insertBitmap [some 2,none] (.list [none,some 1],1)).1.1) := actualPrefix [some 2,none] (.list [none,some 1],1)

end Flapjack.Test.WordToStackInsertPrefixParity
