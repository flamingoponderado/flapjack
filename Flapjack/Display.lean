import Flapjack.Pancake.PanLang
import Flapjack.Pancake.CrepLang
import Flapjack.Pancake.LoopLang
import Flapjack.NumSet

/-!
The small display-language boundary used by Pancake's pass printer.

This is the Lean counterpart of `displayLang$sExp` and the basic helpers in
`presLangScript.sml`.  Keeping the trace parameter explicit preserves the
shape of Cake's `Item (trace option) name children`, even though the first
ported Pancake helpers below all use `NONE`.
-/

namespace Flapjack

inductive DisplayTrace where
  | cons (trace : DisplayTrace) (number : Nat)
  | union (left right : DisplayTrace)
  | sourceLoc (startLine startColumn endLine endColumn : Nat)
  | none
  deriving Repr

inductive DisplayExpr where
  | item (trace : Option DisplayTrace) (name : String) (children : List DisplayExpr)
  | string (value : String)
  | tuple (children : List DisplayExpr)
  | list (children : List DisplayExpr)
  deriving Repr

/-! The small string-tree and pretty intermediate languages used by Cake's
    `display_to_str_tree`/`str_tree_to_strs` boundary. -/

inductive DisplayStrTree where
  | str (value : String)
  | trees (children : List DisplayStrTree)
  | grabLine (tree : DisplayStrTree)

inductive DisplayPretty where
  | parenthesis (body : DisplayPretty)
  | string (value : String)
  | append (left : DisplayPretty) (lineBreak : Bool) (right : DisplayPretty)
  | size (width : Nat) (body : DisplayPretty)

def displayToStrTree : DisplayExpr → DisplayStrTree
  | .item _ name children =>
      .trees (.str name :: children.map displayToStrTree)
  | .string value => .str value
  | .tuple [] => .str "()"
  | .tuple children => .trees (children.map displayToStrTree)
  | .list [] => .str "()"
  | .list children => .trees ((children.map displayToStrTree).map .grabLine)

def displayNewlines : List DisplayPretty → DisplayPretty
  | [] => .string ""
  | [pretty] => pretty
  | pretty :: pretties => .append pretty true (displayNewlines pretties)

def displayV2Pretty : DisplayStrTree → DisplayPretty
  | .str value => .string value
  | .grabLine tree => .size 100000 (displayV2Pretty tree)
  | .trees children => .parenthesis (displayNewlines (children.map displayV2Pretty))

def displayGetSize : DisplayPretty → Nat
  | .size width _ => width
  | .append left _ right => displayGetSize left + displayGetSize right + 1
  | .parenthesis body => displayGetSize body + 2
  | .string _ => 0

def displayGetNextSize : DisplayPretty → Nat
  | .size width _ => width
  | .append left _ _ => displayGetNextSize left
  | .parenthesis body => displayGetNextSize body + 2
  | .string _ => 0

def displayAnnotate : DisplayPretty → DisplayPretty
  | .string value => .size value.length (.string value)
  | .parenthesis body =>
      let annotated := displayAnnotate body
      .size (displayGetSize annotated + 2) (.parenthesis annotated)
  | .append left lineBreak right =>
      .append (displayAnnotate left) lineBreak (displayAnnotate right)
  | .size width body => .size width (displayAnnotate body)

def displayRemoveAll : DisplayPretty → DisplayPretty
  | .parenthesis body => .parenthesis (displayRemoveAll body)
  | .string value => .string value
  | .append left _ right =>
      .append (displayRemoveAll left) false (displayRemoveAll right)
  | .size _ body => displayRemoveAll body

def displaySmartRemove : Nat → Nat → DisplayPretty → DisplayPretty
  | _, _, .string value => .string value
  | indent, column, .size width body =>
      if column + width < 70 then
        displayRemoveAll body
      else
        displaySmartRemove indent column body
  | indent, column, .parenthesis body =>
      .parenthesis (displaySmartRemove (indent + 1) (column + 1) body)
  | indent, column, .append left _lineBreak right =>
      let leftSize := displayGetSize left
      let rightSize := displayGetNextSize right
      if column + leftSize + rightSize < 50 then
        .append (displaySmartRemove indent column left) false
          (displaySmartRemove indent (column + leftSize) right)
      else
        .append (displaySmartRemove indent column left) true
          (displaySmartRemove indent indent right)
termination_by _ _ pretty => sizeOf pretty

def displayPrettyDepth : DisplayPretty → Nat
  | .string _ => 1
  | .size _ body | .parenthesis body => 1 + displayPrettyDepth body
  | .append left _ right =>
      1 + max (displayPrettyDepth left) (displayPrettyDepth right)

def displayFlattenFuel : Nat → String → DisplayPretty → List String → List String
  | 0, _, _, rest => rest
  | fuel + 1, indent, .size _ body, rest => displayFlattenFuel fuel indent body rest
  | fuel + 1, indent, .parenthesis body, rest =>
      "(" :: displayFlattenFuel fuel (indent ++ "   ") body (")" :: rest)
  | _fuel + 1, _indent, .string value, rest => value :: rest
  | fuel + 1, indent, .append left lineBreak right, rest =>
      let rightStrings := displayFlattenFuel fuel indent right rest
      displayFlattenFuel fuel indent left
        ((if lineBreak then indent else " ") :: rightStrings)

def displayFlatten (indent : String) (pretty : DisplayPretty)
    (rest : List String) : List String :=
  displayFlattenFuel (displayPrettyDepth pretty + 1) indent pretty rest

def displayStrTreeToStrings (ending : String) (tree : DisplayStrTree) : List String :=
  displayFlatten "\n"
    (displaySmartRemove 0 0
      (displayAnnotate (displayV2Pretty tree))) [ending]

def mapAppendDisplayStrings (render : α → List String) : List α → List String
  | [] => []
  | value :: values => render value ++ mapAppendDisplayStrings render values

def emptyDisplayItem (name : String) : DisplayExpr :=
  .string name

def opSizeToDisplay : OpSize → DisplayExpr
  | .op8 => emptyDisplayItem "byte"
  | .op16 => emptyDisplayItem "word16"
  | .opW => emptyDisplayItem "word"
  | .op32 => emptyDisplayItem "word32"

def insertDisplayExpressions (value : DisplayExpr)
    (children : List DisplayExpr) : DisplayExpr :=
  match value with
  | .string name => .item none name children
  | expression => expression

def varKindToDisplayString : VarKind → String
  := varKindToString

/-! Cake's `word_to_display_def` prints words as an unpadded, upper-case
    hexadecimal number with a `0x` prefix.  Pancake source words are target
    words, so keep the natural-number projection explicit instead of using a
    potentially different `ToString` instance. -/
class CakeDisplayWord (α : Type u) where
  toNat : α → Nat

instance : CakeDisplayWord Nat where
  toNat := id

instance (width : Nat) : CakeDisplayWord (BitVec width) where
  toNat := BitVec.toNat

def cakeHexUpper : Char → Char
  | 'a' => 'A'
  | 'b' => 'B'
  | 'c' => 'C'
  | 'd' => 'D'
  | 'e' => 'E'
  | 'f' => 'F'
  | digit => digit

def natToCakeHex (value : Nat) : String :=
  "0x" ++ String.ofList ((Nat.toDigits 16 value).map cakeHexUpper)

def wordToDisplay [CakeDisplayWord α] (value : α) : DisplayExpr :=
  emptyDisplayItem (natToCakeHex (CakeDisplayWord.toNat value))


/-! The typed output-boundary counterpart of Cake's `any_pan_prog_pp_def`
    (`pan_passesScript.sml:660-666`).  Backend Cake stages are represented by
    their already-rendered string stream because the source/backend ASTs are
    not part of Flapjack's source-shaped language. -/

def destAnnot (program : Prog α) : Option (String × String) :=
  match program with
  | .annot tag text => some (tag, text)
  | _ => none

end Flapjack
