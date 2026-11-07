import Flapjack.Compiler.Backend.PresLang.Asm
import Flapjack.Compiler.Backend.PresLang.Clos
import Flapjack.Compiler.Backend.PresLang.Data
import Flapjack.Pancake.WordLang

/-! WordLang explorer display following the `word_*_to_display_def` group in
`cakeml/compiler/backend/presLangScript.sml`. This uses the HOL-shaped
WordLang carrier with sparse cut sets, but the display tree uses Lean strings
instead of HOL `mlstring`; correspondence and explorer wiring remain open. -/
namespace Flapjack.Compiler.Backend.PresLang.Word
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def item (name : String) (xs : List DisplayExpr) : DisplayExpr := .item none name xs
private def number (n : Nat) : DisplayExpr := .string (toString n)
private def numbers (name : String) (ns : List Nat) : DisplayExpr := item name (ns.map number)
private def tupleNums (ns : List Nat) : DisplayExpr := .tuple (ns.map number)
private def optional (f : α → DisplayExpr) : Option α → DisplayExpr
  | none => .string "none"
  | some x => item "some" [f x]
private def cutsets (s : WordLangCutsetsHOL) : DisplayExpr := .tuple [Data.liveSet s.1, Data.liveSet s.2]

/-- Display a store name, including its fixed-width temporary index. -/
def store : WordStoreHOL → DisplayExpr
  | .nextFree => .string "NextFree" | .endOfHeap => .string "EndOfHeap"
  | .triggerGC => .string "TriggerGC" | .heapLength => .string "HeapLength"
  | .progStart => .string "ProgStart" | .bitmapBase => .string "BitmapBase"
  | .currHeap => .string "CurrHeap" | .otherHeap => .string "OtherHeap"
  | .allocSize => .string "AllocSize" | .globals => .string "Globals"
  | .globReal => .string "GlobReal" | .handler => .string "Handler"
  | .genStart => .string "GenStart" | .codeBuffer => .string "CodeBuffer"
  | .codeBufferEnd => .string "CodeBufferEnd" | .bitmapBuffer => .string "BitmapBuffer"
  | .bitmapBufferEnd => .string "BitmapBufferEnd" | .temp w => item "Temp" [wordToDisplay w]

/-- Display a WordLang expression. -/
def expression [CakeDisplayWord α] : WordLangExpHOL α → DisplayExpr
  | .const w => item "Const" [wordToDisplay w]
  | .var n => item "Var" [number n]
  | .lookup s => item "Lookup" [store s]
  | .load e => item "MemLoad" [expression e]
  | .op o es => item "Op" (Asm.binop o :: es.map expression)
  | .shift s a b => item "Shift" [Source.shift s, expression a, expression b]

/-- Flatten nested sequence nodes in execution order. -/
def seqs (p : WordLangProgHOL α) (tail : List (WordLangProgHOL α)) : List (WordLangProgHOL α) :=
  match p with
  | .seq a b => seqs a (seqs b tail)
  | _ => p :: tail

mutual
/-- Display a program using the original depth and list fuel semantics. -/
def program [CakeDisplayWord α] : Nat → Spt MlString → WordLangProgHOL α → DisplayExpr
  | 0, _, _ => .string "..."
  | fuel + 1, names, p => match p with
    | .skip => .string "skip"
    | .move priority moves => item "move" [number priority,
        .tuple (moves.map (fun (a,b) => .tuple [number a, .string ":=", number b]))]
    | .inst i => item "inst" [Asm.instruction i]
    | .assign n e => .tuple [number n, .string ":=", expression e]
    | .get n s => .tuple [number n, .string "<-", store s]
    | .set s e => .tuple [store s, .string "<-", expression e]
    | .store e n => .tuple [.string "mem", expression e, .string ":=", number n]
    | .shareInst op n e => .tuple [.string "share_mem", Asm.memoryOp op, number n, expression e]
    | .mustTerminate p => item "must_terminate" [program fuel names p]
    | .call ret target args handler => item "call" [returnHandler fuel names ret,
        optional (fun n => .string (Clos.attachName names (some n))) target,
        tupleNums args, exceptionHandler fuel names handler]
    | .opCurrHeap op a b => .tuple [number a, .string ":=", .string "CurrHeap", Asm.binop op, number b]
    | .seq a b => .list (.string "seq" :: programList fuel names (seqs a (seqs b [])))
    | .ite cmp n r a b => item "if" [.tuple [Asm.comparison cmp, number n, Asm.regImm r], program fuel names a, program fuel names b]
    | .loop live body after => item "Loop" [Data.liveSet live, program fuel names body, Data.liveSet after]
    | .alloc n live => item "alloc" [number n, cutsets live]
    | .storeConsts a b c d ws => item "store_consts" [number a, number b, number c, number d,
        .tuple (ws.map (fun (flag, w) => .tuple [.string (if flag then "True" else "False"), wordToDisplay w]))]
    | .raise n => numbers "raise" [n] | .break n => numbers "break" [n]
    | .continue n => numbers "continue" [n] | .return n vs => item "return" [number n, tupleNums vs]
    | .tick => .string "tick"
    | .locValue a b => item "loc_value" [.string (Clos.attachName names (some a)), number b]
    | .install a b c d live => item "install" [number a, number b, number c, number d, cutsets live]
    | .codeBufferWrite a b => numbers "code_buffer_write" [a,b]
    | .dataBufferWrite a b => numbers "data_buffer_write" [a,b]
    | .ffi name a b c d live => item "ffi" [.string (Source.byteString name), number a, number b, number c, number d, cutsets live]

private def programList [CakeDisplayWord α] : Nat → Spt MlString → List (WordLangProgHOL α) → List DisplayExpr
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, names, p :: ps => program fuel names p :: programList fuel names ps

private def returnHandler [CakeDisplayWord α] : Nat → Spt MlString →
    Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL α × Nat × Nat) → DisplayExpr
  | _, _, none => .string "tail"
  | 0, _, some _ => .string "..."
  | fuel + 1, names, some (vs, live, p, n, m) => item "returning" [.tuple [tupleNums vs,
      cutsets live, program fuel names p, .string (Clos.attachName names (some n)), number m]]

private def exceptionHandler [CakeDisplayWord α] : Nat → Spt MlString →
    Option (Nat × WordLangProgHOL α × Nat × Nat) → DisplayExpr
  | _, _, none => .string "no_handler"
  | 0, _, some _ => .string "..."
  | fuel + 1, names, some (n, p, l, m) => item "handler" [.tuple [number n,
      program fuel names p, .string (Clos.attachName names (some l)), number m]]
end

/-- Render functions with even-numbered argument registers and Cake's
one-billion-step display fuel. -/
def functions [CakeDisplayWord α] (names : Spt MlString)
    (fs : List (Nat × Nat × WordLangProgHOL α)) : List String :=
  mapAppendDisplayStrings (fun (n, arity, body) =>
    displayStrTreeToStrings "\n\n" (displayToStrTree (.tuple [
      .string "func", .string (Clos.attachName names (some n)),
      tupleNums ((List.range arity).map (2 * ·)), program 1000000000 names body]))) fs

/-- Encode byte-valued display text without UTF-8 expansion. -/
def functionBytes [CakeDisplayWord α] (names : Spt MlString)
    (fs : List (Nat × Nat × WordLangProgHOL α)) : List HolChar :=
  (functions names fs).flatMap fun fragment => fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

end Flapjack.Compiler.Backend.PresLang.Word
