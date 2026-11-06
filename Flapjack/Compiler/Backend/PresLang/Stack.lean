import Flapjack.Compiler.Backend.PresLang.Asm
import Flapjack.Compiler.Backend.PresLang.Clos
import Flapjack.Compiler.Backend.StackLang.Prog

/-! StackLang explorer display following the `stack_*_to_display_def` group in
`cakeml/compiler/backend/presLangScript.sml`. The generic assembly payloads
and String-backed display tree need source correspondence review; the
explorer driver does not yet execute this module. -/
namespace Flapjack.Compiler.Backend.PresLang.Stack
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm

/-- Convert the width-indexed source carrier to the corresponding generic
stack carrier using the checked assembly payload codecs. -/
def fromHol {width : Nat} [NeZero width] (p : StackLang.HolProg width) : StackLang.ProgM (BitVec width) :=
  StackLang.Prog.map HolInst.toWordLangInst id HolRegImm.toWordRegImm id id HolAddr.toWordLangAddr id p

private def item (name : String) (xs : List DisplayExpr) : DisplayExpr := .item none name xs
private def number (n : Nat) : DisplayExpr := .string (toString n)
private def numbers (name : String) (ns : List Nat) : DisplayExpr := item name (ns.map number)
private def label (names : Spt MlString) (n : Nat) : DisplayExpr := .string (Clos.attachName names (some n))

/-- The monomorphic stack store-name carrier has a fixed 5-bit temporary. -/
def store : StackLang.StoreName → DisplayExpr
  | .nextFree => .string "NextFree" | .endOfHeap => .string "EndOfHeap"
  | .triggerGC => .string "TriggerGC" | .heapLength => .string "HeapLength"
  | .progStart => .string "ProgStart" | .bitmapBase => .string "BitmapBase"
  | .currHeap => .string "CurrHeap" | .otherHeap => .string "OtherHeap"
  | .allocSize => .string "AllocSize" | .globals => .string "Globals"
  | .globReal => .string "GlobReal" | .handler => .string "Handler"
  | .genStart => .string "GenStart" | .codeBuffer => .string "CodeBuffer"
  | .codeBufferEnd => .string "CodeBufferEnd" | .bitmapBuffer => .string "BitmapBuffer"
  | .bitmapBufferEnd => .string "BitmapBufferEnd" | .temp w => item "Temp" [wordToDisplay w]

/-- Flatten nested sequence nodes without repeated concatenation. -/
def seqs (p : StackLang.ProgM α) (tail : List (StackLang.ProgM α)) : List (StackLang.ProgM α) :=
  match p with
  | .seq a b => seqs a (seqs b tail)
  | _ => p :: tail

mutual
/-- Render StackLang, preserving the source's depth and list fuel. -/
def program [CakeDisplayWord α] : Nat → Spt MlString → StackLang.ProgM α → DisplayExpr
  | 0, _, _ => .string "..."
  | fuel + 1, names, p => match p with
    | .skip => .string "skip"
    | .inst i => Asm.instruction i
    | .get n s => .tuple [number n, .string "<-", store s]
    | .set s n => .tuple [store s, .string "<-", number n]
    | .opCurrHeap op a b => .tuple [number a, .string ":=", .string "CurrHeap", Asm.binop op, number b]
    | .call ret dest handler => item "call" [
        match ret with
        | none => .string "tail"
        | some (body, reg, s, n) => item "returning" [number reg, label names s, number n, program fuel names body],
        match dest with
        | .inl n => item "direct" [label names n]
        | .inr n => numbers "reg" [n],
        match handler with
        | none => .string "no_handler"
        | some (body, s, n) => item "handler" [label names s, number n, program fuel names body]]
    | .seq a b => .list (.string "seq" :: programList fuel names (seqs a (seqs b [])))
    | .ite cmp n r a b => item "if" [.tuple [Asm.comparison cmp, number n, Asm.regImm r],
        program fuel names a, program fuel names b]
    | .loop p => item "loop" [program fuel names p]
    | .jumpLower a b c => numbers "jump_lower" [a,b,c]
    | .alloc n => numbers "alloc" [n]
    | .storeConsts a b _ => numbers "store_consts" [a,b]
    | .raise n => numbers "raise" [n] | .ret n => numbers "return" [n]
    | .break n => numbers "break" [n] | .continue n => numbers "continue" [n]
    | .ffi name a b c d e => item "ffi" (.string (Source.byteString name) :: [a,b,c,d,e].map number)
    | .tick => .string "tick"
    | .locValue a b c => item "loc_value" [number a, label names b, number c]
    | .install a b c d e => numbers "install" [a,b,c,d,e]
    | .shMemOp op n addr => item "sh_mem" [Asm.memoryOp op, number n, Asm.address addr]
    | .codeBufferWrite a b => numbers "code_buffer_write" [a,b]
    | .dataBufferWrite a b => numbers "data_buffer_write" [a,b]
    | .rawCall n => item "raw_call" [label names n]
    | .stackAlloc n => numbers "stack_alloc" [n]
    | .stackFree n => numbers "stack_free" [n]
    | .stackStore n m => .tuple [.string ("stack[" ++ natToCakeHex n ++ "] := " ++ toString m)]
    | .stackStoreAny n m => .tuple [.string ("stack[var " ++ toString n ++ "] := " ++ toString m)]
    | .stackLoad n m => .tuple [.string (toString n ++ " := stack[" ++ natToCakeHex m ++ "]")]
    | .stackLoadAny n m => .tuple [.string (toString n ++ " := stack[var " ++ toString m ++ "]")]
    | .stackGetSize n => numbers "stack_get_size" [n]
    | .stackSetSize n => numbers "stack_set_size" [n]
    | .bitmapLoad n m => .tuple [.string (toString n ++ " := bitmap[" ++ natToCakeHex m ++ "]")]
    | .halt n => numbers "halt" [n]

private def programList [CakeDisplayWord α] : Nat → Spt MlString → List (StackLang.ProgM α) → List DisplayExpr
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, names, p :: ps => program fuel names p :: programList fuel names ps
end

/-- Render stack functions with CakeML's one-billion-step display fuel. -/
def functions [CakeDisplayWord α] (names : Spt MlString) (fs : List (Nat × StackLang.ProgM α)) : List String :=
  mapAppendDisplayStrings (fun (n, body) =>
    displayStrTreeToStrings "\n\n" (displayToStrTree
      (.tuple [.string "func", label names n, program 1000000000 names body]))) fs

/-- Convert byte-valued display characters to their original bytes. -/
def functionBytes [CakeDisplayWord α] (names : Spt MlString) (fs : List (Nat × StackLang.ProgM α)) : List HolChar :=
  (functions names fs).flatMap fun fragment => fragment.toList.map (fun c => BitVec.ofNat 8 c.toNat)

end Flapjack.Compiler.Backend.PresLang.Stack
