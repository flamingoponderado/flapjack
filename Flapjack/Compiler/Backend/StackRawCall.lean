import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Misc.Sptree

/-! Native Stack raw-call transformation. Production routing is a separate
obligation: the broad fuelled StackRawCall helper is not this definition. -/
namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Original entry-allocation recognition. A bare StackAlloc is not an entry. -/
@[hol "cakeml/compiler/backend/stack_rawcallScript.sml" "seq_stack_alloc_def"
  (words_as_type_indexed_bitvec)]
def seqStackAlloc {width : Nat} [NeZero width] : HolProg width → Option Nat
  | .seq (.stackAlloc k) _ => some k
  | _ => none

/-- Original left-to-right information collection; later duplicate keys win. -/
@[hol "cakeml/compiler/backend/stack_rawcallScript.sml" "collect_info_def"
  (words_as_type_indexed_bitvec)]
def collectInfo {width : Nat} [NeZero width] :
    List (Nat × HolProg width) → Spt Nat → Spt Nat
  | [], info => info
  | (n, body) :: rest, info =>
      collectInfo rest (match seqStackAlloc body with
        | none => info
        | some k => sptInsert n k info)

/-- Original recognition of a stack release followed by a direct tail call. -/
@[hol "cakeml/compiler/backend/stack_rawcallScript.sml" "dest_case_def"
  (words_as_type_indexed_bitvec)]
def destCase {width : Nat} [NeZero width] (first second : HolProg width) :
    Option (Nat × Nat) :=
  match first, second with
  | .stackFree k, .call none (.inl dest) none => some (k, dest)
  | _, _ => none

/-- Original raw-call substitution, retaining the supplied default tree. -/
@[hol "cakeml/compiler/backend/stack_rawcallScript.sml" "comp_seq_def"
  (words_as_type_indexed_bitvec)]
def compSeq {width : Nat} [NeZero width] (first second : HolProg width)
    (info : Spt Nat) (fallback : HolProg width) : HolProg width :=
  match destCase first second with
  | none => fallback
  | some (k, dest) =>
      match sptLookup dest info with
      | none => fallback
      | some l =>
          if l = k then .rawCall dest
          else if l < k then .seq (.stackFree (k - l)) (.rawCall dest)
          else .seq .tick (.seq (.stackAlloc (l - k)) (.rawCall dest))

/-- Original recursive compiler. NONE-return calls are unchanged, including
populated handlers; only returning continuations are recursively compiled. -/
@[hol "cakeml/compiler/backend/stack_rawcallScript.sml" "comp_def"
  (words_as_type_indexed_bitvec)]
def comp {width : Nat} [NeZero width] (info : Spt Nat) : HolProg width → HolProg width
  | .seq first second => compSeq first second info (.seq (comp info first) (comp info second))
  | .ite op r ri first second => .ite op r ri (comp info first) (comp info second)
  | .loop body => .loop (comp info body)
  | .call (some (body, lr, l1, l2)) dest none =>
      .call (some (comp info body, lr, l1, l2)) dest none
  | .call (some (body, lr, l1, l2)) dest (some (handler, k1, k2)) =>
      .call (some (comp info body, lr, l1, l2)) dest (some (comp info handler, k1, k2))
  | other => other

/-- Original top-level compiler preserves the first Seq node without applying
compSeq there, so a function entry allocation remains at the entry. -/
@[hol "cakeml/compiler/backend/stack_rawcallScript.sml" "comp_top_def"
  (words_as_type_indexed_bitvec)]
def compTop {width : Nat} [NeZero width] (info : Spt Nat) : HolProg width → HolProg width
  | .seq first second => .seq (comp info first) (comp info second)
  | other => comp info other

/-- Original whole-program wrapper collects frame sizes from the complete input
before compiling any body. Keys, list order and duplicate entries are retained.
This native definition is not yet the executed broad compiler route. -/
@[hol "cakeml/compiler/backend/stack_rawcallScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
def compile {width : Nat} [NeZero width]
    (programs : List (Nat × HolProg width)) : List (Nat × HolProg width) :=
  let info := collectInfo programs .ln
  programs.map fun (name, body) => (name, compTop info body)

end Flapjack.Compiler.Backend.StackRawCall
