import Flapjack.Pancake.WordLang
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.WordAlloc

@[hol "cakeml/compiler/backend/word_allocScript.sml" "even_list_def"]
def evenList (count : Nat) : List Nat :=
  (List.range count).map (fun index => 2 * index)

@[hol "cakeml/compiler/backend/word_allocScript.sml" "next_var_rename_def"]
def nextVarRename (name : Nat) (ssa : Spt Nat) (next : Nat) :
    Nat × Spt Nat × Nat :=
  (next, sptInsert name next ssa, next + 4)

@[hol "cakeml/compiler/backend/word_allocScript.sml" "list_next_var_rename_def"]
def listNextVarRename (names : List Nat) (ssa : Spt Nat) (next : Nat) :
    List Nat × Spt Nat × Nat :=
  match names with
  | [] => ([], ssa, next)
  | name :: names =>
    let (name, ssa', next') := nextVarRename name ssa next
    let (names, ssa'', next'') := listNextVarRename names ssa' next'
    (name :: names, ssa'', next'')

/-- Literal native SSA prologue. The source body argument is unused, but
retains its full native carrier. Executed list-state setup remains tracked
separately; this definition alone does not complete that route. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "setup_ssa_def"
  (words_as_type_indexed_bitvec)]
def setupSSA {width : Nat} [NeZero width] (count limit : Nat)
    (_program : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
  let arguments := evenList count
  let (names, ssa, next) := listNextVarRename arguments .ln limit
  (.move 1 (names.zip arguments), ssa, next)

end Flapjack.Compiler.Backend.WordAlloc
