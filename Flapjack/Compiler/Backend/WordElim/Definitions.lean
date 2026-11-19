module

public import Flapjack.Compiler.Backend.FlatElim.Reachability
public import Flapjack.Pancake.WordLang
public import Flapjack.Misc.Sptree
public import Flapjack.HolRef

@[expose] public section

/-!
# Exact HOL `word_elim` dead-code elimination

Counterpart of `cakeml/compiler/backend/word_elimScript.sml`: the analysis
`analyse_word_code`, the dependency function `find_word_ref`, the closure
`remove_word_prog` and the filter `remove_word_code`.  `word_elim` is not used
by `backend_compile`, so these definitions carry no executable-path obligation;
they are the clause-by-clause port needed to state the `word_elimProof`
theorems.

HOL's `num_set` is the sparse tree `Spt Unit` (`Misc.Sptree.NumSet`), and HOL's
`num_set num_map` is `Spt NumSet`.  The reachable set is computed with the
reviewed `closureTotal` rendering of `closure_spt`
(`Flapjack/Compiler/Backend/FlatElim/Reachability.lean`).
-/

namespace Flapjack.Compiler.Backend.WordElim

open Flapjack.Compiler.Backend.FlatElim

/-- Exact HOL `find_word_loc_def` (`word_elimScript.sml:14-16`):
    `find_word_loc (name, _, _) = name`.  HOL pattern-matches the code-list
    entry tuple, so the definition does too. -/
@[hol "cakeml/compiler/backend/word_elimScript.sml" "find_word_loc_def"]
def findWordLoc {α β : Type} : Nat × α × β → Nat
  | (name, _, _) => name

/-- Exact HOL `find_word_ref_def` (`word_elimScript.sml:18-45`): the functions
    a program can call or jump to.
    * `MustTerminate p` and `Loop _ body _` recurse into the body;
    * `Call ret target _ handler` unions the call target, the return label with
      the return handler's references, and the exception handler's references;
    * `Seq`/`If` union both branches; `LocValue _ n` is `insert n () LN`;
    * every other constructor has no references (`LN`). -/
@[hol "cakeml/compiler/backend/word_elimScript.sml" "find_word_ref_def"]
def findWordRef {α : Type} : WordLangProgHOL α → NumSet
  | .mustTerminate body => findWordRef body
  | .call ret target _ handler =>
      sptUnion
        (match target with
         | none => .ln
         | some n => sptInsert n () .ln)
        (sptUnion
          (match ret with
           | none => .ln
           | some (_, _, retHandler, label, _) =>
               sptInsert label () (findWordRef retHandler))
          (match handler with
           | none => .ln
           | some (_, exceptionHandler, _, _) => findWordRef exceptionHandler))
  | .seq first second => sptUnion (findWordRef first) (findWordRef second)
  | .ite _ _ _ first second => sptUnion (findWordRef first) (findWordRef second)
  | .locValue _ name => sptInsert name () .ln
  | .loop _ body _ => findWordRef body
  | _ => .ln

/-- Exact HOL `analyse_word_code_def` (`word_elimScript.sml:49-52`): build the
    `num_set num_map` from the code list, inserting each entry's references at
    its label.  HOL's empty list gives `LN`. -/
@[hol "cakeml/compiler/backend/word_elimScript.sml" "analyse_word_code_def"]
def analyseWordCode {α β : Type} :
    List (Nat × α × WordLangProgHOL β) → Spt NumSet
  | [] => .ln
  | (name, _, prog) :: rest => sptInsert name (findWordRef prog) (analyseWordCode rest)

/-- Exact HOL `remove_word_code_def` (`word_elimScript.sml:55-57`): keep the
    entries whose label is reachable. -/
@[hol "cakeml/compiler/backend/word_elimScript.sml" "remove_word_code_def"]
def removeWordCode {α : Type} (reachable : NumSet) (code : List (Nat × α)) :
    List (Nat × α) :=
  code.filter (fun entry => (sptLookup entry.1 reachable).isSome)

/-- Exact HOL `remove_word_prog_def` (`word_elimScript.sml:59-61`): close the
    dependency graph of the code from the root label, then drop unreachable
    entries.  The closure is the reviewed `closure_spt` rendering
    `closureTotal`. -/
@[hol "cakeml/compiler/backend/word_elimScript.sml" "remove_word_prog_def"]
def removeWordProg {α β : Type} (start : Nat)
    (code : List (Nat × α × WordLangProgHOL β)) : List (Nat × α × WordLangProgHOL β) :=
  let tree := analyseWordCode code
  let reachable := closureTotal (sptInsert start () .ln) tree
  removeWordCode reachable code

end Flapjack.Compiler.Backend.WordElim
