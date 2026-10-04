import Flapjack.Word
import Flapjack.Misc.Sptree
import Flapjack.Pancake.WordLang

/-!
# Loop-to-word context lookup

Faithful ports of the compilation-context functions at the top of CakeML's
`pancake/loop_to_wordScript.sml`:

* `find_var_def` (line 10): look a loop variable up in the compilation
  context; a variable that is not present maps to wordLang register `0`.
* `find_reg_imm_def` (line 17): apply `find_var` to the register case of a
  register/immediate operand.
* `make_ctxt_def` (line 152): assign consecutive even registers starting at
  `2` to a list of variables.

The context is an association list with first-match lookup and cons-insertion,
matching the observable behaviour of the script's `num |-> num` context
(`LN`/`insert`/`lookup`) for the distinct variable names produced by
`comp_func`.
-/

namespace Flapjack.LoopToWord

/-- Context lookup with first-match semantics and cons-insertion, mirroring
the script's `lookup`/`insert` on a `num |-> num` finite map. -/
def lookupVar : Nat → List (Nat × Nat) → Option Nat
  | _, [] => none
  | name, (key, value) :: rest =>
      if key = name then some value else lookupVar name rest

/-- Script `insert x n l` with later insertions overriding earlier ones. -/
def insertVar (name register : Nat) (context : List (Nat × Nat)) :
    List (Nat × Nat) :=
  (name, register) :: context

/-- Port of `find_var_def` (loop_to_wordScript.sml:10). -/
def findVar (context : List (Nat × Nat)) (name : Nat) : Nat :=
  (lookupVar name context).getD 0

/-- Port of `find_reg_imm_def` (loop_to_wordScript.sml:17). -/
def findRegImm (context : List (Nat × Nat)) : RegImm α → RegImm α
  | .imm value => .imm value
  | .reg name => .reg (findVar context name)

/-- Port of `make_ctxt_def` (loop_to_wordScript.sml:152).  The first variable
receives register `next`; each following variable receives the next even
register. -/
def makeCtxt : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
  | _, [], context => context
  | next, name :: rest, context =>
      makeCtxt (next + 2) rest (insertVar name next context)

def loopReferencedVars : LoopProg α → List Nat
  | .skip => []
  | .assign name value => name :: loopVarsOfExp value
  | .primitive destinations _ arguments => destinations ++ arguments
  | .arith operation =>
      match operation with
      | .longMul left right sourceLeft sourceRight =>
          [left, right, sourceLeft, sourceRight]
      | .longDiv left right sourceLeft sourceRight quotient =>
          [left, right, sourceLeft, sourceRight, quotient]
      | .div destination dividend divisor => [destination, dividend, divisor]
  | .store address value => value :: loopVarsOfExp address
  | .setGlobal _ value => loopVarsOfExp value
  | .load32 address destination => [address, destination]
  | .loadByte address destination => [address, destination]
  | .store32 address value => [address, value]
  | .storeByte address value => [address, value]
  | .seq first second => loopReferencedVars first ++ loopReferencedVars second
  | .ite _ condition right thenBranch elseBranch live =>
      [condition] ++ (match right with | .reg name => [name] | .imm _ => []) ++
        live ++ loopReferencedVars thenBranch ++ loopReferencedVars elseBranch
  | .loop liveIn body liveOut => liveIn ++ loopReferencedVars body ++ liveOut
  | .break label => [label]
  | .continue label => [label]
  | .raise exception => [exception]
  | .return values => values
  | .shMem _ name address => name :: loopVarsOfExp address
  | .tick => []
  | .mark body => loopReferencedVars body
  | .fail => []
  | .locValue destination source => [destination, source]
  | .call returns target arguments handler =>
      (match returns with
       | none => []
       | some (values, live) => values ++ live) ++
      target.toList ++ arguments ++
      (match handler with
       | none => []
       | some (exception, handlerBody, returnBody, live) =>
           exception :: live ++ loopReferencedVars handlerBody ++
             loopReferencedVars returnBody)
  | .ffi _ configuration configurationLength array arrayLength live =>
      [configuration, configurationLength, array, arrayLength] ++ live

/-! A list-backed representation of CakeML's `num_set` for the executable
    Loop-to-Word boundary.  The source `toNumSet_def` builds an sptree set by
    recursively inserting each input name; `loopInsert` is the existing
    first-occurrence list-set adapter used by the RISC-V path. -/
def toNumSet : List Nat → List Nat
  | [] => []
  | name :: names => loopInsert name (toNumSet names)

theorem toNumSet_nodup (names : List Nat) : (toNumSet names).Nodup := by
  induction names with
  | nil => simp [toNumSet]
  | cons name names ih =>
      exact loopInsert_nodup name (toNumSet names) ih

/-! `sptree$toAList` is not insertion order.  Its `foldi` walks the binary
    Patricia tree using `lrnext`; retaining that order is observable because
    `loop_to_word$make_ctxt` assigns consecutive Word registers to
    `fromNumSet (acc_vars ...)`. -/
inductive NumSetTree where
  | empty
  | singleton
  | branch (left right : NumSetTree)
  | branchSingleton (left right : NumSetTree)

def numSetLrnextFuel : Nat → Nat → Nat
  | 0, _ => 1
  | _fuel + 1, 0 => 1
  | fuel + 1, value + 1 =>
      2 * numSetLrnextFuel fuel (value / 2)

def numSetLrnext (value : Nat) : Nat :=
  numSetLrnextFuel (value + 1) value

def numSetInsertFuel : Nat → Nat → NumSetTree → NumSetTree
  | 0, _, tree => tree
  | _fuel + 1, 0, .empty => .singleton
  | _fuel + 1, 0, .singleton => .singleton
  | _fuel + 1, 0, .branch left right => .branchSingleton left right
  | _fuel + 1, 0, .branchSingleton left right => .branchSingleton left right
  | fuel + 1, key + 1, .empty =>
      if (key + 1) % 2 = 0 then
        .branch (numSetInsertFuel fuel (((key + 1) - 1) / 2) .empty) .empty
      else
        .branch .empty (numSetInsertFuel fuel (((key + 1) - 1) / 2) .empty)
  | fuel + 1, key + 1, .singleton =>
      if (key + 1) % 2 = 0 then
        .branchSingleton (numSetInsertFuel fuel (((key + 1) - 1) / 2) .empty) .empty
      else
        .branchSingleton .empty (numSetInsertFuel fuel (((key + 1) - 1) / 2) .empty)
  | fuel + 1, key + 1, .branch left right =>
      if (key + 1) % 2 = 0 then
        .branch (numSetInsertFuel fuel (((key + 1) - 1) / 2) left) right
      else
        .branch left (numSetInsertFuel fuel (((key + 1) - 1) / 2) right)
  | fuel + 1, key + 1, .branchSingleton left right =>
      if (key + 1) % 2 = 0 then
        .branchSingleton (numSetInsertFuel fuel (((key + 1) - 1) / 2) left) right
      else
        .branchSingleton left (numSetInsertFuel fuel (((key + 1) - 1) / 2) right)

def numSetInsert (key : Nat) (tree : NumSetTree) : NumSetTree :=
  numSetInsertFuel (key + 1) key tree

def numSetToAList : NumSetTree → Nat → List Nat → List Nat
  | .empty, _, accumulated => accumulated
  | .singleton, index, accumulated => index :: accumulated
  | .branch left right, index, accumulated =>
      let increment := numSetLrnext index
      numSetToAList right (index + increment)
        (numSetToAList left (index + 2 * increment) accumulated)
  | .branchSingleton left right, index, accumulated =>
      let increment := numSetLrnext index
      numSetToAList right (index + increment)
        (index :: numSetToAList left (index + 2 * increment) accumulated)

def fromNumSet (set : List Nat) : List Nat :=
  let tree := (toNumSet set).foldr (fun key tree => numSetInsert key tree) .empty
  numSetToAList tree 0 []

def sourceFallbackContext : List Nat → List (Nat × Nat)
  | [] => []
  | name :: names => (name, 0) :: sourceFallbackContext names

/-! List-backed port of `mk_new_cutset_def` from
    `loop_to_wordScript.sml:51-53`.  The source always retains register zero
    and maps each live source variable through `find_var` before rebuilding the
    finite set. -/
def mkNewCutset (context : List (Nat × Nat)) (live : List Nat) : List Nat :=
  loopInsert 0 (toNumSet ((fromNumSet live).map (findVar context)))

theorem mkNewCutset_nodup (context : List (Nat × Nat)) (live : List Nat) :
    (mkNewCutset context live).Nodup := by
  exact loopInsert_nodup 0 _ (toNumSet_nodup _)

/-! List-backed `difference` for the source's finite sets.  The left-hand
    order is retained because it is the order exposed by `fromNumSet` at the
    comp_func boundary. -/
def differenceNumSet (names excluded : List Nat) : List Nat :=
  names.filter (fun name => name ∉ excluded)

/-! Port of `comp_func_def` from `loop_to_wordScript.sml:164-169`.
    `loopAccVars` supplies the source `acc_vars` set, parameters are removed,
    `makeCtxt` assigns the consecutive even registers, and the state-threaded
    compiler supplies the first component of `comp`. -/
def loopToWordCompContext (params : List Nat) (body : LoopProg α) :
    List (Nat × Nat) :=
  let assigned := loopAccVars body []
  let variables := fromNumSet (differenceNumSet assigned (toNumSet params))
  let maximum := (params ++ assigned ++ loopReferencedVars body).foldl max 0
  let fallback := sourceFallbackContext (List.range (maximum + 1))
  makeCtxt 2 (params ++ variables) fallback

def loopToWordCompFunc [OfNat α 1] (name : Nat) (params : List Nat)
    (body : LoopProg α) : WordProg α :=
  (loopToWordProgWithLabels { vars := loopToWordCompContext params body }
    (name, 2) body).1

/-! Word names for the formals produced by the same `make_ctxt` used by
    `comp_func`.  The source-facing pipeline must use these names rather than
    adding two to the source variable number: source variables need not be
    contiguous after `acc_vars` has been collected. -/
def loopToWordCompParameters (params : List Nat) (body : LoopProg α) : List Nat :=
  params.map (findVar (loopToWordCompContext params body))

/-! Port of `compile_prog_def` from `loop_to_wordScript.sml:171-174`.
    The source adds one entry slot to each function's parameter count while
    preserving source order. -/
def loopToWordCompileProg [OfNat α 1] :
    List (Nat × List Nat × LoopProg α) →
      List (Nat × Nat × WordProg α)
  | [] => []
  | (name, params, body) :: functions =>
      (name, params.length + 1, loopToWordCompFunc name params body) ::
        loopToWordCompileProg functions

/-! Port of `compile_def` from `loop_to_wordScript.sml:176-177`. -/
def loopToWordCompile [OfNat α 1]
    (program : List (Nat × List Nat × LoopProg α)) :
    List (Nat × Nat × WordProg α) :=
  loopToWordCompileProg program

/-! ### Exact `spt`-carrier ports of the HOL loop_to_word context functions -/

/-- Exact HOL `find_var_def` over the `num |-> num` spt context
(`cakeml/pancake/loop_to_wordScript.sml:10`). -/
@[hol "cakeml/pancake/loop_to_wordScript.sml" "find_var_def"]
def findVarHOL (context : Spt Nat) (name : Nat) : Nat :=
  (sptLookup name context).getD 0

/-- Exact HOL `find_reg_imm_def` (`cakeml/pancake/loop_to_wordScript.sml:17`),
over the fixed-width HOL `reg_imm` immediate carrier `'a word` (rendered as the
positive-width `BitVec width`), matching HOL's type-indexed word. -/
@[hol "cakeml/pancake/loop_to_wordScript.sml" "find_reg_imm_def"
  (words_as_type_indexed_bitvec)]
def findRegImmHOL {width : Nat} [NeZero width] (context : Spt Nat) :
    WordRegImm (BitVec width) → WordRegImm (BitVec width)
  | .imm value => .imm value
  | .reg name => .reg (findVarHOL context name)

/-- Exact HOL `toNumSet_def` (`cakeml/pancake/loop_to_wordScript.sml:42`),
right-recursive like HOL. -/
@[hol "cakeml/pancake/loop_to_wordScript.sml" "toNumSet_def"]
def toNumSetHOL : List Nat → Spt Unit
  | [] => .ln
  | n :: ns => sptInsert n () (toNumSetHOL ns)

/-- Exact HOL `fromNumSet_def` (`cakeml/pancake/loop_to_wordScript.sml:47`),
polymorphic in the spt value type like HOL. -/
@[hol "cakeml/pancake/loop_to_wordScript.sml" "fromNumSet_def"]
def fromNumSetHOL {α : Type} (tree : Spt α) : List Nat :=
  (sptToAList tree).map Prod.fst

/-- Exact HOL `mk_new_cutset_def` (`cakeml/pancake/loop_to_wordScript.sml:51`). -/
@[hol "cakeml/pancake/loop_to_wordScript.sml" "mk_new_cutset_def"]
def mkNewCutsetHOL (context : Spt Nat) (live : Spt Unit) : Spt Unit :=
  sptInsert 0 () (toNumSetHOL ((fromNumSetHOL live).map (findVarHOL context)))

/-- Exact HOL `comp_exp_def` (`cakeml/pancake/loop_to_wordScript.sml:22-40`),
well-founded over the loopLang expression size.  HOL's type-indexed `'a word`
is rendered as the positive-width `BitVec width`; the HOL stackLang
`store_name` `Temp m` (a `5 word`) maps to Lean `WordStore.temp` (`BitVec 5`).
This is the proof-side exact port; routing the production list-based
`loopToWordExp` through it is tracked separately. -/
@[hol "cakeml/pancake/loop_to_wordScript.sml" "comp_exp_def"
  (words_as_type_indexed_bitvec)]
def compExpHOL {width : Nat} [NeZero width] (context : Spt Nat) :
    HolLoopExp width → WordLangExpHOL (BitVec width)
  | .const value => .const value
  | .var name => .var (findVarHOL context name)
  | .lookup address => .lookup (.temp address)
  | .baseAddr => .lookup .currHeap
  | .topAddr =>
      .op .add [.lookup .currHeap,
        .shift .lsl (.lookup .heapLength) (.const (BitVec.ofNat width 1))]
  | .load address => .load (compExpHOL context address)
  | .shift operator left right =>
      .shift operator (compExpHOL context left) (compExpHOL context right)
  | .op operator args => .op operator (args.map (compExpHOL context))
  termination_by expression => sizeOf expression
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

/-- Exact total port of HOL `comp_def` (`cakeml/pancake/loop_to_wordScript.sml:56-150`)
over the exact `HolLoopProg width` carrier with the exact `Spt Nat` variable context
and the threaded label pair. Clause-for-clause with the HOL definition. This
total definition is the reviewed tagged port. The executable production route
is tracked separately (bead `flapjack-pxn.18.5.9.5`); this declaration is the
HOL-shaped reference definition. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def compHOL {width : Nat} [NeZero width] (context : Spt Nat) :
    HolLoopProg width → Nat × Nat → WordLangProgHOL (BitVec width) × (Nat × Nat)
  | .skip, labels => (.skip, labels)
  | .assign name expression, labels =>
      (.assign (findVarHOL context name) (compExpHOL context expression), labels)
  | .primitive destinations .addCarry arguments, labels =>
      match destinations, arguments with
      | [result, carry], [left, right, carryIn] =>
          (.seq (.assign 1 (.var (findVarHOL context carryIn)))
            (.seq (.inst (.arith (.addCarry 3
                (findVarHOL context left) (findVarHOL context right) 1)))
              (.seq (.assign (findVarHOL context carry) (.var 1))
                    (.assign (findVarHOL context result) (.var 3)))), labels)
      | _, _ => (.skip, labels)
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight), labels =>
      (.inst (.arith (.longMul (findVarHOL context destinationLeft)
        (findVarHOL context destinationRight) (findVarHOL context sourceLeft)
        (findVarHOL context sourceRight))), labels)
  | .arith (.longDiv destinationLeft destinationRight sourceLeft sourceRight quotient), labels =>
      (.inst (.arith (.longDiv (findVarHOL context destinationLeft)
        (findVarHOL context destinationRight) (findVarHOL context sourceLeft)
        (findVarHOL context sourceRight) (findVarHOL context quotient))), labels)
  | .arith (.div destination dividend divisor), labels =>
      (.inst (.arith (.div (findVarHOL context destination)
        (findVarHOL context dividend) (findVarHOL context divisor))), labels)
  | .store address value, labels =>
      (.store (compExpHOL context address) (findVarHOL context value), labels)
  | .setGlobal address expression, labels =>
      (.set (.temp address) (compExpHOL context expression), labels)
  | .load32 address destination, labels =>
      (.inst (.mem .load32 (findVarHOL context destination)
        (.addr (findVarHOL context address) (BitVec.ofNat width 0))), labels)
  | .loadByte address destination, labels =>
      (.inst (.mem .load8 (findVarHOL context destination)
        (.addr (findVarHOL context address) (BitVec.ofNat width 0))), labels)
  | .store32 address value, labels =>
      (.inst (.mem .store32 (findVarHOL context value)
        (.addr (findVarHOL context address) (BitVec.ofNat width 0))), labels)
  | .storeByte address value, labels =>
      (.inst (.mem .store8 (findVarHOL context value)
        (.addr (findVarHOL context address) (BitVec.ofNat width 0))), labels)
  | .seq first second, labels =>
      let (wordFirst, labels) := compHOL context first labels
      let (wordSecond, labels) := compHOL context second labels
      (.seq wordFirst wordSecond, labels)
  | .ite operator condition right thenBranch elseBranch _, labels =>
      let (wordThen, labels) := compHOL context thenBranch labels
      let (wordElse, labels) := compHOL context elseBranch labels
      (.seq (.ite operator (findVarHOL context condition)
        (match right with
         | .imm value => .imm value
         | .reg name => .reg (findVarHOL context name))
        wordThen wordElse) .tick, labels)
  | .loop liveIn body liveOut, labels =>
      let (wordBody, labels) := compHOL context body labels
      (.seq .tick (.seq (.loop (mkNewCutsetHOL context liveIn) wordBody
        (mkNewCutsetHOL context liveOut)) .tick), labels)
  | .break n, labels => (.break n, labels)
  | .continue n, labels => (.continue n, labels)
  | .raise v, labels => (.raise (findVarHOL context v), labels)
  | .return vs, labels => (.return 0 (vs.map (findVarHOL context)), labels)
  | .tick, labels => (.tick, labels)
  | .mark body, labels => compHOL context body labels
  | .fail, labels => (.skip, labels)
  | .locValue n m, labels => (.locValue (findVarHOL context n) m, labels)
  | .call returns target arguments handler, labels =>
      let mappedArguments := arguments.map (findVarHOL context)
      match returns with
      | none => (.call none target (0 :: mappedArguments) none, labels)
      | some (vs, live) =>
          let mappedReturns := vs.map (findVarHOL context)
          let cutset := mkNewCutsetHOL context live
          let newLabels := (labels.1, labels.2 + 1)
          match handler with
          | none =>
              (.call (some (mappedReturns, (cutset, .ln), .skip, labels))
                target mappedArguments none, newLabels)
          | some (n, p1, p2, _) =>
              let (wordP1, labels1) := compHOL context p1 newLabels
              let (wordP2, labels2) := compHOL context p2 labels1
              let finalLabels := (labels2.1, labels2.2 + 1)
              (.seq
                (.call (some (mappedReturns, (cutset, .ln), wordP2, labels))
                  target mappedArguments
                  (some (findVarHOL context n, wordP1, labels2)))
                .tick, finalLabels)
  | .ffi function configuration configurationLength array arrayLength live, labels =>
      let cutset := mkNewCutsetHOL context live
      (.ffi function (findVarHOL context configuration)
        (findVarHOL context configurationLength) (findVarHOL context array)
        (findVarHOL context arrayLength) (cutset, .ln), labels)
  | .shMem operator name address, labels =>
      (.shareInst operator (findVarHOL context name) (compExpHOL context address), labels)
termination_by program _ => sizeOf program
decreasing_by all_goals decreasing_trivial

end Flapjack.LoopToWord
