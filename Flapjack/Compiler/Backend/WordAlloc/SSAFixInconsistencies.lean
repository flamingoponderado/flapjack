import Flapjack.Compiler.Backend.WordAlloc.SSAMergeMoves
import Flapjack.Misc.Sptree.ToAList
import Flapjack.Pancake.WordLang

/-!
# word_alloc SSA branch reconciliation

Literal ports of `word_allocScript.sml:34-127`: `option_lookup`, move
`priority`, `fake_move`, `fake_moves` and `fix_inconsistencies`, over the
native `WordLangProgHOL` carrier with HOL's `'a word` as `BitVec width`
(positive width) and `num_map` as `Spt`. HOL `(unit + unit) option` is
`Option (Unit ⊕ Unit)`; `toAList`/`union` are the reviewed `sptToAList` and the
sptree `union` rendering `sptUnion`. Proof-side ports: the executed list-state
SSA pass is not routed through them.
-/

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Literal `option_lookup` (`word_allocScript.sml:34-36`). -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "option_lookup_def"]
def optionLookup (t : Spt Nat) (v : Nat) : Nat :=
  match sptLookup v t with
  | none => 0
  | some x => x

/-- Literal move `priority` (`word_allocScript.sml:88-94`): `INL` is the left
branch, `INR` the right. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "priority_def"]
def priority : Option (Unit ⊕ Unit) → Bool → Nat
  | none, _ => 1
  | some (.inl ()), b => if b then 2 else 1
  | some (.inr ()), b => if b then 1 else 2

/-- Literal `fake_move` (`word_allocScript.sml:56-58`): `Inst (Const v 0w)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def fakeMove {width : Nat} [NeZero width] (v : Nat) : WordLangProgHOL (BitVec width) :=
  .inst (.const v 0)

/-- Literal `fake_moves` (`word_allocScript.sml:97-114`): the tail first, then
a name present on exactly one side gets a fresh register on both sides — a
fake constant move on the missing side and a real move on the present one. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def fakeMoves {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    List Nat → Spt Nat → Spt Nat → Nat →
      WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat × Spt Nat
  | [], ssaL, ssaR, na => (.skip, .skip, na, ssaL, ssaR)
  | x :: xs, ssaL, ssaR, na =>
    let (seqL, seqR, na', ssaL', ssaR') := fakeMoves prio xs ssaL ssaR na
    let optLx := sptLookup x ssaL'
    let optLy := sptLookup x ssaR'
    match optLx, optLy with
    | none, some ly =>
      let lmove := .seq seqL (fakeMove na')
      let rmove := .seq seqR (.move (priority prio false) [(na', ly)])
      (lmove, rmove, na' + 4, sptInsert x na' ssaL', sptInsert x na' ssaR')
    | some lx, none =>
      let lmove := .seq seqL (.move (priority prio true) [(na', lx)])
      let rmove := .seq seqR (fakeMove na')
      (lmove, rmove, na' + 4, sptInsert x na' ssaL', sptInsert x na' ssaR')
    | _, _ => (seqL, seqR, na', ssaL', ssaR')

/-- Literal `fix_inconsistencies` (`word_allocScript.sml:116-127`): merge moves
then fake moves over the keys of `union ssa_L ssa_R` in `toAList` order. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def fixInconsistencies {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit))
    (ssaL ssaR : Spt Nat) (na : Nat) :
    WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width) × Nat × Spt Nat :=
  let varUnion := (sptToAList (sptUnion ssaL ssaR)).map Prod.fst
  let (lmov, rmov, na', ssaL', ssaR') := mergeMoves varUnion ssaL ssaR na
  let (lseq, rseq, na'', ssaL'', _ssaR'') := fakeMoves prio varUnion ssaL' ssaR' na'
  (.seq (.move (priority prio true) lmov) lseq, .seq (.move (priority prio false) rmov) rseq,
    na'', ssaL'')

end Flapjack.Compiler.Backend.WordAlloc
