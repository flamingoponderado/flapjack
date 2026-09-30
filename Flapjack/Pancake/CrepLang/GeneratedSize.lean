import Flapjack.Pancake.CrepLang.Prog
import Flapjack.Pancake.PanLang.Exp

/-!
# HOL's generated `crepLang` datatype sizes

HOL's `Datatype` command generates `exp_size`/`exp1_size` and
`prog_size`/`prog1_size`..`prog4_size` for the crepLang `exp` and `prog`
datatypes (`cakeml/pancake/crepLangScript.sml`).  They are produced by HOL's
datatype package, not written as source declarations, so they have no textual
HOL name for `scripts/check-hol-refs.py` and these transcriptions cannot carry
an `@[hol]` tag (as for the panLang precedent `expSizeHOL`).  The tagged
`unreach_elim_prog_size` (`crep_inlineProofScript.sml:1730`) is stated over
`prog_size`.  The equations below are printed from the real CakeML
`crepLangTheory` by `scripts/hol-probes/crep_lang_size_probeScript.sml` and
pinned in `scripts/hol-probes/crep_lang_size_probe.out`; the concrete rows are
replayed in `Flapjack.Test.CrepLangGeneratedSizeParity`.

```
exp_size f (Const a) = 1 + w2n a            exp_size f (Var a) = 1 + a
exp_size f (Load a) = 1 + exp_size f a      (Load32, LoadByte likewise)
exp_size f (LoadGlob a) = 1 + w2n a
exp_size f (Op a0 a1) = 1 + (binop_size a0 + exp1_size f a1)
exp_size f (Crepop a0 a1) = 1 + (crepop_size a0 + exp1_size f a1)
exp_size f (Cmp a0 a1 a2) = 1 + (cmp_size a0 + (exp_size f a1 + exp_size f a2))
exp_size f (Shift a0 a1 a2) = 1 + (shift_size a0 + (exp_size f a1 + exp_size f a2))
exp_size f BaseAddr = 0                     exp_size f TopAddr = 0
exp1_size f [] = 0     exp1_size f (a0::a1) = 1 + (exp_size f a0 + exp1_size f a1)
prog_size f Skip = 0   prog_size f Tick = 0
prog_size f (Dec a0 a1 a2) = 1 + (a0 + (exp_size f a1 + prog_size f a2))
prog_size f (Assign a0 a1) = 1 + (a0 + exp_size f a1)
prog_size f (Primitive a0 a1 a2) =
  1 + (list_size (λx. x) a0 + (primop_size a1 + list_size (λx. x) a2))
prog_size f (Store a0 a1) = 1 + (exp_size f a0 + exp_size f a1)   (Store32, StoreByte)
prog_size f (StoreGlob a0 a1) = 1 + (w2n a0 + exp_size f a1)
prog_size f (Seq a0 a1) = 1 + (prog_size f a0 + prog_size f a1)
prog_size f (If a0 a1 a2) = 1 + (exp_size f a0 + (prog_size f a1 + prog_size f a2))
prog_size f (While a0 a1) = 1 + (exp_size f a0 + prog_size f a1)
prog_size f (Break a) = 1 + a              prog_size f (Continue a) = 1 + a
prog_size f (Call a0 a1 a2) =
  1 + (prog1_size f a0 + (mlstring_size a1 + list_size (exp_size f) a2))
prog_size f (ExtCall a0 a1 a2 a3 a4) = 1 + (mlstring_size a0 + (a1 + (a2 + (a3 + a4))))
prog_size f (Raise a) = 1 + w2n a
prog_size f (Return a) = 1 + list_size (exp_size f) a
prog_size f (ShMem a0 a1 a2) = 1 + (memop_size a0 + (a1 + exp_size f a2))
prog1_size f NONE = 0   prog1_size f (SOME a) = 1 + prog2_size f a
prog2_size f (a0,a1) = 1 + (list_size (λx. x) a0 + prog3_size f a1)
prog3_size f NONE = 0   prog3_size f (SOME a) = 1 + prog4_size f a
prog4_size f (a0,a1) = 1 + (w2n a0 + prog_size f a1)
```

`crepop`, `primop` and `memop` are enumerations, so their generated sizes are
the constant `0`; `binop`/`cmp`/`shift` reuse the panLang transcriptions.  The
parameter `f : 'a -> num` is unused by every clause (words are sized by `w2n`)
and is kept for HOL's exact shape.  These are Flapjack transcriptions with no
`@[hol]` tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (binopSizeHOL cmpSizeHOL shiftSizeHOL listSizeHOL
  mlstringSizeHOL)

namespace CrepLangGeneratedSize

/-- HOL's generated `crepop_size`: `crepop` is an enumeration. -/
def crepopSizeHOL (_ : CrepOp) : Nat := 0

/-- HOL's generated `primop_size`: `primop` is an enumeration. -/
def primopSizeHOL (_ : PrimOp) : Nat := 0

/-- HOL's generated `memop_size`: `memop` is an enumeration. -/
def memopSizeHOL (_ : WordMemOp) : Nat := 0

mutual
  /-- HOL's generated crepLang `exp_size`. -/
  def crepExpSizeHOL {width : Nat} [NeZero width] {α : Type} (f : α → Nat) :
      CrepExpHOL width → Nat
    | .const value => 1 + value.toNat
    | .var name => 1 + name
    | .load address => 1 + crepExpSizeHOL f address
    | .load32 address => 1 + crepExpSizeHOL f address
    | .loadByte address => 1 + crepExpSizeHOL f address
    | .loadGlob address => 1 + address.toNat
    | .op operator args => 1 + (binopSizeHOL operator + crepExp1SizeHOL f args)
    | .crepOp operator args => 1 + (crepopSizeHOL operator + crepExp1SizeHOL f args)
    | .cmp operator left right =>
        1 + (cmpSizeHOL operator + (crepExpSizeHOL f left + crepExpSizeHOL f right))
    | .shift operator left right =>
        1 + (shiftSizeHOL operator + (crepExpSizeHOL f left + crepExpSizeHOL f right))
    | .baseAddr => 0
    | .topAddr => 0

  /-- HOL's generated crepLang `exp1_size` (expression lists). -/
  def crepExp1SizeHOL {width : Nat} [NeZero width] {α : Type} (f : α → Nat) :
      List (CrepExpHOL width) → Nat
    | [] => 0
    | e :: es => 1 + (crepExpSizeHOL f e + crepExp1SizeHOL f es)
end

mutual
  /-- HOL's generated crepLang `prog_size`. -/
  def crepProgSizeHOL {width : Nat} [NeZero width] {α : Type} (f : α → Nat) :
      CrepProgHOL width → Nat
    | .skip => 0
    | .dec name value body => 1 + (name + (crepExpSizeHOL f value + crepProgSizeHOL f body))
    | .assign name value => 1 + (name + crepExpSizeHOL f value)
    | .primitive names operator args =>
        1 + (listSizeHOL (fun x => x) names + (primopSizeHOL operator + listSizeHOL (fun x => x) args))
    | .store address value => 1 + (crepExpSizeHOL f address + crepExpSizeHOL f value)
    | .store32 address value => 1 + (crepExpSizeHOL f address + crepExpSizeHOL f value)
    | .storeByte address value => 1 + (crepExpSizeHOL f address + crepExpSizeHOL f value)
    | .storeGlob address value => 1 + (address.toNat + crepExpSizeHOL f value)
    | .seq first second => 1 + (crepProgSizeHOL f first + crepProgSizeHOL f second)
    | .ite condition thenBranch elseBranch =>
        1 + (crepExpSizeHOL f condition +
          (crepProgSizeHOL f thenBranch + crepProgSizeHOL f elseBranch))
    | .while condition body => 1 + (crepExpSizeHOL f condition + crepProgSizeHOL f body)
    | .break label => 1 + label
    | .continue label => 1 + label
    | .call returnInfo name args =>
        1 + (crepProg1SizeHOL f returnInfo +
          (mlstringSizeHOL name + listSizeHOL (crepExpSizeHOL f) args))
    | .extCall function a b c d => 1 + (mlstringSizeHOL function + (a + (b + (c + d))))
    | .raise exception => 1 + exception.toNat
    | .return values => 1 + listSizeHOL (crepExpSizeHOL f) values
    | .shMem operator name address =>
        1 + (memopSizeHOL operator + (name + crepExpSizeHOL f address))
    | .tick => 0

  /-- HOL's generated `prog1_size` (the call return information option). -/
  def crepProg1SizeHOL {width : Nat} [NeZero width] {α : Type} (f : α → Nat) :
      Option (List Nat × Option (BitVec width × CrepProgHOL width)) → Nat
    | none => 0
    | some info => 1 + crepProg2SizeHOL f info

  /-- HOL's generated `prog2_size` (destinations and handler pair). -/
  def crepProg2SizeHOL {width : Nat} [NeZero width] {α : Type} (f : α → Nat) :
      List Nat × Option (BitVec width × CrepProgHOL width) → Nat
    | (names, handler) => 1 + (listSizeHOL (fun x => x) names + crepProg3SizeHOL f handler)

  /-- HOL's generated `prog3_size` (the handler option). -/
  def crepProg3SizeHOL {width : Nat} [NeZero width] {α : Type} (f : α → Nat) :
      Option (BitVec width × CrepProgHOL width) → Nat
    | none => 0
    | some handler => 1 + crepProg4SizeHOL f handler

  /-- HOL's generated `prog4_size` (exception id and handler body). -/
  def crepProg4SizeHOL {width : Nat} [NeZero width] {α : Type} (f : α → Nat) :
      BitVec width × CrepProgHOL width → Nat
    | (exception, body) => 1 + (exception.toNat + crepProgSizeHOL f body)
end

end CrepLangGeneratedSize

end Flapjack
