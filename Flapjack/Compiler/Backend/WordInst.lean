import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Misc.Option
import Flapjack.Misc.Sorting

/-!
# `word_inst`: instruction selection and three-to-two register conversion

Counterpart of `cakeml/compiler/backend/word_instScript.sml`: every definition
(`pull_ops`, `is_const`, `rm_const`, `convert_sub`, `op_consts`, `reduce_const`,
`optimize_consts`, `pull_exp`, `flatten_exp`, `is_Lookup_CurrHeap`,
`inst_select_exp`, `inst_select`, `three_to_two_reg`, `three_to_two_reg_prog`)
over the reviewed `WordLangProgHOL`/`WordLangExpHOL` carriers, positive-width
`BitVec` words and the exact `asm$asm_config` carrier `AsmConfigExact`.

HOL `PARTITION` is the tagged `holPartition` (its `PART` accumulators reverse
both sublists, unlike `List.partition`), `MAP` over the argument list is the attached
map (the same list, needed for Lean's termination proof), `THE` is the tagged
`holThe` (so `optimize_consts` is noncomputable, as `THE NONE` is unspecified in
HOL), and the asm overloads `addr_offset_ok`/`hw_offset_ok`/`byte_offset_ok` are
`offset_ok 0` (`asmOffsetOkExact 0`) on the matching configuration field.

This is a proof-side port; the executed compiler's `RiscV/WordInstSelect.lean`
remains a separate untagged implementation whose routing is tracked separately.
-/

namespace Flapjack.Compiler.Backend.WordInst

open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `pull_ops_def` (`word_instScript.sml:24-29`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "pull_ops_def"
  (words_as_type_indexed_bitvec)]
def pullOps {width : Nat} [NeZero width] (op : BinOp) :
    List (WordLangExpHOL (BitVec width)) → List (WordLangExpHOL (BitVec width)) →
      List (WordLangExpHOL (BitVec width))
  | [], acc => acc
  | x :: xs, acc =>
      match x with
      | .op op' ls => if op = op' then pullOps op xs (ls ++ acc) else pullOps op xs (x :: acc)
      | _ => pullOps op xs (x :: acc)

/-- Exact HOL `is_const_def` (`word_instScript.sml:31-34`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "is_const_def"
  (words_as_type_indexed_bitvec)]
def isConst {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → Bool
  | .const _ => true
  | _ => false

/-- Exact HOL `rm_const_def` (`word_instScript.sml:36-40`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "rm_const_def"
  (words_as_type_indexed_bitvec)]
def rmConst {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → BitVec width
  | .const w => w
  | _ => 0

/-- Exact HOL `convert_sub_def` (`word_instScript.sml:42-46`); the clauses are
    tried in source order. -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "convert_sub_def"
  (words_as_type_indexed_bitvec)]
def convertSub {width : Nat} [NeZero width] :
    List (WordLangExpHOL (BitVec width)) → WordLangExpHOL (BitVec width)
  | [.const w1, .const w2] => .const (w1 - w2)
  | [x, .const w] => .op .add [.const (-w), x]
  | ls => .op .sub ls

/-- Exact HOL `op_consts_def` (`word_instScript.sml:62-65`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "op_consts_def"
  (words_as_type_indexed_bitvec)]
def opConsts {width : Nat} [NeZero width] : BinOp → WordLangExpHOL (BitVec width)
  | .and => .const (~~~0)
  | _ => .const 0

/-- Exact HOL `reduce_const_def` (`word_instScript.sml:80-91`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "reduce_const_def"
  (words_as_type_indexed_bitvec)]
def reduceConst {width : Nat} [NeZero width] (op : BinOp) (w : BitVec width)
    (rest : List (WordLangExpHOL (BitVec width))) : WordLangExpHOL (BitVec width) :=
  if w = 0 then
    if op = .add ∨ op = .or ∨ op = .xor then
      match rest with
      | [] => .const w
      | [x] => x
      | _ => .op op rest
    else if op = .and then .const 0
    else .op op (.const w :: rest)
  else .op op (.const w :: rest)

/-- Exact HOL `optimize_consts_def` (`word_instScript.sml:93-101`); `THE` is the
    tagged `holThe`. -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "optimize_consts_def"
  (words_as_type_indexed_bitvec)]
noncomputable def optimizeConsts {width : Nat} [NeZero width] (op : BinOp)
    (ls : List (WordLangExpHOL (BitVec width))) : WordLangExpHOL (BitVec width) :=
  let (constLs, nconstLs) := holPartition (fun e => isConst e) ls
  match constLs with
  | [] => .op op nconstLs
  | _ =>
      let w := holThe (wordOpHOL op (constLs.map rmConst))
      reduceConst op w nconstLs

/-- Exact HOL `pull_exp_def` (`word_instScript.sml:103-125`); clauses in source
    order, so every `Op Sub` goes to `convert_sub`. -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "pull_exp_def"
  (words_as_type_indexed_bitvec)]
noncomputable def pullExp {width : Nat} [NeZero width] :
    WordLangExpHOL (BitVec width) → WordLangExpHOL (BitVec width)
  | .op .sub ls =>
      let newLs := ls.attach.map (fun ⟨e, _⟩ => pullExp e)
      convertSub newLs
  | .op op [] => opConsts op
  | .op _ [x] => pullExp x
  | .op op ls =>
      let newLs := ls.attach.map (fun ⟨e, _⟩ => pullExp e)
      let pullLs := pullOps op newLs []
      optimizeConsts op pullLs
  | .load exp => .load (pullExp exp)
  | .shift shift exp nexp => .shift shift (pullExp exp) (pullExp nexp)
  | exp => exp
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | omega

/-- Exact HOL `flatten_exp_def` (`word_instScript.sml:138-146`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "flatten_exp_def"
  (words_as_type_indexed_bitvec)]
def flattenExp {width : Nat} [NeZero width] :
    WordLangExpHOL (BitVec width) → WordLangExpHOL (BitVec width)
  | .op .sub exps => .op .sub (exps.attach.map (fun ⟨e, _⟩ => flattenExp e))
  | .op op [] => opConsts op
  | .op _ [x] => flattenExp x
  | .op op (x :: xs) => .op op [flattenExp (.op op xs), flattenExp x]
  | .load exp => .load (flattenExp exp)
  | .shift shift exp nexp => .shift shift (flattenExp exp) (flattenExp nexp)
  | exp => exp
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | omega

/-- Exact HOL `is_Lookup_CurrHeap_def` (`word_instScript.sml:184-187`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "is_Lookup_CurrHeap_def"
  (words_as_type_indexed_bitvec)]
def isLookupCurrHeap {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → Bool
  | .lookup .currHeap => true
  | _ => false

/-- HOL `addr_offset_ok c` (`asmScript.sml:279`, an overload): `offset_ok 0
    c.addr_offset`.  Untagged rendering of the overload. -/
def addrOffsetOk {width : Nat} [NeZero width] (c : AsmConfigExact width) (w : BitVec width) :
    Bool :=
  asmOffsetOkExact 0 c.addrOffset w

/-- HOL `hw_offset_ok c` (`asmScript.sml:280`, an overload). -/
def hwOffsetOk {width : Nat} [NeZero width] (c : AsmConfigExact width) (w : BitVec width) :
    Bool :=
  asmOffsetOkExact 0 c.hwOffset w

/-- HOL `byte_offset_ok c` (`asmScript.sml:281`, an overload). -/
def byteOffsetOk {width : Nat} [NeZero width] (c : AsmConfigExact width) (w : BitVec width) :
    Bool :=
  asmOffsetOkExact 0 c.byteOffset w

/-- Exact HOL `inst_select_exp_def` (`word_instScript.sml:206-262`), clause by
    clause; `dimindex (:'a)` is `width`, `w2n`/`n2w` are `toNat`/`ofNat`. -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "inst_select_exp_def"
  (words_as_type_indexed_bitvec)]
def instSelectExp {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    Nat → Nat → WordLangExpHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | tar, temp, .load exp =>
      match _hx : exp with
      | .op .add [exp', .const w] =>
          if addrOffsetOk c w then
            let prog := instSelectExp c temp temp exp'
            .seq prog (.inst (.mem .load tar (.addr temp w)))
          else
            let prog := instSelectExp c temp temp exp
            .seq prog (.inst (.mem .load tar (.addr temp 0)))
      | _ =>
          let prog := instSelectExp c temp temp exp
          .seq prog (.inst (.mem .load tar (.addr temp 0)))
  | tar, _, .const w => .inst (.const tar w)
  | tar, _, .var v => .move 0 [(tar, v)]
  | tar, _, .lookup storeName => .get tar storeName
  | tar, temp, .op op [e1, e2] =>
      if isLookupCurrHeap e2 then
        let p1 := instSelectExp c temp temp e1
        .seq p1 (.opCurrHeap op tar temp)
      else if isLookupCurrHeap e1 ∧ op ≠ .sub then
        let p2 := instSelectExp c temp temp e2
        .seq p2 (.opCurrHeap op tar temp)
      else
        let p1 := instSelectExp c temp temp e1
        match hx : e2 with
        | .const w =>
            if c.validImm (.inl op) w then
              .seq p1 (.inst (.arith (.binop op tar temp (.imm w))))
            else if op = .add ∧ c.validImm (.inl .sub) (-w) then
              .seq p1 (.inst (.arith (.binop .sub tar temp (.imm (-w)))))
            else
              let p2 : WordLangProgHOL (BitVec width) := .inst (.const (temp + 1) w)
              .seq p1 (.seq p2 (.inst (.arith (.binop op tar temp (.reg (temp + 1))))))
        | _ =>
            let p2 := instSelectExp c (temp + 1) (temp + 1) e2
            .seq p1 (.seq p2 (.inst (.arith (.binop op tar temp (.reg (temp + 1))))))
  | tar, temp, .shift sh exp e1 =>
      match hx : e1 with
      | .const shiftLen =>
          let n := shiftLen.toNat
          if n < width then
            let prog := instSelectExp c temp temp exp
            if n = 0 then .seq prog (.move 0 [(tar, temp)])
            else .seq prog (.inst (.arith (.shift sh tar temp (.imm (BitVec.ofNat width n)))))
          else .inst (.const tar 0)
      | _ =>
          let p := instSelectExp c temp temp exp
          let p1 := instSelectExp c (temp + 1) (temp + 1) e1
          .seq p (.seq p1 (.inst (.arith (.shift sh tar temp (.reg (temp + 1))))))
  | _, _, _ => .skip
termination_by _ _ e => sizeOf e
decreasing_by
  all_goals (try subst_vars)
  all_goals simp_wf
  all_goals omega

/-- Exact HOL `inst_select_def` (`word_instScript.sml:284-339`): every clause,
    with HOL's `o` composition applied. -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "inst_select_def"
  (words_as_type_indexed_bitvec)]
noncomputable def instSelect {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp : Nat) : WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .assign v exp => instSelectExp c v temp (flattenExp (pullExp exp))
  | .set store exp =>
      let prog := instSelectExp c temp temp (flattenExp (pullExp exp))
      .seq prog (.set store (.var temp))
  | .store exp var =>
      let exp := flattenExp (pullExp exp)
      match exp with
      | .op .add [exp', .const w] =>
          if addrOffsetOk c w then
            let prog := instSelectExp c temp temp exp'
            .seq prog (.inst (.mem .store var (.addr temp w)))
          else
            let prog := instSelectExp c temp temp exp
            .seq prog (.inst (.mem .store var (.addr temp 0)))
      | _ =>
          let prog := instSelectExp c temp temp exp
          .seq prog (.inst (.mem .store var (.addr temp 0)))
  | .seq p1 p2 => .seq (instSelect c temp p1) (instSelect c temp p2)
  | .mustTerminate p1 => .mustTerminate (instSelect c temp p1)
  | .shareInst op v exp =>
      let exp := flattenExp (pullExp exp)
      match exp with
      | .op .add [exp', .const w] =>
          if ((op = .load ∨ op = .store) ∧ addrOffsetOk c w) ∨
              ((op = .load32 ∨ op = .store32) ∧ addrOffsetOk c w) ∨
              ((op = .load16 ∨ op = .store16) ∧ hwOffsetOk c w) ∨
              ((op = .load8 ∨ op = .store8) ∧ byteOffsetOk c w) then
            let prog := instSelectExp c temp temp exp'
            .seq prog (.shareInst op v (.op .add [.var temp, .const w]))
          else
            let prog := instSelectExp c temp temp exp
            .seq prog (.shareInst op v (.var temp))
      | _ =>
          let prog := instSelectExp c temp temp exp
          .seq prog (.shareInst op v (.var temp))
  | .ite cmp r1 ri c1 c2 => .ite cmp r1 ri (instSelect c temp c1) (instSelect c temp c2)
  | .call ret dest args handler =>
      let retsel :=
        match ret with
        | none => none
        | some (n, names, retHandler, l1, l2) => some (n, names, instSelect c temp retHandler, l1, l2)
      let handlersel :=
        match handler with
        | none => none
        | some (n, h, l1, l2) => some (n, instSelect c temp h, l1, l2)
      .call retsel dest args handlersel
  | .loop names body exitNames => .loop names (instSelect c temp body) exitNames
  | prog => prog

/-- Exact HOL `three_to_two_reg_def` (`word_instScript.sml:394-431`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "three_to_two_reg_def"
  (words_as_type_indexed_bitvec)]
def threeToTwoReg {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .inst (.arith (.binop bop r1 r2 ri)) =>
      .seq (.move 0 [(r1, r2)]) (.inst (.arith (.binop bop r1 r1 ri)))
  | .inst (.arith (.shift l r1 r2 n)) =>
      .seq (.move 0 [(r1, r2)]) (.inst (.arith (.shift l r1 r1 n)))
  | .inst (.arith (.addCarry r1 r2 r3 r4)) =>
      .seq (.move 0 [(r1, r2)]) (.inst (.arith (.addCarry r1 r1 r3 r4)))
  | .inst (.arith (.addOverflow r1 r2 r3 r4)) =>
      .seq (.move 0 [(r1, r2)]) (.inst (.arith (.addOverflow r1 r1 r3 r4)))
  | .inst (.arith (.subOverflow r1 r2 r3 r4)) =>
      .seq (.move 0 [(r1, r2)]) (.inst (.arith (.subOverflow r1 r1 r3 r4)))
  | .opCurrHeap bop r1 r2 => .seq (.move 0 [(r1, r2)]) (.opCurrHeap bop r1 r1)
  | .seq p1 p2 => .seq (threeToTwoReg p1) (threeToTwoReg p2)
  | .mustTerminate p1 => .mustTerminate (threeToTwoReg p1)
  | .ite cmp r1 ri c1 c2 => .ite cmp r1 ri (threeToTwoReg c1) (threeToTwoReg c2)
  | .call ret dest args handler =>
      let retsel :=
        match ret with
        | none => none
        | some (n, names, retHandler, l1, l2) => some (n, names, threeToTwoReg retHandler, l1, l2)
      let handlersel :=
        match handler with
        | none => none
        | some (n, h, l1, l2) => some (n, threeToTwoReg h, l1, l2)
      .call retsel dest args handlersel
  | .loop names body exitNames => .loop names (threeToTwoReg body) exitNames
  | prog => prog

/-- Exact HOL `three_to_two_reg_prog_def` (`word_instScript.sml:470-473`). -/
@[hol "cakeml/compiler/backend/word_instScript.sml" "three_to_two_reg_prog_def"
  (words_as_type_indexed_bitvec)]
def threeToTwoRegProg {width : Nat} [NeZero width] (b : Bool)
    (prog : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  if b then threeToTwoReg prog else prog

end Flapjack.Compiler.Backend.WordInst
