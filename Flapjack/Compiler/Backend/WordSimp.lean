import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Misc.Sptree.InterEq
import Flapjack.Misc.Sptree.FilterV

namespace Flapjack.Compiler.Backend.WordSimp

/-- HOL's left-Skip elimination over the exact WordLang carrier.
Pattern matching implements the source's `p1 = Skip` test without comparing
irrelevant function-backed payloads of other constructors. Production's distinct
`WordProg` carrier operation and full folds correspond through the encoder in
`ProductionSmartSeq`; its measured full-codec performance exception is recorded
in `docs/benchmarks/smartseq-production/README.md`. -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "SmartSeq_def"
  (words_as_type_indexed_bitvec)]
def smartSeqHOL {width : Nat} [NeZero width]
    (first second : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match first with
  | .skip => second
  | _ => .seq first second

/-- Exact HOL `is_gc_const_def` (`word_simpScript.sml:253-255`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "is_gc_const_def"
  (words_as_type_indexed_bitvec)]
def isGcConst {width : Nat} [NeZero width] (c : BitVec width) : Bool :=
  decide (c &&& 1 = 0)

/-- Exact HOL `Seq_assoc_def` (`word_simpScript.sml:21-39`): all seven clauses,
including the catch-all `SmartSeq p1 other`. -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "Seq_assoc_def"
  (words_as_type_indexed_bitvec)]
def seqAssoc {width : Nat} [NeZero width] (p1 : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .skip => p1
  | .seq q1 q2 => seqAssoc (seqAssoc p1 q1) q2
  | .ite v n r q1 q2 => smartSeqHOL p1 (.ite v n r (seqAssoc .skip q1) (seqAssoc .skip q2))
  | .mustTerminate q => smartSeqHOL p1 (.mustTerminate (seqAssoc .skip q))
  | .call retProg dest args handler =>
      smartSeqHOL p1 (.call
        (match retProg with
          | none => none
          | some (x1, x2, q1, x3, x4) => some (x1, x2, seqAssoc .skip q1, x3, x4))
        dest args
        (match handler with
          | none => none
          | some (y1, q2, y2, y3) => some (y1, seqAssoc .skip q2, y2, y3)))
  | .loop names body exitNames => smartSeqHOL p1 (.loop names (seqAssoc .skip body) exitNames)
  | other => smartSeqHOL p1 other

/-- Exact HOL `dest_Seq_def` (`word_simpScript.sml:81-84`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "dest_Seq_def"
  (words_as_type_indexed_bitvec)]
def destSeq {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width)
  | .seq p1 p2 => (p1, p2)
  | p => (.skip, p)

/-- Exact HOL `dest_If_def` (`word_simpScript.sml:99-102`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "dest_If_def"
  (words_as_type_indexed_bitvec)]
def destIf {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) →
      Option (Cmp × Nat × WordRegImm (BitVec width) × WordLangProgHOL (BitVec width) ×
        WordLangProgHOL (BitVec width))
  | .ite x1 x2 x3 p1 p2 => some (x1, x2, x3, p1, p2)
  | _ => none

/-- Exact HOL `dest_If_Eq_Imm_def` (`word_simpScript.sml:117-122`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "dest_If_Eq_Imm_def"
  (words_as_type_indexed_bitvec)]
def destIfEqImm {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    Option (Nat × BitVec width × WordLangProgHOL (BitVec width) × WordLangProgHOL (BitVec width)) :=
  match destIf p with
  | some (.equal, n, .imm w, p1, p2) => some (n, w, p1, p2)
  | _ => none

/-- Exact HOL `dest_Seq_Assign_Const_def` (`word_simpScript.sml:137-143`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "dest_Seq_Assign_Const_def"
  (words_as_type_indexed_bitvec)]
def destSeqAssignConst {width : Nat} [NeZero width] (n : Nat)
    (p : WordLangProgHOL (BitVec width)) : Option (WordLangProgHOL (BitVec width) × BitVec width) :=
  let (p1, p2) := destSeq p
  match p2 with
  | .assign m (.const w) => if m = n then some (p1, w) else none
  | _ => none

/-- Exact HOL `strip_const_def` (`word_simpScript.sml:182-189`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "strip_const_def"
  (words_as_type_indexed_bitvec)]
def stripConst {width : Nat} [NeZero width] :
    List (WordLangExpHOL (BitVec width)) → Option (List (BitVec width))
  | [] => some []
  | .const w :: cs =>
      match stripConst cs with
      | some ws => some (w :: ws)
      | none => none
  | _ => none

/-- Exact HOL `const_fp_exp_def` (`word_simpScript.sml:191-213`).  HOL's
    `MAP (\a. const_fp_exp a cs) args` is the attached map, which is the same
    list; `Const`, `Lookup` and `Load` are returned unchanged. -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "const_fp_exp_def"
  (words_as_type_indexed_bitvec)]
def constFpExp {width : Nat} [NeZero width] :
    WordLangExpHOL (BitVec width) → Spt (BitVec width) → WordLangExpHOL (BitVec width)
  | .var v, cs =>
      match sptLookup v cs with
      | some x => .const x
      | none => .var v
  | .op op args, cs =>
      let constFpArgs := args.attach.map (fun ⟨a, _⟩ => constFpExp a cs)
      match stripConst constFpArgs with
      | some ws =>
          match wordOpHOL op ws with
          | some w => .const w
          | none => .op op (ws.map .const)
      | none => .op op constFpArgs
  | .shift sh e e1, cs =>
      let constFpExpE := constFpExp e cs
      let constFpExpE1 := constFpExp e1 cs
      match constFpExpE, constFpExpE1 with
      | .const c, .const c1 =>
          match wordShiftHOL sh c c1.toNat with
          | some w => .const w
          | none => .shift sh (.const c) (.const c1)
      | _, _ => .shift sh constFpExpE constFpExpE1
  | e, _ => e
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ args›; omega)
    | omega

/-- Exact HOL `const_fp_move_cs_def` (`word_simpScript.sml:215-224`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "const_fp_move_cs_def"
  (words_as_type_indexed_bitvec)]
def constFpMoveCs {width : Nat} [NeZero width] :
    List (Nat × Nat) → Spt (BitVec width) → Spt (BitVec width) → Spt (BitVec width)
  | [], _, cs => cs
  | m :: ms, ocs, ncs =>
      let v := m.1
      let nncs :=
        match sptLookup m.2 ocs with
        | some c => sptInsert v c ncs
        | none => sptDelete v ncs
      constFpMoveCs ms ocs nncs

/-- Exact HOL `const_fp_inst_cs_def` (`word_simpScript.sml:226-246`): every
    clause, positionally on the constructor arguments (so `Load16` and the
    remaining instructions fall to the identity clause, as in HOL), with
    `dimindex (:'a) = 64` as `width = 64`. -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "const_fp_inst_cs_def"
  (words_as_type_indexed_bitvec)]
def constFpInstCs {width : Nat} [NeZero width] :
    WordLangInst (BitVec width) → Spt (BitVec width) → Spt (BitVec width)
  | .const r _, cs => sptDelete r cs
  | .arith (.binop _ r _ _), cs => sptDelete r cs
  | .arith (.shift _ r _ _), cs => sptDelete r cs
  | .arith (.addCarry r1 _ _ r2), cs => sptDelete r2 (sptDelete r1 cs)
  | .arith (.addOverflow r1 _ _ r2), cs => sptDelete r2 (sptDelete r1 cs)
  | .arith (.subOverflow r1 _ _ r2), cs => sptDelete r2 (sptDelete r1 cs)
  | .arith (.longMul r1 r2 _ _), cs => sptDelete r1 (sptDelete r2 cs)
  | .arith (.longDiv r1 r2 _ _ _), cs => sptDelete r1 (sptDelete r2 cs)
  | .arith (.div r1 _ _), cs => sptDelete r1 cs
  | .mem .load r _, cs => sptDelete r cs
  | .mem .load32 r _, cs => sptDelete r cs
  | .mem .load8 r _, cs => sptDelete r cs
  | .fp (.fpLess r _ _), cs => sptDelete r cs
  | .fp (.fpLessEqual r _ _), cs => sptDelete r cs
  | .fp (.fpEqual r _ _), cs => sptDelete r cs
  | .fp (.fpMovToReg r1 r2 _), cs =>
      if width = 64 then sptDelete r1 cs else sptDelete r2 (sptDelete r1 cs)
  | _, cs => cs

/-- Exact HOL `get_var_imm_cs_def` (`word_simpScript.sml:248-251`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "get_var_imm_cs_def"
  (words_as_type_indexed_bitvec)]
def getVarImmCs {width : Nat} [NeZero width] :
    WordRegImm (BitVec width) → Spt (BitVec width) → Option (BitVec width)
  | .reg r, cs => sptLookup r cs
  | .imm i, _ => some i

/-- Exact HOL `all_names_def` (`word_simpScript.sml:258-260`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "all_names_def"]
def allNames {α : Type} (names : Spt α × Spt α) : Spt α :=
  sptUnion names.1 names.2

/-- Exact HOL `drop_consts_def` (`word_simpScript.sml:265-271`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "drop_consts_def"
  (words_as_type_indexed_bitvec)]
def dropConsts {width : Nat} [NeZero width] (cs : Spt (BitVec width)) :
    List Nat → WordLangProgHOL (BitVec width)
  | [] => .skip
  | n :: ns =>
      match sptLookup n cs with
      | none => dropConsts cs ns
      | some w => smartSeqHOL (dropConsts cs ns) (.assign n (.const w))

/-- HOL's local overload `delete_all n l = FOLDR delete l n`
    (`word_simpScript.sml:263`); untagged rendering of an `Overload`. -/
def deleteAll {β : Type} (n : List Nat) (l : Spt β) : Spt β :=
  n.foldr sptDelete l

/-- Exact HOL `const_fp_loop_def` (`word_simpScript.sml:273-340`): every clause
    in source order; the catch-all `(p, cs)` covers `Skip`, `Set`, `Tick`,
    `Raise`, `Return`, `Break`, `Continue` and the buffer writes. -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "const_fp_loop_def"
  (words_as_type_indexed_bitvec)]
def constFpLoop {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → Spt (BitVec width) →
      WordLangProgHOL (BitVec width) × Spt (BitVec width)
  | .move pri moves, cs => (.move pri moves, constFpMoveCs moves cs cs)
  | .inst i, cs => (.inst i, constFpInstCs i cs)
  | .assign v e, cs =>
      let constFpE := constFpExp e cs
      match constFpE with
      | .const c => (.assign v constFpE, sptInsert v c cs)
      | _ => (.assign v constFpE, sptDelete v cs)
  | .get v name, cs => (.get v name, sptDelete v cs)
  | .opCurrHeap b v w, cs => (.opCurrHeap b v w, sptDelete v cs)
  | .mustTerminate p, cs =>
      let (p', cs') := constFpLoop p cs
      (.mustTerminate p', cs')
  | .seq p1 p2, cs =>
      let (p1', cs') := constFpLoop p1 cs
      let (p2', cs'') := constFpLoop p2 cs'
      (.seq p1' p2', cs'')
  | .ite cmp lhs rhs p1 p2, cs =>
      match sptLookup lhs cs, getVarImmCs rhs cs with
      | some clhs, some crhs =>
          if Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp clhs crhs then constFpLoop p1 cs
          else constFpLoop p2 cs
      | _, _ =>
          let (p1', p1cs) := constFpLoop p1 cs
          let (p2', p2cs) := constFpLoop p2 cs
          (.ite cmp lhs rhs p1' p2', sptInterEq p1cs p2cs)
  | .call ret dest args handler, cs =>
      match ret with
      | none =>
          (smartSeqHOL (dropConsts cs args) (.call ret dest args handler),
            sptFilterV isGcConst cs)
      | some (n, names, retHandler, l1, l2) =>
          match handler with
          | none =>
              let cs' := deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names)))
              let (retHandler', cs'') := constFpLoop retHandler cs'
              (smartSeqHOL (dropConsts cs args)
                (.call (some (n, names, retHandler', l1, l2)) dest args handler), cs'')
          | some _ =>
              (smartSeqHOL (dropConsts cs args) (.call ret dest args handler), .ln)
  | .ffi x0 x1 x2 x3 x4 names, cs =>
      (smartSeqHOL (dropConsts cs [x1, x2, x3, x4]) (.ffi x0 x1 x2 x3 x4 names),
        sptInter cs (allNames names))
  | .locValue v x3, cs => (.locValue v x3, sptDelete v cs)
  | .alloc n names, cs =>
      (smartSeqHOL (dropConsts cs [n]) (.alloc n names),
        sptFilterV isGcConst (sptInter cs (allNames names)))
  | .storeConsts a b c d ws, cs =>
      (.storeConsts a b c d ws, sptDelete a (sptDelete b (sptDelete c (sptDelete d cs))))
  | .install r1 r2 r3 r4 names, cs =>
      (smartSeqHOL (dropConsts cs [r1, r2, r3, r4]) (.install r1 r2 r3 r4 names),
        sptDelete r1 (sptFilterV isGcConst (sptInter cs (allNames names))))
  | .store e v, cs => (.store (constFpExp e cs) v, cs)
  | .shareInst .load v e, cs => (.shareInst .load v (constFpExp e cs), sptDelete v cs)
  | .shareInst .load8 v e, cs => (.shareInst .load8 v (constFpExp e cs), sptDelete v cs)
  | .shareInst .load16 v e, cs => (.shareInst .load16 v (constFpExp e cs), sptDelete v cs)
  | .shareInst .load32 v e, cs => (.shareInst .load32 v (constFpExp e cs), sptDelete v cs)
  | .shareInst .store v e, cs => (.shareInst .store v (constFpExp e cs), cs)
  | .shareInst .store8 v e, cs => (.shareInst .store8 v (constFpExp e cs), cs)
  | .shareInst .store16 v e, cs => (.shareInst .store16 v (constFpExp e cs), cs)
  | .shareInst .store32 v e, cs => (.shareInst .store32 v (constFpExp e cs), cs)
  | .loop names body exitNames, _ => (.loop names (constFpLoop body .ln).1 exitNames, .ln)
  | p, cs => (p, cs)

/-- Exact HOL `const_fp_def` (`word_simpScript.sml:342-344`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "const_fp_def"
  (words_as_type_indexed_bitvec)]
def constFp {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  (constFpLoop p .ln).1

/-- Exact HOL `rewrite_duplicate_if_max_reassoc_def` (`word_simpScript.sml:370-372`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "rewrite_duplicate_if_max_reassoc_def"]
def rewriteDuplicateIfMaxReassoc : Nat := 8

/-- Exact HOL `dest_Raise_num_pmatch_def` (`word_simpScript.sml:374-376`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "dest_Raise_num_pmatch_def"
  (words_as_type_indexed_bitvec)]
def destRaiseNum {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Nat
  | .raise n => n
  | _ => 0

/-- Exact HOL `is_simple_pmatch_def` (`word_simpScript.sml:381-388`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "is_simple_pmatch_def"
  (words_as_type_indexed_bitvec)]
def isSimple {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Bool
  | .tick => true
  | .skip => true
  | .move _ _ => true
  | .assign _ _ => true
  | _ => false

/-- Exact HOL `try_if_hoist2_def` (`word_simpScript.sml:393-420`).  HOL's
    `if N = 0n then NONE else ... try_if_hoist2 (N - 1n) ...` is the match on
    `N` with the successor case recursing on its predecessor. -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "try_if_hoist2_def"
  (words_as_type_indexed_bitvec)]
def tryIfHoist2 {width : Nat} [NeZero width] :
    Nat → WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) →
      WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) →
        Option (WordLangProgHOL (BitVec width))
  | 0, _, _, _, _ => none
  | n + 1, p1, interm, dummy, p2 =>
      match p1 with
      | .ite cmp lhs rhs br1 br2 =>
          let res1 := destRaiseNum (destSeq (constFp (.seq (.seq br1 interm) dummy))).2
          if res1 = 0 then none
          else
            let res2 := destRaiseNum (destSeq (constFp (.seq (.seq br2 interm) dummy))).2
            if res1 + res2 ≠ 3 then none
            else some (constFp (.ite cmp lhs rhs (.seq (.seq br1 interm) p2)
              (.seq (.seq br2 interm) p2)))
      | .seq p3 p4 =>
          match destIf p4 with
          | some (cmp, lhs, rhs, br1, br2) =>
              let res1 := destRaiseNum (destSeq (constFp (.seq (.seq br1 interm) dummy))).2
              if res1 = 0 then none
              else
                let res2 := destRaiseNum (destSeq (constFp (.seq (.seq br2 interm) dummy))).2
                if res1 + res2 ≠ 3 then none
                else some (.seq p3 (constFp (.ite cmp lhs rhs (.seq (.seq br1 interm) p2)
                  (.seq (.seq br2 interm) p2))))
          | none =>
              if isSimple p4 then tryIfHoist2 n p3 (.seq p4 interm) dummy p2
              else none
      | _ => none

/-- Exact HOL `try_if_hoist1_def` (`word_simpScript.sml:422-430`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "try_if_hoist1_def"
  (words_as_type_indexed_bitvec)]
def tryIfHoist1 {width : Nat} [NeZero width] (p1 p2 : WordLangProgHOL (BitVec width)) :
    Option (WordLangProgHOL (BitVec width)) :=
  match destIf p2 with
  | none => none
  | some (cmp, lhs, rhs, _, _) =>
      let dummy : WordLangProgHOL (BitVec width) := .ite cmp lhs rhs (.raise 1) (.raise 2)
      tryIfHoist2 rewriteDuplicateIfMaxReassoc p1 .skip dummy p2

/-- Exact HOL `simp_duplicate_if_def` (`word_simpScript.sml:432-459`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "simp_duplicate_if_def"
  (words_as_type_indexed_bitvec)]
def simpDuplicateIf {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .mustTerminate q => .mustTerminate (simpDuplicateIf q)
  | .call retProg dest args handler =>
      .call
        (match retProg with
          | none => none
          | some (x1, x2, q1, x3, x4) => some (x1, x2, simpDuplicateIf q1, x3, x4))
        dest args
        (match handler with
          | none => none
          | some (y1, q2, y2, y3) => some (y1, simpDuplicateIf q2, y2, y3))
  | .ite cmp lhs rhs br1 br2 => .ite cmp lhs rhs (simpDuplicateIf br1) (simpDuplicateIf br2)
  | .seq p1 p2 =>
      let p1x := simpDuplicateIf p1
      let p2x := simpDuplicateIf p2
      match tryIfHoist1 p1x p2x with
      | none => .seq p1x p2x
      | some p3 => seqAssoc .skip p3
  | .loop names body exitNames => .loop names (simpDuplicateIf body) exitNames
  | p => p

/-- Exact HOL `push_out_if_aux_def` (`word_simpScript.sml:461-483`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "push_out_if_aux_def"
  (words_as_type_indexed_bitvec)]
def pushOutIfAux {width : Nat} [NeZero width] :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width) × Bool
  | .mustTerminate q =>
      match pushOutIfAux q with
      | (c, b) => (.mustTerminate c, b)
  | p@(.return _ _) => (p, true)
  | p@(.raise _) => (p, true)
  | p@(.call none _ _ _) => (p, true)
  | .ite cmp r1 ri c1 c2 =>
      match pushOutIfAux c1, pushOutIfAux c2 with
      | (c1', true), (c2', true) => (.ite cmp r1 ri c1' c2', true)
      | (c1', false), (c2', true) => (.seq (.ite cmp r1 ri .skip c2') c1', false)
      | (c1', true), (c2', false) => (.seq (.ite cmp r1 ri c1' .skip) c2', false)
      | (c1', false), (c2', false) => (.ite cmp r1 ri c1' c2', false)
  | .seq c1 c2 =>
      match pushOutIfAux c1 with
      | (c1', true) => (.seq c1' c2, true)
      | (c1', false) =>
          match pushOutIfAux c2 with
          | (c2', b) => (.seq c1' c2', b)
  | .loop names body exitNames => (.loop names (pushOutIfAux body).1 exitNames, false)
  | p => (p, false)

/-- Exact HOL `push_out_if_def` (`word_simpScript.sml:485-487`). -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "push_out_if_def"
  (words_as_type_indexed_bitvec)]
def pushOutIf {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  (pushOutIfAux p).1

/-- Exact HOL `compile_exp_def` (`word_simpScript.sml:491-498`): `Seq_assoc
    Skip`, `const_fp`, `simp_duplicate_if`, then `push_out_if`. -/
@[hol "cakeml/compiler/backend/word_simpScript.sml" "compile_exp_def"
  (words_as_type_indexed_bitvec)]
def compileExp {width : Nat} [NeZero width] (e : WordLangProgHOL (BitVec width)) :
    WordLangProgHOL (BitVec width) :=
  let e := seqAssoc .skip e
  let e := constFp e
  let e := simpDuplicateIf e
  let e := pushOutIf e
  e

end Flapjack.Compiler.Backend.WordSimp
