import Flapjack.Compiler.Backend.Semantics.StackSem.Evaluate

/-! HOL `stackSem$evaluate` and its defining equations `evaluate_def`
(`cakeml/compiler/backend/semantics/stackSemScript.sml:773-1027`) over the exact
`HolProg`/`StackSemStateFiniteExact` carriers.

`evaluate` takes HOL's tupled `(prog, state)` argument and is the assembled
total `evaluateHOL`. `evaluate_def` states all 34 clauses, one conjunct per
constructor in HOL's clause order, each with its own universally quantified
clause variables. Every right-hand side is the source-shaped body of the
reviewed clause fragment, with the recursive calls of `Seq`, `If`, `Loop`,
`JumpLower`, `RawCall` and `Call` written against `evaluate` itself, so the
theorem fixes the evaluator by its equations as HOL's `evaluate_def` does.
HOL's `res = NONE` tests are definitional `none`/`some` splits; HOL's total
equality on the configuration carrier `C` (Install) uses classical decidability.
-/

namespace Flapjack.StackSemEvaluate

open Compiler.Backend.StackLang Compiler.Encoders.Asm StackSemStateOps StackSemControl
open StackSemExpressions StackSemShMem StackSemRegisterTransfers

/-- HOL `stackSem$evaluate` with its tupled `(prog, state)` argument. -/
noncomputable def evaluate {width : Nat} [NeZero width] {C F : Type}
    (ps : HolProg width × StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  evaluateHOL ps.1 ps.2

/-- HOL `evaluate_def` clause for `skip`. -/
theorem evaluate_skip {width : Nat} [NeZero width] {C F : Type} (s : StackSemStateFiniteExact width C F) :
    evaluate ((.skip : HolProg width), s) =
      (none, s) := by
  rw [evaluate, evaluateHOL_skip]
  rfl

/-- HOL `evaluate_def` clause for `halt`. -/
theorem evaluate_halt {width : Nat} [NeZero width] {C F : Type} (v : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.halt v : HolProg width), s) =
      match getVar v s with
      | some w => (some (.halt w), emptyEnv s)
      | none => (some .error, s) := by
  rw [evaluate, evaluateHOL_halt]
  simp only [fromFragment, StackSemLeafTransfers.evaluateLeaf]
  split <;> simp_all

/-- HOL `evaluate_def` clause for `alloc`. -/
theorem evaluate_alloc {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.alloc n : HolProg width), s) =
      if !s.useAlloc then (some .error, s) else
      match getVar n s with
      | some (.word w) => StackSemAllocation.alloc w s
      | _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_alloc]
  rfl

/-- HOL `evaluate_def` clause for `storeConsts`. -/
theorem evaluate_storeConsts {width : Nat} [NeZero width] {C F : Type} (t1 t2 : Nat) (stubOpt : Option Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.storeConsts t1 t2 stubOpt : HolProg width), s) =
      if ¬ s.useStore then (some .error, s)
      else if ¬ s.useAlloc ∧ stubOpt.isSome then (some .error, s)
      else if ¬ StackSemStoreConstsGuard.checkStoreConstsOpt t1 t2 stubOpt s.code then
        (some .error, s)
      else StackSemStoreConsts.storeConstSem t1 t2 s := by
  rw [evaluate, evaluateHOL_storeConsts]
  rfl

/-- HOL `evaluate_def` clause for `inst`. -/
theorem evaluate_inst {width : Nat} [NeZero width] {C F : Type} (i : HolInst width) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.inst i : HolProg width), s) =
      match StackSemInst.instHOL i s with
      | some s1 => (none, s1)
      | none => (some .error, s) := by
  rw [evaluate, evaluateHOL_inst]
  rfl

/-- HOL `evaluate_def` clause for `get`. -/
theorem evaluate_get {width : Nat} [NeZero width] {C F : Type} (v : Nat) (name : StoreName) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.get v name : HolProg width), s) =
      if ¬s.useStore then (some .error, s) else
      match s.store.lookup (storeOfSyntax name) with
      | some x => (none, setVar v x s)
      | none => (some .error, s) := by
  rw [evaluate, evaluateHOL_get]
  simp only [fromFragment, evaluateRegister]
  split
  · rfl
  · split <;> simp_all

/-- HOL `evaluate_def` clause for `set`. -/
theorem evaluate_set {width : Nat} [NeZero width] {C F : Type} (name : StoreName) (v : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.set name v : HolProg width), s) =
      if ¬s.useStore then (some .error, s) else
      match getVar v s with
      | some w => (none, setStore (storeOfSyntax name) w s)
      | none => (some .error, s) := by
  rw [evaluate, evaluateHOL_set]
  simp only [fromFragment, evaluateRegister]
  split
  · rfl
  · split <;> simp_all

/-- HOL `evaluate_def` clause for `opCurrHeap`. -/
theorem evaluate_opCurrHeap {width : Nat} [NeZero width] {C F : Type} (binop : HolBinop) (v src : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.opCurrHeap binop v src : HolProg width), s) =
      if ¬s.useStore then (some .error, s) else
      match wordExp s (.op binop [.var src, .lookup .currHeap]) with
      | some w => (none, setVar v (.word w) s)
      | none => (some .error, s) := by
  rw [evaluate, evaluateHOL_opCurrHeap]
  simp only [fromFragment, evaluateRegister]
  split
  · rfl
  · split <;> simp_all

/-- HOL `evaluate_def` clause for `tick`. -/
theorem evaluate_tick {width : Nat} [NeZero width] {C F : Type} (s : StackSemStateFiniteExact width C F) :
    evaluate ((.tick : HolProg width), s) =
      if s.clock = 0 then (some .timeOut, emptyEnv s)
      else (none, decClock s) := by
  rw [evaluate, evaluateHOL_tick]
  simp only [fromFragment, StackSemLeafTransfers.evaluateLeaf]
  split <;> rfl

/-- HOL `evaluate_def` clause for `seq`. -/
theorem evaluate_seq {width : Nat} [NeZero width] {C F : Type} (c1 c2 : HolProg width) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.seq c1 c2 : HolProg width), s) =
      match fixClock s (evaluate (c1, s)) with
      | (none, s1) => evaluate (c2, s1)
      | (res, s1) => (res, s1) := by
  rw [evaluate, evaluateHOL_seq]
  rfl

/-- HOL `evaluate_def` clause for `ret`. -/
theorem evaluate_ret {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.ret n : HolProg width), s) =
      match getVar n s with
      | some (.loc l1 l2) => (some (.result (.loc l1 l2)), s)
      | _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_ret]
  simp only [fromFragment, StackSemLeafTransfers.evaluateLeaf]
  split <;> simp_all

/-- HOL `evaluate_def` clause for `raise`. -/
theorem evaluate_raise {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.raise n : HolProg width), s) =
      match getVar n s with
      | some (.loc l1 l2) => (some (.exception (.loc l1 l2)), s)
      | _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_raise]
  simp only [fromFragment, StackSemLeafTransfers.evaluateLeaf]
  split <;> simp_all

/-- HOL `evaluate_def` clause for `break`. -/
theorem evaluate_break {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.break n : HolProg width), s) =
      (some (.break n), s) := by
  rw [evaluate, evaluateHOL_break]
  rfl

/-- HOL `evaluate_def` clause for `continue`. -/
theorem evaluate_continue {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.continue n : HolProg width), s) =
      (some (.continue n), s) := by
  rw [evaluate, evaluateHOL_continue]
  rfl

/-- HOL `evaluate_def` clause for `ite`. -/
theorem evaluate_ite {width : Nat} [NeZero width] {C F : Type} (cmp : Cmp) (r1 : Nat) (ri : HolRegImm width) (c1 c2 : HolProg width) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.ite cmp r1 ri c1 c2 : HolProg width), s) =
      match getVar r1 s, StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
      | some x, some y =>
          match wordSemWordCmp cmp x y with
          | some true => evaluate (c1, s)
          | some false => evaluate (c2, s)
          | none => (some .error, s)
      | _, _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_ite]
  rfl

/-- HOL `evaluate_def` clause for `loop`. -/
theorem evaluate_loop {width : Nat} [NeZero width] {C F : Type} (c1 : HolProg width) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.loop c1 : HolProg width), s) =
      match fixClock s (evaluate (c1, s)) with
      | (res, s1) =>
          if StackSemControl.contLoop res then
            (if s1.clock = 0 then (some .timeOut, emptyEnv s1)
             else evaluate (.loop c1, decClock s1))
          else (StackSemControl.exitLoop res, s1) := by
  rw [evaluate, evaluateHOL_loop]
  rfl

/-- HOL `evaluate_def` clause for `jumpLower`. -/
theorem evaluate_jumpLower {width : Nat} [NeZero width] {C F : Type} (r1 r2 dest : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.jumpLower r1 r2 dest : HolProg width), s) =
      match getVar r1 s, getVar r2 s with
      | some (.word x), some (.word y) =>
          if wordCmpHOL .lower x y then
            match findCode (.inl dest) s.regs s.code with
            | none => (some .error, s)
            | some prog =>
                if s.clock = 0 then (some .timeOut, emptyEnv s)
                else
                  match evaluate (prog, decClock s) with
                  | (res, s') => if badFunReturn res then (some .error, s') else (res, s')
          else (none, s)
      | _, _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_jumpLower]
  rfl

/-- HOL `evaluate_def` clause for `rawCall`. -/
theorem evaluate_rawCall {width : Nat} [NeZero width] {C F : Type} (dest : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.rawCall dest : HolProg width), s) =
      match sptLookup dest s.code with
      | none => (some .error, s)
      | some prog =>
          match destSeq prog with
          | some (_, body) =>
              if s.clock = 0 then (some .timeOut, emptyEnv s)
              else
                match evaluate (body, decClock s) with
                | (res, s') => if badFunReturn res then (some .error, s') else (res, s')
          | none => (some .error, s) := by
  rw [evaluate, evaluateHOL_rawCall]
  rfl

/-- HOL `evaluate_def` clause for `call`. -/
theorem evaluate_call {width : Nat} [NeZero width] {C F : Type} (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.call ret dest handler : HolProg width), s) =
      match ret with
      | none =>
          match findCode dest s.regs s.code with
          | none => (some .error, s)
          | some prog =>
              match handler with
              | some _ => (some .error, s)
              | none =>
                  if s.clock = 0 then (some .timeOut, emptyEnv s)
                  else
                    match fixClock (decClock s) (evaluate (prog, decClock s)) with
                    | (res, s2) =>
                        if badFunReturn res then (some .error, s2) else (res, s2)
      | some (ret_handler, link_reg, l1, l2) =>
          match findCode dest (s.regs.eraseEq link_reg) s.code with
          | none => (some .error, s)
          | some prog =>
              if s.clock = 0 then (some .timeOut, emptyEnv s)
              else
                let s' := setVar link_reg (.loc l1 l2) s
                match fixClock (decClock s') (evaluate (prog, decClock s')) with
                | (some (.result x), s2) =>
                    if x ≠ .loc l1 l2 then (some .error, s2)
                    else evaluate (ret_handler, s2)
                | (some (.exception x), s2) =>
                    match handler with
                    | none => (some (.exception x), s2)
                    | some (h, hl1, hl2) =>
                        if x ≠ .loc hl1 hl2 then (some .error, s2)
                        else evaluate (h, s2)
                | (none, s2) => (some .error, s2)
                | (some (.break _), s2) => (some .error, s2)
                | (some (.continue _), s2) => (some .error, s2)
                | (res, s2) => (res, s2) := by
  rw [evaluate, evaluateHOL_call]
  rfl

open Classical in
/-- HOL `evaluate_def` clause for `install`. -/
theorem evaluate_install {width : Nat} [NeZero width] {C F : Type} (ptr len dptr dlen ret : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.install ptr len dptr dlen ret : HolProg width), s) =
      match getVar ptr s, getVar len s, getVar dptr s, getVar dlen s with
      | some (.word w1), some (.word w2), some (.word w3), some (.word w4) =>
          let (cfg, progs, bm) := s.compileOracle 0
          match wordSemBufferFlush s.codeBuffer w1 w2,
                (if s.useStack then wordSemBufferFlush s.dataBuffer w3 w4
                 else some (bm, s.dataBuffer)) with
          | some (bytes, cb), some (data, db) =>
              let newOracle := holShiftSeq 1 s.compileOracle
              match s.compile cfg progs, progs with
              | some (bytes', cfg'), (k, _prog) :: _ =>
                  if bytes = bytes' ∧ data = bm ∧ (newOracle 0).1 = cfg' then
                    (none, { s with
                      bitmaps := s.bitmaps ++ bm
                      codeBuffer := cb
                      dataBuffer := db
                      code := sptUnion s.code (sptFromAList progs)
                      regs := (restrictIn s.regs s.ffiSaveRegs).updateEq (ptr, .loc k 0)
                      fpRegs := HolFiniteMapExact.empty
                      compileOracle := newOracle })
                  else (some .error, s)
              | _, _ => (some .error, s)
          | _, _ => (some .error, s)
      | _, _, _, _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_install]
  rfl

/-- HOL `evaluate_def` clause for `shMemOp`. -/
theorem evaluate_shMemOp {width : Nat} [NeZero width] {C F : Type} (op : HolMemop) (r a : Nat) (w : BitVec width) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.shMemOp op r (.addr a w) : HolProg width), s) =
      match wordExp s (.op .add [.var a, .const w]) with
      | some a' => if s.clock = 0 then (some .timeOut, emptyEnv s)
                   else shMemOp op r a' (decClock s)
      | none => (some .error, s) := by
  rw [evaluate, evaluateHOL_shMemOp]
  rfl

/-- HOL `evaluate_def` clause for `codeBufferWrite`. -/
theorem evaluate_codeBufferWrite {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.codeBufferWrite r1 r2 : HolProg width), s) =
      match getVar r1 s, getVar r2 s with
      | some (.word w1), some (.word w2) =>
          match wordSemBufferWrite s.codeBuffer w1 (w2.setWidth 8) with
          | some newCb => (none, { s with codeBuffer := newCb })
          | none => (some .error, s)
      | _, _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_codeBufferWrite]
  rfl

/-- HOL `evaluate_def` clause for `dataBufferWrite`. -/
theorem evaluate_dataBufferWrite {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.dataBufferWrite r1 r2 : HolProg width), s) =
      if ¬s.useStack then (some .error, s) else
      match getVar r1 s, getVar r2 s with
      | some (.word w1), some (.word w2) =>
          match wordSemBufferWrite s.dataBuffer w1 w2 with
          | some newDb => (none, { s with dataBuffer := newDb })
          | none => (some .error, s)
      | _, _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_dataBufferWrite]
  rfl

/-- HOL `evaluate_def` clause for `ffi`. -/
theorem evaluate_ffi {width : Nat} [NeZero width] {C F : Type} (ffiIndex : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluate ((.ffi ffiIndex ptr len ptr2 len2 ret : HolProg width), s) =
      match getVar len s, getVar ptr s, getVar len2 s, getVar ptr2 s with
      | some (.word w), some (.word w2), some (.word w3), some (.word w4) =>
          match readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact s.memory s.mdomain s.be),
                readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
          | some bytes, some bytes2 =>
              match callFFIHOL s.ffi (.extCall ffiIndex) bytes bytes2 with
              | .final outcome => (some (.finalFFI outcome), s)
              | .ret newFfi newBytes =>
                  (none, { s with
                    memory := writeBytearrayExact w4 newBytes s.memory s.mdomain s.be
                    regs := restrictIn s.regs s.ffiSaveRegs
                    fpRegs := HolFiniteMapExact.empty
                    ffi := newFfi })
          | _, _ => (some .error, s)
      | _, _, _, _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_ffi]
  rfl

open Classical in
/-- HOL `evaluate_def` clause for `locValue`. -/
theorem evaluate_locValue {width : Nat} [NeZero width] {C F : Type} (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.locValue r l1 l2 : HolProg width), s) =
      if StackSem.locCheckExact s.code (l1, l2) then (none, setVar r (.loc l1 l2) s)
      else (some .error, s) := by
  rw [evaluate, evaluateHOL_locValue]
  rfl

/-- HOL `evaluate_def` clause for `stackAlloc`. -/
theorem evaluate_stackAlloc {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.stackAlloc n : HolProg width), s) =
      if !s.useStack then (some .error, s)
      else if s.stackSpace < n then (some (.halt (.word (BitVec.ofNat width 2))), emptyEnv s)
      else (none, { s with stackSpace := s.stackSpace - n }) := by
  rw [evaluate, evaluateHOL_stackAlloc]
  rfl

/-- HOL `evaluate_def` clause for `stackFree`. -/
theorem evaluate_stackFree {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.stackFree n : HolProg width), s) =
      if !s.useStack then (some .error, s)
      else if s.stack.length < s.stackSpace + n then (some .error, emptyEnv s)
      else (none, { s with stackSpace := s.stackSpace + n }) := by
  rw [evaluate, evaluateHOL_stackFree]
  rfl

/-- HOL `evaluate_def` clause for `stackLoad`. -/
theorem evaluate_stackLoad {width : Nat} [NeZero width] {C F : Type} (r n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.stackLoad r n : HolProg width), s) =
      if !s.useStack then (some .error, s)
      else if h : s.stackSpace + n < s.stack.length then
        (none, setVar r s.stack[s.stackSpace + n] s)
      else (some .error, emptyEnv s) := by
  rw [evaluate, evaluateHOL_stackLoad]
  rfl

/-- HOL `evaluate_def` clause for `stackLoadAny`. -/
theorem evaluate_stackLoadAny {width : Nat} [NeZero width] {C F : Type} (r rn : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.stackLoadAny r rn : HolProg width), s) =
      if !s.useStack then (some .error, s)
      else match getVar rn s with
        | some (.word w) =>
          let shifted := w >>> wordShiftAmount width
          let i := s.stackSpace + shifted.toNat
          if h : i < s.stack.length ∧ shifted <<< wordShiftAmount width = w then
            (none, setVar r (s.stack[i]'h.1) s)
          else (some .error, emptyEnv s)
        | _ => (some .error, emptyEnv s) := by
  rw [evaluate, evaluateHOL_stackLoadAny]
  rfl

/-- HOL `evaluate_def` clause for `stackStore`. -/
theorem evaluate_stackStore {width : Nat} [NeZero width] {C F : Type} (r n : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.stackStore r n : HolProg width), s) =
      if !s.useStack then (some .error, s)
      else if s.stack.length ≤ s.stackSpace + n then (some .error, emptyEnv s)
      else match getVar r s with
        | none => (some .error, emptyEnv s)
        | some value => (none, { s with stack := s.stack.set (s.stackSpace + n) value }) := by
  rw [evaluate, evaluateHOL_stackStore]
  rfl

/-- HOL `evaluate_def` clause for `stackStoreAny`. -/
theorem evaluate_stackStoreAny {width : Nat} [NeZero width] {C F : Type} (r rn : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.stackStoreAny r rn : HolProg width), s) =
      if !s.useStack then (some .error, s)
      else match getVar r s, getVar rn s with
        | some value, some (.word w) =>
          let shifted := w >>> wordShiftAmount width
          let i := s.stackSpace + shifted.toNat
          if i < s.stack.length ∧ shifted <<< wordShiftAmount width = w then
            (none, { s with stack := s.stack.set i value })
          else (some .error, emptyEnv s)
        | _, _ => (some .error, emptyEnv s) := by
  rw [evaluate, evaluateHOL_stackStoreAny]
  rfl

/-- HOL `evaluate_def` clause for `stackGetSize`. -/
theorem evaluate_stackGetSize {width : Nat} [NeZero width] {C F : Type} (r : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.stackGetSize r : HolProg width), s) =
      if !s.useStack then (some .error, s)
      else (none, setVar r (.word (BitVec.ofNat width s.stackSpace)) s) := by
  rw [evaluate, evaluateHOL_stackGetSize]
  rfl

/-- HOL `evaluate_def` clause for `stackSetSize`. -/
theorem evaluate_stackSetSize {width : Nat} [NeZero width] {C F : Type} (r : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.stackSetSize r : HolProg width), s) =
      if !s.useStack then (some .error, s)
      else match getVar r s with
        | some (.word word) =>
            if s.stack.length ≤ word.toNat then (some .error, emptyEnv s)
            else (none, setVar r (.word (word <<< wordShiftAmount width))
              {s with stackSpace := word.toNat})
        | _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_stackSetSize]
  rfl

/-- HOL `evaluate_def` clause for `bitmapLoad`. -/
theorem evaluate_bitmapLoad {width : Nat} [NeZero width] {C F : Type} (r v : Nat) (s : StackSemStateFiniteExact width C F) :
    evaluate ((.bitmapLoad r v : HolProg width), s) =
      if !s.useStack || r == v then (some .error, s)
      else match getVar v s with
        | some (.word word) =>
            if h : s.bitmaps.length ≤ word.toNat then (some .error, s)
            else (none, setVar r (.word s.bitmaps[word.toNat]) s)
        | _ => (some .error, s) := by
  rw [evaluate, evaluateHOL_bitmapLoad]
  rfl

/-- Holds the canonical finite-support codec for the owning state carrier, as
required by the `fmap_as_finite_support` qualifier of `evaluate_def`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

open Classical in
/-- HOL `evaluate_def` (`stackSemScript.sml:773-1027`): the 34 defining clauses of
`stackSem$evaluate`, in HOL's clause order, over the exact `HolProg` and
`StackSemStateFiniteExact` carriers (`regs`, `fpRegs` and `store` are the
canonical finite-support maps). Each conjunct is the corresponding
`evaluate_*` clause theorem above. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "evaluate_def" 773
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_def {width : Nat} [NeZero width] {C F : Type} :
    (∀ (s : StackSemStateFiniteExact width C F),
        evaluate ((.skip : HolProg width), s) =
          (none, s)) ∧
    (∀ (v : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.halt v : HolProg width), s) =
          match getVar v s with
          | some w => (some (.halt w), emptyEnv s)
          | none => (some .error, s)) ∧
    (∀ (n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.alloc n : HolProg width), s) =
          if !s.useAlloc then (some .error, s) else
          match getVar n s with
          | some (.word w) => StackSemAllocation.alloc w s
          | _ => (some .error, s)) ∧
    (∀ (t1 t2 : Nat) (stubOpt : Option Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.storeConsts t1 t2 stubOpt : HolProg width), s) =
          if ¬ s.useStore then (some .error, s)
          else if ¬ s.useAlloc ∧ stubOpt.isSome then (some .error, s)
          else if ¬ StackSemStoreConstsGuard.checkStoreConstsOpt t1 t2 stubOpt s.code then
            (some .error, s)
          else StackSemStoreConsts.storeConstSem t1 t2 s) ∧
    (∀ (i : HolInst width) (s : StackSemStateFiniteExact width C F),
        evaluate ((.inst i : HolProg width), s) =
          match StackSemInst.instHOL i s with
          | some s1 => (none, s1)
          | none => (some .error, s)) ∧
    (∀ (v : Nat) (name : StoreName) (s : StackSemStateFiniteExact width C F),
        evaluate ((.get v name : HolProg width), s) =
          if ¬s.useStore then (some .error, s) else
          match s.store.lookup (storeOfSyntax name) with
          | some x => (none, setVar v x s)
          | none => (some .error, s)) ∧
    (∀ (name : StoreName) (v : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.set name v : HolProg width), s) =
          if ¬s.useStore then (some .error, s) else
          match getVar v s with
          | some w => (none, setStore (storeOfSyntax name) w s)
          | none => (some .error, s)) ∧
    (∀ (binop : HolBinop) (v src : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.opCurrHeap binop v src : HolProg width), s) =
          if ¬s.useStore then (some .error, s) else
          match wordExp s (.op binop [.var src, .lookup .currHeap]) with
          | some w => (none, setVar v (.word w) s)
          | none => (some .error, s)) ∧
    (∀ (s : StackSemStateFiniteExact width C F),
        evaluate ((.tick : HolProg width), s) =
          if s.clock = 0 then (some .timeOut, emptyEnv s)
          else (none, decClock s)) ∧
    (∀ (c1 c2 : HolProg width) (s : StackSemStateFiniteExact width C F),
        evaluate ((.seq c1 c2 : HolProg width), s) =
          match fixClock s (evaluate (c1, s)) with
          | (none, s1) => evaluate (c2, s1)
          | (res, s1) => (res, s1)) ∧
    (∀ (n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.ret n : HolProg width), s) =
          match getVar n s with
          | some (.loc l1 l2) => (some (.result (.loc l1 l2)), s)
          | _ => (some .error, s)) ∧
    (∀ (n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.raise n : HolProg width), s) =
          match getVar n s with
          | some (.loc l1 l2) => (some (.exception (.loc l1 l2)), s)
          | _ => (some .error, s)) ∧
    (∀ (n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.break n : HolProg width), s) =
          (some (.break n), s)) ∧
    (∀ (n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.continue n : HolProg width), s) =
          (some (.continue n), s)) ∧
    (∀ (cmp : Cmp) (r1 : Nat) (ri : HolRegImm width) (c1 c2 : HolProg width) (s : StackSemStateFiniteExact width C F),
        evaluate ((.ite cmp r1 ri c1 c2 : HolProg width), s) =
          match getVar r1 s, StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
          | some x, some y =>
              match wordSemWordCmp cmp x y with
              | some true => evaluate (c1, s)
              | some false => evaluate (c2, s)
              | none => (some .error, s)
          | _, _ => (some .error, s)) ∧
    (∀ (c1 : HolProg width) (s : StackSemStateFiniteExact width C F),
        evaluate ((.loop c1 : HolProg width), s) =
          match fixClock s (evaluate (c1, s)) with
          | (res, s1) =>
              if StackSemControl.contLoop res then
                (if s1.clock = 0 then (some .timeOut, emptyEnv s1)
                 else evaluate (.loop c1, decClock s1))
              else (StackSemControl.exitLoop res, s1)) ∧
    (∀ (r1 r2 dest : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.jumpLower r1 r2 dest : HolProg width), s) =
          match getVar r1 s, getVar r2 s with
          | some (.word x), some (.word y) =>
              if wordCmpHOL .lower x y then
                match findCode (.inl dest) s.regs s.code with
                | none => (some .error, s)
                | some prog =>
                    if s.clock = 0 then (some .timeOut, emptyEnv s)
                    else
                      match evaluate (prog, decClock s) with
                      | (res, s') => if badFunReturn res then (some .error, s') else (res, s')
              else (none, s)
          | _, _ => (some .error, s)) ∧
    (∀ (dest : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.rawCall dest : HolProg width), s) =
          match sptLookup dest s.code with
          | none => (some .error, s)
          | some prog =>
              match destSeq prog with
              | some (_, body) =>
                  if s.clock = 0 then (some .timeOut, emptyEnv s)
                  else
                    match evaluate (body, decClock s) with
                    | (res, s') => if badFunReturn res then (some .error, s') else (res, s')
              | none => (some .error, s)) ∧
    (∀ (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat)) (s : StackSemStateFiniteExact width C F),
        evaluate ((.call ret dest handler : HolProg width), s) =
          match ret with
          | none =>
              match findCode dest s.regs s.code with
              | none => (some .error, s)
              | some prog =>
                  match handler with
                  | some _ => (some .error, s)
                  | none =>
                      if s.clock = 0 then (some .timeOut, emptyEnv s)
                      else
                        match fixClock (decClock s) (evaluate (prog, decClock s)) with
                        | (res, s2) =>
                            if badFunReturn res then (some .error, s2) else (res, s2)
          | some (ret_handler, link_reg, l1, l2) =>
              match findCode dest (s.regs.eraseEq link_reg) s.code with
              | none => (some .error, s)
              | some prog =>
                  if s.clock = 0 then (some .timeOut, emptyEnv s)
                  else
                    let s' := setVar link_reg (.loc l1 l2) s
                    match fixClock (decClock s') (evaluate (prog, decClock s')) with
                    | (some (.result x), s2) =>
                        if x ≠ .loc l1 l2 then (some .error, s2)
                        else evaluate (ret_handler, s2)
                    | (some (.exception x), s2) =>
                        match handler with
                        | none => (some (.exception x), s2)
                        | some (h, hl1, hl2) =>
                            if x ≠ .loc hl1 hl2 then (some .error, s2)
                            else evaluate (h, s2)
                    | (none, s2) => (some .error, s2)
                    | (some (.break _), s2) => (some .error, s2)
                    | (some (.continue _), s2) => (some .error, s2)
                    | (res, s2) => (res, s2)) ∧
    (∀ (ptr len dptr dlen ret : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.install ptr len dptr dlen ret : HolProg width), s) =
          match getVar ptr s, getVar len s, getVar dptr s, getVar dlen s with
          | some (.word w1), some (.word w2), some (.word w3), some (.word w4) =>
              let (cfg, progs, bm) := s.compileOracle 0
              match wordSemBufferFlush s.codeBuffer w1 w2,
                    (if s.useStack then wordSemBufferFlush s.dataBuffer w3 w4
                     else some (bm, s.dataBuffer)) with
              | some (bytes, cb), some (data, db) =>
                  let newOracle := holShiftSeq 1 s.compileOracle
                  match s.compile cfg progs, progs with
                  | some (bytes', cfg'), (k, _prog) :: _ =>
                      if bytes = bytes' ∧ data = bm ∧ (newOracle 0).1 = cfg' then
                        (none, { s with
                          bitmaps := s.bitmaps ++ bm
                          codeBuffer := cb
                          dataBuffer := db
                          code := sptUnion s.code (sptFromAList progs)
                          regs := (restrictIn s.regs s.ffiSaveRegs).updateEq (ptr, .loc k 0)
                          fpRegs := HolFiniteMapExact.empty
                          compileOracle := newOracle })
                      else (some .error, s)
                  | _, _ => (some .error, s)
              | _, _ => (some .error, s)
          | _, _, _, _ => (some .error, s)) ∧
    (∀ (op : HolMemop) (r a : Nat) (w : BitVec width) (s : StackSemStateFiniteExact width C F),
        evaluate ((.shMemOp op r (.addr a w) : HolProg width), s) =
          match wordExp s (.op .add [.var a, .const w]) with
          | some a' => if s.clock = 0 then (some .timeOut, emptyEnv s)
                       else shMemOp op r a' (decClock s)
          | none => (some .error, s)) ∧
    (∀ (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.codeBufferWrite r1 r2 : HolProg width), s) =
          match getVar r1 s, getVar r2 s with
          | some (.word w1), some (.word w2) =>
              match wordSemBufferWrite s.codeBuffer w1 (w2.setWidth 8) with
              | some newCb => (none, { s with codeBuffer := newCb })
              | none => (some .error, s)
          | _, _ => (some .error, s)) ∧
    (∀ (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.dataBufferWrite r1 r2 : HolProg width), s) =
          if ¬s.useStack then (some .error, s) else
          match getVar r1 s, getVar r2 s with
          | some (.word w1), some (.word w2) =>
              match wordSemBufferWrite s.dataBuffer w1 w2 with
              | some newDb => (none, { s with dataBuffer := newDb })
              | none => (some .error, s)
          | _, _ => (some .error, s)) ∧
    (∀ (ffiIndex : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.ffi ffiIndex ptr len ptr2 len2 ret : HolProg width), s) =
          match getVar len s, getVar ptr s, getVar len2 s, getVar ptr2 s with
          | some (.word w), some (.word w2), some (.word w3), some (.word w4) =>
              match readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact s.memory s.mdomain s.be),
                    readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
              | some bytes, some bytes2 =>
                  match callFFIHOL s.ffi (.extCall ffiIndex) bytes bytes2 with
                  | .final outcome => (some (.finalFFI outcome), s)
                  | .ret newFfi newBytes =>
                      (none, { s with
                        memory := writeBytearrayExact w4 newBytes s.memory s.mdomain s.be
                        regs := restrictIn s.regs s.ffiSaveRegs
                        fpRegs := HolFiniteMapExact.empty
                        ffi := newFfi })
              | _, _ => (some .error, s)
          | _, _, _, _ => (some .error, s)) ∧
    (∀ (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.locValue r l1 l2 : HolProg width), s) =
          if StackSem.locCheckExact s.code (l1, l2) then (none, setVar r (.loc l1 l2) s)
          else (some .error, s)) ∧
    (∀ (n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.stackAlloc n : HolProg width), s) =
          if !s.useStack then (some .error, s)
          else if s.stackSpace < n then (some (.halt (.word (BitVec.ofNat width 2))), emptyEnv s)
          else (none, { s with stackSpace := s.stackSpace - n })) ∧
    (∀ (n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.stackFree n : HolProg width), s) =
          if !s.useStack then (some .error, s)
          else if s.stack.length < s.stackSpace + n then (some .error, emptyEnv s)
          else (none, { s with stackSpace := s.stackSpace + n })) ∧
    (∀ (r n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.stackLoad r n : HolProg width), s) =
          if !s.useStack then (some .error, s)
          else if h : s.stackSpace + n < s.stack.length then
            (none, setVar r s.stack[s.stackSpace + n] s)
          else (some .error, emptyEnv s)) ∧
    (∀ (r rn : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.stackLoadAny r rn : HolProg width), s) =
          if !s.useStack then (some .error, s)
          else match getVar rn s with
            | some (.word w) =>
              let shifted := w >>> wordShiftAmount width
              let i := s.stackSpace + shifted.toNat
              if h : i < s.stack.length ∧ shifted <<< wordShiftAmount width = w then
                (none, setVar r (s.stack[i]'h.1) s)
              else (some .error, emptyEnv s)
            | _ => (some .error, emptyEnv s)) ∧
    (∀ (r n : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.stackStore r n : HolProg width), s) =
          if !s.useStack then (some .error, s)
          else if s.stack.length ≤ s.stackSpace + n then (some .error, emptyEnv s)
          else match getVar r s with
            | none => (some .error, emptyEnv s)
            | some value => (none, { s with stack := s.stack.set (s.stackSpace + n) value })) ∧
    (∀ (r rn : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.stackStoreAny r rn : HolProg width), s) =
          if !s.useStack then (some .error, s)
          else match getVar r s, getVar rn s with
            | some value, some (.word w) =>
              let shifted := w >>> wordShiftAmount width
              let i := s.stackSpace + shifted.toNat
              if i < s.stack.length ∧ shifted <<< wordShiftAmount width = w then
                (none, { s with stack := s.stack.set i value })
              else (some .error, emptyEnv s)
            | _, _ => (some .error, emptyEnv s)) ∧
    (∀ (r : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.stackGetSize r : HolProg width), s) =
          if !s.useStack then (some .error, s)
          else (none, setVar r (.word (BitVec.ofNat width s.stackSpace)) s)) ∧
    (∀ (r : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.stackSetSize r : HolProg width), s) =
          if !s.useStack then (some .error, s)
          else match getVar r s with
            | some (.word word) =>
                if s.stack.length ≤ word.toNat then (some .error, emptyEnv s)
                else (none, setVar r (.word (word <<< wordShiftAmount width))
                  {s with stackSpace := word.toNat})
            | _ => (some .error, s)) ∧
    (∀ (r v : Nat) (s : StackSemStateFiniteExact width C F),
        evaluate ((.bitmapLoad r v : HolProg width), s) =
          if !s.useStack || r == v then (some .error, s)
          else match getVar v s with
            | some (.word word) =>
                if h : s.bitmaps.length ≤ word.toNat then (some .error, s)
                else (none, setVar r (.word s.bitmaps[word.toNat]) s)
            | _ => (some .error, s)) :=
  ⟨evaluate_skip, evaluate_halt, evaluate_alloc, evaluate_storeConsts, evaluate_inst, evaluate_get, evaluate_set, evaluate_opCurrHeap, evaluate_tick, evaluate_seq, evaluate_ret, evaluate_raise, evaluate_break, evaluate_continue, evaluate_ite, evaluate_loop, evaluate_jumpLower, evaluate_rawCall, evaluate_call, evaluate_install, evaluate_shMemOp, evaluate_codeBufferWrite, evaluate_dataBufferWrite, evaluate_ffi, evaluate_locValue, evaluate_stackAlloc, evaluate_stackFree, evaluate_stackLoad, evaluate_stackLoadAny, evaluate_stackStore, evaluate_stackStoreAny, evaluate_stackGetSize, evaluate_stackSetSize, evaluate_bitmapLoad⟩

end Flapjack.StackSemEvaluate
