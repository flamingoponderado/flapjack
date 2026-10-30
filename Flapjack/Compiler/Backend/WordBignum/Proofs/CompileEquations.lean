import Flapjack.Compiler.Backend.WordBignum.Proofs.FuelMonotone

/-! Source-shaped equations for the total executable mini compiler. These
lemmas justify the executable implementation and are Flapjack infrastructure,
not separate HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.WordBignum

private theorem compileFuel_of_bound {width : Nat} [NeZero width] (fuel n l i : Nat)
    (cs : CodeAcc width) (code : Mini (BitVec width)) (bound : miniBudget code < fuel) :
    compileFuel fuel n l i cs code = some (compile n l i cs code) := by
  obtain ⟨result, h⟩ := compileFuel_succeeds fuel n l i cs code bound
  have eq := compile_eq_of_success fuel n l i cs code result h
  simpa [eq] using h

theorem compile_skip {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width) :
    compile n l i cs .skip = (.skip, l, i, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_continue {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width) :
    compile n l i cs .continue = (.call none (some n) [0] none, l, i, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_loopBody {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (body : MiniHOL width) : compile n l i cs (.loopBody body) = compile n l i cs body := by
  apply compile_eq_of_success (miniBudget body + 2)
  have h := compileFuel_of_bound (miniBudget body + 1) n l i cs body (by omega)
  simpa [compileFuel] using h

theorem compile_seq {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (a b : MiniHOL width) :
    compile n l i cs (.seq a b) =
      let (a', la, ia, ca) := compile n l i cs a
      let (b', lb, ib, cb) := compile n la ia ca b
      (.seq a' b', lb, ib, cb) := by
  let fuel := 2 + miniBudget a + miniBudget b
  generalize ha : compile n l i cs a = first
  obtain ⟨a', la, ia, ca⟩ := first
  generalize hb : compile n la ia ca b = second
  obtain ⟨b', lb, ib, cb⟩ := second
  have hfa := compileFuel_of_bound fuel n l i cs a (by dsimp [fuel]; omega)
  have hfb := compileFuel_of_bound fuel n la ia ca b (by dsimp [fuel]; omega)
  rw [ha] at hfa
  rw [hb] at hfb
  apply compile_eq_of_success (fuel + 1)
  simp [compileFuel, hfa, hfb, hb]

theorem compile_ite {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (op : Cmp) (r : Nat) (arg : WordRegImm (BitVec width)) (a b : MiniHOL width) :
    compile n l i cs (.ite op r arg a b) =
      let (a', la, ia, ca) := compile n l i cs a
      let (b', lb, ib, cb) := compile n la ia ca b
      match arg with
      | .reg r2 => (seqTemp ib r (seqTemp (ib + 1) r2 (.ite op ib (.reg (ib + 1)) a' b')),
          lb, ib + 2, cb)
      | .imm w => (seqTemp ib r (.ite op ib (.imm w) a' b'), lb, ib + 1, cb) := by
  let fuel := 2 + miniBudget a + miniBudget b
  generalize ha : compile n l i cs a = first
  obtain ⟨a', la, ia, ca⟩ := first
  generalize hb : compile n la ia ca b = second
  obtain ⟨b', lb, ib, cb⟩ := second
  have hfa := compileFuel_of_bound fuel n l i cs a (by dsimp [fuel]; omega)
  have hfb := compileFuel_of_bound fuel n la ia ca b (by dsimp [fuel]; omega)
  rw [ha] at hfa
  rw [hb] at hfb
  cases arg <;> apply compile_eq_of_success (fuel + 1) <;>
    simp [compileFuel, hfa, hfb, hb]

theorem compile_loop {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (recs : Bool) (live : List Nat) (body : MiniHOL width) :
    compile n l i cs (.loop recs live body) =
      match hasCompiled body cs with
      | .inl existing =>
        (.call (some ([i], (.ls (), .ln), .skip, n, l)) (some existing) [] none, l + 1, i + 1, cs)
      | .inr index =>
        let (body', _, _, cs') := compile index 2 1 (codeAccNext cs) body
        (.call (some ([i], (.ls (), .ln), .skip, n, l)) (some index) [] none,
          l + 1, i + 1, install (body, index, body') cs') := by
  cases hc : hasCompiled body cs with
  | inl existing =>
    apply compile_eq_of_success 1
    simp [compileFuel, hc]
  | inr index =>
    generalize hb : compile index 2 1 (codeAccNext cs) body = result
    obtain ⟨body', label, temp, cs'⟩ := result
    have hfb := compileFuel_of_bound (miniBudget body + 1) index 2 1 (codeAccNext cs) body (by omega)
    rw [hb] at hfb
    apply compile_eq_of_success ((miniBudget body + 1) + 1)
    rw [compileFuel]
    simp [hc, hfb, hb]

theorem compile_recurse {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (save names : List Nat) :
    compile n l i cs (.recurse save names) =
      (loadRegs save (.call (some ([1], (.ls (), sptListInsert (save.map (· + 2)) .ln),
        saveRegs save, n, l)) (some n) [] none), l + 1, i, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_assign {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (j : Nat) (e : WordLangExpHOL (BitVec width)) :
    compile n l i cs (.assign j e) =
      (.seq (.assign i (compileExp e)) (.set (.temp (BitVec.ofNat 5 j)) (.var i)), l, i + 1, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_delete {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (registers : List Nat) : compile n l i cs (.delete registers) = (.skip, l, i, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_swap {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width) :
    compile n l i cs .swap = (.seq (.assign i (.lookup tempIn1))
      (.seq (.set tempIn1 (.lookup tempIn2)) (.set tempIn2 (.var i))), l, i + 1, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_store {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width) (r1 r2 : Nat) :
    compile n l i cs (.store r1 r2) =
      (seqTemp i r1 (seqIndex (i + 1) r2 .out (.store (.var (i + 1)) i)), l, i + 2, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_load {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (r1 r2 : Nat) (arr : Address) :
    compile n l i cs (.load r1 r2 arr) =
      (seqIndex i r2 arr (.seq (.assign (i + 1) (.load (.var i)))
        (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 1)))), l, i + 2, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_add {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (r0 r1 r2 : Nat) (r3 r4 : WordRegImm (BitVec width)) :
    compile n l i cs (.add r0 r1 r2 r3 r4) =
      (seqTempImm (i + 4) r4 (seqTempImm (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 4))))))), l, i + 5, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_sub {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (r0 r1 r2 : Nat) (r3 r4 : WordRegImm (BitVec width)) :
    compile n l i cs (.sub r0 r1 r2 r3 r4) =
      (seqTempImm (i + 4) r4 (seqTempImmNot (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 4))))))), l, i + 5, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_mul {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (r0 r1 r2 r3 : Nat) :
    compile n l i cs (.mul r0 r1 r2 r3) =
      (seqTemp (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.longMul i (i + 1) (i + 2) (i + 3))))
          (.seq (.set (.temp (BitVec.ofNat 5 r1)) (.var i))
            (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))))), l, i + 4, cs) := by
  apply compile_eq_of_success 1
  rfl

theorem compile_div {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (r0 r1 r2 r3 r4 : Nat) :
    compile n l i cs (.div r0 r1 r2 r3 r4) =
      (seqTemp (i + 4) r4 (seqTemp (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (divCode n l i (i + 1) (i + 2) (i + 3) (i + 4))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var i))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 1))))))), l + 1, i + 5, cs) := by
  apply compile_eq_of_success 1
  rfl

end Flapjack.Compiler.Backend.WordBignum
