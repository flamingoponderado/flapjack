module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.AuxLemma
public import Flapjack.Compiler.Backend.WordBignum.Generate

@[expose] public section

/-! Evaluation support for `generated_bignum_stubs_eq`: Flapjack-only proof
infrastructure, no HOL counterpart.

HOL proves `generated_bignum_stubs_eq` by `EVAL` at an arbitrary word dimension.
Lean's kernel cannot run `compile` at a symbolic `width` directly: its cache
lookup `hasCompiled` decides equality of mini-programs whose `BitVec width`
constants do not reduce, and the well-founded `compileExp` recursion measures
those constants. This module defines `compileFuelK`, the same compiler with a
structural expression translation and a cache lookup that compares programs
with their word constants erased (`skel`), and proves that it agrees with
`compileFuel` whenever every pair of cached loop bodies with equal skeletons is
equal. For `mcIopCode` that separation is checked on the width-independent
`Mini Nat` program it is the image of. The kernel then evaluates
`generatedBignumStubsK`, which never inspects a word constant. -/

namespace Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq
open Flapjack

open Lean Elab Tactic Meta in
/-- Close an equation goal `lhs = rhs` by kernel definitional unfolding only:
the goal, with its local context reverted, becomes an auxiliary theorem whose
proof is `Eq.refl lhs` and which only the kernel checks (as `decide +kernel`
does for a closed decidable proposition). -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let (_, goal) ← goal.revert (clearAuxDeclsInsteadOfRevert := true)
    (← goal.getDecl).lctx.getFVarIds
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    if type.hasMVar then
      throwError "kernel_rfl: the goal contains metavariables"
    let proof ← forallTelescope type fun xs body => do
      let some (_, lhs, _) := body.eq? | throwError "kernel_rfl: the goal is not an equation"
      mkLambdaFVars xs (← mkEqRefl lhs)
    let levelsInType := (collectLevelParams {} type).params
    let levels := (← Term.getLevelNames).reverse.filter levelsInType.contains
    let name ← withOptions (Elab.async.set · false) do
      mkAuxLemma levels type proof
    goal.assign (mkConst name (levels.map .param))
  replaceMainGoal []

/-! ### Constant maps and skeletons -/

mutual
/-- Map the word constants of an expression. -/
def expMap {α β : Type} (f : α → β) : WordLangExpHOL α → WordLangExpHOL β
  | .const v => .const (f v)
  | .var n => .var n
  | .lookup s => .lookup s
  | .load a => .load (expMap f a)
  | .op o xs => .op o (expListMap f xs)
  | .shift s a b => .shift s (expMap f a) (expMap f b)
termination_by structural e => e

/-- Map the word constants of a list of expressions. -/
def expListMap {α β : Type} (f : α → β) : List (WordLangExpHOL α) → List (WordLangExpHOL β)
  | [] => []
  | x :: xs => expMap f x :: expListMap f xs
termination_by structural xs => xs
end

/-- Map the word constant of a register-or-immediate operand. -/
def regImmMap {α β : Type} (f : α → β) : WordRegImm α → WordRegImm β
  | .reg r => .reg r
  | .imm w => .imm (f w)

/-- Map the word constants of a mini-program. -/
def miniMap {α β : Type} (f : α → β) : Mini α → Mini β
  | .skip => .skip
  | .assign d e => .assign d (expMap f e)
  | .delete r => .delete r
  | .seq a b => .seq (miniMap f a) (miniMap f b)
  | .load a b c => .load a b c
  | .store a b => .store a b
  | .ite o l r y n => .ite o l (regImmMap f r) (miniMap f y) (miniMap f n)
  | .swap => .swap
  | .add a b c d e => .add a b c (regImmMap f d) (regImmMap f e)
  | .sub a b c d e => .sub a b c (regImmMap f d) (regImmMap f e)
  | .mul a b c d => .mul a b c d
  | .div a b c d e => .div a b c d e
  | .loop r l b => .loop r l (miniMap f b)
  | .continue => .continue
  | .recurse a b => .recurse a b
  | .loopBody b => .loopBody (miniMap f b)

theorem expMap_comp {α β γ : Type} (f : α → β) (g : β → γ) (e : WordLangExpHOL α) :
    expMap g (expMap f e) = expMap (g ∘ f) e := by
  refine WordLangExpHOL.rec
    (motive_1 := fun e => expMap g (expMap f e) = expMap (g ∘ f) e)
    (motive_2 := fun xs => expListMap g (expListMap f xs) = expListMap (g ∘ f) xs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro v; rfl
  · intro v; rfl
  · intro v; rfl
  · intro a ih; simp only [expMap, ih]
  · intro o xs ih; simp only [expMap, ih]
  · intro s a b iha ihb; simp only [expMap, iha, ihb]
  · rfl
  · intro x xs ihx ihxs; simp only [expListMap, ihx, ihxs]

theorem regImmMap_comp {α β γ : Type} (f : α → β) (g : β → γ) (r : WordRegImm α) :
    regImmMap g (regImmMap f r) = regImmMap (g ∘ f) r := by
  cases r <;> rfl

theorem miniMap_comp {α β γ : Type} (f : α → β) (g : β → γ) (p : Mini α) :
    miniMap g (miniMap f p) = miniMap (g ∘ f) p := by
  induction p <;> simp_all [miniMap, expMap_comp, regImmMap_comp]

/-- A mini-program with its word constants erased. -/
def skel {α : Type} (p : Mini α) : Mini Unit := miniMap (fun _ => ()) p

theorem skel_miniMap {α β : Type} (f : α → β) (p : Mini α) : skel (miniMap f p) = skel p := by
  simp only [skel, miniMap_comp]

/-- The bodies of all loops of a mini-program, including nested loops. -/
def loopBodies {α : Type} : Mini α → List (Mini α)
  | .loop _ _ b => b :: loopBodies b
  | .loopBody b => loopBodies b
  | .seq a b => loopBodies a ++ loopBodies b
  | .ite _ _ _ a b => loopBodies a ++ loopBodies b
  | _ => []

theorem loopBodies_miniMap {α β : Type} (f : α → β) (p : Mini α) :
    loopBodies (miniMap f p) = (loopBodies p).map (miniMap f) := by
  induction p <;> simp_all [miniMap, loopBodies]

/-! ### The kernel-evaluable compiler -/

/-- `compileExp` by structural recursion. -/
def compileExpK {width : Nat} [NeZero width] :
    WordLangExpHOL (BitVec width) → WordLangExpHOL (BitVec width)
  | .op op [x, y] => .op op [compileExpK x, compileExpK y]
  | .var n => .lookup (.temp (BitVec.ofNat 5 n))
  | .const w => .const w
  | .shift sh x y => .shift sh (compileExpK x) (compileExpK y)
  | _ => .const 0
termination_by structural e => e

theorem compileExp_eq_K {width : Nat} [NeZero width] (e : WordLangExpHOL (BitVec width)) :
    compileExp e = compileExpK e := by
  fun_induction compileExp e <;> simp_all [compileExpK]

/-- `seqTempImmNot` with HOL's evaluated `~0w`, `n2w (dimword (:α) − 1)`. -/
def seqTempImmNotK {width : Nat} [NeZero width] (i : Nat) (arg : WordRegImm (BitVec width))
    (p : WordLangProgHOL (BitVec width)) : WordLangProgHOL (BitVec width) :=
  match arg with
  | .reg r => seqTemp i r (.seq (.assign i (.op .xor [.var i,
      .const (BitVec.ofNat width (2 ^ width - 1))])) p)
  | .imm w => .seq (.assign i (.const (~~~w))) p

theorem not_zero_eq_ofNat {width : Nat} :
    ~~~(0 : BitVec width) = BitVec.ofNat width (2 ^ width - 1) := by
  apply BitVec.eq_of_toNat_eq
  have : 2 ^ width - 1 < 2 ^ width := Nat.sub_lt (Nat.two_pow_pos width) Nat.one_pos
  simp [Nat.mod_eq_of_lt this]

theorem seqTempImmNot_eq_K {width : Nat} [NeZero width] (i : Nat) (arg : WordRegImm (BitVec width))
    (p : WordLangProgHOL (BitVec width)) : seqTempImmNot i arg p = seqTempImmNotK i arg p := by
  cases arg <;> simp only [seqTempImmNot, seqTempImmNotK, not_zero_eq_ofNat]

/-- The cache lookup on skeletons. -/
def hasCompiledK {width : Nat} (code : Mini (BitVec width)) (cs : CodeAcc width) : Sum Nat Nat :=
  hasCompiled (skel code) (cs.1, cs.2.map fun e => (skel e.1, e.2))

theorem hasCompiled_eq_K {width : Nat} (code : Mini (BitVec width)) (cs : CodeAcc width)
    (sep : ∀ e ∈ cs.2, skel code = skel e.1 → code = e.1) :
    hasCompiled code cs = hasCompiledK code cs := by
  obtain ⟨next, entries⟩ := cs
  have key : entries.lookup code = (entries.map fun e => (skel e.1, e.2)).lookup (skel code) := by
    induction entries with
    | nil => rfl
    | cons e rest ih =>
      obtain ⟨k, v⟩ := e
      have hrest := ih (fun e he => sep e (List.mem_cons_of_mem _ he))
      have hk : code = k ↔ skel code = skel k :=
        ⟨fun h => h ▸ rfl, sep (k, v) List.mem_cons_self⟩
      by_cases h : code = k
      · subst h; simp [List.lookup]
      · have h' : ¬ skel code = skel k := fun h' => h (hk.mpr h')
        rw [List.map_cons, List.lookup, List.lookup, beq_false_of_ne h, beq_false_of_ne h']
        exact hrest
  simp only [hasCompiledK, hasCompiled]
  rw [key]

/-- `compileFuel` with `compileExpK`, `seqTempImmNotK` and `hasCompiledK`. -/
def compileFuelK {width : Nat} [NeZero width] : Nat → Nat → Nat → Nat → CodeAcc width →
    Mini (BitVec width) → Option (WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width)
  | 0, _, _, _, _, _ => none
  | fuel + 1, n, l, i, cs, code => do
    match code with
    | .skip => pure (.skip, l, i, cs)
    | .continue => pure (.call none (some n) [0] none, l, i, cs)
    | .recurse save _ =>
      let cuts : WordLangCutsetsHOL := (.ls (), sptListInsert (save.map (· + 2)) .ln)
      pure (loadRegs save (.call (some ([1], cuts, saveRegs save, n, l)) (some n) [] none),
        l + 1, i, cs)
    | .loop _ _ body =>
      match hasCompiledK body cs with
      | .inl existing =>
        pure (.call (some ([i], (.ls (), .ln), .skip, n, l)) (some existing) [] none,
          l + 1, i + 1, cs)
      | .inr index =>
        let (newCode, _, _, cs) ← compileFuelK fuel index 2 1 (codeAccNext cs) body
        pure (.call (some ([i], (.ls (), .ln), .skip, n, l)) (some index) [] none,
          l + 1, i + 1, install (body, index, newCode) cs)
    | .loopBody body => compileFuelK fuel n l i cs body
    | .seq a b =>
      let (a, l, i, cs) ← compileFuelK fuel n l i cs a
      let (b, l, i, cs) ← compileFuelK fuel n l i cs b
      pure (.seq a b, l, i, cs)
    | .ite op r arg a b =>
      let (a, l, i, cs) ← compileFuelK fuel n l i cs a
      let (b, l, i, cs) ← compileFuelK fuel n l i cs b
      match arg with
      | .reg r2 => pure (seqTemp i r (seqTemp (i + 1) r2 (.ite op i (.reg (i + 1)) a b)),
          l, i + 2, cs)
      | .imm w => pure (seqTemp i r (.ite op i (.imm w) a b), l, i + 1, cs)
    | .assign j e =>
      pure (.seq (.assign i (compileExpK e)) (.set (.temp (BitVec.ofNat 5 j)) (.var i)),
        l, i + 1, cs)
    | .delete _ => pure (.skip, l, i, cs)
    | .swap =>
      pure (.seq (.assign i (.lookup tempIn1))
        (.seq (.set tempIn1 (.lookup tempIn2)) (.set tempIn2 (.var i))), l, i + 1, cs)
    | .store r1 r2 =>
      pure (seqTemp i r1 (seqIndex (i + 1) r2 .out (.store (.var (i + 1)) i)), l, i + 2, cs)
    | .load r1 r2 arr =>
      pure (seqIndex i r2 arr (.seq (.assign (i + 1) (.load (.var i)))
        (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 1)))), l, i + 2, cs)
    | .add r0 r1 r2 r3 r4 =>
      pure (seqTempImm (i + 4) r4 (seqTempImm (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 4))))))), l, i + 5, cs)
    | .sub r0 r1 r2 r3 r4 =>
      pure (seqTempImm (i + 4) r4 (seqTempImmNotK (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.addCarry (i + 1) (i + 2) (i + 3) (i + 4))))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 4))))))), l, i + 5, cs)
    | .mul r0 r1 r2 r3 =>
      pure (seqTemp (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (.inst (.arith (.longMul i (i + 1) (i + 2) (i + 3))))
          (.seq (.set (.temp (BitVec.ofNat 5 r1)) (.var i))
            (.set (.temp (BitVec.ofNat 5 r0)) (.var (i + 1)))))), l, i + 4, cs)
    | .div r0 r1 r2 r3 r4 =>
      pure (seqTemp (i + 4) r4 (seqTemp (i + 3) r3 (seqTemp (i + 2) r2
        (.seq (divCode n l i (i + 1) (i + 2) (i + 3) (i + 4))
          (.seq (.set (.temp (BitVec.ofNat 5 r0)) (.var i))
            (.set (.temp (BitVec.ofNat 5 r1)) (.var (i + 1))))))), l + 1, i + 5, cs)

/-- Every cache entry produced by `compileFuelK` was already cached or is a
loop body of the compiled program. -/
theorem compileFuelK_keys {width : Nat} [NeZero width] :
    ∀ (fuel n l i : Nat) (cs : CodeAcc width) (code : Mini (BitVec width))
      (result : WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width),
      compileFuelK fuel n l i cs code = some result →
      ∀ e ∈ result.2.2.2.2, e ∈ cs.2 ∨ e.1 ∈ loopBodies code := by
  intro fuel
  induction fuel with
  | zero => intro n l i cs code result h; simp [compileFuelK] at h
  | succ fuel ih =>
    intro n l i cs code result h e he
    cases code with
    | loop recs live body =>
      simp only [compileFuelK] at h
      cases hc : hasCompiledK body cs with
      | inl existing =>
        simp only [hc] at h; cases h; exact .inl he
      | inr index =>
        simp only [hc] at h
        cases hb : compileFuelK fuel index 2 1 (codeAccNext cs) body with
        | none => simp [hb] at h
        | some r =>
          obtain ⟨body', lb, ib, cb⟩ := r
          simp only [hb, Option.bind_eq_bind, Option.bind_some] at h
          cases h
          simp only [install, List.mem_cons] at he
          rcases he with rfl | he
          · exact .inr (by simp [loopBodies])
          · rcases ih _ _ _ _ _ _ hb e he with h1 | h1
            · exact .inl h1
            · exact .inr (by simp [loopBodies, h1])
    | loopBody body =>
      simp only [compileFuelK] at h
      rcases ih _ _ _ _ _ _ h e he with h1 | h1
      · exact .inl h1
      · exact .inr (by simpa [loopBodies] using h1)
    | seq a b =>
      simp only [compileFuelK] at h
      cases ha : compileFuelK fuel n l i cs a with
      | none => simp [ha] at h
      | some ra =>
        obtain ⟨a', la, ia, ca⟩ := ra
        cases hb : compileFuelK fuel n la ia ca b with
        | none => simp [ha, hb] at h
        | some rb =>
          obtain ⟨b', lb, ib, cb⟩ := rb
          simp only [ha, hb, Option.bind_eq_bind, Option.bind_some] at h
          cases h
          rcases ih _ _ _ _ _ _ hb e he with h1 | h1
          · rcases ih _ _ _ _ _ _ ha e h1 with h2 | h2
            · exact .inl h2
            · exact .inr (by simp [loopBodies, h2])
          · exact .inr (by simp [loopBodies, h1])
    | ite op r arg a b =>
      simp only [compileFuelK] at h
      cases ha : compileFuelK fuel n l i cs a with
      | none => simp [ha] at h
      | some ra =>
        obtain ⟨a', la, ia, ca⟩ := ra
        cases hb : compileFuelK fuel n la ia ca b with
        | none => simp [ha, hb] at h
        | some rb =>
          obtain ⟨b', lb, ib, cb⟩ := rb
          have hcb : result.2.2.2 = cb := by
            cases arg <;> simp only [ha, hb, Option.bind_eq_bind, Option.bind_some] at h <;>
              cases h <;> rfl
          rw [hcb] at he
          rcases ih _ _ _ _ _ _ hb e he with h1 | h1
          · rcases ih _ _ _ _ _ _ ha e h1 with h2 | h2
            · exact .inl h2
            · exact .inr (by simp [loopBodies, h2])
          · exact .inr (by simp [loopBodies, h1])
    | _ => simp only [compileFuelK] at h; cases h; exact .inl he

/-- Separation of a set of mini-programs: equal skeletons mean equal programs. -/
def Separated {width : Nat} (S : List (Mini (BitVec width))) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, skel a = skel b → a = b

theorem compileFuel_eq_K {width : Nat} [NeZero width] (S : List (Mini (BitVec width)))
    (sep : Separated S) :
    ∀ (fuel n l i : Nat) (cs : CodeAcc width) (code : Mini (BitVec width)),
      (∀ b ∈ loopBodies code, b ∈ S) → (∀ e ∈ cs.2, e.1 ∈ S) →
      compileFuel fuel n l i cs code = compileFuelK fuel n l i cs code := by
  intro fuel
  induction fuel with
  | zero => intro n l i cs code _ _; rfl
  | succ fuel ih =>
    intro n l i cs code hcode hcs
    cases code with
    | loop recs live body =>
      have hbody : body ∈ S := hcode body (by simp [loopBodies])
      have hinner : ∀ b ∈ loopBodies body, b ∈ S := fun b hb => hcode b (by simp [loopBodies, hb])
      have hc : hasCompiled body cs = hasCompiledK body cs :=
        hasCompiled_eq_K body cs fun e he hs => sep _ hbody _ (hcs e he) hs
      simp only [compileFuel, compileFuelK, hc]
      cases hasCompiledK body cs with
      | inl existing => rfl
      | inr index =>
        simp only
        rw [ih index 2 1 (codeAccNext cs) body hinner (fun e he => hcs e he)]
    | loopBody body =>
      simp only [compileFuel, compileFuelK]
      exact ih n l i cs body (fun b hb => hcode b (by simpa [loopBodies] using hb)) hcs
    | seq a b =>
      have ha : ∀ x ∈ loopBodies a, x ∈ S := fun x hx => hcode x (by simp [loopBodies, hx])
      have hb : ∀ x ∈ loopBodies b, x ∈ S := fun x hx => hcode x (by simp [loopBodies, hx])
      simp only [compileFuel, compileFuelK]
      rw [ih n l i cs a ha hcs]
      cases hra : compileFuelK fuel n l i cs a with
      | none => rfl
      | some ra =>
        obtain ⟨a', la, ia, ca⟩ := ra
        have hca : ∀ e ∈ ca.2, e.1 ∈ S := fun e he => by
          rcases compileFuelK_keys _ _ _ _ _ _ _ hra e he with h | h
          · exact hcs e h
          · exact ha _ h
        simp only [Option.bind_eq_bind, Option.bind_some]
        rw [ih n la ia ca b hb hca]
    | ite op r arg a b =>
      have ha : ∀ x ∈ loopBodies a, x ∈ S := fun x hx => hcode x (by simp [loopBodies, hx])
      have hb : ∀ x ∈ loopBodies b, x ∈ S := fun x hx => hcode x (by simp [loopBodies, hx])
      simp only [compileFuel, compileFuelK]
      rw [ih n l i cs a ha hcs]
      cases hra : compileFuelK fuel n l i cs a with
      | none => rfl
      | some ra =>
        obtain ⟨a', la, ia, ca⟩ := ra
        have hca : ∀ e ∈ ca.2, e.1 ∈ S := fun e he => by
          rcases compileFuelK_keys _ _ _ _ _ _ _ hra e he with h | h
          · exact hcs e h
          · exact ha _ h
        simp only [Option.bind_eq_bind, Option.bind_some, ih n la ia ca b hb hca]
        cases arg <;> rfl
    | assign j e => simp only [compileFuel, compileFuelK, compileExp_eq_K]
    | sub r0 r1 r2 r3 r4 => simp only [compileFuel, compileFuelK, seqTempImmNot_eq_K]
    | _ => rfl

/-- `compile` through `compileFuelK`. -/
def compileK {width : Nat} [NeZero width] (n l i : Nat) (cs : CodeAcc width)
    (code : MiniHOL width) : WordLangProgHOL (BitVec width) × Nat × Nat × CodeAcc width :=
  (compileFuelK (miniBudget code + 1) n l i cs code).getD (.skip, l, i, cs)

/-- `generatedBignumStubs` through `compileK`. -/
def generatedBignumStubsK (width : Nat) [NeZero width] (location : Nat) :
    List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
  let (body, _, _, (_, installed)) :=
    compileK location 2 1 (location + 1, []) (mcIopCode width)
  (location, 1, .seq body (.return 0 [0])) ::
    installed.map fun (_, index, code) => (index, 1, .seq code (.return 0 [0]))

/-- `mcIopCode` with its word constants as numerals. -/
def mcIopNat : Mini Nat := miniMap BitVec.toNat (mcIopCode 64)

theorem mcIopCode_eq_miniMap (width : Nat) [NeZero width] :
    mcIopCode width = miniMap (fun k => BitVec.ofNat width k) mcIopNat := by
  kernel_rfl

theorem mcIopNat_separated :
    ∀ a ∈ loopBodies mcIopNat, ∀ b ∈ loopBodies mcIopNat, skel a = skel b → a = b := by
  decide +kernel

theorem mcIopCode_separated (width : Nat) [NeZero width] :
    Separated (loopBodies (mcIopCode width)) := by
  intro a ha b hb hs
  rw [mcIopCode_eq_miniMap, loopBodies_miniMap, List.mem_map] at ha hb
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  rw [skel_miniMap, skel_miniMap] at hs
  rw [mcIopNat_separated a ha b hb hs]

theorem generatedBignumStubs_eq_K (width : Nat) [NeZero width] (location : Nat) :
    generatedBignumStubs width location = generatedBignumStubsK width location := by
  have h := compileFuel_eq_K (loopBodies (mcIopCode width)) (mcIopCode_separated width)
    (miniBudget (mcIopCode width) + 1) location 2 1 (location + 1, []) (mcIopCode width)
    (fun _ hb => hb) (fun _ he => by simp at he)
  simp only [generatedBignumStubs, generatedBignumStubsK, compile, compileK, h]

end Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq
