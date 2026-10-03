import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorSetWF

namespace Flapjack.WordAlloc
open RiscV.CakeAlloc RiscV.CakeRegAlloc Flapjack.Compiler.Encoders.Asm

/-! Complete actual RISC-V forced-pair producer correspondence. These are
untagged implementation equations without independent HOL originals. The
production target is RISC-V; actual carrier acceptance excludes the separate
five-register AddCarry and has no floating-point instruction constructors. -/

theorem forcedInstruction_production {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (target : config.isa = .riscv)
    (instruction : WordInst (BitVec width)) (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL instruction = some native) (acc : List (Nat × Nat)) :
    cakeGetForcedAux (.inst instruction) acc = getForced config (.inst native) acc := by
  cases instruction with
  | arith operation =>
      cases operation <;> simp [wordLangInstToHOL, wordLangArithToHOL] at encoded
      all_goals subst native
      all_goals simp [cakeGetForcedAux, cakeForcedArith, getForced,
        getForcedAddCarry, getForcedLongMul, target, List.append_assoc]
  | const register value =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      simp only [cakeGetForcedAux, getForced]
  | mem operator register address =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      simp only [cakeGetForcedAux, getForced]
  | memOffset operator register address offset =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      simp only [cakeGetForcedAux, getForced]

/-- Full original ordered forced pairs, with arbitrary accumulator and every
recursive production constructor. Acceptance is of the actual source encoder,
not of allocation or execution. -/
theorem forcedProgram_production {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (target : config.isa = .riscv)
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) (acc : List (Nat × Nat)) :
    cakeGetForcedAux program acc = getForced config native acc := by
  cases program
  case inst instruction =>
    cases hi : wordLangInstToHOL instruction <;> simp [wordLangProgToHOL, hi] at encoded
    subst native
    exact forcedInstruction_production config target instruction _ hi acc
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body with
    | none => simp [wordLangProgToHOL, hb] at encoded
    | some nb =>
      simp only [wordLangProgToHOL, hb, Option.map_some, Option.some.injEq] at encoded
      subst native
      simpa only [cakeGetForcedAux, getForced] using forcedProgram_production config target body nb hb acc
  case seq first second =>
    cases hf : wordLangProgToHOL first <;> cases hs : wordLangProgToHOL second <;>
      simp [wordLangProgToHOL, hf, hs] at encoded
    subst native
    simp only [cakeGetForcedAux, getForced,
      forcedProgram_production config target first _ hf,
      forcedProgram_production config target second _ hs]
  case ite cmp register right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    simp only [cakeGetForcedAux, getForced,
      forcedProgram_production config target yes _ hy,
      forcedProgram_production config target no _ hn]
  case loop names body exits =>
    cases hb : wordLangProgToHOL body with
    | none => simp [wordLangProgToHOL, hb] at encoded
    | some nb =>
      simp [wordLangProgToHOL, hb] at encoded
      subst native
      simpa only [cakeGetForcedAux, getForced] using forcedProgram_production config target body nb hb acc
  case call returns destination arguments handler =>
    cases hReturns : returns with
    | none =>
      cases hHandler : handler with
      | none =>
          simp [wordLangProgToHOL, hReturns, hHandler] at encoded
          subst native
          simp only [cakeGetForcedAux, getForced]
      | some h =>
          rcases h with ⟨exception, body, l1, l2⟩
          cases hb : wordLangProgToHOL body with
          | none => simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          | some nb =>
              simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
              subst native
              simp only [cakeGetForcedAux, getForced]
    | some r =>
      rcases r with ⟨values, sets, body, l1, l2⟩
      cases hb : wordLangProgToHOL body with
      | none => simp [wordLangProgToHOL, hReturns, hb] at encoded
      | some nb =>
        cases hHandler : handler with
        | none =>
          simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
          subst native
          simpa only [cakeGetForcedAux, getForced] using forcedProgram_production config target body nb hb acc
        | some h =>
          rcases h with ⟨exception, handlerBody, h1, h2⟩
          cases hh : wordLangProgToHOL handlerBody with
          | none => simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
          | some nh =>
            simp [wordLangProgToHOL, hReturns, hHandler, hb, hh] at encoded
            subst native
            simp only [cakeGetForcedAux, getForced,
              forcedProgram_production config target body nb hb,
              forcedProgram_production config target handlerBody nh hh]
  all_goals simp only [wordLangProgToHOL, Option.some.injEq] at encoded
  all_goals subst native
  all_goals simp only [cakeGetForcedAux, getForced]
termination_by sizeOf program
decreasing_by
  all_goals
    simp_wf
    subst program
    try rw [hReturns]
    try rw [hHandler]
    try simp
    all_goals omega

/-- The actual complete RISC-V producer supplies precisely the original
forced input list, including ordering and equality guards. -/
theorem getForced_production {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (target : config.isa = .riscv)
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    cakeGetForced program = getForced config native [] :=
  forcedProgram_production config target program native encoded []

end Flapjack.WordAlloc
