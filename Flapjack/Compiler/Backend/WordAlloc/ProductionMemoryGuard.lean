import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.RiscV.AllocatorMemoryInvariant

namespace Flapjack.WordAlloc

/-- Native-carrier rendering of the additional production memory guard.
This predicate has no HOL original and is not an allocation correctness
hypothesis: it records the present runtime domain that must be discharged
separately when connecting the executed caller to the full HOL statement. -/
def nativeMemorySupported {α : Type u} : WordLangProgHOL α → Bool
  | .inst (.mem .load16 _ _) | .inst (.mem .store16 _ _) => false
  | .seq first second => nativeMemorySupported first && nativeMemorySupported second
  | .ite _ _ _ first second => nativeMemorySupported first && nativeMemorySupported second
  | .loop _ body _ | .mustTerminate body => nativeMemorySupported body
  | .call returns _ _ handler =>
      (match returns with
       | none => true
       | some (_, _, body, _, _) => nativeMemorySupported body) &&
      (match handler with
       | none => true
       | some (_, body, _, _) => nativeMemorySupported body)
  | _ => true
termination_by program => sizeOf program

/-- Accepted instruction encoding retains the actual guard, including both
zero-offset production forms. No supported-memory premise is assumed.
This is Flapjack implementation correspondence with no HOL original. -/
theorem memoryGuardInst_production {width : Nat}
    (actual : WordInst (BitVec width)) (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL actual = some native) :
    nativeMemorySupported (.inst native) = RiscV.allocatorMemorySupported (.inst actual) := by
  cases actual with
  | const name value =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      simp only [nativeMemorySupported, RiscV.allocatorMemorySupported]
  | arith operation =>
      cases accepted : wordLangArithToHOL operation <;>
        simp [wordLangInstToHOL, accepted] at encoded
      subst native
      simp only [nativeMemorySupported, RiscV.allocatorMemorySupported]
  | mem operator name address =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases operator <;> simp only [nativeMemorySupported, RiscV.allocatorMemorySupported]
  | memOffset operator name address offset =>
      simp only [wordLangInstToHOL, Option.some.injEq] at encoded
      subst native
      cases operator <;> simp only [nativeMemorySupported, RiscV.allocatorMemorySupported]

/-- The whole accepted input encoder preserves the actual memory guard.
Both optional call continuations are checked independently, and memory
offsets and all constructors are retained. There is no assumed guard success
or target evaluation. This infrastructure has no HOL original. -/
theorem memoryGuardProgram_production {width : Nat}
    (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    nativeMemorySupported native = RiscV.allocatorMemorySupported program := by
  cases program
  case inst instruction =>
    cases hi : wordLangInstToHOL instruction <;> simp [wordLangProgToHOL, hi] at encoded
    subst native
    exact memoryGuardInst_production instruction _ hi
  case mustTerminate body =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simp only [nativeMemorySupported, RiscV.allocatorMemorySupported,
      memoryGuardProgram_production body _ hb]
  case loop names body exits =>
    cases hb : wordLangProgToHOL body <;> simp [wordLangProgToHOL, hb] at encoded
    subst native
    simp [nativeMemorySupported, RiscV.allocatorMemorySupported,
      memoryGuardProgram_production body _ hb]
  case seq first second =>
    cases hf : wordLangProgToHOL first <;> cases hs : wordLangProgToHOL second <;>
      simp [wordLangProgToHOL, hf, hs] at encoded
    subst native
    simp [nativeMemorySupported, RiscV.allocatorMemorySupported,
      memoryGuardProgram_production first _ hf,
      memoryGuardProgram_production second _ hs]
  case ite compare condition right yes no =>
    cases hy : wordLangProgToHOL yes <;> cases hn : wordLangProgToHOL no <;>
      simp [wordLangProgToHOL, hy, hn] at encoded
    subst native
    simp [nativeMemorySupported, RiscV.allocatorMemorySupported,
      memoryGuardProgram_production yes _ hy,
      memoryGuardProgram_production no _ hn]
  case call returns target arguments handler =>
    cases hReturns : returns with
    | none =>
        cases hHandler : handler with
        | none =>
            simp [wordLangProgToHOL, hReturns, hHandler] at encoded
            subst native
            simp [nativeMemorySupported, RiscV.allocatorMemorySupported]
        | some exception =>
            rcases exception with ⟨name, body, label1, label2⟩
            cases hb : wordLangProgToHOL body <;>
              simp [wordLangProgToHOL, hReturns, hHandler, hb] at encoded
            subst native
            simp [nativeMemorySupported, RiscV.allocatorMemorySupported,
              memoryGuardProgram_production body _ hb]
    | some ret =>
        rcases ret with ⟨values, sets, body, label1, label2⟩
        cases hb : wordLangProgToHOL body <;>
          simp [wordLangProgToHOL, hReturns, hb] at encoded
        cases hHandler : handler with
        | none =>
            simp [hHandler] at encoded
            subst native
            simp [nativeMemorySupported, RiscV.allocatorMemorySupported,
              memoryGuardProgram_production body _ hb]
        | some exception =>
            rcases exception with ⟨name, handlerBody, handlerLabel1, handlerLabel2⟩
            cases hh : wordLangProgToHOL handlerBody <;>
              simp [hHandler, hh] at encoded
            subst native
            simp [nativeMemorySupported, RiscV.allocatorMemorySupported,
              memoryGuardProgram_production body _ hb,
              memoryGuardProgram_production handlerBody _ hh,
              ]
  case alloc destination sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp [nativeMemorySupported, RiscV.allocatorMemorySupported]
  case install code codeLength data dataLength sets =>
    rcases sets with ⟨left, right⟩
    simp only [wordLangProgToHOL, Option.some.injEq] at encoded
    subst native
    simp [nativeMemorySupported, RiscV.allocatorMemorySupported]
  all_goals simp only [wordLangProgToHOL, Option.some.injEq] at encoded
  all_goals subst native
  all_goals simp [nativeMemorySupported, RiscV.allocatorMemorySupported]
termination_by sizeOf program
decreasing_by
  all_goals simp_wf
  all_goals subst program
  all_goals try rw [hReturns]
  all_goals try rw [hHandler]
  all_goals try simp
  all_goals omega


end Flapjack.WordAlloc
