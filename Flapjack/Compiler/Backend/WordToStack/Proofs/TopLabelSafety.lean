import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.CodeLabelSafety
import Flapjack.Compiler.Backend.WordToStack.Proofs.HandlerLabels

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack proof factoring: the two compiler-generated stubs contain no
referenced code labels. This packages computation, not a separate HOL theorem. -/
private theorem stubCodeLabelsEmpty {width : Nat} [NeZero width] (registers : Nat) :
    getCodeLabels (raiseStubNative (width := width) false registers) = ∅ ∧
    getCodeLabels (storeConstsStubNative (width := width) registers) = ∅ := by
  simp [raiseStubNative, storeConstsStubNative, getCodeLabels]

/-- Complete original top-level code-label safety: the actual compiler's full
output equation and source safety are the only premises. Both generated stub
entries are owned by the returned program; the external set stays arbitrary. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackGoodCodeLabels {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bytes : List (BitVec width)) (cfg : Config) (frames : List Nat)
    (program : List (Nat × HolProg width)) (externalLabels : Set Nat)
    (compiled : compileNative conf false rows = (bytes,cfg,frames,program))
    (good : goodCodeLabelsHOL rows externalLabels) :
    stackGoodCodeLabels program externalLabels := by
  let registers := conf.regCount - (5 + conf.avoidRegs.length)
  let initial : AppList (BitVec width) × Nat := (.list [4],1)
  rcases hi : compileWordToStackNative conf false registers rows initial with
    ⟨bodies,innerFrames,bitmaps⟩
  have output :
      (raiseStubLocation,raiseStubNative false registers) ::
      (storeConstsStubLocation,storeConstsStubNative registers) :: bodies = program := by
    have h := congrArg (fun x => x.2.2.2) compiled
    dsimp only [compileNative] at h
    simp only [Bool.false_eq_true, if_false] at h
    rw [hi] at h
    exact h
  subst program
  have bound := compileWordToStackCodeLabels conf false registers rows initial bodies
    (innerFrames,bitmaps) good.1 rfl hi
  have keys := Flapjack.WordToStackProofs.mapFstCompileWordToStack conf false registers
    rows initial bodies (innerFrames,bitmaps) hi
  have empty := stubCodeLabelsEmpty (width := width) registers
  unfold stackGoodCodeLabels
  intro label member
  rcases member with ⟨labels,⟨body,present,rfl⟩,referenced⟩
  simp only [List.map_cons, List.mem_cons] at present
  rcases present with h | h | h
  · subst body
    simp only [empty.1,Set.mem_empty_iff_false] at referenced
  · subst body
    simp only [empty.2,Set.mem_empty_iff_false] at referenced
  · have inner : label ∈ ⋃₀ (getCodeLabels '' {p | p ∈ bodies.map Prod.snd}) :=
      ⟨getCodeLabels body,⟨body,h,rfl⟩,referenced⟩
    rcases bound inner with hr | hs | hr | hh
    · subst label
      exact Or.inl (Or.inl (Or.inl (Or.inr
        ⟨raiseStubLocation,by simp,rfl⟩)))
    · subst label
      exact Or.inl (Or.inl (Or.inl (Or.inr
        ⟨storeConstsStubLocation,by simp,rfl⟩)))
    · rcases hr with ⟨name,reference,equation⟩
      rcases good.2 reference with owned | external
      · change name ∈ rows.map Prod.fst at owned
        have ownedTop : name ∈
            ((raiseStubLocation,raiseStubNative false registers) ::
              (storeConstsStubLocation,storeConstsStubNative registers) :: bodies).map Prod.fst := by
          simp only [List.map_cons,List.mem_cons]
          exact Or.inr (Or.inr (by simpa only [keys] using owned))
        exact Or.inl (Or.inl (Or.inl (Or.inr ⟨name,ownedTop,equation⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨name,external,equation⟩))
    · rcases hh with ⟨handlers,present,member⟩
      have presentTop : handlers ∈
          (((raiseStubLocation,raiseStubNative false registers) ::
            (storeConstsStubLocation,storeConstsStubNative registers) :: bodies).map
              (fun row => stackGetHandlerLabels row.1 row.2)) := by
        simp only [List.map_cons,List.mem_cons]
        exact Or.inr (Or.inr present)
      exact Or.inl (Or.inl (Or.inl (Or.inl
        ⟨handlers,presentTop,member⟩)))

/-- Complete original top-level handler-label safety, retaining EVERY
good_handlers and the full four-component native compiler equation. No source
code-label safety or desired target predicate is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackGoodHandlerLabels {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bytes : List (BitVec width)) (cfg : Config) (frames : List Nat)
    (program : List (Nat × HolProg width))
    (good : rows.all (fun row => goodHandlersHOL row.1 row.2.2) = true)
    (compiled : compileNative conf false rows = (bytes,cfg,frames,program)) :
    stackGoodHandlerLabels program := by
  let registers := conf.regCount - (5 + conf.avoidRegs.length)
  let initial : AppList (BitVec width) × Nat := (.list [4],1)
  rcases hi : compileWordToStackNative conf false registers rows initial with
    ⟨bodies,innerFrames,bitmaps⟩
  have output :
      (raiseStubLocation,raiseStubNative false registers) ::
      (storeConstsStubLocation,storeConstsStubNative registers) :: bodies = program := by
    have h := congrArg (fun x => x.2.2.2) compiled
    dsimp only [compileNative] at h
    simp only [Bool.false_eq_true, if_false] at h
    rw [hi] at h
    exact h
  subst program
  have bound := compileWordToStackCodeLabels conf false registers rows initial bodies
    (innerFrames,bitmaps) good rfl hi
  have empty := stubCodeLabelsEmpty (width := width) registers
  unfold stackGoodHandlerLabels
  intro label member
  rcases member.1 with ⟨labels,⟨body,present,rfl⟩,referenced⟩
  simp only [List.map_cons,List.mem_cons] at present
  rcases present with h | h | h
  · subst body
    simp only [empty.1,Set.mem_empty_iff_false] at referenced
  · subst body
    simp only [empty.2,Set.mem_empty_iff_false] at referenced
  · have inner : label ∈ ⋃₀ (getCodeLabels '' {p | p ∈ bodies.map Prod.snd}) :=
      ⟨getCodeLabels body,⟨body,h,rfl⟩,referenced⟩
    rcases bound inner with hr | hs | hr | hh
    · subst label
      exact False.elim (member.2 rfl)
    · subst label
      exact False.elim (member.2 rfl)
    · rcases hr with ⟨name,_,equation⟩
      subst label
      exact False.elim (member.2 rfl)
    · rcases hh with ⟨handlers,present,member⟩
      have presentTop : handlers ∈
          (((raiseStubLocation,raiseStubNative false registers) ::
            (storeConstsStubLocation,storeConstsStubNative registers) :: bodies).map
              (fun row => stackGetHandlerLabels row.1 row.2)) := by
        simp only [List.map_cons,List.mem_cons]
        exact Or.inr (Or.inr present)
      exact Or.inl ⟨handlers,presentTop,member⟩

end Flapjack.Compiler.Backend.WordToStack.Native
