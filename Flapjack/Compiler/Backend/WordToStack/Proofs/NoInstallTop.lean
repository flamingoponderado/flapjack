import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallPrograms
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallCode
namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Full original code-map top-level theorem. Distinct source identifiers and
safety of the actual fromAList code map imply the source-list convention
internally; no list-safety premise is substituted for the original map guard.
Both injected stubs and all four output components are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem wordToStackCompileNoInstall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (frameConfig : Config)
    (frames : List Nat) (outputs : List (Nat × HolProg width))
    (distinct : (programs.map Prod.fst).Nodup)
    (codeGuard : WordProps.noInstallCode (sptFromAList programs))
    (compiled : compileNative conf false programs = (bitmaps,frameConfig,frames,outputs)) :
    (outputs.all fun row => noInstall row.2) = true := by
  have lookupAt : ∀ (rows : List (Nat × Nat × WordLangProgHOL (BitVec width))),
      (rows.map Prod.fst).Nodup → ∀ (key : Nat) (value : Nat × WordLangProgHOL (BitVec width)),
      (key,value) ∈ rows → sptAListLookup key rows = some value := by
    intro rows
    induction rows with
    | nil => intro _ key value h; cases h
    | cons entry rows ih =>
      rcases entry with ⟨first,firstValue⟩
      intro hDistinct key value hmem
      have parts : first ∉ rows.map Prod.fst ∧ (rows.map Prod.fst).Nodup := by
        simpa only [List.map_cons,List.nodup_cons] using hDistinct
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        simp [sptAListLookup]
      · have hkey : key ≠ first := by
          intro heq
          subst key
          exact parts.1 (List.mem_map.mpr ⟨(first,value),htail,rfl⟩)
        simpa [sptAListLookup,hkey] using ih parts.2 key value htail
  have sourceGuard : (programs.all fun row => noInstallSubprogsHOL row.2.2) = true := by
    apply List.all_eq_true.mpr
    intro row hmem
    rcases row with ⟨key,count,program⟩
    apply codeGuard key count program
    rw [sptLookup_sptFromAList]
    exact lookupAt programs distinct key (count,program) hmem
  have bodiesSafe := compileWordToStackNoInstall conf false
    (conf.regCount - (5 + conf.avoidRegs.length)) programs (.list [4],1)
    (compileWordToStackNative conf false (conf.regCount - (5 + conf.avoidRegs.length))
      programs (.list [4],1)).1
    (compileWordToStackNative conf false (conf.regCount - (5 + conf.avoidRegs.length))
      programs (.list [4],1)).2.1
    (compileWordToStackNative conf false (conf.regCount - (5 + conf.avoidRegs.length))
      programs (.list [4],1)).2.2 sourceGuard rfl rfl
  have result := congrArg (fun row => row.2.2.2) compiled
  simp only [compileNative, Bool.false_eq_true, ↓reduceIte] at result
  rw [← result]
  simpa only [List.all_cons, raiseStubNative, storeConstsStubNative,
    noInstall, Bool.false_eq_true, ↓reduceIte, Bool.true_and] using bodiesSafe
end Flapjack.Compiler.Backend.WordToStack.Native
