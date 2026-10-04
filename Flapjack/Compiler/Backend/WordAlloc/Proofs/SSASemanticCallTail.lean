import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticReturn
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Call

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Private factoring of original Call_tail's argument-renaming and convention
register argument. It has no separate HOL declaration; the full case must derive
this preparation from its original locals premise and actual get_vars branch. -/
private theorem tailArguments {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (args : List Nat) (values : List (WordLocW width))
    (related : ssaLocalsRel next ssa source.locals target.locals)
    (read : WordSemStateFiniteExact.getVars args source = some values) :
    let renamed := args.map (optionLookup ssa)
    let registers := (List.range renamed.length).map fun key => 2 * key
    WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) target =
      (none,WordSemStateFiniteExact.setVars registers values target) ∧
    WordSemStateFiniteExact.getVars registers
      (WordSemStateFiniteExact.setVars registers values target) = some values := by
  dsimp only
  let renamed := args.map (optionLookup ssa)
  let registers := (List.range renamed.length).map fun key => 2 * key
  have lengths := Flapjack.WordAlloc.getVarsLength args source values read
  have distinct : registers.Nodup := by
    apply List.Nodup.map _ List.nodup_range
    intro x y equal
    change 2 * x = 2 * y at equal
    omega
  have same : registers.length = renamed.length := by simp [registers]
  have valuesLength : values.length = registers.length := by simp [registers,renamed,lengths]
  have renamedRead := ssaLocalsRelGetVars args values next ssa source target ⟨related,read⟩
  change WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) target =
    (none,WordSemStateFiniteExact.setVars registers values target) ∧ _
  constructor
  · simp only [WordSemStateFiniteExact.evaluate,List.map_fst_zip (Nat.le_of_eq same),
      List.map_snd_zip (Nat.le_of_eq same.symm),distinct,if_true]
    rw [show WordSemStateFiniteExact.getVars renamed target = some values from renamedRead]
  · exact getVarsSetVarsEq registers values target ⟨distinct,valuesLength⟩


/-- Private reduction of Call_tail's destination guard. The generated convention
register list is empty exactly when the original argument list is empty; this
is proof factoring, not a separately tagged HOL declaration. -/
private theorem tailDestinationGuard (dest : Option Nat) (args : List Nat)
    (ssa : Spt Nat) :
    wordSemBadDestArgs dest
      ((List.range (args.map (optionLookup ssa)).length).map fun key => 2 * key) =
      wordSemBadDestArgs dest args := by
  cases args <;> simp [wordSemBadDestArgs]


namespace SemanticCallTailWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticCallTailWitnesses

/-- Full original tail Call semantic case (resumed source8268-8296), with all
six original premises and the complete existential source permutation,
Error exemption, target result, frame and result-sensitive locals conclusion.
Argument moves, destination/arity lookup and callee state equality are derived
internally. No callee induction hypothesis is needed: both runs enter the same
callee state. Missing arguments/destination/code/handler and bad callee returns
retain the original Error exemption; timeout flushes and accepted returns have
the original complete conclusion. The imported total evaluator inherits
reals_as_rational_cuts (SOUNDNESS item 8). Full SSA assembly remains open. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaCcTransCorrectCallTail {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next))
        (.call none dest args handler : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.call none dest args handler) source target ssa next tables := by
  classical
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  refine ⟨target.permute, ?_⟩
  change let sr := WordSemStateFiniteExact.evaluate (.call none dest args handler) permuted
         if sr.1 = some .error then True else
           let compiled := ssaCcTrans (.call none dest args handler) ssa next tables
           let tr := WordSemStateFiniteExact.evaluate compiled.1 target
           sr.1 = tr.1 ∧ Flapjack.WordAlloc.wordStateEqRel sr.2 tr.2 ∧
             match sr.1 with
             | none => ssaLocalsRel compiled.2.2 compiled.2.1 sr.2.locals tr.2.locals
             | some (.break n) => match tables[n]? with
               | none => True
               | some (dest,_,exits) => Flapjack.WordAlloc.strongLocalsRel
                   (optionLookup dest) (sptDomain exits) sr.2.locals tr.2.locals
             | some (.continue n) => match tables[n]? with
               | none => True
               | some (dest,entries,_) => Flapjack.WordAlloc.strongLocalsRel
                   (optionLookup dest) (sptDomain entries) sr.2.locals tr.2.locals
             | some _ => sr.2.locals = tr.2.locals
  cases read : WordSemStateFiniteExact.getVars args permuted with
  | none => simp [WordSemStateFiniteExact.evaluate, read]
  | some values =>
    by_cases bad : wordSemBadDestArgs dest args = true
    · simp [WordSemStateFiniteExact.evaluate, read, bad]
    have good : wordSemBadDestArgs dest args = false := Bool.eq_false_iff.mpr bad
    cases found : wordSemFindCode dest values permuted.code permuted.stackSize with
    | none => simp [WordSemStateFiniteExact.evaluate, read, good, wordSemAddRetLoc, found]
    | some triple =>
      obtain ⟨calleeArgs,callee,size⟩ := triple
      cases handler with
      | some handler => simp [WordSemStateFiniteExact.evaluate, read, good, wordSemAddRetLoc, found]
      | none =>
        let renamed := args.map (optionLookup ssa)
        let registers := (List.range renamed.length).map fun key => 2 * key
        let moved := WordSemStateFiniteExact.setVars registers values target
        have preparation := tailArguments permuted target ssa next args values h.2.1 read
        have moveRun : WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) target =
            (none,moved) := preparation.1
        have reread : WordSemStateFiniteExact.getVars registers moved = some values := preparation.2
        have guard : wordSemBadDestArgs dest registers = false := by
          rw [tailDestinationGuard]; exact good
        have movedFrame : Flapjack.WordAlloc.wordStateEqRel permuted moved := by
          simpa [moved,WordSemStateFiniteExact.setVars,Flapjack.WordAlloc.wordStateEqRel] using frame
        have fields := movedFrame
        unfold Flapjack.WordAlloc.wordStateEqRel at fields
        have codeEq := fields.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have sizeEq := fields.2.2.2.2.2.2.1
        have clockEq := fields.2.2.2.2.2.2.2.2.2.2.2.2.1
        have calleeState : WordSemStateFiniteExact.callEnv calleeArgs size
            (WordSemStateFiniteExact.decClock moved) =
            WordSemStateFiniteExact.callEnv calleeArgs size
              (WordSemStateFiniteExact.decClock permuted) := by
          simpa [permuted,moved,WordSemStateFiniteExact.setVars] using
            Flapjack.WordAlloc.callEnv_decClock_wsr movedFrame calleeArgs size
        have compiled : ssaCcTrans (width := width) (.call none dest args none) ssa next tables =
            (.seq (.move 1 (registers.zip renamed)) (.call none dest registers none),ssa,next) := rfl
        have seqRun : WordSemStateFiniteExact.evaluate
            (.seq (.move 1 (registers.zip renamed)) (.call none dest registers none)) target =
            WordSemStateFiniteExact.evaluate (.call none dest registers none) moved := by
          rw [WordSemStateFiniteExact.evaluate,moveRun]
          have fixed : target.fixClock ((none : Option (WordSemResult width)),moved) = (none,moved) := by
            simp [WordSemStateFiniteExact.fixClock,moved,WordSemStateFiniteExact.setVars]
          rw [fixed]
        simp only [compiled,seqRun]
        simp only [WordSemStateFiniteExact.evaluate,read,reread,good,guard,
          Bool.false_eq_true,if_false,wordSemAddRetLoc,codeEq,sizeEq,found,clockEq,calleeState]
        by_cases zero : permuted.clock = 0
        · simp only [zero]
          simp [WordSemStateFiniteExact.flushState,Flapjack.WordAlloc.wordStateEqRel]
          tauto
        · simp only [zero]
          cases run : WordSemStateFiniteExact.evaluate callee
              (WordSemStateFiniteExact.callEnv calleeArgs size (WordSemStateFiniteExact.decClock permuted)) with
          | mk result after =>
            cases result with
            | none => simp [wordSemBadFunReturn]
            | some result => cases result <;> simp [wordSemBadFunReturn,Flapjack.WordAlloc.wordStateEqRel]

end Flapjack.Compiler.Backend.WordAlloc
