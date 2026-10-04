import Flapjack.Compiler.Backend.WordToStack.ProductionCleanupConventions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.ClashOccurrences
import Flapjack.Pancake.Proofs.LoopToWord.ContextSupport

namespace Flapjack.ProductionGcCutsets
open RiscV

/-- Names actually consumed by a GC bitmap at Alloc or returning Call, including
all recursively compiled continuations/handlers. Tail-call handlers are ignored
by the actual compiler. This source-consumer inventory has no HOL original. -/
inductive GcName (name : Nat) : WordProg α → Prop
  | alloc (destination : Nat) (other live : List Nat) (member : name ∈ live) :
      GcName name (.alloc destination (other, live))
  | call (values other live : List Nat) (body : WordProg α) (l1 l2 : Nat)
      (target : Option Nat) (arguments : List Nat)
      (handler : Option (Nat × WordProg α × Nat × Nat)) (member : name ∈ live) :
      GcName name (.call (some (values, (other, live), body, l1, l2)) target arguments handler)
  | seqLeft (first second : WordProg α) (inside : GcName name first) : GcName name (.seq first second)
  | seqRight (first second : WordProg α) (inside : GcName name second) : GcName name (.seq first second)
  | iteLeft (op : Cmp) (condition : Nat) (right : WordRegImm α) (first second : WordProg α)
      (inside : GcName name first) : GcName name (.ite op condition right first second)
  | iteRight (op : Cmp) (condition : Nat) (right : WordRegImm α) (first second : WordProg α)
      (inside : GcName name second) : GcName name (.ite op condition right first second)
  | loop (liveIn liveOut : List Nat) (body : WordProg α) (inside : GcName name body) :
      GcName name (.loop liveIn body liveOut)
  | mustTerminate (body : WordProg α) (inside : GcName name body) : GcName name (.mustTerminate body)
  | returnBody (values other live : List Nat) (body : WordProg α) (l1 l2 : Nat)
      (target : Option Nat) (arguments : List Nat)
      (handler : Option (Nat × WordProg α × Nat × Nat)) (inside : GcName name body) :
      GcName name (.call (some (values, (other, live), body, l1, l2)) target arguments handler)
  | handlerBody (values other live : List Nat) (body : WordProg α) (l1 l2 : Nat)
      (target : Option Nat) (arguments : List Nat) (exception : Nat)
      (handler : WordProg α) (h1 h2 : Nat) (inside : GcName name handler) :
      GcName name (.call (some (values, (other, live), body, l1, l2)) target arguments
        (some (exception, handler, h1, h2)))

/-- Every consumed GC name is already in the actual location-map name domain,
including both nested Call subtrees. No location success is assumed. -/
theorem GcName.variables {α : Type} {name : Nat} {program : WordProg α}
    (occurs : GcName name program) : name ∈ wordProgVariables program := by
  induction occurs <;>
    simp_all only [wordProgVariables, wordProgReadVars, wordProgWriteVars,
      List.mem_append, List.mem_cons]
  case call values other live body l1 l2 target arguments handler member =>
    rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩ <;>
      simp_all [wordProgReadVars, wordProgWriteVars]
  case returnBody values other live body l1 l2 target arguments handler inside ih =>
    rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩ <;>
      simp_all [wordProgReadVars, wordProgWriteVars] <;> tauto
  all_goals tauto

private theorem everyName_gc (predicate : Nat → Bool) (other live : List Nat)
    (names : everyNameHOL predicate (wordCutsetsToHOL (other, live)) = true)
    (name : Nat) (member : name ∈ live) : predicate name = true := by
  simp only [everyNameHOL, wordCutsetsToHOL, Bool.and_eq_true, List.all_eq_true,
    sptMemMapFstToAList, LoopToWord.sptDomain_toNumSetHOL] at names
  exact names.2 name member

/-- Native every-stack-variable checks supply the actual bitmap-name predicate.
Codec/cutset correspondence is proved, not supplied as a per-name callback. -/
theorem GcName.stackPredicate {width : Nat} [NeZero width]
    {name : Nat} {program : WordProg (BitVec width)} (occurs : GcName name program)
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (predicate : Nat → Bool) (checked : everyStackVarHOL predicate native = true) :
    predicate name = true := by
  induction occurs generalizing native
  all_goals simp only [wordLangProgToHOL, bind, pure, Option.bind_some,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at encoded
  case alloc destination other live member =>
    subst native
    exact everyName_gc predicate other live checked name member
  case seqLeft first second inside ih =>
    rcases encoded with ⟨left, hl, right, hr, rfl⟩
    simp only [everyStackVarHOL, Bool.and_eq_true] at checked
    exact ih left hl checked.1
  case seqRight first second inside ih =>
    rcases encoded with ⟨left, hl, right, hr, rfl⟩
    simp only [everyStackVarHOL, Bool.and_eq_true] at checked
    exact ih right hr checked.2
  case iteLeft op condition right first second inside ih =>
    rcases encoded with ⟨left, hl, right, hr, rfl⟩
    simp only [everyStackVarHOL, Bool.and_eq_true] at checked
    exact ih left hl checked.1
  case iteRight op condition right first second inside ih =>
    rcases encoded with ⟨left, hl, right, hr, rfl⟩
    simp only [everyStackVarHOL, Bool.and_eq_true] at checked
    exact ih right hr checked.2
  case loop liveIn liveOut body inside ih =>
    rcases encoded with ⟨body, hb, rfl⟩
    exact ih body hb checked
  case mustTerminate body inside ih =>
    rcases encoded with ⟨body, hb, rfl⟩
    exact ih body hb checked
  case call values other live body l1 l2 target arguments handler member =>
    rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩
    all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq] at encoded
    · rcases encoded with ⟨ret, hr, rfl⟩
      simp only [everyStackVarHOL, Bool.and_eq_true] at checked
      exact everyName_gc predicate other live checked.1.1 name member
    · rcases encoded with ⟨ret, hr, handler, hh, rfl⟩
      simp only [everyStackVarHOL, Bool.and_eq_true] at checked
      exact everyName_gc predicate other live checked.1.1 name member
  case returnBody values other live body l1 l2 target arguments handler inside ih =>
    rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩
    all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq] at encoded
    · rcases encoded with ⟨ret, hr, rfl⟩
      simp only [everyStackVarHOL, Bool.and_eq_true] at checked
      exact ih ret hr checked.1.2
    · rcases encoded with ⟨ret, hr, handler, hh, rfl⟩
      simp only [everyStackVarHOL, Bool.and_eq_true] at checked
      exact ih ret hr checked.1.2
  case handlerBody values other live body l1 l2 target arguments exception handler h1 h2 inside ih =>
    rcases encoded with ⟨ret, hr, handler, hh, rfl⟩
    simp only [everyStackVarHOL, Bool.and_eq_true] at checked
    exact ih handler hh checked.2

/-- Checking every program name also checks the subset stored in cutsets.
This local consequence supplies the clash-tree predicate at actual GC sites;
it is infrastructure, with no separate HOL declaration asserted. -/
theorem everyVar_stackSubset {width : Nat} [NeZero width]
    (predicate : Nat → Bool) (program : WordLangProgHOL (BitVec width))
    (checked : everyVarHOL predicate program = true) : everyStackVarHOL predicate program = true := by
  fun_induction everyStackVarHOL predicate program <;>
    simp_all [everyVarHOL, Bool.and_eq_true]
  case case4 target arguments handler values names body l1 l2 ihReturns ihHandler =>
    rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩ <;>
      simp_all [everyVarHOL, Bool.and_eq_true]

/-- Every actual consumed GC name lies in the native allocator clash tree,
using the complete original every-var occurrence theorem. -/
theorem GcName.clash {width : Nat} [NeZero width]
    {name : Nat} {program : WordProg (BitVec width)} (occurs : GcName name program)
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    RegAlloc.inClashTree (WordAlloc.getClashTree native []) name := by
  classical
  have allNames := WordAlloc.everyVar_inGetClashTree native []
  have checked := everyVar_stackSubset _ native allNames
  have member := occurs.stackPredicate native encoded _ checked
  exact of_decide_eq_true member

/-- Full actual allocator pre-conventions supply each consumed name's original
stack-variable guard, rather than assuming it per bitmap entry. -/
theorem GcName.stack {width : Nat} [NeZero width]
    {name : Nat} {program : WordProg (BitVec width)} (occurs : GcName name program)
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (pre : preAllocConventionsHOL native = true) : isStackVar name = true := by
  simp only [preAllocConventionsHOL, Bool.and_eq_true] at pre
  exact occurs.stackPredicate native encoded isStackVar pre.1

end Flapjack.ProductionGcCutsets
