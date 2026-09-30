import Flapjack.Word

namespace Flapjack.RiscV

/-- The reviewed allocator instruction routes do not rename or record live
registers for the two 16-bit ordinary memory forms. Reject those forms at the
allocation boundary, including offset-bearing memory and nested handlers. -/
def allocatorMemorySupported {α : Type u} : WordProg α → Bool
  | .inst (.mem .load16 _ _) | .inst (.mem .store16 _ _) => false
  | .inst (.memOffset .load16 _ _ _) | .inst (.memOffset .store16 _ _ _) => false
  | .seq first second => allocatorMemorySupported first && allocatorMemorySupported second
  | .ite _ _ _ first second => allocatorMemorySupported first && allocatorMemorySupported second
  | .loop _ body _ | .mustTerminate body => allocatorMemorySupported body
  | .call returns _ _ handler =>
      (match returns with
       | none => true
       | some (_, _, body, _, _) => allocatorMemorySupported body) &&
      (match handler with
       | none => true
       | some (_, body, _, _) => allocatorMemorySupported body)
  | _ => true
termination_by program => sizeOf program

/-- An unsupported ordinary memory instruction occurs anywhere in the tree.
This occurrence predicate is Flapjack-specific allocator infrastructure. -/
inductive UnsupportedAllocatorMemory {α : Type u} : WordProg α → Prop where
  | load16 : UnsupportedAllocatorMemory (.inst (.mem .load16 dst address))
  | store16 : UnsupportedAllocatorMemory (.inst (.mem .store16 value address))
  | load16Offset : UnsupportedAllocatorMemory (.inst (.memOffset .load16 dst address offset))
  | store16Offset : UnsupportedAllocatorMemory (.inst (.memOffset .store16 value address offset))
  | seqLeft : UnsupportedAllocatorMemory first → UnsupportedAllocatorMemory (.seq first second)
  | seqRight : UnsupportedAllocatorMemory second → UnsupportedAllocatorMemory (.seq first second)
  | iteLeft : UnsupportedAllocatorMemory first → UnsupportedAllocatorMemory (.ite cmp left right first second)
  | iteRight : UnsupportedAllocatorMemory second → UnsupportedAllocatorMemory (.ite cmp left right first second)
  | loop : UnsupportedAllocatorMemory body → UnsupportedAllocatorMemory (.loop condition body cutset)
  | mustTerminate : UnsupportedAllocatorMemory body → UnsupportedAllocatorMemory (.mustTerminate body)
  | callReturn : UnsupportedAllocatorMemory body →
      UnsupportedAllocatorMemory (.call (some (ret, live, body, label, loc)) target args handler)
  | callHandler : UnsupportedAllocatorMemory body →
      UnsupportedAllocatorMemory (.call returns target args (some (exception, body, label)))

/-- The checked Boolean excludes every unsupported occurrence, including both
call continuations. It assumes no source-to-boundary closure property. -/
theorem allocatorMemorySupported_excludes {α : Type u} {program : WordProg α}
    (supported : allocatorMemorySupported program = true) :
    ¬ UnsupportedAllocatorMemory program := by
  intro occurrence
  induction occurrence <;> simp_all [allocatorMemorySupported]
  all_goals
    unfold allocatorMemorySupported at supported
    split at supported <;> simp_all

def assertAllocatorMemorySupported {α : Type u} (program : WordProg α) : Option (WordProg α) :=
  if allocatorMemorySupported program then some program else none

/-- Every successful boundary assertion preserves the input and validates the
complete recursive instruction tree. Flapjack-only production invariant. -/
theorem assertAllocatorMemorySupported_success {α : Type u} (program output : WordProg α)
    (h : assertAllocatorMemorySupported program = some output) :
    output = program ∧ allocatorMemorySupported program = true := by
  unfold assertAllocatorMemorySupported at h
  split at h <;> simp_all

end Flapjack.RiscV
