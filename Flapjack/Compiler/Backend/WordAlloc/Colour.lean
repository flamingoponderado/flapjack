import Flapjack.Compiler.Backend.WordAlloc.Expressions
import Flapjack.Compiler.Backend.WordAlloc.Instructions
import Flapjack.Compiler.Backend.WordAlloc.KeyMaps

namespace Flapjack.WordAlloc

/-- Exact HOL program colouring `apply_colour_def`
(`word_allocScript.sml`), clause by clause over the exact `wordLang$prog`
carrier. `Move` keeps HOL's literal `ZIP (MAP (f o FST) ls, MAP (f o SND) ls)`;
returning-call cut sets, `Install`, `FFI` and `Alloc` rename both cut-set trees
with the tagged `apply_nummaps_key`, and `Loop` renames its live-in/live-out
sets with `apply_nummap_key`. Float registers, labels, store names, constant
lists and the `Set` store are unchanged. HOL's final catch-all (`Break`,
`Continue`) returns the program unchanged. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def applyColour {width : Nat} [NeZero width] (f : Nat → Nat) :
    WordLangProgHOL (BitVec width) → WordLangProgHOL (BitVec width)
  | .skip => .skip
  | .move pri ls => .move pri (List.zip (ls.map (f ∘ Prod.fst)) (ls.map (f ∘ Prod.snd)))
  | .inst i => .inst (applyColourInst f i)
  | .assign num exp => .assign (f num) (applyColourExp f exp)
  | .get num store => .get (f num) store
  | .store exp num => .store (applyColourExp f exp) (f num)
  | .call ret dest args h =>
      let ret' := match ret with
        | none => none
        | some (vs, cutset, retHandler, l1, l2) =>
            some (vs.map f, applyNummapsKey f cutset, applyColour f retHandler, l1, l2)
      let args' := args.map f
      let h' := match h with
        | none => none
        | some (v, prog, l1, l2) => some (f v, applyColour f prog, l1, l2)
      .call ret' dest args' h'
  | .seq s1 s2 => .seq (applyColour f s1) (applyColour f s2)
  | .mustTerminate s1 => .mustTerminate (applyColour f s1)
  | .ite cmp r1 ri e2 e3 =>
      .ite cmp (f r1) (applyColourImm f ri) (applyColour f e2) (applyColour f e3)
  | .install r1 r2 r3 r4 numset =>
      .install (f r1) (f r2) (f r3) (f r4) (applyNummapsKey f numset)
  | .codeBufferWrite r1 r2 => .codeBufferWrite (f r1) (f r2)
  | .dataBufferWrite r1 r2 => .dataBufferWrite (f r1) (f r2)
  | .ffi ffiIndex ptr1 len1 ptr2 len2 numset =>
      .ffi ffiIndex (f ptr1) (f len1) (f ptr2) (f len2) (applyNummapsKey f numset)
  | .locValue r l1 => .locValue (f r) l1
  | .alloc num numset => .alloc (f num) (applyNummapsKey f numset)
  | .storeConsts a b c d ws => .storeConsts (f a) (f b) (f c) (f d) ws
  | .raise num => .raise (f num)
  | .return num1 nums => .return (f num1) (nums.map f)
  | .tick => .tick
  | .set n exp => .set n (applyColourExp f exp)
  | .opCurrHeap b n1 n2 => .opCurrHeap b (f n1) (f n2)
  | .shareInst op v exp => .shareInst op (f v) (applyColourExp f exp)
  | .loop names body exitNames =>
      .loop (applyNummapKey f names) (applyColour f body) (applyNummapKey f exitNames)
  | p@(.break _) => p
  | p@(.continue _) => p

end Flapjack.WordAlloc
