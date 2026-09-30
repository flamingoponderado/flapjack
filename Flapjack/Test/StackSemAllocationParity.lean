import Flapjack.Compiler.Backend.Semantics.StackSem.Allocation

open Flapjack Flapjack.StackSemAllocation

/- Original HOL observations: scripts/hol-probes/stacksem_allocation_probe.out.
The base state below is arbitrary: every field inspected by these transitions
is fixed by the fixture, and untouched fields do not enter the observation. -/
private def spaceStore : HolFiniteMapExact WordStoreHOL (WordLocW 8) :=
  (HolFiniteMapExact.empty.updateEq (.nextFree,.word 5)).updateEq (.triggerGC,.word 20)
-- space_true=SOME T
example : hasSpace (.word 10 : WordLocW 8) spaceStore = some true := by decide +kernel
-- space_false=SOME F
example : hasSpace (.word 16 : WordLocW 8) spaceStore = some false := by decide +kernel
-- space_wrap=SOME T
example : hasSpace (.word 250 : WordLocW 8)
    ((HolFiniteMapExact.empty.updateEq (.nextFree,(.word 10 : WordLocW 8))).updateEq
      (.triggerGC,.word 4)) = some true := by decide +kernel
-- space_loc=NONE
example : hasSpace (.loc 1 0 : WordLocW 8) spaceStore = none := by decide +kernel
-- space_missing=NONE
example : hasSpace (.word 0 : WordLocW 8)
    (HolFiniteMapExact.empty : HolFiniteMapExact WordStoreHOL (WordLocW 8)) = none := by decide +kernel
-- space_next_loc=NONE
example : hasSpace (.word 0 : WordLocW 8)
    ((HolFiniteMapExact.empty.updateEq (.nextFree,(.loc 1 0 : WordLocW 8))).updateEq
      (.triggerGC,.word 20)) = none := by decide +kernel
-- space_mixed=SOME T
example : hasSpace (.word 1 : WordLocW 1) spaceStore = some true := by decide +kernel

variable {C F : Type} (s : StackSemStateFiniteExact 8 C F)
-- gc_short=NONE
example : gc {s with stack := [],stackSpace := 1} = none := by
  cbv
-- gc_bad_stack=NONE
example : gc {s with stack := [],stackSpace := 0,bitmaps := []} = none := by
  cbv
-- gc_none=NONE
example : gc {s with stack := [.word 0],stackSpace := 0,bitmaps := [], gcFun := fun _ => none} = none := by
  cbv
-- gc_decode_fail=NONE
example : gc {s with stack := [.word 0],stackSpace := 0,bitmaps := [], gcFun := fun (_,m,_,st) => some ([.word 1],m,st)} = none := by
  cbv
-- gc_success=SOME ([Word 99w; Word 1w; Word 9w; Word 0w],NONE,SOME (Word 5w),Word 8w)
example : (gc {s with stack := [.word 99,.word 1,.word 7,.word 0], stackSpace := 1,bitmaps := [3],regs := HolFiniteMapExact.empty.updateEq (9,.word 2), memory := fun _ => .word 0,mdomain := fun _ => true, store := HolFiniteMapExact.empty.updateEq (.allocSize,.word 4), gcFun := fun (_,_,_,st) => some ([.word 9],(fun _ => .word 8),st.updateEq (.allocSize,.word 5))}).map
      (fun t => (t.stack,t.regs.lookup 9,t.store.lookup .allocSize,t.memory 0)) =
    some ([.word 99,.word 1,.word 9,.word 0],none,some (.word 5),.word 8) := by
  cbv

private def allocationFixture (s : StackSemStateFiniteExact 8 C F)
    (callback : WordSemGcFun 8) : StackSemStateFiniteExact 8 C F :=
  { s with stack := [.word 0],stackSpace := 0,bitmaps := [], regs := HolFiniteMapExact.empty.updateEq (9,.word 2),memory := fun _ => .word 0, mdomain := fun _ => true, store := ((HolFiniteMapExact.empty.updateEq (.allocSize,.word 4)).updateEq (.nextFree,.word 5)).updateEq (.triggerGC,.word 20),gcFun := callback }
private def observation (result : Option (StackSemResult 8) × StackSemStateFiniteExact 8 C F) :=
  (result.1,result.2.stack,result.2.regs.lookup 9,result.2.store.lookup .allocSize,result.2.memory 0)
example : observation (alloc 10 (allocationFixture s (fun (wl,m,_,st) => some (wl,m,st)))) =
    (none,[.word 0],none,some (.word 10),.word 0) := by
  cbv
example : observation (alloc 16 (allocationFixture s (fun (wl,m,_,st) => some (wl,m,st)))) =
    (some (.halt (.word 1)),[],none,some (.word 16),.word 0) := by
  cbv
example : observation (alloc 10 (allocationFixture s (fun _ => none))) =
    (some .error,[.word 0],some (.word 2),some (.word 4),.word 0) := by
  cbv
example : observation (alloc 10 (allocationFixture s (fun (wl,m,_,_) => some (wl,m,HolFiniteMapExact.empty)))) =
    (some .error,[.word 0],none,none,.word 0) := by
  cbv
example : observation (alloc 10 (allocationFixture s (fun (wl,m,_,st) => some (wl,m,st.updateEq (.allocSize,.loc 1 0))))) =
    (some .error,[.word 0],none,some (.loc 1 0),.word 0) := by
  cbv
example : observation (alloc 10 (allocationFixture s (fun (wl,m,_,_) =>
    some (wl,m,(HolFiniteMapExact.empty.updateEq (.allocSize,.word 10)).updateEq (.triggerGC,.word 20))))) =
    (some .error,[.word 0],none,some (.word 10),.word 0) := by
  cbv
