module

public import Flapjack.Pancake.CrepToLoop
public import Flapjack.Pancake.LoopCall
public import Flapjack.LoopSemantics

@[expose] public section

/-!
Structural analyses for the Loop language. These are the list-based
counterparts of CakeML's `loop_live` inputs; a later pass can replace the
lists with a finite-set representation without changing the syntax layer.
-/

namespace Flapjack

def loopVarsOfExp : LoopExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => loopVarsOfExp address
  | .op _ arguments => arguments.flatMap loopVarsOfExp
  | .crepOp _ arguments => arguments.flatMap loopVarsOfExp
  | .cmp _ left right => loopVarsOfExp left ++ loopVarsOfExp right
  | .shift _ left right => loopVarsOfExp left ++ loopVarsOfExp right
  | .baseAddr => []
  | .topAddr => []

/-!
Context-aware port of the structured part of `loop_live$shrink`. The
context is stored outermost-first, so label `0` denotes the innermost
loop, matching HOL's `oEL` lookup.
-/

mutual
  /-- Exact port of HOL `loop_live$vars_of_exp_def`
      (`cakeml/pancake/loop_liveScript.sml:10-21`) over the faithful
      width-indexed `HolLoopExp` carrier and the exact `num_set`
      (`NumSet = Spt Unit`, `sptInsert`).  HOL declares `vars_of_exp` and
      `vars_of_exp_list` as one mutual definition; the second half is
      `varsOfExpListHOL` below. -/
  @[hol "cakeml/pancake/loop_liveScript.sml" "vars_of_exp_def"
    (words_as_type_indexed_bitvec)]
  def varsOfExpHOL {width : Nat} [NeZero width] :
      HolLoopExp width → NumSet → NumSet
    | .var name, live => sptInsert name () live
    | .const _, live => live
    | .lookup _, live => live
    | .load address, live => varsOfExpHOL address live
    | .op _ arguments, live => varsOfExpListHOL arguments live
    | .shift _ left right, live => varsOfExpHOL left (varsOfExpHOL right live)
    | .baseAddr, live => live
    | .topAddr, live => live

  /-- The `vars_of_exp_list` half of HOL's mutual `vars_of_exp_def`
      (`cakeml/pancake/loop_liveScript.sml:19-21`).  Untagged because HOL
      declares it inside the single `vars_of_exp_def` definition rather than
      as a separate declaration; its `@[hol]` reference is
      `varsOfExpHOL` above. -/
  def varsOfExpListHOL {width : Nat} [NeZero width] :
      List (HolLoopExp width) → NumSet → NumSet
    | [], live => live
    | expression :: rest, live => varsOfExpHOL expression (varsOfExpListHOL rest live)
end

def deleteNatSorted (name : Nat) : List Nat → List Nat
  | [] => []
  | head :: tail =>
      if name == head then deleteNatSorted name tail
      else head :: deleteNatSorted name tail

/-! Source-shaped port of `loop_live$arith_vars`
    (`cakeml/pancake/loop_liveScript.sml:50`). -/
def arithVars : LoopArith → List Nat → List Nat
  | .longMul destinationLeft destinationRight sourceLeft sourceRight, live =>
      insertNatSorted sourceLeft
        (insertNatSorted sourceRight
          (deleteNatSorted destinationLeft
            (deleteNatSorted destinationRight live)))
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient, live =>
      insertNatSorted sourceLeft
        (insertNatSorted sourceRight
          (insertNatSorted quotient
            (deleteNatSorted destinationLeft
              (deleteNatSorted destinationRight live))))
  | .div destination dividend divisor, live =>
      insertNatSorted dividend
        (insertNatSorted divisor (deleteNatSorted destination live))

/-- Exact port of HOL `loop_live$arith_vars`
    (`cakeml/pancake/loop_liveScript.sml:50-58`) over the faithful
    `LoopArith`/`NumSet` carriers (`insert`/`delete` are the spt-tree
    operations). The executable list-based `arithVars` above is the
    `List Nat` rendering; this is the exact-set form used by `shrink`. -/
@[hol "cakeml/pancake/loop_liveScript.sml" "arith_vars"]
def arithVarsHOL : LoopArith → NumSet → NumSet
  | .longMul destinationLeft destinationRight sourceLeft sourceRight, live =>
      sptInsert sourceLeft ()
        (sptInsert sourceRight ()
          (sptDelete destinationLeft (sptDelete destinationRight live)))
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient, live =>
      sptInsert sourceLeft ()
        (sptInsert sourceRight ()
          (sptInsert quotient ()
            (sptDelete destinationLeft (sptDelete destinationRight live))))
  | .div destination dividend divisor, live =>
      sptInsert dividend ()
        (sptInsert divisor () (sptDelete destination live))

def loopListDeleteSorted (names : List Nat) (live : List Nat) : List Nat :=
  names.foldl (fun current name => deleteNatSorted name current) live

/-- `deleteNatSorted` is a filter; this makes the membership facts below
    immediate. -/
theorem deleteNatSorted_eq_filter (name : Nat) (live : List Nat) :
    deleteNatSorted name live = live.filter (fun x => decide (x ≠ name)) := by
  induction live with
  | nil => simp [deleteNatSorted]
  | cons head tail ih =>
      rw [deleteNatSorted, ih, List.filter_cons]
      by_cases h : (name == head) = true
      · rw [if_pos h]
        have : decide (head ≠ name) = false := by
          rw [decide_eq_false_iff_not]
          exact fun hne => hne (beq_iff_eq.mp h).symm
        simp [this]
      · rw [if_neg h]
        have : decide (head ≠ name) = true := by
          rw [decide_eq_true_iff]
          exact fun hx => h (beq_iff_eq.mpr hx.symm)
        simp [this]

/-- Membership in `deleteNatSorted`: the removed name is the only difference. -/
theorem deleteNatSorted_mem (name : Nat) (live : List Nat) (x : Nat) :
    x ∈ deleteNatSorted name live ↔ x ∈ live ∧ x ≠ name := by
  rw [deleteNatSorted_eq_filter, List.mem_filter, decide_eq_true_iff]

/-- Cake's `domain_list_delete`
    (`cakeml/pancake/proofs/loop_liveProofScript.sml:561`): deleting a list of
    names removes exactly those names from the live set.  CakeML states this on
    HOL sets (`domain s DIFF set vs`); the list-backed Flapjack port states the
    same fact with membership. -/
theorem loopListDeleteSorted_mem (names : List Nat) (live : List Nat) (x : Nat) :
    x ∈ loopListDeleteSorted names live ↔ x ∈ live ∧ x ∉ names := by
  induction names generalizing live with
  | nil => simp [loopListDeleteSorted]
  | cons name names ih =>
      rw [show loopListDeleteSorted (name :: names) live =
          loopListDeleteSorted names (deleteNatSorted name live) from rfl]
      rw [ih, deleteNatSorted_mem]
      simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨hmem, hne⟩, hnotnames⟩
        exact ⟨hmem, hne, hnotnames⟩
      · rintro ⟨hmem, hne, hnotnames⟩
        exact ⟨⟨hmem, hne⟩, hnotnames⟩

def loopIntersectSorted (left right : List Nat) : List Nat :=
  left.filter (fun name => name ∈ right)

/-! Cake's fixedpoint grows only within `liveIn`, so at most one strict growth
    step is possible for each live name before the final stabilization check. -/
def loopFixedpointFuel (liveIn : List Nat) : Nat :=
  liveIn.length + 1

def loopContextAt : Nat → List (List Nat × List Nat) → Option (List Nat × List Nat)
  | _, [] => none
  | 0, context :: _ => some context
  | fuel + 1, _ :: contexts => loopContextAt fuel contexts

/-! Faithful port of CakeML Pancake's `locals_touched_def` from
    `cakeml/pancake/loopLangScript.sml:77`.  The source definition is used on
    the original Loop expressions, before the later Flapjack-only `crepOp` and
    comparison expression forms are introduced; those forms are nevertheless
    handled structurally here so the analysis remains total on `LoopExp`. -/
def loopLocalsTouched : LoopExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => loopLocalsTouched address
  | .op _ arguments => arguments.flatMap loopLocalsTouched
  | .crepOp _ arguments => arguments.flatMap loopLocalsTouched
  | .cmp _ left right => loopLocalsTouched left ++ loopLocalsTouched right
  | .shift _ left right => loopLocalsTouched left ++ loopLocalsTouched right
  | .baseAddr => []
  | .topAddr => []

@[simp] theorem loopLocalsTouched_const (value : α) :
    loopLocalsTouched (.const value) = [] := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_var (α : Type u) (name : Nat) :
    loopLocalsTouched (α := α) (.var name) = [name] := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_lookup {α : Type u} (address : BitVec 5) :
    loopLocalsTouched (α := α) (.lookup address) = [] := by
  simp [loopLocalsTouched]

def loopAssignedVars : LoopProg α → List Nat
  | .skip => []
  | .assign name _ => [name]
  | .primitive destinations _ _ => destinations
  | .arith operation =>
      match operation with
      | .longMul left right _ _ => [left, right]
      | .longDiv left right _ _ _ => [left, right]
      | .div destination _ _ => [destination]
  | .load32 _ destination => [destination]
  | .loadByte _ destination => [destination]
  | .seq first second => loopAssignedVars first ++ loopAssignedVars second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopAssignedVars thenBranch ++ loopAssignedVars elseBranch
  | .locValue destination _ => [destination]
  | .shMem _ destination _ => [destination]
  | .mark body => loopAssignedVars body
  | .loop _ body _ => loopAssignedVars body
  | .call none _ _ _ => []
  | .call (some (returns, _)) _ _ none => returns
  | .call (some (returns, _)) _ _ (some (exception, handler, normal, _)) =>
      returns ++ exception :: loopAssignedVars handler ++ loopAssignedVars normal
  | _ => []

def loopInsert (name : Nat) (names : List Nat) : List Nat :=
  if name ∈ names then names else name :: names

def loopInsertAll : List Nat → List Nat → List Nat
  | [], names => names
  | name :: rest, names => loopInsert name (loopInsertAll rest names)

def loopAccVars : LoopProg α → List Nat → List Nat
  | .seq first second, names => loopAccVars first (loopAccVars second names)
  | .break _, names => names
  | .continue _, names => names
  | .loop _ body _, names => loopAccVars body names
  | .ite _ _ _ thenBranch elseBranch _, names =>
      /- `loopLang$acc_vars` intentionally records assigned variables only;
         condition operands are reads and are not part of the dense
         `loop_to_word` context.  In particular, do not include the
         condition or register operand here (`loopLangScript.sml:123`). -/
      loopAccVars thenBranch (loopAccVars elseBranch names)
  | .arith operation, names =>
      match operation with
      | .longMul left right _ _ => loopInsertAll [left, right] names
      | .longDiv left right _ _ _ => loopInsertAll [left, right] names
      | .div destination _ _ => loopInsert destination names
  | .mark body, names => loopAccVars body names
  | .tick, names => names
  | .skip, names => names
  | .fail, names => names
  | .raise _, names => names
  | .return _, names => names
  | .call none _ _ _, names => names
  | .call (some (returns, _)) _ _ none, names =>
      loopInsertAll returns names
  | .call (some (returns, _)) _ _
      (some (exception, handler, normal, _)), names =>
      let names := loopAccVars handler (loopAccVars normal names)
      loopInsert exception (loopInsertAll returns names)
  | .locValue destination _label, names => loopInsert destination names
  | .assign destination _, names => loopInsert destination names
  | .primitive destinations _ _, names => loopInsertAll destinations names
  | .shMem _ destination _, names => loopInsert destination names
  | .store _ _, names => names
  | .setGlobal _ _, names => names
  | .load32 _ destination, names => loopInsert destination names
  | .loadByte _ destination, names => loopInsert destination names
  | .store32 _ _, names => names
  | .storeByte _ _, names => names
  | .ffi _ _ _ _ _ _, names => names

/-! Cake `loopPropsScript.sml:40` `cut_sets_def`: the list-backed live set
    after executing a Loop statement.  Cake's HOL `insert`/`num_set` is
    replaced by the sorted-list `insertNatSorted`, matching the rest of the
    Flapjack live-set layer. -/

def loopCutSets (live : List Nat) : LoopProg α → List Nat
  | .skip => live
  | .locValue destination _ => insertNatSorted destination live
  | .assign name _ => insertNatSorted name live
  | .load32 _ destination => insertNatSorted destination live
  | .loadByte _ destination => insertNatSorted destination live
  | .seq first second => loopCutSets (loopCutSets live first) second
  | .ite _ _ _ _ _ live' => live'
  | .arith (.longMul destinationLeft destinationRight _ _) =>
      insertNatSorted destinationLeft (insertNatSorted destinationRight live)
  | .arith (.longDiv destinationLeft destinationRight _ _ _) =>
      insertNatSorted destinationLeft (insertNatSorted destinationRight live)
  | .arith (.div destination _ _) => insertNatSorted destination live
  | _ => live

/-- Counterpart of Cake `survives_def` (`cakeml/pancake/semantics/loopPropsScript.sml:25`):
    a variable survives a Loop program when every control-flow path that can
    reach a use of it keeps it live.  Flapjack's live sets are plain lists, so
    Cake's `n ∈ domain cs` becomes list membership. -/
def loopSurvives (name : Nat) : LoopProg α → Prop
  | .ite _ _ _ thenBranch elseBranch live =>
      loopSurvives name thenBranch ∧ loopSurvives name elseBranch ∧ name ∈ live
  | .loop liveIn body liveOut =>
      name ∈ liveIn ∧ name ∈ liveOut ∧ loopSurvives name body
  | .call (some (_, cs)) _ _ none => name ∈ cs
  | .call (some (_, cs)) _ _ (some (_, first, second, ps)) =>
      name ∈ cs ∧ name ∈ ps ∧ loopSurvives name first ∧ loopSurvives name second
  | .ffi _ _ _ _ _ live => name ∈ live
  | .mark body => loopSurvives name body
  | .seq first second => loopSurvives name first ∧ loopSurvives name second
  | _ => True
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def loopCompSyntaxOk (live : List Nat) : LoopProg α → Prop
  | .skip => True
  | .assign _ _ => True
  | .arith _ => True
  | .break _ => True
  | .locValue _ _ => True
  | .load32 _ _ => True
  | .loadByte _ _ => True
  | .seq first second =>
      loopCompSyntaxOk live first ∧ loopCompSyntaxOk (loopCutSets live first) second
  | .ite _ _ _ thenBranch elseBranch liveOut =>
      loopCompSyntaxOk live thenBranch ∧ loopCompSyntaxOk live elseBranch ∧
        ∃ ns : List Nat, liveOut = ns.foldl (fun current name => insertNatSorted name current) live
  | .loop liveIn body liveOut =>
      live = liveIn ∧ live = liveOut ∧ loopCompSyntaxOk liveIn body
  | _ => False

theorem loopInsert_mem (name : Nat) (names : List Nat) (x : Nat) :
    x ∈ loopInsert name names ↔ x = name ∨ x ∈ names := by
  by_cases hname : name ∈ names
  · rw [loopInsert, if_pos hname]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun heq => heq ▸ hname) id⟩
  · rw [loopInsert, if_neg hname]
    exact List.mem_cons

theorem loopInsertAll_mem (added : List Nat) (names : List Nat) (x : Nat) :
    x ∈ loopInsertAll added names ↔ x ∈ added ∨ x ∈ names := by
  induction added generalizing names with
  | nil => simp [loopInsertAll]
  | cons name rest ih =>
      simp only [loopInsertAll]
      rw [loopInsert_mem name (loopInsertAll rest names) x, ih names]
      simp only [List.mem_cons]
      constructor
      · rintro (h | (h | h))
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

set_option linter.unusedSimpArgs false in
private theorem loopAccVars_mem_aux : ∀ (program : LoopProg α) (_acc : List Nat)
    (names : List Nat) (x : Nat),
    x ∈ loopAccVars program names ↔ x ∈ names ∨ x ∈ loopAccVars program [] := by
  apply loopAccVars.induct (motive := fun program _ =>
    ∀ names x, x ∈ loopAccVars program names ↔ x ∈ names ∨ x ∈ loopAccVars program [])
  · intro first second names ihSecond ihFirst names' x
    simp only [loopAccVars]
    rw [ihFirst (loopAccVars second names') x, ihFirst (loopAccVars second []) x,
      ihSecond names' x, ihSecond [] x]
    simp only [List.not_mem_nil, or_false]
    simp only [or_comm, or_left_comm]
  · intro label names names' x; simp [loopAccVars]
  · intro label names names' x; simp [loopAccVars]
  · intro liveIn body liveOut names ih names' x
    simp only [loopAccVars]; exact ih names' x
  · intro operator condition right thenBranch elseBranch live names ihElse ihThen names' x
    simp only [loopAccVars]
    rw [ihThen (loopAccVars elseBranch names') x, ihThen (loopAccVars elseBranch []) x,
      ihElse names' x, ihElse [] x]
    simp only [List.not_mem_nil, or_false]
    simp only [or_comm, or_left_comm]
  · intro names left right sourceLeft sourceRight names' x
    simp only [loopAccVars, loopInsertAll_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro names left right sourceLeft sourceRight quotient names' x
    simp only [loopAccVars, loopInsertAll_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro names destination dividend divisor names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro body names ih names' x
    simp only [loopAccVars]; exact ih names' x
  · intro names names' x; simp [loopAccVars]
  · intro names names' x; simp [loopAccVars]
  · intro names names' x; simp [loopAccVars]
  · intro exception names names' x; simp [loopAccVars]
  · intro values names names' x; simp [loopAccVars]
  · intro target arguments handler names names' x; simp [loopAccVars]
  · intro returns snd target arguments names names' x
    simp only [loopAccVars, loopInsertAll_mem, List.not_mem_nil, or_false]
    simp only [or_comm, or_left_comm]
  · intro returns snd target arguments exception handler normal snd_1 names ihNormal ihHandler names' x
    simp only [loopAccVars, loopInsert_mem, loopInsertAll_mem]
    rw [ihHandler (loopAccVars normal names') x, ihHandler (loopAccVars normal []) x,
      ihNormal names' x, ihNormal [] x]
    simp only [List.not_mem_nil, or_false, false_or]
    simp only [or_comm, or_left_comm]
  · intro destination _label names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro destination value names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro destinations operator arguments names names' x
    simp only [loopAccVars, loopInsertAll_mem, List.not_mem_nil, or_false]
    simp only [or_comm, or_left_comm]
  · intro operator destination address names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro address value names names' x; simp [loopAccVars]
  · intro address value names names' x; simp [loopAccVars]
  · intro address destination names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro address destination names names' x
    simp only [loopAccVars, loopInsert_mem, List.not_mem_nil, or_false, List.mem_cons]
    simp only [or_comm, or_left_comm]
  · intro address value names names' x; simp [loopAccVars]
  · intro address value names names' x; simp [loopAccVars]
  · intro function configuration configurationLength array arrayLength live names names' x
    simp [loopAccVars]

/-! ## Exact `loop_live` shrink/fixedpoint over the faithful carrier

Source-shaped port of the single HOL declaration `loop_live$shrink_def`
(`cakeml/pancake/loop_liveScript.sml:62-160`), over the faithful
`HolLoopProg`/`NumSet` carrier.  HOL declares BOTH `shrink` and `fixedpoint`
inside that one mutual block (there is no separate `fixedpoint_def`), with the
lexicographic termination measure `(prog_size (K 0) body, 0/1,
size live_in - size l1)`; the Lean definitions keep that mutual shape and
measure (`sizeOf` in place of `prog_size`, and `sptSize_inter_le` in place of
`size_inter`).  `shrinkHOL` is the tagged half carrying
`@[hol ... "shrink_def"]`, while `fixedpointHOL` is the untagged mutual half,
analogous to `varsOfExpListHOL`/`vars_of_exp_list`. -/

/-- Exact port of HOL `loop_liveScript.sml:28-31 size_mk_BN`. -/
@[hol "cakeml/pancake/loop_liveScript.sml" "size_mk_BN"]
theorem sptSize_mkBN {α : Type} (t1 t2 : Spt α) :
    sptSize (sptMkBN t1 t2) = sptSize (.bn t1 t2) := by
  cases t1 <;> cases t2 <;> simp [sptMkBN, sptSize]

/-- Exact port of HOL `loop_liveScript.sml:34-36 size_mk_BS`:
    `size (mk_BS t1 x t2) = size (BS t1 x t2)`. -/
@[hol "cakeml/pancake/loop_liveScript.sml" "size_mk_BS"]
theorem sptSize_mkBS {α : Type} (t1 t2 : Spt α) (x : α) :
    sptSize (sptMkBS t1 x t2) = sptSize (.bs t1 x t2) := by
  cases t1 <;> cases t2 <;> simp [sptMkBS, sptSize]

/-- Exact port of HOL `loop_liveScript.sml:40-48 size_inter`. -/
@[hol "cakeml/pancake/loop_liveScript.sml" "size_inter"]
theorem sptSize_inter_le {α β : Type} (l1 : Spt α) (l2 : Spt β) :
    sptSize (sptInter l1 l2) <= sptSize l1 := by
  induction l1 generalizing l2 with
  | ln => simp [sptInter]
  | ls value => cases l2 <;> simp [sptInter]
  | bn first second ihFirst ihSecond =>
      cases l2 with
      | ln => simp [sptInter]
      | ls value => simp [sptInter]
      | bn f s =>
          simp only [sptInter, sptSize_bn, sptSize_mkBN]
          have h1 := ihFirst f
          have h2 := ihSecond s
          omega
      | bs f value s =>
          simp only [sptInter, sptSize_bn, sptSize_mkBN]
          have h1 := ihFirst f
          have h2 := ihSecond s
          omega
  | bs first value second ihFirst ihSecond =>
      cases l2 with
      | ln => simp [sptInter]
      | ls v => simp [sptInter]
      | bn f s =>
          simp only [sptInter, sptSize_bs, sptSize_bn, sptSize_mkBN]
          have h1 := ihFirst f
          have h2 := ihSecond s
          omega
      | bs f v s =>
          simp only [sptInter, sptSize_bs, sptSize_mkBS]
          have h1 := ihFirst f
          have h2 := ihSecond s
          omega
mutual
  /-- The `fixedpoint` half of HOL's single `loop_live$shrink_def` mutual block
      (`cakeml/pancake/loop_liveScript.sml:142-150`): iterate `shrink` on the
      loop body until `inter live_in l0` stabilizes, returning the shrunk body
      and its live set, or `none` when no progress can be made.  This is the
      untagged mutual half of the tagged `shrinkHOL` (analogous to
      `varsOfExpListHOL`), since HOL has no separate `fixedpoint_def`. -/
  def fixedpointHOL {width : Nat} [NeZero width] :
      List (NumSet × NumSet) → NumSet → NumSet → NumSet → HolLoopProg width →
        Option (HolLoopProg width × NumSet)
    | lt, liveIn, l1, l2, body =>
        let (b, l0) := shrinkHOL ((sptInter liveIn l1, l2) :: lt) body l2
        if sptInter liveIn l0 = l1 then
          some (b, l0)
        else if h1 : sptSize (sptInter liveIn l0) ≤ sptSize l1 then
          none
        else
          have _hb : sptSize (sptInter liveIn l0) ≤ sptSize liveIn :=
            sptSize_inter_le liveIn l0
          have _hlt : sptSize l1 < sptSize (sptInter liveIn l0) :=
            Nat.lt_of_not_le h1
          fixedpointHOL lt liveIn (sptInter liveIn l0) l2 body
  termination_by _lt liveIn l1 _l2 body =>
    (sizeOf body, 1, sptSize liveIn - sptSize l1)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Prod.lex_def]
    all_goals simp
    all_goals omega

  /-- Exact port of HOL's single `loop_live$shrink_def`
      (`cakeml/pancake/loop_liveScript.sml:62-160`): shrink every cutset of
      `prog` and delete assignments to dead variables, returning the rewritten
      program and the resulting live set.  `lt` is the `break`/`continue`
      context, outermost first.  HOL declares `shrink` and `fixedpoint` in that
      one mutual block; `fixedpointHOL` above is the untagged mutual half. -/
  @[hol "cakeml/pancake/loop_liveScript.sml" "shrink_def" (words_as_type_indexed_bitvec)]
  def shrinkHOL {width : Nat} [NeZero width]
      (lt : List (NumSet × NumSet)) :
      HolLoopProg width → NumSet → HolLoopProg width × NumSet
    | .seq p1 p2, l =>
        let (p2', l) := shrinkHOL lt p2 l
        let (p1', l) := shrinkHOL lt p1 l
        (.seq p1' p2', l)
    | .loop liveIn body liveOut, l =>
        let l2 := sptInter liveOut l
        let bex := sptUnion liveIn l2
        match fixedpointHOL lt liveIn .ln bex body with
        | some (body', l0) =>
            let l' := sptInter liveIn l0
            (.loop l' body' l2, l')
        | none =>
            let (b, _) := shrinkHOL ((liveIn, l2) :: lt) body bex
            (.loop liveIn b l2, liveIn)
    | .ite x1 x2 x3 p1 p2 l1, l =>
        let l' := sptInter l l1
        let (p1', l1') := shrinkHOL lt p1 l'
        let (p2', l2') := shrinkHOL lt p2 l'
        let l3 := match x3 with | .reg r => sptInsert r () .ln | _ => .ln
        (.ite x1 x2 x3 p1' p2' l', sptInsert x2 () (sptUnion l3 (sptUnion l1' l2')))
    | .mark p1, l => shrinkHOL lt p1 l
    | .break n, _ =>
        (.break n, match sptOel n lt with | some (_, brk) => brk | none => .ln)
    | .continue n, _ =>
        (.continue n, match sptOel n lt with | some (cont, _) => cont | none => .ln)
    | .fail, _ => (.fail, .ln)
    | .skip, l => (.skip, l)
    | .return vs, _ => (.return vs, sptListInsert vs .ln)
    | .raise v, _ => (.raise v, sptInsert v () .ln)
    | .arith a, l => (.arith a, arithVarsHOL a l)
    | .primitive lhss pop rhss, l =>
        (.primitive lhss pop rhss, sptListInsert rhss (sptListDelete lhss l))
    | .locValue n m, l =>
        match sptLookup n l with
        | none => (.skip, l)
        | some _ => (.locValue n m, sptDelete n l)
    | .assign n x, l =>
        match sptLookup n l with
        | none => (.skip, l)
        | some _ => (.assign n x, varsOfExpHOL x (sptDelete n l))
    | .shMem op r ad, l => (.shMem op r ad, varsOfExpHOL ad (sptInsert r () l))
    | .store e n, l => (.store e n, varsOfExpHOL e (sptInsert n () l))
    | .setGlobal name e, l => (.setGlobal name e, varsOfExpHOL e l)
    | .call ret dest args handler, l =>
        let a := sptFromAList (args.map fun x => (x, ()))
        match ret with
        | none => (.call none dest args none, sptUnion a l)
        | some (ns, l1) =>
            match handler with
            | none =>
                let l3 := sptListDelete ns (sptInter l l1)
                (.call (some (ns, l3)) dest args none, sptUnion a l3)
            | some (e, h, r, liveOut) =>
                let (r', l2) := shrinkHOL lt r l
                let (h', l3) := shrinkHOL lt h l
                let l1' := sptInter l1 (sptUnion (sptListDelete ns l2) (sptDelete e l3))
                (.call (some (ns, l1')) dest args (some (e, h', r', sptInter l liveOut)),
                  sptUnion a l1')
    | .ffi n r1 r2 r3 r4 l1, l =>
        (.ffi n r1 r2 r3 r4 (sptInter l1 l),
          sptInsert r1 () (sptInsert r2 () (sptInsert r3 () (sptInsert r4 () (sptInter l1 l)))))
    | .load32 x y, l => (.load32 x y, sptInsert x () (sptDelete y l))
    | .loadByte x y, l => (.loadByte x y, sptInsert x () (sptDelete y l))
    | .store32 x y, l => (.store32 x y, sptInsert x () (sptInsert y () l))
    | .storeByte x y, l => (.storeByte x y, sptInsert x () (sptInsert y () l))
    | .tick, l => (.tick, l)
  termination_by prog _l => (sizeOf prog, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals simp only [Prod.lex_def]
    all_goals simp
    all_goals omega
end

/-- Exact HOL `loop_live$mark_all` (`cakeml/pancake/loop_liveScript.sml:189-215`)
over `HolLoopProg width`.  Runs after `shrinkHOL`; returns the rewritten program
and a Boolean flag recording whether the program is a `Mark`-able compound.  The
final catch-all clause mirrors HOL's `mark_all prog = (Mark prog, T)`. -/
@[hol "cakeml/pancake/loop_liveScript.sml" "mark_all_def" (words_as_type_indexed_bitvec)]
def markAllHOL {width : Nat} [NeZero width] : HolLoopProg width → HolLoopProg width × Bool
  | .seq first second =>
      let (first', firstMarked) := markAllHOL first
      let (second', secondMarked) := markAllHOL second
      let marked := firstMarked && secondMarked
      (if marked then .mark (.seq first' second') else .seq first' second', marked)
  | .loop liveIn body liveOut =>
      let (body', _) := markAllHOL body
      (.loop liveIn body' liveOut, false)
  | .ite operator condition right thenBranch elseBranch live =>
      let (then', thenMarked) := markAllHOL thenBranch
      let (else', elseMarked) := markAllHOL elseBranch
      let marked := thenMarked && elseMarked
      let program := .ite operator condition right then' else' live
      (if marked then .mark program else program, marked)
  | .mark body => markAllHOL body
  | .call returns target arguments none =>
      (.mark (.call returns target arguments none), true)
  | .call returns target arguments (some (exception, handler, normal, liveOut)) =>
      let (handler', handlerMarked) := markAllHOL handler
      let (normal', normalMarked) := markAllHOL normal
      let marked := handlerMarked && normalMarked
      let program :=
        .call returns target arguments (some (exception, handler', normal', liveOut))
      (if marked then .mark program else program, marked)
  | program => (.mark program, true)

/-- Exact HOL `loop_live$comp` (`cakeml/pancake/loop_liveScript.sml:217-219`):
`comp prog = FST (mark_all (FST (shrink [] prog LN)))` over `HolLoopProg width`. -/
@[hol "cakeml/pancake/loop_liveScript.sml" "comp_def" (words_as_type_indexed_bitvec)]
def compHOL {width : Nat} [NeZero width] (prog : HolLoopProg width) : HolLoopProg width :=
  (markAllHOL (shrinkHOL [] prog .ln).1).1

/-! ## `optimise` (composes `loop_live$comp` with `loop_call$comp`) -/

/-- Exact port of HOL `loop_live$optimise` (`cakeml/pancake/loop_liveScript.sml:221-223`):
`optimise prog = (comp o FST o loop_call$comp LN) prog`.  Here `comp` is the
loop_live `comp` (already ported as `compHOL`), and the `loop_call$comp` map is
the empty `num |-> num` (`Spt Nat`). -/
@[hol "cakeml/pancake/loop_liveScript.sml" "optimise_def" (words_as_type_indexed_bitvec)]
def optimiseHOL {width : Nat} [NeZero width] (prog : HolLoopProg width) : HolLoopProg width :=
  compHOL (loopCallCompHOL (.ln : Spt Nat) prog).1

end Flapjack
