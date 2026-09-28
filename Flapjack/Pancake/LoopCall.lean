import Flapjack.Pancake.LoopLang

/-!
# Pancake `loop_call.comp`

This is the executable port of `cakeml/pancake/loop_callScript.sml:18-92`.
The environment is the source pass's `num |-> num` map, represented here by
an association list with first-match lookup and newest-entry insertion.  The
pass only carries location information through the cases where CakeML's
`comp_def` does so; all other forms return the source environment unchanged
or clear it exactly as the source equations specify.
-/

namespace Flapjack

namespace LoopCall

abbrev LocationEnv := List (Nat × Nat)

def lookup (name : Nat) : LocationEnv → Option Nat
  | [] => none
  | (candidate, location) :: entries =>
      if candidate = name then some location else lookup name entries

def insert (name location : Nat) (environment : LocationEnv) : LocationEnv :=
  (name, location) :: environment

def delete (name : Nat) : LocationEnv → LocationEnv
  | [] => []
  | (candidate, location) :: entries =>
      if candidate = name then delete name entries
      else (candidate, location) :: delete name entries

def listDelete (names : List Nat) (environment : LocationEnv) : LocationEnv :=
  names.foldl (fun environment name => delete name environment) environment

def splitLast : List α → Option (List α × α)
  | [] => none
  | value :: values =>
      match splitLast values with
      | none => some ([], value)
      | some (pre, lastValue) => some (value :: pre, lastValue)
termination_by values => sizeOf values

def compArith (environment : LocationEnv) : LoopArith → LocationEnv
  | .longMul sourceLeft sourceRight _ _
  | .longDiv sourceLeft sourceRight _ _ _ =>
      match lookup sourceLeft environment, lookup sourceRight environment with
      | none, none => environment
      | some _, none => delete sourceLeft environment
      | none, some _ => delete sourceRight environment
      | some _, some _ => delete sourceLeft (delete sourceRight environment)
  | .div destination _ _ =>
      match lookup destination environment with
      | none => environment
      | some _ => delete destination environment

def compCall (environment : LocationEnv)
    (returns : Option (List Nat × List Nat)) (target : Option Nat)
    (arguments : List Nat) (handler : Option (Nat × LoopProg α × LoopProg α × List Nat)) :
    LoopProg α × LocationEnv :=
  match target with
  | some _ => (.call returns target arguments handler, [])
  | none =>
      match splitLast arguments with
      | none => (.skip, [])
      | some (pre, lastValue) =>
          match lookup lastValue environment with
          | none => (.call returns none arguments handler, [])
          | some destination =>
              (.call returns (some destination) pre handler, [])

def comp : LocationEnv → LoopProg α → LoopProg α × LocationEnv
  | environment, .skip => (.skip, environment)
  | environment, .call returns target arguments handler =>
      compCall environment returns target arguments handler
  | environment, program@(.locValue destination source) =>
      (program, insert destination source environment)
  | environment, program@(.assign destination (.var source)) =>
      (program,
        match lookup destination environment, lookup source environment with
        | none, none => environment
        | some _, none => delete destination environment
        | _, some location => insert destination location environment)
  | environment, program@(.assign destination _) =>
      (program,
        match lookup destination environment with
        | none => environment
        | some _ => delete destination environment)
  | _, program@(.shMem _ _ _) => (program, [])
  | environment, program@(.load32 _ destination) =>
      (program,
        match lookup destination environment with
        | none => environment
        | some _ => delete destination environment)
  | environment, program@(.loadByte _ destination) =>
      (program,
        match lookup destination environment with
        | none => environment
        | some _ => delete destination environment)
  | environment, .seq first second =>
      let (compiledFirst, nextEnvironment) := comp environment first
      let (compiledSecond, _) := comp nextEnvironment second
      (.seq compiledFirst compiledSecond, [])
  | environment, .ite operator condition right thenBranch elseBranch live =>
      let (compiledThen, _) := comp environment thenBranch
      let (compiledElse, _) := comp environment elseBranch
      (.ite operator condition right compiledThen compiledElse live, [])
  | _, .loop liveIn body liveOut =>
      let (compiledBody, _) := comp [] body
      (.loop liveIn compiledBody liveOut, [])
  | environment, .mark body =>
      let (compiledBody, nextEnvironment) := comp environment body
      (.mark compiledBody, nextEnvironment)
  | _, program@(.ffi _ _ _ _ _ _) => (program, [])
  | _, program@.tick => (program, [])
  | _, program@(.raise _) => (program, [])
  | _, program@(.return _) => (program, [])
  | environment, program@(.primitive destinations _ _) =>
      (program, listDelete destinations environment)
  | environment, program@(.arith operation) =>
      (program, compArith environment operation)
  | environment, program => (program, environment)
termination_by _ program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! Basic lookup facts for the association-list location environment.  These
    are the list-backed counterparts of the `num |-> num` map facts
    (`lookup_insert`, `lookup_delete`) that CakeML's `loop_call` correctness
    proof relies on. -/

theorem lookup_cons (name candidate location : Nat) (entries : LocationEnv) :
    lookup name ((candidate, location) :: entries) =
      if candidate = name then some location else lookup name entries := rfl

theorem delete_cons (name candidate location : Nat) (entries : LocationEnv) :
    delete name ((candidate, location) :: entries) =
      if candidate = name then delete name entries
      else (candidate, location) :: delete name entries := rfl

theorem lookup_insert_same (name location : Nat) (environment : LocationEnv) :
    lookup name (insert name location environment) = some location := by
  simp [lookup, insert]

theorem lookup_insert_other (name location other : Nat) (environment : LocationEnv)
    (h : other ≠ name) :
    lookup other (insert name location environment) = lookup other environment := by
  simp only [insert]
  rw [lookup_cons, if_neg (fun hc => h hc.symm)]

theorem lookup_delete_same (name : Nat) (environment : LocationEnv) :
    lookup name (delete name environment) = none := by
  induction environment with
  | nil => simp [delete, lookup]
  | cons entry environment ih =>
      obtain ⟨candidate, location⟩ := entry
      rw [delete_cons]
      by_cases hc : candidate = name
      · rw [if_pos hc]
        exact ih
      · rw [if_neg hc]
        rw [lookup_cons, if_neg hc]
        exact ih

theorem lookup_delete_other (name other : Nat) (environment : LocationEnv)
    (h : other ≠ name) :
    lookup other (delete name environment) = lookup other environment := by
  induction environment with
  | nil => simp [delete, lookup]
  | cons entry environment ih =>
      obtain ⟨candidate, location⟩ := entry
      rw [delete_cons]
      by_cases hc : candidate = name
      · rw [if_pos hc]
        rw [lookup_cons, if_neg (fun hc' => h (hc'.symm.trans hc))]
        exact ih
      · rw [if_neg hc]
        by_cases ho : candidate = other
        · rw [lookup_cons, if_pos ho, lookup_cons, if_pos ho]
        · rw [lookup_cons, if_neg ho]
          rw [lookup_cons, if_neg ho]
          exact ih

end LoopCall

/-! ## `loop_call$comp` (`comp_def`) over the exact `HolLoopProg`/`Spt` carriers -/

/-- Exact port of HOL `loop_call$comp` (`cakeml/pancake/loop_callScript.sml:18-98`).
The live map is `num |-> num` (a `Spt Nat`), matching HOL: `LocValue` inserts a
number value, so the map value type is `num` (HOL `num_set = unit spt` is a
different, unrelated map).  The HOL declaration is `comp_def` in
`cakeml/pancake/loop_callScript.sml`. -/
@[hol "cakeml/pancake/loop_callScript.sml" "comp_def" (words_as_type_indexed_bitvec)]
def loopCallCompHOL {width : Nat} [NeZero width] (l : Spt Nat) :
    HolLoopProg width → HolLoopProg width × Spt Nat
  | .skip => (.skip, l)
  | .call returns target arguments handler =>
      let compiled :=
        match target with
        | some _ => .call returns target arguments handler
        | none =>
            match arguments.getLast? with
            | none => .skip
            | some last =>
                match sptLookup last l with
                | none => .call returns none arguments handler
                | some n => .call returns (some n) arguments.dropLast handler
      (compiled, .ln)
  | .locValue destination source =>
      (.locValue destination source, sptInsert destination source l)
  | .assign name (.var m) =>
      (.assign name (.var m),
        match sptLookup name l, sptLookup m l with
        | none, none => l
        | some _, none => sptDelete name l
        | _, some loc => sptInsert name loc l)
  | .assign name value =>
      (.assign name value,
        match sptLookup name l with
        | none => l
        | some _ => sptDelete name l)
  | .shMem operator name address => (.shMem operator name address, .ln)
  | .load32 address destination =>
      (.load32 address destination,
        match sptLookup destination l with
        | none => l
        | some _ => sptDelete destination l)
  | .loadByte address destination =>
      (.loadByte address destination,
        match sptLookup destination l with
        | none => l
        | some _ => sptDelete destination l)
  | .seq first second =>
      let (np, nl) := loopCallCompHOL l first
      let (nq, _) := loopCallCompHOL nl second
      (.seq np nq, .ln)
  | .ite operator condition right thenBranch elseBranch live =>
      let (np, _) := loopCallCompHOL l thenBranch
      let (nq, _) := loopCallCompHOL l elseBranch
      (.ite operator condition right np nq live, .ln)
  | .loop liveIn body liveOut =>
      let (np, _) := loopCallCompHOL .ln body
      (.loop liveIn np liveOut, .ln)
  | .mark body =>
      let (np, nl) := loopCallCompHOL l body
      (.mark np, nl)
  | .ffi function configuration configurationLength array arrayLength live =>
      (.ffi function configuration configurationLength array arrayLength live, .ln)
  | .tick => (.tick, .ln)
  | .raise exception => (.raise exception, .ln)
  | .return values => (.return values, .ln)
  | .primitive destinations operator arguments =>
      (.primitive destinations operator arguments, sptListDelete destinations l)
  | .arith operation =>
      (.arith operation,
        match operation with
        | .longMul destinationLeft destinationRight _ _ =>
            match sptLookup destinationLeft l, sptLookup destinationRight l with
            | none, none => l
            | some _, none => sptDelete destinationLeft l
            | none, some _ => sptDelete destinationRight l
            | _, _ => sptDelete destinationLeft (sptDelete destinationRight l)
        | .longDiv destinationLeft destinationRight _ _ _ =>
            match sptLookup destinationLeft l, sptLookup destinationRight l with
            | none, none => l
            | some _, none => sptDelete destinationLeft l
            | none, some _ => sptDelete destinationRight l
            | _, _ => sptDelete destinationLeft (sptDelete destinationRight l)
        | .div destination _ _ =>
            match sptLookup destination l with
            | none => l
            | some _ => sptDelete destination l)
  | program => (program, l)
termination_by prog => sizeOf prog
decreasing_by
  all_goals decreasing_trivial

end Flapjack
