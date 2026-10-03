import Flapjack.Compiler.Backend.WordSimp.Proofs.GcConsts

namespace Flapjack.Test.WordSimpGenericCarriersParity
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordSimp

example {κ : Type} [DecidableEq κ]
    {width : Nat} [NeZero width] :
    ∀ (l1 l2 : List (κ × WordLocW width)) (k : κ) (v : WordLocW width),
      List.Forall₂ (fun (a b : κ × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l1 l2 ∧
        isGcWordConst v = true ∧ l1.lookup k = some v →
        l2.lookup k = some v := ALOOKUP_LIST_REL_sf_gc_consts

example
    {width : Nat} [NeZero width] :
    ∀ (l1 l2 : List (String × WordLocW width)) (k : String) (v : WordLocW width),
      List.Forall₂ (fun (a b : String × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l1 l2 ∧
        isGcWordConst v = true ∧ l1.lookup k = some v →
        l2.lookup k = some v := ALOOKUP_LIST_REL_sf_gc_consts

example {κ : Type} [DecidableEq κ]
    {width : Nat} [NeZero width] {ν : Type} (_v : ν) :
    ∀ (l1 l2 : List (κ × WordLocW width)) (k : κ),
      List.Forall₂ (fun (a b : κ × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l1 l2 ∧
        l1.lookup k = none → l2.lookup k = none := ALOOKUP_LIST_REL_sf_gc_consts_NONE _v

example
    {width : Nat} [NeZero width] {ν : Type} (_v : ν) :
    ∀ (l1 l2 : List (String × WordLocW width)) (k : String),
      List.Forall₂ (fun (a b : String × WordLocW width) =>
          a.1 = b.1 ∧ (isGcWordConst a.2 = true → b.2 = a.2)) l1 l2 ∧
        l1.lookup k = none → l2.lookup k = none := ALOOKUP_LIST_REL_sf_gc_consts_NONE _v

example {κ β : Type} [DecidableEq κ] :
    ∀ (f : β → Prop) (l' l : List (κ × β)) (k : κ) (v : β),
      List.Forall₂ (fun (a b : κ × β) => a.1 = b.1 ∧ (f a.2 → b.2 = a.2)) l' l ∧
        l'.lookup k = some v ∧ f v → l.lookup k = some v := ALOOKUP_LIST_REL_value_rel

example {β : Type} :
    ∀ (f : β → Prop) (l' l : List (String × β)) (k : String) (v : β),
      List.Forall₂ (fun (a b : String × β) => a.1 = b.1 ∧ (f a.2 → b.2 = a.2)) l' l ∧
        l'.lookup k = some v ∧ f v → l.lookup k = some v := ALOOKUP_LIST_REL_value_rel

example {κ β : Type} [DecidableEq κ] :
    ∀ l1 l2 : List (κ × β), (l1.map Prod.fst).Nodup ∧ holPerm l1 l2 →
      (fun k => l1.lookup k) = (fun k => l2.lookup k) := ALOOKUP_ALL_DISTINCT_FST_PERM

example {β : Type} :
    ∀ l1 l2 : List (String × β), (l1.map Prod.fst).Nodup ∧ holPerm l1 l2 →
      (fun k => l1.lookup k) = (fun k => l2.lookup k) := ALOOKUP_ALL_DISTINCT_FST_PERM

example {κ β : Type} [DecidableEq κ] :
    ∀ (l1 : List (κ × β)) (f : List (κ × β) → List (κ × β)) (k : κ) (v : β),
      (l1.map Prod.fst).Nodup ∧ holPerm l1 (f l1) ∧ l1.lookup k = some v →
        (f l1).lookup k = some v := ALOOKUP_ALL_DISTINCT_FST_PERM_SOME

example {β : Type} :
    ∀ (l1 : List (String × β)) (f : List (String × β) → List (String × β)) (k : String) (v : β),
      (l1.map Prod.fst).Nodup ∧ holPerm l1 (f l1) ∧ l1.lookup k = some v →
        (f l1).lookup k = some v := ALOOKUP_ALL_DISTINCT_FST_PERM_SOME

example {width : Nat} [NeZero width] {C : Type} {F : Type} {α : Type} :
    ∀ (moves : List (Nat × α)) (x : List (WordLocW width)) (s s' : WordSemStateFiniteExact width C F)
      (v : Nat),
      setVars (moves.map Prod.fst) x s = s' ∧ sptAListLookup v moves = none →
        getVar v s' = getVar v s := set_vars_move_NONE

example {width : Nat} [NeZero width] {C : Type} {F : Type}  :
    ∀ (moves : List (Nat × String)) (x : List (WordLocW width)) (s s' : WordSemStateFiniteExact width C F)
      (v : Nat),
      setVars (moves.map Prod.fst) x s = s' ∧ sptAListLookup v moves = none →
        getVar v s' = getVar v s := set_vars_move_NONE

example {α : Type} (names : Spt α × Spt α) :
    Compiler.Backend.WordSimp.allNames names = sptUnion names.1 names.2 := rfl

example (names : Spt Bool × Spt Bool) :
    Compiler.Backend.WordSimp.allNames names = sptUnion names.1 names.2 := rfl

end Flapjack.Test.WordSimpGenericCarriersParity
