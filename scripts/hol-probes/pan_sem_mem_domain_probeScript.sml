(*
  Direct HOL-EVAL oracle for the panSem ordinary-memory domain boundary used by
  the production/exact PanSemState bridge (`StateBridge.PanSemMemoryRel`).

  HOL `memory` is total (`'a word -> 'a word_lab`) and every word/byte/32-bit
  access is gated by `memaddrs` *before* the cell is read:
    mem_load_def       :137-155  (One: `if addr IN dm then SOME (Val (m addr))`)
    mem_load_byte_def  :86-92    (`if byte_align w IN dm then ...`)
    mem_load_32_def    :94-106   (`if aligned 2 w ... if byte_align w IN dm ...`)
    mem_store_def      :373-378
    mem_stores_def     :380-386
    evaluate Store     :583-589 and eval Load :244-249

  The rows below pin: an in-domain load hit, an out-of-domain miss even when a
  word cell is present, and a store-then-load roundtrip.  They are the oracle
  for the Lean regressions in `Flapjack.Test.PanSemStateBridgeParity`, where the
  analogous production memory is partial (absent off `memaddrs`).
*)
load "bossLib";
load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end;

val s = ``(s:(64,unit) panSem$state)``;
val v = ``0x1122334455667788w:64 word``;
val stored = ``0x99w:64 word``;
val st = ``(^s with <|
  locals := FEMPTY; globals := FEMPTY; structs := []; code := FEMPTY;
  memory := (\a:64 word. if a = 0w then Word ^v else ARB);
  memaddrs := {0w}; sh_memaddrs := {0w}; be := F; clock := 10 |>)``;

(* In-domain `Load One` reads the total word cell. *)
val _ = print_eval "domain_load_hit"
  ``eval ^st (panLang$Load One (panLang$Const 0w))``;

(* Out-of-domain `Load One` misses even though the cell holds a word. *)
val _ = print_eval "domain_load_miss_present"
  ``eval (^st with memaddrs := ({} : 64 word set))
      (panLang$Load One (panLang$Const 0w))``;

(* Store then load at the same in-domain address returns the stored word. *)
val _ = print_eval "domain_store_then_load_hit"
  ``FST (evaluate
      (panLang$Seq
        (panLang$Store (panLang$Const 0w) (panLang$Const ^stored))
        (panLang$Return (panLang$Load One (panLang$Const 0w))),
       ^st))``;

(* The store itself fails out of domain. *)
val _ = print_eval "domain_store_miss"
  ``FST (evaluate
      (panLang$Store (panLang$Const 0w) (panLang$Const ^stored),
       ^st with memaddrs := ({} : 64 word set)))``;

(* `mem_stores` then `mem_load` at the raw definition level. *)
val _ = print_eval "domain_mem_stores_load_roundtrip"
  ``(case mem_stores (0w:64 word) [Word ^stored] ({(0w:64 word)} : 64 word set)
        (\a:64 word. if a = 0w then Word ^v else ARB) of
        SOME m => mem_load One (0w:64 word) ({(0w:64 word)} : 64 word set) m []
      | NONE => NONE)``;

val _ = print_eval "pan_sem_mem_domain_done" ``0``;
