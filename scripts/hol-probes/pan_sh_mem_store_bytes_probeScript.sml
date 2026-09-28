(* Direct HOL-EVAL probes for CakeML Pancake sh_mem_store payload bytes.
   Source: cakeml/pancake/semantics/panSemScript.sml sh_mem_store_def (528-547).
   sh_mem_store never writes local memory: it calls call_FFI (SharedMem
   MappedWrite) with `TAKE nb (word_to_bytes w F) ++ word_to_bytes addr F`
   (F = little-endian) and returns the input state with the new ffi.

   We use a `(64, word8 list) panSem$state` whose oracle echoes the payload
   back as the new ffi_state, so `s'.ffi.ffi_state` is exactly the payload
   bytes handed to the FFI. *)

load "preamble";
load "panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");

(* An oracle that stores the payload bytes in `ffi_state` and returns a
   same-length zero list, so `call_FFI` takes the FFI_return branch (it
   requires LENGTH bytes' = LENGTH bytes) and `s'.ffi.ffi_state` is exactly
   the payload handed to the FFI. *)
val echoOracle = ``(\(_ : ffiname) (st : word8 list) (conf : word8 list) (bytes : word8 list).
    Oracle_return bytes (REPLICATE (LENGTH bytes) (0w : word8))) : word8 list oracle``;
val echoFfi = ``(<| oracle := ^echoOracle; ffi_state := ([] : word8 list);
                   io_events := [] |>) : word8 list ffi_state``;
val finalOracle = ``(\(_ : ffiname) (st : word8 list) (conf : word8 list) (bytes : word8 list).
    Oracle_final FFI_failed) : word8 list oracle``;
val finalFfi = ``(<| oracle := ^finalOracle; ffi_state := ([] : word8 list);
                    io_events := [] |>) : word8 list ffi_state``;

val s = ``(s : (64, word8 list) panSem$state)``;

val base = ``(^s : (64, word8 list) panSem$state) with
    <| locals := FEMPTY; sh_memaddrs := {(0w:64 word)}; ffi := ^echoFfi |>``;
val missBase = ``(^s : (64, word8 list) panSem$state) with
    <| locals := FEMPTY; sh_memaddrs := {(1w:64 word)}; ffi := ^echoFfi |>``;
val finalBase = ``(^s : (64, word8 list) panSem$state) with
    <| locals := FEMPTY; sh_memaddrs := {(0w:64 word)}; ffi := ^finalFfi |>``;

val value = ``(0x1122334455667788w : 64 word)``;
val addr = ``(0w : 64 word)``;

fun payload nb =
  ``case sh_mem_store ^value ^addr ^nb ^base of
      | (NONE, s') => s'.ffi.ffi_state
      | _ => ([] : word8 list)``;

val _ = print_eval "store_w_payload" (payload ``(0:num)``);
val _ = print_eval "store_8_payload" (payload ``(1:num)``);
val _ = print_eval "store_16_payload" (payload ``(2:num)``);
val _ = print_eval "store_32_payload" (payload ``(4:num)``);

val _ = print_eval "store_16_result"
  ``FST (sh_mem_store ^value ^addr (2:num) ^base)``;
val _ = print_eval "store_16_miss"
  ``FST (sh_mem_store ^value ^addr (2:num) ^missBase)``;
val _ = print_eval "store_16_final_unchanged"
  ``case sh_mem_store ^value ^addr (2:num) ^finalBase of
      | (SOME (FinalFFI (Final_event _ _ _ oc)), s') =>
          (LENGTH s'.ffi.ffi_state, oc)
      | _ => (0, FFI_diverged)``;

print "done\n";