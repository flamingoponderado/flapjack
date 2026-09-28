(* Direct HOL evaluations for HOL.byteTheory.word_of_bytes
   (HOL/src/n-bit/byteScript.sml:197), the byte decoder used by the exact
   CakeML shared-memory load: panSemScript.sml:517/524 and crepSemScript.sml
   install `word_of_bytes F 0w new_bytes` for the FFI-returned byte list
   `new_bytes`, with no length premise. The FFI may therefore return MORE
   bytes than one word holds, so the overlong behaviour matters.

   `word_of_bytes_def` recurses `word_of_bytes be a (b::bs) =
   set_byte a b (word_of_bytes be (a + 1w) bs) be`, so the FIRST byte of the
   list is written OUTERMOST at address 0 and later bytes are written at
   increasing addresses (which wrap modulo `dimindex (:'a) DIV 8`). Hence at
   address 0 the earliest byte of each residue wins and only the first
   `dimindex (:'a) DIV 8` bytes survive; the discarded bytes are exactly the
   ones the Lean `panWordOfBytesHOL`/`crepClockWordOfBytes` little-endian
   decoders drop modulo `2 ^ dimindex`.

   `set_byte_def` is `[nocompute]`, so `EVAL` alone leaves the recursive chain
   symbolic; the rows below first unfold `word_of_bytes_def`/`set_byte_def`
   with `SIMP_CONV` and then `EVAL` the ground word terms.

   This probe is deliberately rooted at the separate HOL checkout (like
   fupdate_list_append_commutes_probeScript.sml); byteTheory is a standard
   HOL theory, so no CakeML build is required. Regenerate with:

     HOL4=<HOL checkout> CAKEML=<any CakeML source checkout> \
       HOL_PROBE_ONLY=pan_word_of_bytes_overlong_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   The output is captured in pan_word_of_bytes_overlong_probe.out. *)

load "bossLib";
load "byteTheory";
load "wordsLib";
load "boolSyntax";
open bossLib;
open HolKernel Parse;
open boolSyntax;
open byteTheory;
open wordsLib;

val decode_simps = [word_of_bytes_def, set_byte_def, byte_index_def, word_slice_alt_def];

(* `set_byte_def` is `[nocompute]`, so neither `EVAL` nor `SIMP_CONV` reduces
   the whole chain alone; alternate them until a fixed point. *)
fun try_eval q = (EVAL q) handle _ => REFL q;
fun try_simp q = (SIMP_CONV (std_ss) decode_simps q) handle _ => REFL q;

fun reduce q =
  let
    val q1 = rhs (concl (try_simp (rhs (concl (try_eval q)))))
    val q2 = rhs (concl (try_eval q1))
    val q3 = rhs (concl (try_simp q2))
  in
    rhs (concl (try_eval q3))
  end;

fun print_eval label q =
  print (label ^ "=" ^ term_to_string (reduce q) ^ "\n");

val _ = print ("source_def=" ^ term_to_string (concl word_of_bytes_def) ^ "\n");

(* Width 8: one byte per word, so the two trailing bytes wrap and are erased. *)
val _ = print_eval "w8_overlong_three"
  (``word_of_bytes F (0w : 8 word) [1w; 2w; 3w] : 8 word``);
val _ = print_eval "w8_overlong_take_one"
  (``word_of_bytes F (0w : 8 word) [1w; 2w; 3w] =
     word_of_bytes F (0w : 8 word) (TAKE 1 [1w; 2w; 3w])``);

(* Width 16: two bytes per word; the third byte wraps onto the low byte and is
   overwritten by the outermost write at address 0, so the result is 0x0201. *)
val _ = print_eval "w16_overlong_three"
  (``word_of_bytes F (0w : 16 word) [1w; 2w; 3w] : 16 word``);
val _ = print_eval "w16_overlong_sum"
  (``word_of_bytes F (0w : 16 word) [1w; 2w; 3w] = 1w + 2w * 256w : 16 word``);
val _ = print_eval "w16_overlong_take_two"
  (``word_of_bytes F (0w : 16 word) [1w; 2w; 3w] =
     word_of_bytes F (0w : 16 word) (TAKE 2 [1w; 2w; 3w])``);

(* Width 64: eight bytes per word; a ten-byte list keeps exactly the first
   eight bytes, so 255 and 7 are discarded. *)
val _ =
  print_eval "w64_overlong_ten"
    (``word_of_bytes F (0w : 64 word)
        [1w; 2w; 3w; 4w; 5w; 6w; 7w; 8w; 255w; 7w] : 64 word``);
val _ = print_eval "w64_overlong_take_eight"
  (``word_of_bytes F (0w : 64 word)
        [1w; 2w; 3w; 4w; 5w; 6w; 7w; 8w; 255w; 7w] =
     word_of_bytes F (0w : 64 word)
        (TAKE 8 [1w; 2w; 3w; 4w; 5w; 6w; 7w; 8w; 255w; 7w])``);
val _ = print_eval "w64_discarded_bytes_irrelevant"
  (``word_of_bytes F (0w : 64 word)
        [1w; 2w; 3w; 4w; 5w; 6w; 7w; 8w; 255w; 7w] =
     word_of_bytes F (0w : 64 word)
        [1w; 2w; 3w; 4w; 5w; 6w; 7w; 8w]``);

(* Width 9: `dimindex DIV 8 = 1`, so only the first byte survives (the low
   eight bits).  This is the non-multiple-of-eight case where a naive
   last-write-wins fold would keep the wrapped second byte and give
   `1 + 3 * 256 mod 512 = 257w` instead of `1w`. *)
val _ = print_eval "w9_overlong_two"
  (``word_of_bytes F (0w : 9 word) [1w; 3w] : 9 word``);
val _ = print_eval "w9_overlong_three"
  (``word_of_bytes F (0w : 9 word) [1w; 3w; 5w] : 9 word``);
val _ = print_eval "w9_overlong_take_one"
  (``word_of_bytes F (0w : 9 word) [1w; 3w; 5w] =
     word_of_bytes F (0w : 9 word) (TAKE 1 [1w; 3w; 5w])``);

(* Width 12: `dimindex DIV 8 = 1`, same one-byte-per-word behaviour. *)
val _ = print_eval "w12_overlong_four"
  (``word_of_bytes F (0w : 12 word) [7w; 9w; 11w; 13w] : 12 word``);

val _ = print ("done=ok\n");
