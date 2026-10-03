load "preamble"; load "miscTheory";
open HolKernel Parse bossLib preamble miscTheory wordsTheory;
val _ = Globals.linewidth := 1000000;
val domain_full = prove(``∀a bs m md k. bytes_in_memory a bs m md ∧ k < LENGTH bs ⇒ ((a + n2w k) ∈ md)``,
Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  \\ Cases_on`k` \\ fs[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp[ADD1, GSYM word_add_n2w]);
val _ = if null(hyp domain_full) andalso null(free_vars(concl domain_full)) then () else raise Fail "open theorem";
val _ = print("domain_full_statement=" ^ term_to_string(concl domain_full) ^ "\n");
val _ = print("domain_full_proved=" ^ term_to_string(rhs(concl(EQT_INTRO domain_full))) ^ "\n");
fun row label tm = (print(label ^ "="); print_term(rhs(concl(EVAL tm))); print "\n");
val _ = row "domain_w1_k0" ``let a = 1w:1 word; bs = [7w:word8;7w;7w]; m = (\p:1 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 0 < LENGTH bs,w2n(a+n2w 0),a+n2w 0 IN d)``;
val _ = row "domain_w1_k1" ``let a = 1w:1 word; bs = [7w:word8;7w;7w]; m = (\p:1 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 1 < LENGTH bs,w2n(a+n2w 1),a+n2w 1 IN d)``;
val _ = row "domain_w1_k2" ``let a = 1w:1 word; bs = [7w:word8;7w;7w]; m = (\p:1 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 2 < LENGTH bs,w2n(a+n2w 2),a+n2w 2 IN d)``;
val _ = row "domain_w8_k0" ``let a = 255w:8 word; bs = [7w:word8;7w;7w]; m = (\p:8 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 0 < LENGTH bs,w2n(a+n2w 0),a+n2w 0 IN d)``;
val _ = row "domain_w8_k1" ``let a = 255w:8 word; bs = [7w:word8;7w;7w]; m = (\p:8 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 1 < LENGTH bs,w2n(a+n2w 1),a+n2w 1 IN d)``;
val _ = row "domain_w8_k2" ``let a = 255w:8 word; bs = [7w:word8;7w;7w]; m = (\p:8 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 2 < LENGTH bs,w2n(a+n2w 2),a+n2w 2 IN d)``;
val _ = row "domain_w64_k0" ``let a = 18446744073709551615w:64 word; bs = [7w:word8;7w;7w]; m = (\p:64 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 0 < LENGTH bs,w2n(a+n2w 0),a+n2w 0 IN d)``;
val _ = row "domain_w64_k1" ``let a = 18446744073709551615w:64 word; bs = [7w:word8;7w;7w]; m = (\p:64 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 1 < LENGTH bs,w2n(a+n2w 1),a+n2w 1 IN d)``;
val _ = row "domain_w64_k2" ``let a = 18446744073709551615w:64 word; bs = [7w:word8;7w;7w]; m = (\p:64 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 2 < LENGTH bs,w2n(a+n2w 2),a+n2w 2 IN d)``;
val _ = row "domain_w80_k0" ``let a = 1208925819614629174706175w:80 word; bs = [7w:word8;7w;7w]; m = (\p:80 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 0 < LENGTH bs,w2n(a+n2w 0),a+n2w 0 IN d)``;
val _ = row "domain_w80_k1" ``let a = 1208925819614629174706175w:80 word; bs = [7w:word8;7w;7w]; m = (\p:80 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 1 < LENGTH bs,w2n(a+n2w 1),a+n2w 1 IN d)``;
val _ = row "domain_w80_k2" ``let a = 1208925819614629174706175w:80 word; bs = [7w:word8;7w;7w]; m = (\p:80 word. 7w:word8); d = {a;a+1w;a+2w} in (bytes_in_memory a bs m d /\ 2 < LENGTH bs,w2n(a+n2w 2),a+n2w 2 IN d)``;
val _ = row "domain_empty" ``(bytes_in_memory (255w:word8) [] (\p:word8. 7w:word8) {}, 0 < LENGTH ([]:word8 list), 255w:word8 IN {})``;
val _ = row "domain_hole" ``(bytes_in_memory (255w:word8) [7w:word8;7w;7w] (\p:word8. 7w:word8) {255w;1w}, 1 < LENGTH ([7w:word8;7w;7w]), (255w:word8)+1w IN {255w;1w})``;
val _ = row "domain_wrong_byte" ``(bytes_in_memory (255w:word8) [7w:word8;8w;7w] (\p:word8. 7w:word8) {255w;0w;1w}, 1 < LENGTH ([7w:word8;8w;7w]), (255w:word8)+1w IN {255w;0w;1w})``;
val _ = row "domain_past_end" ``(bytes_in_memory (255w:word8) [7w:word8;7w;7w] (\p:word8. 7w:word8) {255w;0w;1w}, 3 < LENGTH ([7w:word8;7w;7w]), (255w:word8)+3w IN {255w;0w;1w})``;
