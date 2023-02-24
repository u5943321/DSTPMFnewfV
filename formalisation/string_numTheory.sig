signature string_numTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val n2nsum_def : thm
    val n2s_def_primitive : thm
    val nsum2n_def : thm
    val s2n_def : thm
    val s2ssum_def : thm
    val ssum2s_def : thm
  
  (*  Theorems  *)
    val n2nsum_nsum2n : thm
    val n2s_11 : thm
    val n2s_def : thm
    val n2s_ind : thm
    val n2s_onto : thm
    val n2s_s2n : thm
    val nsum2n_n2nsum : thm
    val s2n_11 : thm
    val s2n_n2s : thm
    val s2n_onto : thm
    val s2ssum_ssum2s : thm
    val ssum2s_s2ssum : thm
  
  val string_num_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Pf0Drv] Parent theory of "string_num"
   
   [n2nsum_def]  Definition
      
      ⊢ ∀n. n2nsum n = if ODD n then INL (n DIV 2) else INR (n DIV 2)
   
   [n2s_def_primitive]  Definition
      
      ⊢ n2s =
        WFREC
          (@R. WF R ∧
               ∀n r0 r.
                 n ≠ 0 ∧ r0 = n MOD 256 ∧ r = (if r0 = 0 then 256 else r0) ⇒
                 R ((n − r) DIV 256) n)
          (λn2s a.
               I
                 (if a = 0 then ""
                  else
                    (let
                       r0 = a MOD 256;
                       r = if r0 = 0 then 256 else r0;
                       s0 = n2s ((a − r) DIV 256)
                     in
                       STRING (CHR (r − 1)) s0)))
   
   [nsum2n_def]  Definition
      
      ⊢ (∀n. nsum2n (INL n) = 2 * n + 1) ∧ ∀n. nsum2n (INR n) = 2 * n
   
   [s2n_def]  Definition
      
      ⊢ s2n "" = 0 ∧ ∀c s. s2n (STRING c s) = s2n s * 256 + ORD c + 1
   
   [s2ssum_def]  Definition
      
      ⊢ ∀s. s2ssum s = SUM_MAP n2s n2s (n2nsum (s2n s))
   
   [ssum2s_def]  Definition
      
      ⊢ ∀sm. ssum2s sm = n2s (nsum2n (SUM_MAP s2n s2n sm))
   
   [n2nsum_nsum2n]  Theorem
      
      ⊢ n2nsum (nsum2n ns) = ns
   
   [n2s_11]  Theorem
      
      ⊢ n2s x = n2s y ⇔ x = y
   
   [n2s_def]  Theorem
      
      ⊢ ∀n. n2s n =
            if n = 0 then ""
            else
              (let
                 r0 = n MOD 256;
                 r = if r0 = 0 then 256 else r0;
                 s0 = n2s ((n − r) DIV 256)
               in
                 STRING (CHR (r − 1)) s0)
   
   [n2s_ind]  Theorem
      
      ⊢ ∀P. (∀n. (∀r0 r.
                    n ≠ 0 ∧ r0 = n MOD 256 ∧
                    r = (if r0 = 0 then 256 else r0) ⇒
                    P ((n − r) DIV 256)) ⇒
                 P n) ⇒
            ∀v. P v
   
   [n2s_onto]  Theorem
      
      ⊢ ∀s. ∃n. s = n2s n
   
   [n2s_s2n]  Theorem
      
      ⊢ n2s (s2n s) = s
   
   [nsum2n_n2nsum]  Theorem
      
      ⊢ nsum2n (n2nsum n) = n
   
   [s2n_11]  Theorem
      
      ⊢ s2n x = s2n y ⇔ x = y
   
   [s2n_n2s]  Theorem
      
      ⊢ ∀n. s2n (n2s n) = n
   
   [s2n_onto]  Theorem
      
      ⊢ ∀n. ∃s. n = s2n s
   
   [s2ssum_ssum2s]  Theorem
      
      ⊢ s2ssum (ssum2s sm) = sm
   
   [ssum2s_s2ssum]  Theorem
      
      ⊢ ssum2s (s2ssum s) = s
   
   
*)
end
