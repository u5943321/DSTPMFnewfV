signature tmatchTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val complete_def : thm
    val cstt_def : thm
    val finput_def : thm
    val form_TY_DEF : thm
    val form_case_def : thm
    val form_size_def : thm
    val foutput_def : thm
    val is_cont_def : thm
    val o_vmap_def : thm
    val sort_TY_DEF : thm
    val sort_case_def : thm
    val sort_of_def : thm
    val stms_def : thm
    val term_TY_DEF : thm
    val term_case_def : thm
    val term_size_def : thm
    val tfv_def_UNION_extract0 : thm
    val tfv_def_UNION_extract1 : thm
    val tfv_def_UNION_primitive : thm
    val tinst_def_UNION_extract0 : thm
    val tinst_def_UNION_extract1 : thm
    val tinst_def_UNION_primitive : thm
    val tmatch_def_UNION_AUX : thm
    val tmatch_def_UNION_extract0 : thm
    val tmatch_def_UNION_extract1 : thm
    val tmatch_def_UNION_extract2 : thm
    val tmatch_def_UNION_primitive : thm
    val tsubtm_def_UNION_extract0 : thm
    val tsubtm_def_UNION_extract1 : thm
    val tsubtm_def_UNION_primitive : thm
    val vmap_fix_def : thm
  
  (*  Theorems  *)
    val DRESTRICT_SUBMAP_SUBSET : thm
    val DRESTRICT_UNION_SING : thm
    val FAPPLY_o_vmap : thm
    val FDOM_o_vmap : thm
    val FEMPTY_complete : thm
    val FEMPTY_cstt : thm
    val FUNION_COMM1 : thm
    val IS_SOME_match : thm
    val IS_SOME_match_FEMPTY : thm
    val MEM_list_size_leq : thm
    val SUBMAP_DRESTRICT_IFF : thm
    val UNION_is_cont : thm
    val better_tm_induction : thm
    val complete_FDOM_is_cont : thm
    val cstt_SUBMAP : thm
    val cstt_sort_of_tinst : thm
    val datatype_form : thm
    val datatype_term : thm
    val fmap_fv_inst_eq : thm
    val form_11 : thm
    val form_Axiom : thm
    val form_case_cong : thm
    val form_case_eq : thm
    val form_distinct : thm
    val form_induction : thm
    val form_nchotomy : thm
    val fv_subtm : thm
    val inst_o_vmap : thm
    val match_SOME_cstt : thm
    val match_SOME_iff_inst : thm
    val match_SOME_iff_inst' : thm
    val match_SUBMAP : thm
    val match_complete : thm
    val o_vmap_cstt : thm
    val sfv_tfv : thm
    val sort_11 : thm
    val sort_Axiom : thm
    val sort_case_cong : thm
    val sort_case_eq : thm
    val sort_induction : thm
    val sort_nchotomy : thm
    val ssubtm_tsubtm : thm
    val term_11 : thm
    val term_Axiom : thm
    val term_case_cong : thm
    val term_case_eq : thm
    val term_distinct : thm
    val term_induction : thm
    val term_nchotomy : thm
    val term_size_eq : thm
    val tfv_def : thm
    val tfv_ind : thm
    val tfv_is_cont : thm
    val tfv_sinst : thm
    val tfv_thm : thm
    val tinst_def : thm
    val tinst_ind : thm
    val tinst_subtm : thm
    val tinst_vmap_id : thm
    val tlmatch_FEMPTY_each : thm
    val tlmatch_LENGTH : thm
    val tlmatch_SOME_MAP : thm
    val tlmatch_each : thm
    val tlmatch_each_imp_tinst : thm
    val tlmatch_each_lemma : thm
    val tlmatch_tinst_imp_SOME : thm
    val tlmatch_tinst_imp_SOME' : thm
    val tm_induction2 : thm
    val tm_tree_WF : thm
    val tm_tree_size_less : thm
    val tmatch_FDOM_SUBMAP : thm
    val tmatch_FEMPTY : thm
    val tmatch_FEMPTY_property : thm
    val tmatch_SOME_tinst : thm
    val tmatch_TRANS : thm
    val tmatch_TRANS_lemma : thm
    val tmatch_def : thm
    val tmatch_ind : thm
    val tsubtm_REFL : thm
    val tsubtm_def : thm
    val tsubtm_ind : thm
    val update_inst_lemma : thm
    val vmap_fix_FEMPTY : thm
    val vsort_tfv_closed : thm
    val wfvmap_cont_DRESTRICT : thm
  
  val tmatch_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [finite_map] Parent theory of "tmatch"
   
   [finite_set] Parent theory of "tmatch"
   
   [string] Parent theory of "tmatch"
   
   [complete_def]  Definition
      
      ⊢ ∀σ. complete σ ⇔ ∀n s. (n,s) ∈ FDOM σ ⇒ ∀v. v ∈ sfv s ⇒ v ∈ FDOM σ
   
   [cstt_def]  Definition
      
      ⊢ ∀σ. cstt σ ⇔ ∀n s. (n,s) ∈ FDOM σ ⇒ sort_of (σ ' (n,s)) = sinst σ s
   
   [finput_def]  Definition
      
      ⊢ ∀Σf f. finput Σf f = SND (Σf ' f)
   
   [form_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('form').
                   (∀a0'.
                      a0' =
                      ind_type$CONSTR 0 (ARB,ARB,ARB,ARB)
                        (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC 0) (a0,a1,ARB,ARB)
                                (λn. ind_type$BOTTOM)) a0 a1) ∨
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC 0))
                                (ARB,ARB,ARB,ARB)
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('form') a0 ∧ $var$('form') a1) ∨
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR (SUC (SUC (SUC 0)))
                                (a0,ARB,a1,ARB)
                                (ind_type$FCONS a2 (λn. ind_type$BOTTOM)))
                           a0 a1 a2 ∧ $var$('form') a2) ∨
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR (SUC (SUC (SUC (SUC 0))))
                                (a0,a2,ARB,a1) (λn. ind_type$BOTTOM)) a0 a1
                           a2) ⇒
                      $var$('form') a0') ⇒
                   $var$('form') a0') rep
   
   [form_case_def]  Definition
      
      ⊢ (∀v f f1 f2 f3. form_CASE False v f f1 f2 f3 = v) ∧
        (∀a0 a1 v f f1 f2 f3. form_CASE (Pred a0 a1) v f f1 f2 f3 = f a0 a1) ∧
        (∀a0 a1 v f f1 f2 f3. form_CASE (IMP a0 a1) v f f1 f2 f3 = f1 a0 a1) ∧
        (∀a0 a1 a2 v f f1 f2 f3.
           form_CASE (FALL a0 a1 a2) v f f1 f2 f3 = f2 a0 a1 a2) ∧
        ∀a0 a1 a2 v f f1 f2 f3.
          form_CASE (fVar a0 a1 a2) v f f1 f2 f3 = f3 a0 a1 a2
   
   [form_size_def]  Definition
      
      ⊢ form_size False = 0 ∧
        (∀a0 a1.
           form_size (Pred a0 a1) =
           1 + (list_size char_size a0 + list_size term_size a1)) ∧
        (∀a0 a1. form_size (IMP a0 a1) = 1 + (form_size a0 + form_size a1)) ∧
        (∀a0 a1 a2.
           form_size (FALL a0 a1 a2) =
           1 + (list_size char_size a0 + (sort_size a1 + form_size a2))) ∧
        ∀a0 a1 a2.
          form_size (fVar a0 a1 a2) =
          1 +
          (list_size char_size a0 +
           (list_size (pair_size (list_size char_size) sort_size) a1 +
            list_size term_size a2))
   
   [foutput_def]  Definition
      
      ⊢ ∀Σf f. foutput Σf f = FST (Σf ' f)
   
   [is_cont_def]  Definition
      
      ⊢ ∀ct. is_cont ct ⇔ ∀n s. (n,s) ∈ ct ⇒ sfv s ⊆ ct
   
   [o_vmap_def]  Definition
      
      ⊢ ∀σ2 σ1. o_vmap σ2 σ1 = FMAP_MAP2 (λ((n,s),t). tinst σ2 t) σ1
   
   [sort_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa1'.
                 ∀ $var$('term') $var$('sort')
                     $var$('@temp @ind_typetmatch0list').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 a0
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('sort') a1) ∨
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR (SUC 0) a0
                                (ind_type$FCONS a1
                                   (ind_type$FCONS a2 (λn. ind_type$BOTTOM))))
                           a0 a1 a2 ∧ $var$('sort') a1 ∧
                         $var$('@temp @ind_typetmatch0list') a2) ⇒
                      $var$('term') a0') ∧
                   (∀a1'.
                      (∃a0 a1.
                         a1' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC 0)) a0
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('@temp @ind_typetmatch0list') a1) ⇒
                      $var$('sort') a1') ∧
                   (∀a2'.
                      a2' =
                      ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                        (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a2' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC (SUC (SUC 0)))) ARB
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('term') a0 ∧
                         $var$('@temp @ind_typetmatch0list') a1) ⇒
                      $var$('@temp @ind_typetmatch0list') a2') ⇒
                   $var$('sort') a1') rep
   
   [sort_case_def]  Definition
      
      ⊢ ∀a0 a1 f. sort_CASE (St a0 a1) f = f a0 a1
   
   [sort_of_def]  Definition
      
      ⊢ (∀n s. sort_of (Var n s) = s) ∧ ∀f s l. sort_of (Fn f s l) = s
   
   [stms_def]  Definition
      
      ⊢ ∀n tl. stms (St n tl) = tl
   
   [term_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('term') $var$('sort')
                     $var$('@temp @ind_typetmatch0list').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 a0
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('sort') a1) ∨
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR (SUC 0) a0
                                (ind_type$FCONS a1
                                   (ind_type$FCONS a2 (λn. ind_type$BOTTOM))))
                           a0 a1 a2 ∧ $var$('sort') a1 ∧
                         $var$('@temp @ind_typetmatch0list') a2) ⇒
                      $var$('term') a0') ∧
                   (∀a1'.
                      (∃a0 a1.
                         a1' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC 0)) a0
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('@temp @ind_typetmatch0list') a1) ⇒
                      $var$('sort') a1') ∧
                   (∀a2'.
                      a2' =
                      ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                        (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a2' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC (SUC (SUC 0)))) ARB
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('term') a0 ∧
                         $var$('@temp @ind_typetmatch0list') a1) ⇒
                      $var$('@temp @ind_typetmatch0list') a2') ⇒
                   $var$('term') a0') rep
   
   [term_case_def]  Definition
      
      ⊢ (∀a0 a1 f f1. term_CASE (Var a0 a1) f f1 = f a0 a1) ∧
        ∀a0 a1 a2 f f1. term_CASE (Fn a0 a1 a2) f f1 = f1 a0 a1 a2
   
   [term_size_def]  Definition
      
      ⊢ (∀a0 a1.
           term_size (Var a0 a1) =
           1 + (list_size char_size a0 + sort_size a1)) ∧
        (∀a0 a1 a2.
           term_size (Fn a0 a1 a2) =
           1 + (list_size char_size a0 + (sort_size a1 + term1_size a2))) ∧
        (∀a0 a1.
           sort_size (St a0 a1) =
           1 + (list_size char_size a0 + term1_size a1)) ∧
        term1_size [] = 0 ∧
        ∀a0 a1. term1_size (a0::a1) = 1 + (term_size a0 + term1_size a1)
   
   [tfv_def_UNION_extract0]  Definition
      
      ⊢ ∀x. tfv x = tfv_def_UNION (INL x)
   
   [tfv_def_UNION_extract1]  Definition
      
      ⊢ ∀x. sfv x = tfv_def_UNION (INR x)
   
   [tfv_def_UNION_primitive]  Definition
      
      ⊢ tfv_def_UNION =
        WFREC
          (@R. WF R ∧ (∀n s. R (INR s) (INL (Var n s))) ∧
               (∀tl n s. R (INR s) (INL (Fn n s tl))) ∧
               (∀s n tl a. MEM a tl ⇒ R (INL a) (INL (Fn n s tl))) ∧
               ∀n tl a. MEM a tl ⇒ R (INL a) (INR (St n tl)))
          (λtfv_def_UNION a'.
               case a' of
                 INL (Var n s) => I ({(n,s)} ∪ tfv_def_UNION (INR s))
               | INL (Fn n' s' tl) =>
                 I
                   (BIGUNION (set (MAP (λa. tfv_def_UNION (INL a)) tl)) ∪
                    tfv_def_UNION (INR s'))
               | INR (St n'' tl') =>
                 I (BIGUNION (set (MAP (λa. tfv_def_UNION (INL a)) tl'))))
   
   [tinst_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0. tinst x x0 = OUTL (tinst_def_UNION (INL (x,x0)))
   
   [tinst_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0. sinst x x0 = OUTR (tinst_def_UNION (INR (x,x0)))
   
   [tinst_def_UNION_primitive]  Definition
      
      ⊢ tinst_def_UNION =
        WFREC
          (@R. WF R ∧
               (∀σ s n. (n,s) ∉ FDOM σ ⇒ R (INR (σ,s)) (INL (σ,Var n s))) ∧
               (∀tl f s σ. R (INR (σ,s)) (INL (σ,Fn f s tl))) ∧
               (∀s f σ tl a. MEM a tl ⇒ R (INL (σ,a)) (INL (σ,Fn f s tl))) ∧
               ∀n σ tl a. MEM a tl ⇒ R (INL (σ,a)) (INR (σ,St n tl)))
          (λtinst_def_UNION a'.
               case a' of
                 INL (σ,Var n s) =>
                   I
                     (INL
                        (if (n,s) ∉ FDOM σ then
                           Var n (OUTR (tinst_def_UNION (INR (σ,s))))
                         else σ ' (n,s)))
               | INL (σ,Fn f s' tl) =>
                 I
                   (INL
                      (Fn f (OUTR (tinst_def_UNION (INR (σ,s'))))
                         (MAP (λa. OUTL (tinst_def_UNION (INL (σ,a)))) tl)))
               | INR (σ',St n' tl') =>
                 I
                   (INR
                      (St n'
                         (MAP (λa. OUTL (tinst_def_UNION (INL (σ',a)))) tl'))))
   
   [tmatch_def_UNION_AUX]  Definition
      
      ⊢ ∀R. tmatch_def_UNION_aux R =
            WFREC R
              (λtmatch_def_UNION a.
                   case a of
                     INL (lcs,Var n s,ct,f) =>
                       I
                         (if (n,s) ∈ lcs then
                            if Var n s = ct then SOME f else NONE
                          else if (n,s) ∈ FDOM f then
                            if ct = f ' (n,s) then SOME f else NONE
                          else
                            (case
                               tmatch_def_UNION
                                 (INR (INL (lcs,s,sort_of ct,f)))
                             of
                               NONE => NONE
                             | SOME f0 => SOME (f0 |+ ((n,s),ct))))
                   | INL (lcs,Fn f1 s1 tl1,Var v3 v4,f) => I NONE
                   | INL (lcs,Fn f1 s1 tl1,Fn f2 s2 tl2,f) =>
                     I
                       (if f1 = f2 then
                          (case
                             tmatch_def_UNION (INR (INR (lcs,tl1,tl2,f)))
                           of
                             NONE => NONE
                           | SOME σ0 =>
                             tmatch_def_UNION (INR (INL (lcs,s1,s2,σ0))))
                        else NONE)
                   | INR (INL (lcs',St n1 tl1',St n2 tl2',f')) =>
                     I
                       (if n1 = n2 then
                          tmatch_def_UNION (INR (INR (lcs',tl1',tl2',f')))
                        else NONE)
                   | INR (INR (lcs'',[],[],f'')) => I (SOME f'')
                   | INR (INR (lcs'',h'::t',[],f'')) => I NONE
                   | INR (INR (lcs'',[],h::t,f'')) => I NONE
                   | INR (INR (lcs'',h1::t1,h::t,f'')) =>
                     I
                       (case tmatch_def_UNION (INL (lcs'',h1,h,f'')) of
                          NONE => NONE
                        | SOME f1 =>
                          tmatch_def_UNION (INR (INR (lcs'',t1,t,f1)))))
   
   [tmatch_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0 x1 x2.
          tmatch x x0 x1 x2 = tmatch_def_UNION (INL (x,x0,x1,x2))
   
   [tmatch_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0 x1 x2.
          smatch x x0 x1 x2 = tmatch_def_UNION (INR (INL (x,x0,x1,x2)))
   
   [tmatch_def_UNION_extract2]  Definition
      
      ⊢ ∀x x0 x1 x2.
          tlmatch x x0 x1 x2 = tmatch_def_UNION (INR (INR (x,x0,x1,x2)))
   
   [tmatch_def_UNION_primitive]  Definition
      
      ⊢ tmatch_def_UNION =
        tmatch_def_UNION_aux
          (@R. WF R ∧
               (∀ct f lcs s n.
                  (n,s) ∉ lcs ∧ (n,s) ∉ FDOM f ⇒
                  R (INR (INL (lcs,s,sort_of ct,f)))
                    (INL (lcs,Var n s,ct,f))) ∧
               (∀s2 s1 f tl2 tl1 lcs f2 f1.
                  f1 = f2 ⇒
                  R (INR (INR (lcs,tl1,tl2,f)))
                    (INL (lcs,Fn f1 s1 tl1,Fn f2 s2 tl2,f))) ∧
               (∀s2 s1 f tl2 tl1 lcs f2 f1 σ0.
                  f1 = f2 ∧
                  tmatch_def_UNION_aux R (INR (INR (lcs,tl1,tl2,f))) =
                  SOME σ0 ⇒
                  R (INR (INL (lcs,s1,s2,σ0)))
                    (INL (lcs,Fn f1 s1 tl1,Fn f2 s2 tl2,f))) ∧
               (∀f tl2 tl1 lcs n2 n1.
                  n1 = n2 ⇒
                  R (INR (INR (lcs,tl1,tl2,f)))
                    (INR (INL (lcs,St n1 tl1,St n2 tl2,f)))) ∧
               (∀t2 t1 f h2 h1 lcs f1.
                  tmatch_def_UNION_aux R (INL (lcs,h1,h2,f)) = SOME f1 ⇒
                  R (INR (INR (lcs,t1,t2,f1)))
                    (INR (INR (lcs,h1::t1,h2::t2,f)))) ∧
               ∀t2 t1 f h2 h1 lcs.
                 R (INL (lcs,h1,h2,f)) (INR (INR (lcs,h1::t1,h2::t2,f))))
   
   [tsubtm_def_UNION_extract0]  Definition
      
      ⊢ ∀x. tsubtm x = tsubtm_def_UNION (INL x)
   
   [tsubtm_def_UNION_extract1]  Definition
      
      ⊢ ∀x. ssubtm x = tsubtm_def_UNION (INR x)
   
   [tsubtm_def_UNION_primitive]  Definition
      
      ⊢ tsubtm_def_UNION =
        WFREC
          (@R. WF R ∧ (∀n s. R (INR s) (INL (Var n s))) ∧
               (∀l f s. R (INR s) (INL (Fn f s l))) ∧
               (∀s f l a. MEM a l ⇒ R (INL a) (INL (Fn f s l))) ∧
               ∀n l a. MEM a l ⇒ R (INL a) (INR (St n l)))
          (λtsubtm_def_UNION a'.
               case a' of
                 INL (Var n s) =>
                   I (Var n s INSERT tsubtm_def_UNION (INR s))
               | INL (Fn f s' l) =>
                 I
                   (Fn f s' l INSERT
                    tsubtm_def_UNION (INR s') ∪
                    BIGUNION (set (MAP (λa. tsubtm_def_UNION (INL a)) l)))
               | INR (St n' l') =>
                 I (BIGUNION (set (MAP (λa. tsubtm_def_UNION (INL a)) l'))))
   
   [vmap_fix_def]  Definition
      
      ⊢ ∀σ vs.
          vmap_fix σ vs ⇔ ∀n s. (n,s) ∈ FDOM σ ∩ vs ⇒ σ ' (n,s) = Var n s
   
   [DRESTRICT_SUBMAP_SUBSET]  Theorem
      
      ⊢ f ⊑ g ⇒ ∀s. s ⊆ FDOM f ⇒ DRESTRICT f s = DRESTRICT g s
   
   [DRESTRICT_UNION_SING]  Theorem
      
      ⊢ x ∈ FDOM σ ⇒ DRESTRICT σ (s ∪ {x}) = DRESTRICT σ s |+ (x,σ ' x)
   
   [FAPPLY_o_vmap]  Theorem
      
      ⊢ (n,s) ∈ FDOM σ1 ⇒ o_vmap σ2 σ1 ' (n,s) = tinst σ2 (σ1 ' (n,s))
   
   [FDOM_o_vmap]  Theorem
      
      ⊢ FDOM (o_vmap σ2 σ1) = FDOM σ1
   
   [FEMPTY_complete]  Theorem
      
      ⊢ complete FEMPTY
   
   [FEMPTY_cstt]  Theorem
      
      ⊢ cstt FEMPTY
   
   [FUNION_COMM1]  Theorem
      
      ⊢ ∀f g. (∀x. x ∈ FDOM f ∧ x ∈ FDOM g ⇒ f ' x = g ' x) ⇒ f ⊌ g = g ⊌ f
   
   [IS_SOME_match]  Theorem
      
      ⊢ (∀t f σ.
           complete f ∧ cstt σ ∧ tfv t ⊆ FDOM σ ∧
           (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ tfv t ⇒ f ' (n,s) = σ ' (n,s)) ⇒
           tmatch ∅ t (tinst σ t) f = SOME (f ⊌ DRESTRICT σ (tfv t))) ∧
        (∀st f σ.
           complete f ∧ cstt σ ∧ sfv st ⊆ FDOM σ ∧
           (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ sfv st ⇒ f ' (n,s) = σ ' (n,s)) ⇒
           smatch ∅ st (sinst σ st) f = SOME (f ⊌ DRESTRICT σ (sfv st))) ∧
        ∀l f σ.
          complete f ∧ cstt σ ∧ BIGUNION {tfv t | MEM t l} ⊆ FDOM σ ∧
          (∀n s.
             (n,s) ∈ FDOM f ∩ FDOM σ ∩ BIGUNION {tfv t | MEM t l} ⇒
             f ' (n,s) = σ ' (n,s)) ⇒
          tlmatch ∅ l (MAP (tinst σ) l) f =
          SOME (f ⊌ DRESTRICT σ (BIGUNION {tfv t | MEM t l}))
   
   [IS_SOME_match_FEMPTY]  Theorem
      
      ⊢ (∀t σ.
           cstt σ ∧ tfv t ⊆ FDOM σ ⇒
           tmatch ∅ t (tinst σ t) FEMPTY = SOME (DRESTRICT σ (tfv t))) ∧
        (∀st σ.
           cstt σ ∧ sfv st ⊆ FDOM σ ⇒
           smatch ∅ st (sinst σ st) FEMPTY = SOME (DRESTRICT σ (sfv st))) ∧
        ∀l σ.
          cstt σ ∧ BIGUNION {tfv t | MEM t l} ⊆ FDOM σ ⇒
          tlmatch ∅ l (MAP (tinst σ) l) FEMPTY =
          SOME (DRESTRICT σ (BIGUNION {tfv t | MEM t l}))
   
   [MEM_list_size_leq]  Theorem
      
      ⊢ ∀l x. MEM x l ⇒ size x ≤ list_size size l
   
   [SUBMAP_DRESTRICT_IFF]  Theorem
      
      ⊢ f ⊑ g ⇔ f = DRESTRICT g (FDOM f)
   
   [UNION_is_cont]  Theorem
      
      ⊢ is_cont s1 ∧ is_cont s2 ⇒ is_cont (s1 ∪ s2)
   
   [better_tm_induction]  Theorem
      
      ⊢ ∀Pt Ps.
          (∀s. Ps s ⇒ ∀s0. Pt (Var s0 s)) ∧
          (∀s l. Ps s ∧ (∀t. MEM t l ⇒ Pt t) ⇒ ∀s0. Pt (Fn s0 s l)) ∧
          (∀l. (∀t. MEM t l ⇒ Pt t) ⇒ ∀s. Ps (St s l)) ⇒
          (∀t. Pt t) ∧ ∀s. Ps s
   
   [complete_FDOM_is_cont]  Theorem
      
      ⊢ complete f ⇔ is_cont (FDOM f)
   
   [cstt_SUBMAP]  Theorem
      
      ⊢ cstt f ∧ f ⊑ σ ∧ complete f ∧
        (∀n s.
           (n,s) ∈ FDOM σ ∧ (n,s) ∉ FDOM f ⇒
           sort_of (σ ' (n,s)) = sinst σ s) ⇒
        cstt σ
   
   [cstt_sort_of_tinst]  Theorem
      
      ⊢ cstt σ ⇒ sort_of (tinst σ t) = sinst σ (sort_of t)
   
   [datatype_form]  Theorem
      
      ⊢ DATATYPE (form False Pred IMP FALL fVar)
   
   [datatype_term]  Theorem
      
      ⊢ DATATYPE (term Var Fn ∧ sort St)
   
   [fmap_fv_inst_eq]  Theorem
      
      ⊢ (∀t σ1 σ2.
           DRESTRICT σ1 (tfv t) = DRESTRICT σ2 (tfv t) ⇒
           tinst σ1 t = tinst σ2 t) ∧
        ∀s σ1 σ2.
          DRESTRICT σ1 (sfv s) = DRESTRICT σ2 (sfv s) ⇒
          sinst σ1 s = sinst σ2 s
   
   [form_11]  Theorem
      
      ⊢ (∀a0 a1 a0' a1'. Pred a0 a1 = Pred a0' a1' ⇔ a0 = a0' ∧ a1 = a1') ∧
        (∀a0 a1 a0' a1'. IMP a0 a1 = IMP a0' a1' ⇔ a0 = a0' ∧ a1 = a1') ∧
        (∀a0 a1 a2 a0' a1' a2'.
           FALL a0 a1 a2 = FALL a0' a1' a2' ⇔
           a0 = a0' ∧ a1 = a1' ∧ a2 = a2') ∧
        ∀a0 a1 a2 a0' a1' a2'.
          fVar a0 a1 a2 = fVar a0' a1' a2' ⇔ a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
   
   [form_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4. ∃fn.
          fn False = f0 ∧ (∀a0 a1. fn (Pred a0 a1) = f1 a0 a1) ∧
          (∀a0 a1. fn (IMP a0 a1) = f2 a0 a1 (fn a0) (fn a1)) ∧
          (∀a0 a1 a2. fn (FALL a0 a1 a2) = f3 a0 a1 a2 (fn a2)) ∧
          ∀a0 a1 a2. fn (fVar a0 a1 a2) = f4 a0 a1 a2
   
   [form_case_cong]  Theorem
      
      ⊢ ∀M M' v f f1 f2 f3.
          M = M' ∧ (M' = False ⇒ v = v') ∧
          (∀a0 a1. M' = Pred a0 a1 ⇒ f a0 a1 = f' a0 a1) ∧
          (∀a0 a1. M' = IMP a0 a1 ⇒ f1 a0 a1 = f1' a0 a1) ∧
          (∀a0 a1 a2. M' = FALL a0 a1 a2 ⇒ f2 a0 a1 a2 = f2' a0 a1 a2) ∧
          (∀a0 a1 a2. M' = fVar a0 a1 a2 ⇒ f3 a0 a1 a2 = f3' a0 a1 a2) ⇒
          form_CASE M v f f1 f2 f3 = form_CASE M' v' f' f1' f2' f3'
   
   [form_case_eq]  Theorem
      
      ⊢ form_CASE x v f f1 f2 f3 = v' ⇔
        x = False ∧ v = v' ∨ (∃s l. x = Pred s l ∧ f s l = v') ∨
        (∃f' f0. x = IMP f' f0 ∧ f1 f' f0 = v') ∨
        (∃s0 s f'. x = FALL s0 s f' ∧ f2 s0 s f' = v') ∨
        ∃s l l0. x = fVar s l l0 ∧ f3 s l l0 = v'
   
   [form_distinct]  Theorem
      
      ⊢ (∀a1 a0. False ≠ Pred a0 a1) ∧ (∀a1 a0. False ≠ IMP a0 a1) ∧
        (∀a2 a1 a0. False ≠ FALL a0 a1 a2) ∧
        (∀a2 a1 a0. False ≠ fVar a0 a1 a2) ∧
        (∀a1' a1 a0' a0. Pred a0 a1 ≠ IMP a0' a1') ∧
        (∀a2 a1' a1 a0' a0. Pred a0 a1 ≠ FALL a0' a1' a2) ∧
        (∀a2 a1' a1 a0' a0. Pred a0 a1 ≠ fVar a0' a1' a2) ∧
        (∀a2 a1' a1 a0' a0. IMP a0 a1 ≠ FALL a0' a1' a2) ∧
        (∀a2 a1' a1 a0' a0. IMP a0 a1 ≠ fVar a0' a1' a2) ∧
        ∀a2' a2 a1' a1 a0' a0. FALL a0 a1 a2 ≠ fVar a0' a1' a2'
   
   [form_induction]  Theorem
      
      ⊢ ∀P. P False ∧ (∀s l. P (Pred s l)) ∧
            (∀f f0. P f ∧ P f0 ⇒ P (IMP f f0)) ∧
            (∀f. P f ⇒ ∀s s0. P (FALL s0 s f)) ∧ (∀s l l0. P (fVar s l l0)) ⇒
            ∀f. P f
   
   [form_nchotomy]  Theorem
      
      ⊢ ∀ff.
          ff = False ∨ (∃s l. ff = Pred s l) ∨ (∃f f0. ff = IMP f f0) ∨
          (∃s0 s f. ff = FALL s0 s f) ∨ ∃s l l0. ff = fVar s l l0
   
   [fv_subtm]  Theorem
      
      ⊢ (∀t n st. (n,st) ∈ tfv t ⇔ ∃t0. t0 ∈ tsubtm t ∧ (n,st) ∈ tfv t0) ∧
        ∀s n st. (n,st) ∈ sfv s ⇔ ∃t0. t0 ∈ ssubtm s ∧ (n,st) ∈ tfv t0
   
   [inst_o_vmap]  Theorem
      
      ⊢ (∀t σ1 σ2.
           tfv t ⊆ FDOM σ1 ∧ tfv (tinst σ1 t) ⊆ FDOM σ2 ⇒
           tinst σ2 (tinst σ1 t) = tinst (o_vmap σ2 σ1) t) ∧
        ∀s σ1 σ2.
          sfv s ⊆ FDOM σ1 ∧ sfv (sinst σ1 s) ⊆ FDOM σ2 ⇒
          sinst σ2 (sinst σ1 s) = sinst (o_vmap σ2 σ1) s
   
   [match_SOME_cstt]  Theorem
      
      ⊢ (∀t1 t2 f σ.
           complete f ∧ cstt f ∧ tmatch ∅ t1 t2 f = SOME σ ⇒ cstt σ) ∧
        (∀st1 st2 f σ.
           complete f ∧ cstt f ∧ smatch ∅ st1 st2 f = SOME σ ⇒ cstt σ) ∧
        ∀tl1 tl2 f σ.
          complete f ∧ cstt f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒ cstt σ
   
   [match_SOME_iff_inst]  Theorem
      
      ⊢ ∀t1 t2.
          IS_SOME (tmatch ∅ t1 t2 FEMPTY) ⇔
          ∃σ. cstt σ ∧ tfv t1 ⊆ FDOM σ ∧ t2 = tinst σ t1
   
   [match_SOME_iff_inst']  Theorem
      
      ⊢ ∀t1 t2.
          IS_SOME (tmatch ∅ t1 t2 FEMPTY) ⇔
          ∃σ. cstt σ ∧ tfv t1 = FDOM σ ∧ t2 = tinst σ t1
   
   [match_SUBMAP]  Theorem
      
      ⊢ (∀t1 t2 f σ.
           complete f ∧ tmatch ∅ t1 t2 f = SOME σ ⇒
           f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ tfv t1) ∧
        (∀s1 s2 f σ.
           complete f ∧ smatch ∅ s1 s2 f = SOME σ ⇒
           f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ sfv s1) ∧
        ∀tl1 tl2 f σ.
          complete f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒
          f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ BIGUNION {tfv t | MEM t tl1}
   
   [match_complete]  Theorem
      
      ⊢ (∀t1 t2 f σ.
           complete f ∧ tmatch ∅ t1 t2 f = SOME σ ⇒
           tfv t1 ⊆ FDOM σ ∧ FDOM f ⊆ FDOM σ ∧ complete σ) ∧
        (∀s1 s2 f σ.
           complete f ∧ smatch ∅ s1 s2 f = SOME σ ⇒
           sfv s1 ⊆ FDOM σ ∧ FDOM f ⊆ FDOM σ ∧ complete σ) ∧
        ∀tl1 tl2 f σ.
          complete f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒
          (∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧ FDOM f ⊆ FDOM σ ∧ complete σ
   
   [o_vmap_cstt]  Theorem
      
      ⊢ cstt σ1 ∧ cstt σ2 ∧ complete σ1 ∧
        (∀x. x ∈ FDOM σ1 ⇒ tfv (σ1 ' x) ⊆ FDOM σ2) ⇒
        cstt (o_vmap σ2 σ1)
   
   [sfv_tfv]  Theorem
      
      ⊢ ∀t n s. (n,s) ∈ sfv (sort_of t) ⇒ (n,s) ∈ tfv t
   
   [sort_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'. St a0 a1 = St a0' a1' ⇔ a0 = a0' ∧ a1 = a1'
   
   [sort_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4. ∃fn0 fn1 fn2.
          (∀a0 a1. fn0 (Var a0 a1) = f0 a0 a1 (fn1 a1)) ∧
          (∀a0 a1 a2. fn0 (Fn a0 a1 a2) = f1 a0 a1 a2 (fn1 a1) (fn2 a2)) ∧
          (∀a0 a1. fn1 (St a0 a1) = f2 a0 a1 (fn2 a1)) ∧ fn2 [] = f3 ∧
          ∀a0 a1. fn2 (a0::a1) = f4 a0 a1 (fn0 a0) (fn2 a1)
   
   [sort_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a0 a1. M' = St a0 a1 ⇒ f a0 a1 = f' a0 a1) ⇒
          sort_CASE M f = sort_CASE M' f'
   
   [sort_case_eq]  Theorem
      
      ⊢ sort_CASE x f = v ⇔ ∃s l. x = St s l ∧ f s l = v
   
   [sort_induction]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀s. P1 s ⇒ ∀s0. P0 (Var s0 s)) ∧
          (∀s l. P1 s ∧ P2 l ⇒ ∀s0. P0 (Fn s0 s l)) ∧
          (∀l. P2 l ⇒ ∀s. P1 (St s l)) ∧ P2 [] ∧
          (∀t l. P0 t ∧ P2 l ⇒ P2 (t::l)) ⇒
          (∀t. P0 t) ∧ (∀s. P1 s) ∧ ∀l. P2 l
   
   [sort_nchotomy]  Theorem
      
      ⊢ ∀ss. ∃s l. ss = St s l
   
   [ssubtm_tsubtm]  Theorem
      
      ⊢ ∀t0 t. t0 ∈ ssubtm (sort_of t) ⇒ t0 ∈ tsubtm t
   
   [term_11]  Theorem
      
      ⊢ (∀a0 a1 a0' a1'. Var a0 a1 = Var a0' a1' ⇔ a0 = a0' ∧ a1 = a1') ∧
        ∀a0 a1 a2 a0' a1' a2'.
          Fn a0 a1 a2 = Fn a0' a1' a2' ⇔ a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
   
   [term_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4. ∃fn0 fn1 fn2.
          (∀a0 a1. fn0 (Var a0 a1) = f0 a0 a1 (fn1 a1)) ∧
          (∀a0 a1 a2. fn0 (Fn a0 a1 a2) = f1 a0 a1 a2 (fn1 a1) (fn2 a2)) ∧
          (∀a0 a1. fn1 (St a0 a1) = f2 a0 a1 (fn2 a1)) ∧ fn2 [] = f3 ∧
          ∀a0 a1. fn2 (a0::a1) = f4 a0 a1 (fn0 a0) (fn2 a1)
   
   [term_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a0 a1. M' = Var a0 a1 ⇒ f a0 a1 = f' a0 a1) ∧
          (∀a0 a1 a2. M' = Fn a0 a1 a2 ⇒ f1 a0 a1 a2 = f1' a0 a1 a2) ⇒
          term_CASE M f f1 = term_CASE M' f' f1'
   
   [term_case_eq]  Theorem
      
      ⊢ term_CASE x f f1 = v ⇔
        (∃s0 s. x = Var s0 s ∧ f s0 s = v) ∨
        ∃s0 s l. x = Fn s0 s l ∧ f1 s0 s l = v
   
   [term_distinct]  Theorem
      
      ⊢ ∀a2 a1' a1 a0' a0. Var a0 a1 ≠ Fn a0' a1' a2
   
   [term_induction]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀s. P1 s ⇒ ∀s0. P0 (Var s0 s)) ∧
          (∀s l. P1 s ∧ P2 l ⇒ ∀s0. P0 (Fn s0 s l)) ∧
          (∀l. P2 l ⇒ ∀s. P1 (St s l)) ∧ P2 [] ∧
          (∀t l. P0 t ∧ P2 l ⇒ P2 (t::l)) ⇒
          (∀t. P0 t) ∧ (∀s. P1 s) ∧ ∀l. P2 l
   
   [term_nchotomy]  Theorem
      
      ⊢ ∀tt. (∃s0 s. tt = Var s0 s) ∨ ∃s0 s l. tt = Fn s0 s l
   
   [term_size_eq]  Theorem
      
      ⊢ term1_size = list_size term_size
   
   [tfv_def]  Theorem
      
      ⊢ (∀s n. tfv (Var n s) = {(n,s)} ∪ sfv s) ∧
        (∀tl s n.
           tfv (Fn n s tl) = BIGUNION (set (MAP (λa. tfv a) tl)) ∪ sfv s) ∧
        ∀tl n. sfv (St n tl) = BIGUNION (set (MAP (λa. tfv a) tl))
   
   [tfv_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀n s. P1 s ⇒ P0 (Var n s)) ∧
          (∀n s tl. (∀a. MEM a tl ⇒ P0 a) ∧ P1 s ⇒ P0 (Fn n s tl)) ∧
          (∀n tl. (∀a. MEM a tl ⇒ P0 a) ⇒ P1 (St n tl)) ⇒
          (∀v0. P0 v0) ∧ ∀v0. P1 v0
   
   [tfv_is_cont]  Theorem
      
      ⊢ (∀t. is_cont (tfv t)) ∧ ∀s. is_cont (sfv s)
   
   [tfv_sinst]  Theorem
      
      ⊢ (∀t σ.
           cstt σ ∧ tfv t ⊆ FDOM σ ⇒
           ∀n st.
             (n,st) ∈ tfv (tinst σ t) ⇔
             ∃n0 st0. (n0,st0) ∈ tfv t ∧ (n,st) ∈ tfv (σ ' (n0,st0))) ∧
        ∀s σ.
          cstt σ ∧ sfv s ⊆ FDOM σ ⇒
          ∀n st.
            (n,st) ∈ sfv (sinst σ s) ⇔
            ∃n0 st0. (n0,st0) ∈ sfv s ∧ (n,st) ∈ tfv (σ ' (n0,st0))
   
   [tfv_thm]  Theorem
      
      ⊢ tfv (Var n s) = {(n,s)} ∪ sfv s ∧
        tfv (Fn n s tl) = BIGUNION {tfv t | MEM t tl} ∪ sfv s ∧
        sfv (St n tl) = BIGUNION {tfv t | MEM t tl}
   
   [tinst_def]  Theorem
      
      ⊢ (∀σ s n.
           tinst σ (Var n s) =
           if (n,s) ∉ FDOM σ then Var n (sinst σ s) else σ ' (n,s)) ∧
        (∀σ tl s f.
           tinst σ (Fn f s tl) = Fn f (sinst σ s) (MAP (λa. tinst σ a) tl)) ∧
        ∀σ tl n. sinst σ (St n tl) = St n (MAP (λa. tinst σ a) tl)
   
   [tinst_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀σ n s. ((n,s) ∉ FDOM σ ⇒ P1 σ s) ⇒ P0 σ (Var n s)) ∧
          (∀σ f s tl. (∀a. MEM a tl ⇒ P0 σ a) ∧ P1 σ s ⇒ P0 σ (Fn f s tl)) ∧
          (∀σ n tl. (∀a. MEM a tl ⇒ P0 σ a) ⇒ P1 σ (St n tl)) ⇒
          (∀v0 v1. P0 v0 v1) ∧ ∀v0 v1. P1 v0 v1
   
   [tinst_subtm]  Theorem
      
      ⊢ (∀t σ n st.
           (n,st) ∈ FDOM σ ∩ tfv t ∧ cstt σ ⇒
           σ ' (n,st) ∈ tsubtm (tinst σ t)) ∧
        ∀s σ n st.
          (n,st) ∈ FDOM σ ∩ sfv s ∧ cstt σ ⇒
          σ ' (n,st) ∈ ssubtm (sinst σ s)
   
   [tinst_vmap_id]  Theorem
      
      ⊢ (∀t σ.
           (∀n s. (n,s) ∈ FDOM σ ∩ tfv t ⇒ σ ' (n,s) = Var n s) ⇒
           tinst σ t = t) ∧
        ∀st σ.
          (∀n s. (n,s) ∈ FDOM σ ∩ sfv st ⇒ σ ' (n,s) = Var n s) ⇒
          sinst σ st = st
   
   [tlmatch_FEMPTY_each]  Theorem
      
      ⊢ ∀tl1 tl2.
          tl1 ≠ [] ∧ tl2 ≠ [] ∧ LENGTH tl1 = LENGTH tl2 ⇒
          ∀σ. tlmatch ∅ tl1 tl2 FEMPTY = SOME σ ⇔
              FDOM σ = BIGUNION {tfv t | MEM t tl1} ∧
              ∀n. n < LENGTH tl1 ⇒
                  tmatch ∅ (EL n tl1) (EL n tl2) FEMPTY =
                  SOME (DRESTRICT σ (tfv (EL n tl1)))
   
   [tlmatch_LENGTH]  Theorem
      
      ⊢ ∀tl1 tl2 f σ.
          tlmatch lcs tl1 tl2 f = SOME σ ⇒ LENGTH tl1 = LENGTH tl2
   
   [tlmatch_SOME_MAP]  Theorem
      
      ⊢ ∀tl1 tl2 f σ.
          complete f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒
          tl2 = MAP (tinst σ) tl1
   
   [tlmatch_each]  Theorem
      
      ⊢ ∀tl1 tl2 f.
          complete f ∧ cstt f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧
          LENGTH tl1 = LENGTH tl2 ⇒
          ∀σ. tlmatch ∅ tl1 tl2 f = SOME σ ⇔
              FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
              ∀n. n < LENGTH tl1 ⇒
                  tmatch ∅ (EL n tl1) (EL n tl2) f =
                  SOME (DRESTRICT σ (FDOM f ∪ tfv (EL n tl1)))
   
   [tlmatch_each_imp_tinst]  Theorem
      
      ⊢ ∀tl1 tl2 f.
          complete f ∧ cstt f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧
          LENGTH tl1 = LENGTH tl2 ⇒
          ∀σ. tlmatch ∅ tl1 tl2 f = SOME σ ⇒
              FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
              ∀n. n < LENGTH tl1 ⇒ EL n tl2 = tinst σ (EL n tl1)
   
   [tlmatch_each_lemma]  Theorem
      
      ⊢ complete f ∧ cstt f ∧ tmatch ∅ t1 t2 f = SOME σ ∧ f ⊑ f1 ∧
        complete f1 ∧ cstt f1 ∧
        (∀x. x ∈ FDOM f1 ∧ x ∈ FDOM σ ⇒ f1 ' x = σ ' x) ⇒
        tmatch ∅ t1 t2 f1 = SOME (f1 ⊌ σ)
   
   [tlmatch_tinst_imp_SOME]  Theorem
      
      ⊢ ∀tl1 tl2 f.
          complete f ∧ cstt f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧
          LENGTH tl1 = LENGTH tl2 ⇒
          ∀σ. f ⊑ σ ∧ cstt σ ∧
              FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
              (∀n. n < LENGTH tl1 ⇒ EL n tl2 = tinst σ (EL n tl1)) ⇒
              tlmatch ∅ tl1 tl2 f = SOME σ
   
   [tlmatch_tinst_imp_SOME']  Theorem
      
      ⊢ ∀tl1 tl2 f.
          complete f ∧ cstt f ∧ LENGTH tl1 = LENGTH tl2 ⇒
          ∀σ. f ⊑ σ ∧ cstt σ ∧
              FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
              (∀n. n < LENGTH tl1 ⇒ EL n tl2 = tinst σ (EL n tl1)) ⇒
              tlmatch ∅ tl1 tl2 f = SOME σ
   
   [tm_induction2]  Theorem
      
      ⊢ ∀P. (∀s. (∀t. MEM t (stms s) ⇒ P t) ⇒ ∀s0. P (Var s0 s)) ∧
            (∀s l.
               (∀t. MEM t (stms s) ⇒ P t) ∧ (∀t. MEM t l ⇒ P t) ⇒
               ∀s0. P (Fn s0 s l)) ⇒
            ∀t. P t
   
   [tm_tree_WF]  Theorem
      
      ⊢ ∀s n. (n,s) ∉ sfv s
   
   [tm_tree_size_less]  Theorem
      
      ⊢ (∀t n st. (n,st) ∈ tfv t ⇒ sort_size st < term_size t) ∧
        ∀s n st. (n,st) ∈ sfv s ⇒ sort_size st < sort_size s
   
   [tmatch_FDOM_SUBMAP]  Theorem
      
      ⊢ (∀t1 t2 f σ.
           complete f ∧ tmatch ∅ t1 t2 f = SOME σ ⇒
           complete σ ∧ f ⊑ σ ∧ FDOM σ = FDOM f ∪ tfv t1) ∧
        (∀s1 s2 f σ.
           complete f ∧ smatch ∅ s1 s2 f = SOME σ ⇒
           complete σ ∧ f ⊑ σ ∧ FDOM σ = FDOM f ∪ sfv s1) ∧
        ∀tl1 tl2 f σ.
          complete f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒
          complete σ ∧ f ⊑ σ ∧
          FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1}
   
   [tmatch_FEMPTY]  Theorem
      
      ⊢ ∀f. complete f ∧ cstt f ⇒
            (tmatch ∅ t1 t2 f = SOME σ ⇔
             ∃σ0.
               (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ0 ⇒ f ' (n,s) = σ0 ' (n,s)) ∧
               tmatch ∅ t1 t2 FEMPTY = SOME σ0 ∧ σ = f ⊌ σ0)
   
   [tmatch_FEMPTY_property]  Theorem
      
      ⊢ tmatch ∅ t1 t2 FEMPTY = SOME σ ⇒ complete σ ∧ FDOM σ = tfv t1
   
   [tmatch_SOME_tinst]  Theorem
      
      ⊢ (∀t1 t2 f σ.
           complete f ∧ tmatch ∅ t1 t2 f = SOME σ ⇒ tinst σ t1 = t2) ∧
        (∀st1 st2 f σ.
           complete f ∧ smatch ∅ st1 st2 f = SOME σ ⇒ sinst σ st1 = st2) ∧
        ∀tl1 tl2 f σ.
          complete f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒
          ∀n. n < LENGTH tl1 ⇒ tinst σ (EL n tl1) = EL n tl2
   
   [tmatch_TRANS]  Theorem
      
      ⊢ ∀t1 t2 t3.
          IS_SOME (tmatch ∅ t1 t2 FEMPTY) ∧ IS_SOME (tmatch ∅ t2 t3 FEMPTY) ⇒
          IS_SOME (tmatch ∅ t1 t3 FEMPTY)
   
   [tmatch_TRANS_lemma]  Theorem
      
      ⊢ cstt σ ∧ sfv s ⊆ tfv t ∧ tfv t ⊆ FDOM σ ⇒
        sfv (sinst σ s) ⊆ tfv (tinst σ t)
   
   [tmatch_def]  Theorem
      
      ⊢ (∀s n lcs f ct.
           tmatch lcs (Var n s) ct f =
           if (n,s) ∈ lcs then if Var n s = ct then SOME f else NONE
           else if (n,s) ∈ FDOM f then
             if ct = f ' (n,s) then SOME f else NONE
           else
             case smatch lcs s (sort_of ct) f of
               NONE => NONE
             | SOME f0 => SOME (f0 |+ ((n,s),ct))) ∧
        (∀tl2 tl1 s2 s1 lcs f2 f1 f.
           tmatch lcs (Fn f1 s1 tl1) (Fn f2 s2 tl2) f =
           if f1 = f2 then
             case tlmatch lcs tl1 tl2 f of
               NONE => NONE
             | SOME σ0 => smatch lcs s1 s2 σ0
           else NONE) ∧
        (∀v4 v3 v2 v1 v0 lcs f.
           tmatch lcs (Fn v0 v1 v2) (Var v3 v4) f = NONE) ∧
        (∀tl2 tl1 n2 n1 lcs f.
           smatch lcs (St n1 tl1) (St n2 tl2) f =
           if n1 = n2 then tlmatch lcs tl1 tl2 f else NONE) ∧
        (∀lcs f. tlmatch lcs [] [] f = SOME f) ∧
        (∀t lcs h f. tlmatch lcs [] (h::t) f = NONE) ∧
        (∀t lcs h f. tlmatch lcs (h::t) [] f = NONE) ∧
        ∀t2 t1 lcs h2 h1 f.
          tlmatch lcs (h1::t1) (h2::t2) f =
          case tmatch lcs h1 h2 f of
            NONE => NONE
          | SOME f1 => tlmatch lcs t1 t2 f1
   
   [tmatch_ind]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀lcs n s ct f.
             ((n,s) ∉ lcs ∧ (n,s) ∉ FDOM f ⇒ P1 lcs s (sort_of ct) f) ⇒
             P0 lcs (Var n s) ct f) ∧
          (∀lcs f1 s1 tl1 f2 s2 tl2 f.
             (∀σ0.
                f1 = f2 ∧ tlmatch lcs tl1 tl2 f = SOME σ0 ⇒ P1 lcs s1 s2 σ0) ∧
             (f1 = f2 ⇒ P2 lcs tl1 tl2 f) ⇒
             P0 lcs (Fn f1 s1 tl1) (Fn f2 s2 tl2) f) ∧
          (∀lcs v0 v1 v2 v3 v4 f. P0 lcs (Fn v0 v1 v2) (Var v3 v4) f) ∧
          (∀lcs n1 tl1 n2 tl2 f.
             (n1 = n2 ⇒ P2 lcs tl1 tl2 f) ⇒
             P1 lcs (St n1 tl1) (St n2 tl2) f) ∧ (∀lcs f. P2 lcs [] [] f) ∧
          (∀lcs h t f. P2 lcs [] (h::t) f) ∧
          (∀lcs h t f. P2 lcs (h::t) [] f) ∧
          (∀lcs h1 t1 h2 t2 f.
             (∀f1. tmatch lcs h1 h2 f = SOME f1 ⇒ P2 lcs t1 t2 f1) ∧
             P0 lcs h1 h2 f ⇒
             P2 lcs (h1::t1) (h2::t2) f) ⇒
          (∀v0 v1 v2 v3. P0 v0 v1 v2 v3) ∧ (∀v0 v1 v2 v3. P1 v0 v1 v2 v3) ∧
          ∀v0 v1 v2 v3. P2 v0 v1 v2 v3
   
   [tsubtm_REFL]  Theorem
      
      ⊢ ∀t. t ∈ tsubtm t
   
   [tsubtm_def]  Theorem
      
      ⊢ (∀s n. tsubtm (Var n s) = Var n s INSERT ssubtm s) ∧
        (∀s l f.
           tsubtm (Fn f s l) =
           Fn f s l INSERT ssubtm s ∪ BIGUNION (set (MAP (λa. tsubtm a) l))) ∧
        ∀n l. ssubtm (St n l) = BIGUNION (set (MAP (λa. tsubtm a) l))
   
   [tsubtm_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀n s. P1 s ⇒ P0 (Var n s)) ∧
          (∀f s l. (∀a. MEM a l ⇒ P0 a) ∧ P1 s ⇒ P0 (Fn f s l)) ∧
          (∀n l. (∀a. MEM a l ⇒ P0 a) ⇒ P1 (St n l)) ⇒
          (∀v0. P0 v0) ∧ ∀v0. P1 v0
   
   [update_inst_lemma]  Theorem
      
      ⊢ v ∉ sfv s ∧ v ∉ FDOM σ ⇒ sinst σ s = sinst (σ |+ (v,t)) s
   
   [vmap_fix_FEMPTY]  Theorem
      
      ⊢ vmap_fix FEMPTY vs
   
   [vsort_tfv_closed]  Theorem
      
      ⊢ (∀h n s v. (n,s) ∈ tfv h ∧ v ∈ sfv s ⇒ v ∈ tfv h) ∧
        ∀st n s v. (n,s) ∈ sfv st ∧ v ∈ sfv s ⇒ v ∈ sfv st
   
   [wfvmap_cont_DRESTRICT]  Theorem
      
      ⊢ cstt σ ∧ complete σ ∧ is_cont s ⇒ cstt (DRESTRICT σ s)
   
   
*)
end
