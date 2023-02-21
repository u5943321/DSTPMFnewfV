signature tmsytxTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val FMAP_MAP_DEF : thm
    val complete_def : thm
    val cstt_def : thm
    val cvmap_def : thm
    val evmap_def : thm
    val finput_def : thm
    val foutput_def : thm
    val fsymin_def : thm
    val fsymout_def : thm
    val is_bound_def : thm
    val is_cont_def : thm
    val isfsym_def : thm
    val mk_bmap_def : thm
    val no_bound_def : thm
    val o_vmap_def : thm
    val ok_abs_def : thm
    val shift_bmap_def : thm
    val slbounds_def : thm
    val slprpl_def : thm
    val sort_TY_DEF : thm
    val sort_case_def : thm
    val sort_of_def : thm
    val specsl_def : thm
    val stms_def : thm
    val tabs_def_UNION_extract0 : thm
    val tabs_def_UNION_extract1 : thm
    val tabs_def_UNION_primitive : thm
    val tbounds_def_UNION_extract0 : thm
    val tbounds_def_UNION_extract1 : thm
    val tbounds_def_UNION_primitive : thm
    val term_TY_DEF : thm
    val term_case_def : thm
    val term_size_def : thm
    val tfv_def_UNION_extract0 : thm
    val tfv_def_UNION_extract1 : thm
    val tfv_def_UNION_primitive : thm
    val tinst_def_UNION_extract0 : thm
    val tinst_def_UNION_extract1 : thm
    val tinst_def_UNION_primitive : thm
    val tlfv_def : thm
    val tmatch_def_UNION_AUX : thm
    val tmatch_def_UNION_extract0 : thm
    val tmatch_def_UNION_extract1 : thm
    val tmatch_def_UNION_extract2 : thm
    val tmatch_def_UNION_primitive : thm
    val tprpl_def_UNION_extract0 : thm
    val tprpl_def_UNION_extract1 : thm
    val tprpl_def_UNION_primitive : thm
    val tpsubtm_def : thm
    val trpl_def_UNION_extract0 : thm
    val trpl_def_UNION_extract1 : thm
    val trpl_def_UNION_primitive : thm
    val tshift_def_UNION_extract0 : thm
    val tshift_def_UNION_extract1 : thm
    val tshift_def_UNION_primitive : thm
    val tsstt_def_UNION_extract0 : thm
    val tsstt_def_UNION_extract1 : thm
    val tsstt_def_UNION_primitive : thm
    val tsubst_def_UNION_extract0 : thm
    val tsubst_def_UNION_extract1 : thm
    val tsubst_def_UNION_primitive : thm
    val tsubtm_def_UNION_extract0 : thm
    val tsubtm_def_UNION_extract1 : thm
    val tsubtm_def_UNION_primitive : thm
    val vmap_fix_def : thm
    val wfcod_def : thm
    val wft_def_UNION_extract0 : thm
    val wft_def_UNION_extract1 : thm
    val wft_def_UNION_primitive : thm
  
  (*  Theorems  *)
    val BIGUNION_tbounds : thm
    val BIGUNION_tbounds' : thm
    val Bound_NOT_wft : thm
    val Bound_tsubtm : thm
    val DRESTRICT_SUBMAP_SUBSET : thm
    val DRESTRICT_UNION_SING : thm
    val DRESTRICT_cstt : thm
    val DRESTRICT_eq : thm
    val DRESTRICT_no_bound : thm
    val DRESTRICT_wfcod : thm
    val EL_REVERSE1 : thm
    val EL_REVERSE2 : thm
    val FAPPLY_DOMSUB : thm
    val FAPPLY_FMAP_MAP : thm
    val FAPPLY_cvmap : thm
    val FAPPLY_mk_bmap : thm
    val FAPPLY_o_vmap : thm
    val FAPPLY_shift_bmap : thm
    val FDOM_FINITE_lemma : thm
    val FDOM_FMAP_MAP : thm
    val FDOM_TO_FMAP : thm
    val FDOM_cvmap : thm
    val FDOM_evmap : thm
    val FDOM_mk_bmap : thm
    val FDOM_o_vmap : thm
    val FDOM_shift_bmap : thm
    val FEMPTY_complete : thm
    val FEMPTY_cstt : thm
    val FEMPTY_no_bound : thm
    val FUNION_COMM1 : thm
    val FUPDATE_cstt : thm
    val FUPDATE_wfcod : thm
    val Fn_tpsubtm : thm
    val Fn_tpsubtm_neq : thm
    val IN_slbounds : thm
    val IS_SOME_match : thm
    val IS_SOME_match_FEMPTY : thm
    val IS_SOME_tlmatch_inst : thm
    val LENGTH_abssl : thm
    val LENGTH_slabs : thm
    val LENGTH_slprpl : thm
    val LENGTH_specsl : thm
    val MAP_fix : thm
    val MAP_sinst_abssl : thm
    val MAP_sinst_specsl : thm
    val MEM_list_size_leq : thm
    val NOTIN_slbounds_abssl : thm
    val NOTIN_slbounds_slabs : thm
    val NOT_ok_abs : thm
    val NOT_ok_abssl : thm
    val SUBMAP_DRESTRICT_IFF : thm
    val TO_FMAP_MEM : thm
    val UNION_is_cont : thm
    val Var_tpsubtm : thm
    val Var_tpsubtm_neq : thm
    val Var_tsubtm_tfv : thm
    val abssl_EL : thm
    val abssl_def : thm
    val abssl_id : thm
    val abssl_ind : thm
    val abssl_ok_abs : thm
    val abssl_specsl : thm
    val better_tm_induction : thm
    val complete_FDOM_is_cont : thm
    val cstt_FUPDATE : thm
    val cstt_SUBMAP : thm
    val cstt_cvmap : thm
    val cstt_sort_of_tinst : thm
    val cstt_sort_of_tinst' : thm
    val datatype_term : thm
    val fmap_fv_inst_eq : thm
    val fmap_fv_inst_eq_alt : thm
    val fv_subtm : thm
    val ill_formed_tabs_still_in : thm
    val inst_o_vmap : thm
    val is_bound_alt : thm
    val match_SOME_cstt : thm
    val match_SOME_iff_inst : thm
    val match_SOME_iff_inst' : thm
    val match_SUBMAP : thm
    val match_complete : thm
    val mk_bmap_MAP : thm
    val no_bound_FUPDATE : thm
    val no_bound_not_bound : thm
    val no_bound_not_is_bound : thm
    val o_vmap_cstt : thm
    val o_vmap_no_bound : thm
    val ok_abs_HD : thm
    val ok_abs_abssl : thm
    val sabs_sinst : thm
    val sbounds_St : thm
    val sbounds_tbounds : thm
    val sfv_tfv : thm
    val shift_bmap_0 : thm
    val shift_bmap_FEMPTY : thm
    val shift_bmap_FMAP_MAP_tabs : thm
    val shift_bmap_SUM : thm
    val sinst_srpl : thm
    val slabs_EL : thm
    val slabs_abssl : thm
    val slabs_def : thm
    val slabs_id : thm
    val slabs_ind : thm
    val slbounds_abssl : thm
    val slbounds_sbounds : thm
    val slbounds_slabs : thm
    val slbounds_specsl_DELETE : thm
    val slprpl_EL : thm
    val slprpl_FEMPTY : thm
    val sort_11 : thm
    val sort_Axiom : thm
    val sort_case_cong : thm
    val sort_case_eq : thm
    val sort_induction : thm
    val sort_nchotomy : thm
    val specsl_EL : thm
    val specsl_abssl : thm
    val specsl_sbounds : thm
    val specsl_sbounds_SUBSET : thm
    val ssubst_sinst : thm
    val ssubtm_tsubtm : thm
    val subtm_size_less : thm
    val tabs_def : thm
    val tabs_id : thm
    val tabs_ind : thm
    val tabs_tbounds_in : thm
    val tabs_tinst : thm
    val tabs_trpl : thm
    val tabs_tsubst : thm
    val tbounds_EMPTY_tinst_no_bound : thm
    val tbounds_Fn : thm
    val tbounds_def : thm
    val tbounds_ind : thm
    val tbounds_tabs : thm
    val tbounds_tabs_SUBSET : thm
    val tbounds_thm : thm
    val tbounds_tsubst : thm
    val tbounds_tsubst_SUBSET : thm
    val term_11 : thm
    val term_Axiom : thm
    val term_case_cong : thm
    val term_case_eq : thm
    val term_distinct : thm
    val term_induction : thm
    val term_nchotomy : thm
    val term_size_eq : thm
    val tfv_FINITE : thm
    val tfv_def : thm
    val tfv_ind : thm
    val tfv_is_cont : thm
    val tfv_sinst : thm
    val tfv_tabs : thm
    val tfv_tabs_SUBSET : thm
    val tfv_thm : thm
    val tfv_tinst_SUBSET_lemma : thm
    val tfv_tprpl : thm
    val tfv_trpl : thm
    val tfv_trpl_SUBSET : thm
    val tfv_tshift : thm
    val tfv_tsubst : thm
    val tfv_tsubst_SUBSET : thm
    val tfv_tsubtm_closed : thm
    val tinst_def : thm
    val tinst_eq_cvmap : thm
    val tinst_ind : thm
    val tinst_subtm : thm
    val tinst_tabs : thm
    val tinst_tsubst : thm
    val tinst_vmap_id : thm
    val tlfv_is_cont : thm
    val tlmatch_EMPTY_TRANS_lemma : thm
    val tlmatch_FEMPTY_each : thm
    val tlmatch_LENGTH : thm
    val tlmatch_SOME_MAP : thm
    val tlmatch_TRANS_o_vmap : thm
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
    val tmatch_no_bound : thm
    val tprpl_FEMPTY : thm
    val tprpl_FMAP_MAP_tabs : thm
    val tprpl_def : thm
    val tprpl_id : thm
    val tprpl_ind : thm
    val tprpl_mk_bmap_CONS : thm
    val tpsubtm_size_LESS : thm
    val trpl_def : thm
    val trpl_eliminate : thm
    val trpl_eliminate0 : thm
    val trpl_id : thm
    val trpl_ind : thm
    val trpl_tabs : thm
    val tshift_0 : thm
    val tshift_SUM : thm
    val tshift_def : thm
    val tshift_id : thm
    val tshift_ind : thm
    val tshift_tabs : thm
    val tsstt_back : thm
    val tsstt_def : thm
    val tsstt_fix : thm
    val tsstt_id : thm
    val tsstt_ind : thm
    val tsstt_itself : thm
    val tsstt_tsstt : thm
    val tsstt_tsstt1 : thm
    val tsstt_tsubtm : thm
    val tsubst_def : thm
    val tsubst_eq_tinst : thm
    val tsubst_eq_tinst1 : thm
    val tsubst_id : thm
    val tsubst_id' : thm
    val tsubst_ind : thm
    val tsubst_tbounds_in : thm
    val tsubst_tinst : thm
    val tsubst_tsstt : thm
    val tsubtm_REFL : thm
    val tsubtm_def : thm
    val tsubtm_ind : thm
    val update_inst_lemma : thm
    val variant_NOT_fIN : thm
    val variant_def : thm
    val variant_ind : thm
    val variant_var_NOTIN : thm
    val vmap_fix_FEMPTY : thm
    val vsort_tfv_closed : thm
    val wfabsap_LENGTH : thm
    val wfabsap_def : thm
    val wfabsap_ind : thm
    val wfabsap_ok_abs : thm
    val wfabsap_sfv_SUBSET : thm
    val wfabsap_sfv_sbounds : thm
    val wfabsap_sinst_tinst : thm
    val wfabsap_slbounds : thm
    val wfabsap_wfs : thm
    val wfabsap_wft : thm
    val wfcod_no_bound : thm
    val wfcod_no_bound0 : thm
    val wft_def : thm
    val wft_ind : thm
    val wft_no_bound : thm
    val wft_tbounds : thm
    val wft_tinst : thm
    val wft_tsubtm : thm
    val wft_wfs : thm
    val wfvmap_cont_DRESTRICT : thm
  
  val tmsytx_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [finite_map] Parent theory of "tmsytx"
   
   [finite_set] Parent theory of "tmsytx"
   
   [string] Parent theory of "tmsytx"
   
   [FMAP_MAP_DEF]  Definition
      
      ⊢ ∀f σ. FMAP_MAP f σ = FUN_FMAP (λx. f (σ ' x)) (FDOM σ)
   
   [complete_def]  Definition
      
      ⊢ ∀σ. complete σ ⇔ ∀n s. (n,s) ∈ FDOM σ ⇒ ∀v. v ∈ sfv s ⇒ v ∈ FDOM σ
   
   [cstt_def]  Definition
      
      ⊢ ∀σ. cstt σ ⇔ ∀n s. (n,s) ∈ FDOM σ ⇒ sort_of (σ ' (n,s)) = sinst σ s
   
   [cvmap_def]  Definition
      
      ⊢ ∀s. cvmap s = FUN_FMAP (λ(n,s). Var n s) s
   
   [evmap_def]  Definition
      
      ⊢ ∀σ s. evmap σ s = σ ⊌ cvmap s
   
   [finput_def]  Definition
      
      ⊢ ∀Σf f. finput Σf f = SND (Σf ' f)
   
   [foutput_def]  Definition
      
      ⊢ ∀Σf f. foutput Σf f = FST (Σf ' f)
   
   [fsymin_def]  Definition
      
      ⊢ ∀Σf f. fsymin Σf f = SND (Σf ' f)
   
   [fsymout_def]  Definition
      
      ⊢ ∀Σf f. fsymout Σf f = FST (Σf ' f)
   
   [is_bound_def]  Definition
      
      ⊢ (∀v0 v1. is_bound (Var v0 v1) ⇔ F) ∧
        (∀v2 v3 v4. is_bound (Fn v2 v3 v4) ⇔ F) ∧
        ∀v5. is_bound (Bound v5) ⇔ T
   
   [is_cont_def]  Definition
      
      ⊢ ∀ct. is_cont ct ⇔ ∀n s. (n,s) ∈ ct ⇒ sfv s ⊆ ct
   
   [isfsym_def]  Definition
      
      ⊢ ∀Σf f. isfsym Σf f ⇔ f ∈ FDOM Σf
   
   [mk_bmap_def]  Definition
      
      ⊢ ∀tl. mk_bmap tl = FUN_FMAP (λn. EL n tl) (count (LENGTH tl))
   
   [no_bound_def]  Definition
      
      ⊢ ∀σ. no_bound σ ⇔ ∀x. x ∈ FDOM σ ⇒ tbounds (σ ' x) = ∅
   
   [o_vmap_def]  Definition
      
      ⊢ ∀σ2 σ1. o_vmap σ2 σ1 = FMAP_MAP2 (λ((n,s),t). tinst σ2 t) σ1
   
   [ok_abs_def]  Definition
      
      ⊢ ∀sl. ok_abs sl ⇔ ∀n. n < LENGTH sl ⇒ sbounds (EL n sl) ⊆ count n
   
   [shift_bmap_def]  Definition
      
      ⊢ ∀i bmap.
          shift_bmap i bmap =
          FUN_FMAP (λn. tshift i (bmap ' (n − i)))
            (IMAGE ($+ i) (FDOM bmap))
   
   [slbounds_def]  Definition
      
      ⊢ slbounds [] = ∅ ∧
        ∀h t. slbounds (h::t) = sbounds h ∪ IMAGE PRE (slbounds t DELETE 0)
   
   [slprpl_def]  Definition
      
      ⊢ (∀bmap. slprpl bmap [] = []) ∧
        ∀bmap h t.
          slprpl bmap (h::t) = sprpl bmap h::slprpl (shift_bmap 1 bmap) t
   
   [sort_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa1'.
                 ∀ $var$('term') $var$('sort')
                     $var$('@temp @ind_typetmsytx0list').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 (a0,ARB)
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('sort') a1) ∨
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR (SUC 0) (a0,ARB)
                                (ind_type$FCONS a1
                                   (ind_type$FCONS a2 (λn. ind_type$BOTTOM))))
                           a0 a1 a2 ∧ $var$('sort') a1 ∧
                         $var$('@temp @ind_typetmsytx0list') a2) ∨
                      (∃a. a0' =
                           (λa.
                                ind_type$CONSTR (SUC (SUC 0)) (ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('term') a0') ∧
                   (∀a1'.
                      (∃a0 a1.
                         a1' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC (SUC 0))) (a0,ARB)
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('@temp @ind_typetmsytx0list') a1) ⇒
                      $var$('sort') a1') ∧
                   (∀a2'.
                      a2' =
                      ind_type$CONSTR (SUC (SUC (SUC (SUC 0)))) (ARB,ARB)
                        (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a2' =
                         (λa0 a1.
                              ind_type$CONSTR
                                (SUC (SUC (SUC (SUC (SUC 0))))) (ARB,ARB)
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('term') a0 ∧
                         $var$('@temp @ind_typetmsytx0list') a1) ⇒
                      $var$('@temp @ind_typetmsytx0list') a2') ⇒
                   $var$('sort') a1') rep
   
   [sort_case_def]  Definition
      
      ⊢ ∀a0 a1 f. sort_CASE (St a0 a1) f = f a0 a1
   
   [sort_of_def]  Definition
      
      ⊢ (∀n s. sort_of (Var n s) = s) ∧ ∀f s l. sort_of (Fn f s l) = s
   
   [specsl_def]  Definition
      
      ⊢ (∀i t. specsl i t [] = []) ∧
        ∀i t s sl. specsl i t (s::sl) = srpl i t s::specsl (i + 1) t sl
   
   [stms_def]  Definition
      
      ⊢ ∀n tl. stms (St n tl) = tl
   
   [tabs_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0 x1. tabs x x0 x1 = OUTL (tabs_def_UNION (INL (x,x0,x1)))
   
   [tabs_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0 x1. sabs x x0 x1 = OUTR (tabs_def_UNION (INR (x,x0,x1)))
   
   [tabs_def_UNION_primitive]  Definition
      
      ⊢ tabs_def_UNION =
        WFREC
          (@R. WF R ∧
               (∀tl f st i s m.
                  R (INR ((m,s),i,st)) (INL ((m,s),i,Fn f st tl))) ∧
               (∀st f i s m tl a.
                  MEM a tl ⇒ R (INL ((m,s),i,a)) (INL ((m,s),i,Fn f st tl))) ∧
               ∀n i s m tl a.
                 MEM a tl ⇒ R (INL ((m,s),i,a)) (INR ((m,s),i,St n tl)))
          (λtabs_def_UNION a'.
               case a' of
                 INL ((m,s),i,Var n st) =>
                   I (INL (if m = n ∧ s = st then Bound i else Var n st))
               | INL ((m,s),i,Fn f st' tl) =>
                 I
                   (INL
                      (Fn f (OUTR (tabs_def_UNION (INR ((m,s),i,st'))))
                         (MAP (λa. OUTL (tabs_def_UNION (INL ((m,s),i,a))))
                            tl)))
               | INL ((m,s),i,Bound i') => I (INL (Bound i'))
               | INR ((m',s'),i'',St n' tl') =>
                 I
                   (INR
                      (St n'
                         (MAP
                            (λa.
                                 OUTL
                                   (tabs_def_UNION (INL ((m',s'),i'',a))))
                            tl'))))
   
   [tbounds_def_UNION_extract0]  Definition
      
      ⊢ ∀x. tbounds x = tbounds_def_UNION (INL x)
   
   [tbounds_def_UNION_extract1]  Definition
      
      ⊢ ∀x. sbounds x = tbounds_def_UNION (INR x)
   
   [tbounds_def_UNION_primitive]  Definition
      
      ⊢ tbounds_def_UNION =
        WFREC
          (@R. WF R ∧ (∀n s. R (INR s) (INL (Var n s))) ∧
               (∀l n s. R (INR s) (INL (Fn n s l))) ∧
               (∀s n l a. MEM a l ⇒ R (INL a) (INL (Fn n s l))) ∧
               ∀n tl a. MEM a tl ⇒ R (INL a) (INR (St n tl)))
          (λtbounds_def_UNION a'.
               case a' of
                 INL (Var n s) => I (tbounds_def_UNION (INR s))
               | INL (Fn n' s' l) =>
                 I
                   (BIGUNION (set (MAP (λa. tbounds_def_UNION (INL a)) l)) ∪
                    tbounds_def_UNION (INR s'))
               | INL (Bound i) => I {i}
               | INR (St n'' tl) =>
                 I
                   (BIGUNION (set (MAP (λa. tbounds_def_UNION (INL a)) tl))))
   
   [term_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('term') $var$('sort')
                     $var$('@temp @ind_typetmsytx0list').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 (a0,ARB)
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('sort') a1) ∨
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR (SUC 0) (a0,ARB)
                                (ind_type$FCONS a1
                                   (ind_type$FCONS a2 (λn. ind_type$BOTTOM))))
                           a0 a1 a2 ∧ $var$('sort') a1 ∧
                         $var$('@temp @ind_typetmsytx0list') a2) ∨
                      (∃a. a0' =
                           (λa.
                                ind_type$CONSTR (SUC (SUC 0)) (ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('term') a0') ∧
                   (∀a1'.
                      (∃a0 a1.
                         a1' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC (SUC 0))) (a0,ARB)
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('@temp @ind_typetmsytx0list') a1) ⇒
                      $var$('sort') a1') ∧
                   (∀a2'.
                      a2' =
                      ind_type$CONSTR (SUC (SUC (SUC (SUC 0)))) (ARB,ARB)
                        (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a2' =
                         (λa0 a1.
                              ind_type$CONSTR
                                (SUC (SUC (SUC (SUC (SUC 0))))) (ARB,ARB)
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('term') a0 ∧
                         $var$('@temp @ind_typetmsytx0list') a1) ⇒
                      $var$('@temp @ind_typetmsytx0list') a2') ⇒
                   $var$('term') a0') rep
   
   [term_case_def]  Definition
      
      ⊢ (∀a0 a1 f f1 f2. term_CASE (Var a0 a1) f f1 f2 = f a0 a1) ∧
        (∀a0 a1 a2 f f1 f2. term_CASE (Fn a0 a1 a2) f f1 f2 = f1 a0 a1 a2) ∧
        ∀a f f1 f2. term_CASE (Bound a) f f1 f2 = f2 a
   
   [term_size_def]  Definition
      
      ⊢ (∀a0 a1.
           term_size (Var a0 a1) =
           1 + (list_size char_size a0 + sort_size a1)) ∧
        (∀a0 a1 a2.
           term_size (Fn a0 a1 a2) =
           1 + (list_size char_size a0 + (sort_size a1 + term1_size a2))) ∧
        (∀a. term_size (Bound a) = 1 + a) ∧
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
               | INL (Bound v0) => I ∅
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
               | INL (σ,Bound i) => I (INL (Bound i))
               | INR (σ',St n' tl') =>
                 I
                   (INR
                      (St n'
                         (MAP (λa. OUTL (tinst_def_UNION (INL (σ',a)))) tl'))))
   
   [tlfv_def]  Definition
      
      ⊢ ∀l. tlfv l = BIGUNION {tfv t | MEM t l}
   
   [tmatch_def_UNION_AUX]  Definition
      
      ⊢ ∀R. tmatch_def_UNION_aux R =
            WFREC R
              (λtmatch_def_UNION a.
                   case a of
                     INL (lcs,Var n s,ct,f) =>
                       I
                         (if tbounds ct ≠ ∅ then NONE
                          else if (n,s) ∈ lcs then
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
                   | INL (lcs,Fn f1 s1 tl1,Bound v8,f) => I NONE
                   | INL (lcs,Bound i,Var v9 v10,f) => I NONE
                   | INL (lcs,Bound i,Fn v11 v12 v13,f) => I NONE
                   | INL (lcs,Bound i,Bound j,f) =>
                     I (if i = j then SOME f else NONE)
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
               (∀f lcs s n ct.
                  ¬(tbounds ct ≠ ∅) ∧ (n,s) ∉ lcs ∧ (n,s) ∉ FDOM f ⇒
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
   
   [tprpl_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0. tprpl x x0 = OUTL (tprpl_def_UNION (INL (x,x0)))
   
   [tprpl_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0. sprpl x x0 = OUTR (tprpl_def_UNION (INR (x,x0)))
   
   [tprpl_def_UNION_primitive]  Definition
      
      ⊢ tprpl_def_UNION =
        WFREC
          (@R. WF R ∧
               (∀tl f s bmap. R (INR (bmap,s)) (INL (bmap,Fn f s tl))) ∧
               (∀s f bmap tl a.
                  MEM a tl ⇒ R (INL (bmap,a)) (INL (bmap,Fn f s tl))) ∧
               ∀n bmap tl a.
                 MEM a tl ⇒ R (INL (bmap,a)) (INR (bmap,St n tl)))
          (λtprpl_def_UNION a'.
               case a' of
                 INL (bmap,Var n s) => I (INL (Var n s))
               | INL (bmap,Fn f s' tl) =>
                 I
                   (INL
                      (Fn f (OUTR (tprpl_def_UNION (INR (bmap,s'))))
                         (MAP (λa. OUTL (tprpl_def_UNION (INL (bmap,a))))
                            tl)))
               | INL (bmap,Bound i) =>
                 I (INL (if i ∈ FDOM bmap then bmap ' i else Bound i))
               | INR (bmap',St n' tl') =>
                 I
                   (INR
                      (St n'
                         (MAP (λa. OUTL (tprpl_def_UNION (INL (bmap',a))))
                            tl'))))
   
   [tpsubtm_def]  Definition
      
      ⊢ ∀t. tpsubtm t = tsubtm t DELETE t
   
   [trpl_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0 x1. trpl x x0 x1 = OUTL (trpl_def_UNION (INL (x,x0,x1)))
   
   [trpl_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0 x1. srpl x x0 x1 = OUTR (trpl_def_UNION (INR (x,x0,x1)))
   
   [trpl_def_UNION_primitive]  Definition
      
      ⊢ trpl_def_UNION =
        WFREC
          (@R. WF R ∧
               (∀tl f s new i. R (INR (i,new,s)) (INL (i,new,Fn f s tl))) ∧
               (∀s f new i tl a.
                  MEM a tl ⇒ R (INL (i,new,a)) (INL (i,new,Fn f s tl))) ∧
               ∀n new i tl a.
                 MEM a tl ⇒ R (INL (i,new,a)) (INR (i,new,St n tl)))
          (λtrpl_def_UNION a'.
               case a' of
                 INL (i,new,Var n s) => I (INL (Var n s))
               | INL (i,new,Fn f s' tl) =>
                 I
                   (INL
                      (Fn f (OUTR (trpl_def_UNION (INR (i,new,s'))))
                         (MAP (λa. OUTL (trpl_def_UNION (INL (i,new,a))))
                            tl)))
               | INL (i,new,Bound j) =>
                 I (INL (if i = j then new else Bound j))
               | INR (i',new',St n' tl') =>
                 I
                   (INR
                      (St n'
                         (MAP (λa. OUTL (trpl_def_UNION (INL (i',new',a))))
                            tl'))))
   
   [tshift_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0. tshift x x0 = OUTL (tshift_def_UNION (INL (x,x0)))
   
   [tshift_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0. sshift x x0 = OUTR (tshift_def_UNION (INR (x,x0)))
   
   [tshift_def_UNION_primitive]  Definition
      
      ⊢ tshift_def_UNION =
        WFREC
          (@R. WF R ∧ (∀l f s i. R (INR (i,s)) (INL (i,Fn f s l))) ∧
               (∀s f i l a. MEM a l ⇒ R (INL (i,a)) (INL (i,Fn f s l))) ∧
               ∀n i l a. MEM a l ⇒ R (INL (i,a)) (INR (i,St n l)))
          (λtshift_def_UNION a'.
               case a' of
                 INL (i,Var n s) => I (INL (Var n s))
               | INL (i,Fn f s' l) =>
                 I
                   (INL
                      (Fn f (OUTR (tshift_def_UNION (INR (i,s'))))
                         (MAP (λa. OUTL (tshift_def_UNION (INL (i,a)))) l)))
               | INL (i,Bound j) => I (INL (Bound (j + i)))
               | INR (i',St n' l') =>
                 I
                   (INR
                      (St n'
                         (MAP (λa. OUTL (tshift_def_UNION (INL (i',a)))) l'))))
   
   [tsstt_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0 x1. tsstt x x0 x1 = OUTL (tsstt_def_UNION (INL (x,x0,x1)))
   
   [tsstt_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0 x1. ssstt x x0 x1 = OUTR (tsstt_def_UNION (INR (x,x0,x1)))
   
   [tsstt_def_UNION_primitive]  Definition
      
      ⊢ tsstt_def_UNION =
        WFREC
          (@R. WF R ∧
               (∀new old s n.
                  Var n s ≠ old ⇒
                  R (INR (old,new,s)) (INL (old,new,Var n s))) ∧
               (∀new old tl st f.
                  Fn f st tl ≠ old ⇒
                  R (INR (old,new,st)) (INL (old,new,Fn f st tl))) ∧
               (∀new old tl st f a.
                  Fn f st tl ≠ old ∧ MEM a tl ⇒
                  R (INL (old,new,a)) (INL (old,new,Fn f st tl))) ∧
               ∀n new old tl a.
                 MEM a tl ⇒ R (INL (old,new,a)) (INR (old,new,St n tl)))
          (λtsstt_def_UNION a'.
               case a' of
                 INL (old,new,Var n s) =>
                   I
                     (INL
                        (if Var n s = old then new
                         else
                           Var n (OUTR (tsstt_def_UNION (INR (old,new,s))))))
               | INL (old,new,Fn f st tl) =>
                 I
                   (INL
                      (if Fn f st tl = old then new
                       else
                         Fn f (OUTR (tsstt_def_UNION (INR (old,new,st))))
                           (MAP
                              (λa. OUTL (tsstt_def_UNION (INL (old,new,a))))
                              tl)))
               | INL (old,new,Bound i) =>
                 I (INL (if Bound i = old then new else Bound i))
               | INR (old',new',St n' tl') =>
                 I
                   (INR
                      (St n'
                         (MAP
                            (λa. OUTL (tsstt_def_UNION (INL (old',new',a))))
                            tl'))))
   
   [tsubst_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0 x1. tsubst x x0 x1 = OUTL (tsubst_def_UNION (INL (x,x0,x1)))
   
   [tsubst_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0 x1. ssubst x x0 x1 = OUTR (tsubst_def_UNION (INR (x,x0,x1)))
   
   [tsubst_def_UNION_primitive]  Definition
      
      ⊢ tsubst_def_UNION =
        WFREC
          (@R. WF R ∧
               (∀t st s n m.
                  ¬(m = n ∧ s = st) ⇒
                  R (INR ((m,s),t,st)) (INL ((m,s),t,Var n st))) ∧
               (∀tl f st t s m.
                  R (INR ((m,s),t,st)) (INL ((m,s),t,Fn f st tl))) ∧
               (∀st f t s m tl a.
                  MEM a tl ⇒ R (INL ((m,s),t,a)) (INL ((m,s),t,Fn f st tl))) ∧
               ∀n t s m tl a.
                 MEM a tl ⇒ R (INL ((m,s),t,a)) (INR ((m,s),t,St n tl)))
          (λtsubst_def_UNION a'.
               case a' of
                 INL ((m,s),t,Var n st) =>
                   I
                     (INL
                        (if m = n ∧ s = st then t
                         else
                           Var n
                             (OUTR (tsubst_def_UNION (INR ((m,s),t,st))))))
               | INL ((m,s),t,Fn f st' tl) =>
                 I
                   (INL
                      (Fn f (OUTR (tsubst_def_UNION (INR ((m,s),t,st'))))
                         (MAP
                            (λa. OUTL (tsubst_def_UNION (INL ((m,s),t,a))))
                            tl)))
               | INL ((m,s),t,Bound i) => I (INL (Bound i))
               | INR ((m',s'),t',St n' tl') =>
                 I
                   (INR
                      (St n'
                         (MAP
                            (λa.
                                 OUTL
                                   (tsubst_def_UNION (INL ((m',s'),t',a))))
                            tl'))))
   
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
               | INL (Bound i) => I {Bound i}
               | INR (St n' l') =>
                 I (BIGUNION (set (MAP (λa. tsubtm_def_UNION (INL a)) l'))))
   
   [vmap_fix_def]  Definition
      
      ⊢ ∀σ vs.
          vmap_fix σ vs ⇔ ∀n s. (n,s) ∈ FDOM σ ∩ vs ⇒ σ ' (n,s) = Var n s
   
   [wfcod_def]  Definition
      
      ⊢ ∀Σf σ. wfcod Σf σ ⇔ ∀n s. (n,s) ∈ FDOM σ ⇒ wft Σf (σ ' (n,s))
   
   [wft_def_UNION_extract0]  Definition
      
      ⊢ ∀x x0. wft x x0 ⇔ wft_def_UNION (INL (x,x0))
   
   [wft_def_UNION_extract1]  Definition
      
      ⊢ ∀x x0. wfs x x0 ⇔ wft_def_UNION (INR (x,x0))
   
   [wft_def_UNION_primitive]  Definition
      
      ⊢ wft_def_UNION =
        WFREC
          (@R. WF R ∧ (∀n s Σf. R (INR (Σf,s)) (INL (Σf,Var n s))) ∧
               (∀tl f s Σf. R (INR (Σf,s)) (INL (Σf,Fn f s tl))) ∧
               (∀s f Σf tl t.
                  MEM t tl ⇒ R (INL (Σf,t)) (INL (Σf,Fn f s tl))) ∧
               ∀n Σf tl a. MEM a tl ⇒ R (INL (Σf,a)) (INR (Σf,St n tl)))
          (λwft_def_UNION a'.
               case a' of
                 INL (Σf,Var n s) => I (wft_def_UNION (INR (Σf,s)))
               | INL (Σf,Fn f s' tl) =>
                 I
                   (wft_def_UNION (INR (Σf,s')) ∧
                    (∀t. MEM t tl ⇒ wft_def_UNION (INL (Σf,t))) ∧
                    isfsym Σf f ∧
                    IS_SOME (tlmatch ∅ (MAP Var' (fsymin Σf f)) tl FEMPTY) ∧
                    sinst
                      (THE (tlmatch ∅ (MAP Var' (fsymin Σf f)) tl FEMPTY))
                      (fsymout Σf f) =
                    s')
               | INL (Σf,Bound i) => I F
               | INR (Σf',St n' tl') =>
                 I (EVERY (λa. wft_def_UNION (INL (Σf',a))) tl'))
   
   [BIGUNION_tbounds]  Theorem
      
      ⊢ (∀n1 s1. (n1,s1) ∈ BIGUNION {tfv y | MEM y l0} ⇒ sbounds s1 = ∅) ∧
        MEM y l0 ∧ (n,s) ∈ tfv y ⇒
        BIGUNION
          {tbounds t | (∃y. t = tsubst (n,s) (Bound i) y ∧ MEM y l0)} =
        {i} ∪ BIGUNION {tbounds t | MEM t l0}
   
   [BIGUNION_tbounds']  Theorem
      
      ⊢ (∀n1 s1. (n1,s1) ∈ BIGUNION {tfv y | MEM y l0} ⇒ (n,s) ∉ sfv s1) ∧
        (∀n1 s1. (n1,s1) ∈ BIGUNION {tfv y | MEM y l0} ⇒ sbounds s1 = ∅) ∧
        MEM y l0 ∧ (n,s) ∈ tfv y ⇒
        BIGUNION {tbounds t | (∃y. t = tabs (n,s) i y ∧ MEM y l0)} =
        {i} ∪ BIGUNION {tbounds t | MEM t l0}
   
   [Bound_NOT_wft]  Theorem
      
      ⊢ ¬wft Σf (Bound i)
   
   [Bound_tsubtm]  Theorem
      
      ⊢ (∀t. Bound i ∈ tsubtm t ⇔ i ∈ tbounds t) ∧
        ∀s. Bound i ∈ ssubtm s ⇔ i ∈ sbounds s
   
   [DRESTRICT_SUBMAP_SUBSET]  Theorem
      
      ⊢ f ⊑ g ⇒ ∀s. s ⊆ FDOM f ⇒ DRESTRICT f s = DRESTRICT g s
   
   [DRESTRICT_UNION_SING]  Theorem
      
      ⊢ x ∈ FDOM σ ⇒ DRESTRICT σ (s ∪ {x}) = DRESTRICT σ s |+ (x,σ ' x)
   
   [DRESTRICT_cstt]  Theorem
      
      ⊢ cstt σ ∧ s ⊆ FDOM σ ∧ is_cont s ⇒ cstt (DRESTRICT σ s)
   
   [DRESTRICT_eq]  Theorem
      
      ⊢ s ⊆ FDOM σ1 ∧ s ⊆ FDOM σ2 ∧ (∀x. x ∈ s ⇒ σ1 ' x = σ2 ' x) ⇒
        DRESTRICT σ1 s = DRESTRICT σ2 s
   
   [DRESTRICT_no_bound]  Theorem
      
      ⊢ no_bound σ ⇒ no_bound (DRESTRICT σ s)
   
   [DRESTRICT_wfcod]  Theorem
      
      ⊢ wfcod Σf σ ⇒ ∀s. wfcod Σf (DRESTRICT σ s)
   
   [EL_REVERSE1]  Theorem
      
      ⊢ n < LENGTH l ⇒ EL n (REVERSE l ⧺ [e]) = EL n (REVERSE l)
   
   [EL_REVERSE2]  Theorem
      
      ⊢ EL (LENGTH l) (REVERSE l ⧺ [e]) = e
   
   [FAPPLY_DOMSUB]  Theorem
      
      ⊢ x ∈ FDOM σ ⇒ (σ \\ x0) ' x = if x = x0 then FEMPTY ' x else σ ' x
   
   [FAPPLY_FMAP_MAP]  Theorem
      
      ⊢ ∀σ f x. x ∈ FDOM σ ⇒ FMAP_MAP f σ ' x = f (σ ' x)
   
   [FAPPLY_cvmap]  Theorem
      
      ⊢ FINITE vs ∧ (n,s) ∈ vs ⇒ cvmap vs ' (n,s) = Var n s
   
   [FAPPLY_mk_bmap]  Theorem
      
      ⊢ n < LENGTH tl ⇒ mk_bmap tl ' n = EL n tl
   
   [FAPPLY_o_vmap]  Theorem
      
      ⊢ (n,s) ∈ FDOM σ1 ⇒ o_vmap σ2 σ1 ' (n,s) = tinst σ2 (σ1 ' (n,s))
   
   [FAPPLY_shift_bmap]  Theorem
      
      ⊢ x ∈ FDOM bmap ⇒ shift_bmap i bmap ' (i + x) = tshift i (bmap ' x)
   
   [FDOM_FINITE_lemma]  Theorem
      
      ⊢ FINITE {f x | x ∈ FDOM fmap}
   
   [FDOM_FMAP_MAP]  Theorem
      
      ⊢ FDOM (FMAP_MAP f σ) = FDOM σ
   
   [FDOM_TO_FMAP]  Theorem
      
      ⊢ FDOM (TO_FMAP l) = set (MAP FST l)
   
   [FDOM_cvmap]  Theorem
      
      ⊢ FINITE vs ⇒ FDOM (cvmap vs) = vs
   
   [FDOM_evmap]  Theorem
      
      ⊢ FINITE vs ⇒ FDOM (evmap σ vs) = FDOM σ ∪ vs
   
   [FDOM_mk_bmap]  Theorem
      
      ⊢ FDOM (mk_bmap tl) = count (LENGTH tl)
   
   [FDOM_o_vmap]  Theorem
      
      ⊢ FDOM (o_vmap σ2 σ1) = FDOM σ1
   
   [FDOM_shift_bmap]  Theorem
      
      ⊢ FDOM (shift_bmap i bmap) = IMAGE ($+ i) (FDOM bmap)
   
   [FEMPTY_complete]  Theorem
      
      ⊢ complete FEMPTY
   
   [FEMPTY_cstt]  Theorem
      
      ⊢ cstt FEMPTY
   
   [FEMPTY_no_bound]  Theorem
      
      ⊢ no_bound FEMPTY
   
   [FUNION_COMM1]  Theorem
      
      ⊢ ∀f g. (∀x. x ∈ FDOM f ∧ x ∈ FDOM g ⇒ f ' x = g ' x) ⇒ f ⊌ g = g ⊌ f
   
   [FUPDATE_cstt]  Theorem
      
      ⊢ complete σ ∧ cstt σ ∧ sfv s0 ⊆ FDOM σ ∧
        (∀n s. (n,s) ∈ FDOM σ ⇒ (n0,s0) ∉ sfv s) ⇒
        ∀t. sort_of t = sinst σ s0 ⇒ cstt (σ |+ ((n0,s0),t))
   
   [FUPDATE_wfcod]  Theorem
      
      ⊢ wfcod Σf σ ⇒ ∀x t. wft Σf t ⇒ wfcod Σf (σ |+ ((n,s),t))
   
   [Fn_tpsubtm]  Theorem
      
      ⊢ (t0 ∈ ssubtm s ⇒ t0 ∈ tpsubtm (Fn f s tl)) ∧
        ∀t. MEM t tl ∧ t0 ∈ tsubtm t ⇒ t0 ∈ tpsubtm (Fn f s tl)
   
   [Fn_tpsubtm_neq]  Theorem
      
      ⊢ (t0 ∈ ssubtm s ⇒ t0 ≠ Fn f s tl) ∧
        ∀t. MEM t tl ∧ t0 ∈ tsubtm t ⇒ t0 ≠ Fn f s tl
   
   [IN_slbounds]  Theorem
      
      ⊢ ∀l i. i ∈ slbounds l ⇔ ∃m. m < LENGTH l ∧ i + m ∈ sbounds (EL m l)
   
   [IS_SOME_match]  Theorem
      
      ⊢ (∀t f σ.
           complete f ∧ cstt σ ∧ no_bound σ ∧ tfv t ⊆ FDOM σ ∧
           (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ tfv t ⇒ f ' (n,s) = σ ' (n,s)) ⇒
           tmatch ∅ t (tinst σ t) f = SOME (f ⊌ DRESTRICT σ (tfv t))) ∧
        (∀st f σ.
           complete f ∧ cstt σ ∧ no_bound σ ∧ sfv st ⊆ FDOM σ ∧
           (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ sfv st ⇒ f ' (n,s) = σ ' (n,s)) ⇒
           smatch ∅ st (sinst σ st) f = SOME (f ⊌ DRESTRICT σ (sfv st))) ∧
        ∀l f σ.
          complete f ∧ cstt σ ∧ no_bound σ ∧
          BIGUNION {tfv t | MEM t l} ⊆ FDOM σ ∧
          (∀n s.
             (n,s) ∈ FDOM f ∩ FDOM σ ∩ BIGUNION {tfv t | MEM t l} ⇒
             f ' (n,s) = σ ' (n,s)) ⇒
          tlmatch ∅ l (MAP (tinst σ) l) f =
          SOME (f ⊌ DRESTRICT σ (BIGUNION {tfv t | MEM t l}))
   
   [IS_SOME_match_FEMPTY]  Theorem
      
      ⊢ (∀t σ.
           cstt σ ∧ tfv t ⊆ FDOM σ ∧ no_bound σ ⇒
           tmatch ∅ t (tinst σ t) FEMPTY = SOME (DRESTRICT σ (tfv t))) ∧
        (∀st σ.
           cstt σ ∧ sfv st ⊆ FDOM σ ∧ no_bound σ ⇒
           smatch ∅ st (sinst σ st) FEMPTY = SOME (DRESTRICT σ (sfv st))) ∧
        ∀l σ.
          cstt σ ∧ BIGUNION {tfv t | MEM t l} ⊆ FDOM σ ∧ no_bound σ ⇒
          tlmatch ∅ l (MAP (tinst σ) l) FEMPTY =
          SOME (DRESTRICT σ (BIGUNION {tfv t | MEM t l}))
   
   [IS_SOME_tlmatch_inst]  Theorem
      
      ⊢ cstt σ ∧ wfcod Σf σ ∧ BIGUNION {tfv t | MEM t l} ⊆ FDOM σ ∧
        IS_SOME (tlmatch ∅ l0 l FEMPTY) ⇒
        IS_SOME (tlmatch ∅ l0 (MAP (tinst σ) l) FEMPTY)
   
   [LENGTH_abssl]  Theorem
      
      ⊢ ∀l n s i. LENGTH (abssl (n,s) i l) = LENGTH l
   
   [LENGTH_slabs]  Theorem
      
      ⊢ ∀l n s i. LENGTH (slabs (n,s) i l) = LENGTH l
   
   [LENGTH_slprpl]  Theorem
      
      ⊢ ∀l bmap. LENGTH (slprpl bmap l) = LENGTH l
   
   [LENGTH_specsl]  Theorem
      
      ⊢ ∀sl t i. LENGTH (specsl i t sl) = LENGTH sl
   
   [MAP_fix]  Theorem
      
      ⊢ MAP f l = l ⇔ ∀x. MEM x l ⇒ f x = x
   
   [MAP_sinst_abssl]  Theorem
      
      ⊢ ∀l i σ nn an ast.
          BIGUNION {sfv s | MEM s l} ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧
          (an,ast) ∉ FDOM σ ∧
          (∀x s.
             x ∈ BIGUNION {sfv s | MEM s l} ∪ sfv ast ∧ x ≠ (an,ast) ⇒
             (nn,s) ∉ tfv (σ ' x)) ∧
          (∀n1 s1. (n1,s1) ∈ BIGUNION {sfv s | MEM s l} ⇒ (an,ast) ∉ sfv s1) ⇒
          abssl (nn,sinst σ ast) i
            (MAP (sinst (σ |+ ((an,ast),Var nn (sinst σ ast)))) l) =
          MAP (sinst σ) (abssl (an,ast) i l)
   
   [MAP_sinst_specsl]  Theorem
      
      ⊢ ∀sl i t σ.
          (∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = ∅) ∧
          (∀n s st. MEM st sl ∧ (n,s) ∈ sfv st ⇒ sbounds s = ∅) ∧
          BIGUNION {sfv s | MEM s sl} ⊆ FDOM σ ⇒
          MAP (sinst σ) (specsl i t sl) =
          specsl i (tinst σ t) (MAP (sinst σ) sl)
   
   [MEM_list_size_leq]  Theorem
      
      ⊢ ∀l x. MEM x l ⇒ size x ≤ list_size size l
   
   [NOTIN_slbounds_abssl]  Theorem
      
      ⊢ (∀s1. MEM s1 l ⇒ (n,s) ∉ sfv s1) ⇒ abssl (n,s) i l = l
   
   [NOTIN_slbounds_slabs]  Theorem
      
      ⊢ (∀s1. MEM s1 l ⇒ (n,s) ∉ sfv s1) ⇒ slabs (n,s) i l = l
   
   [NOT_ok_abs]  Theorem
      
      ⊢ ∀l i n s st. MEM st l ∧ (n,s) ∈ sfv st ⇒ ¬ok_abs (slabs (n,s) i l)
   
   [NOT_ok_abssl]  Theorem
      
      ⊢ ∀l i n s st.
          (∀n1 s1 s0. MEM s0 l ∧ (n1,s1) ∈ sfv s0 ⇒ (n,s) ∉ sfv s1) ∧
          MEM st l ∧ (n,s) ∈ sfv st ⇒
          ¬ok_abs (abssl (n,s) i l)
   
   [SUBMAP_DRESTRICT_IFF]  Theorem
      
      ⊢ f ⊑ g ⇔ f = DRESTRICT g (FDOM f)
   
   [TO_FMAP_MEM]  Theorem
      
      ⊢ ALL_DISTINCT (MAP FST l) ⇒ MEM (a,b) l ⇒ TO_FMAP l ' a = b
   
   [UNION_is_cont]  Theorem
      
      ⊢ is_cont s1 ∧ is_cont s2 ⇒ is_cont (s1 ∪ s2)
   
   [Var_tpsubtm]  Theorem
      
      ⊢ t0 ∈ ssubtm s ⇒ t0 ∈ tpsubtm (Var n s)
   
   [Var_tpsubtm_neq]  Theorem
      
      ⊢ t0 ∈ ssubtm s ⇒ t0 ≠ Var n s
   
   [Var_tsubtm_tfv]  Theorem
      
      ⊢ (∀tm n s. Var n s ∈ tsubtm tm ⇔ (n,s) ∈ tfv tm) ∧
        ∀st n s. Var n s ∈ ssubtm st ⇔ (n,s) ∈ sfv st
   
   [abssl_EL]  Theorem
      
      ⊢ ∀l n s m i.
          m < LENGTH l ⇒
          EL m (abssl (n,s) i l) = sabs (n,s) (i + m) (EL m l)
   
   [abssl_def]  Theorem
      
      ⊢ (∀s n i. abssl (n,s) i [] = []) ∧
        ∀t s n i h.
          abssl (n,s) i (h::t) = sabs (n,s) i h::abssl (n,s) (i + 1) t
   
   [abssl_id]  Theorem
      
      ⊢ ∀l i n s. (∀st. MEM st l ⇒ (n,s) ∉ sfv st) ⇒ abssl (n,s) i l = l
   
   [abssl_ind]  Theorem
      
      ⊢ ∀P. (∀n s i. P (n,s) i []) ∧
            (∀n s i h t. P (n,s) (i + 1) t ⇒ P (n,s) i (h::t)) ⇒
            ∀v v1 v2 v3. P (v,v1) v2 v3
   
   [abssl_ok_abs]  Theorem
      
      ⊢ ∀l i n s.
          (∀n1 s1 s0. MEM s0 l ∧ (n1,s1) ∈ sfv s0 ⇒ (n,s) ∉ sfv s1) ⇒
          (ok_abs (abssl (n,s) i l) ⇔
           ok_abs l ∧ ∀st. MEM st l ⇒ (n,s) ∉ sfv st)
   
   [abssl_specsl]  Theorem
      
      ⊢ ∀sl i n s.
          (∀st. MEM st sl ⇒ (n,s) ∉ sfv st) ⇒
          abssl (n,s) i (specsl i (Var n s) sl) = sl
   
   [better_tm_induction]  Theorem
      
      ⊢ ∀Pt Ps.
          (∀s. Ps s ⇒ ∀s0. Pt (Var s0 s)) ∧
          (∀s l. Ps s ∧ (∀t. MEM t l ⇒ Pt t) ⇒ ∀s0. Pt (Fn s0 s l)) ∧
          (∀n. Pt (Bound n)) ∧ (∀l. (∀t. MEM t l ⇒ Pt t) ⇒ ∀s. Ps (St s l)) ⇒
          (∀t. Pt t) ∧ ∀s. Ps s
   
   [complete_FDOM_is_cont]  Theorem
      
      ⊢ complete f ⇔ is_cont (FDOM f)
   
   [cstt_FUPDATE]  Theorem
      
      ⊢ FINITE vs ∧ (∀n s. (n,s) ∈ vs ⇒ (en,es) ∉ sfv s) ∧ ¬is_bound t ∧
        sort_of t = es ⇒
        cstt (cvmap vs |+ ((en,es),t))
   
   [cstt_SUBMAP]  Theorem
      
      ⊢ cstt f ∧ f ⊑ σ ∧ complete f ∧
        (∀n s.
           (n,s) ∈ FDOM σ ∧ (n,s) ∉ FDOM f ⇒
           sort_of (σ ' (n,s)) = sinst σ s) ⇒
        cstt σ
   
   [cstt_cvmap]  Theorem
      
      ⊢ FINITE s ⇒ cstt (cvmap s)
   
   [cstt_sort_of_tinst]  Theorem
      
      ⊢ cstt σ ∧ no_bound σ ∧ tbounds t = ∅ ⇒
        sort_of (tinst σ t) = sinst σ (sort_of t)
   
   [cstt_sort_of_tinst']  Theorem
      
      ⊢ cstt σ ∧ no_bound σ ∧ ¬is_bound t ⇒
        sort_of (tinst σ t) = sinst σ (sort_of t)
   
   [datatype_term]  Theorem
      
      ⊢ DATATYPE (term Var Fn Bound ∧ sort St)
   
   [fmap_fv_inst_eq]  Theorem
      
      ⊢ (∀t σ1 σ2.
           DRESTRICT σ1 (tfv t) = DRESTRICT σ2 (tfv t) ⇒
           tinst σ1 t = tinst σ2 t) ∧
        ∀s σ1 σ2.
          DRESTRICT σ1 (sfv s) = DRESTRICT σ2 (sfv s) ⇒
          sinst σ1 s = sinst σ2 s
   
   [fmap_fv_inst_eq_alt]  Theorem
      
      ⊢ (∀t σ1 σ2.
           tfv t ⊆ FDOM σ1 ∧ tfv t ⊆ FDOM σ2 ∧
           (∀x. x ∈ tfv t ⇒ σ1 ' x = σ2 ' x) ⇒
           tinst σ1 t = tinst σ2 t) ∧
        ∀s σ1 σ2.
          sfv s ⊆ FDOM σ1 ∧ sfv s ⊆ FDOM σ2 ∧
          (∀x. x ∈ sfv s ⇒ σ1 ' x = σ2 ' x) ⇒
          sinst σ1 s = sinst σ2 s
   
   [fv_subtm]  Theorem
      
      ⊢ (∀t n st. (n,st) ∈ tfv t ⇔ ∃t0. t0 ∈ tsubtm t ∧ (n,st) ∈ tfv t0) ∧
        ∀s n st. (n,st) ∈ sfv s ⇔ ∃t0. t0 ∈ ssubtm s ∧ (n,st) ∈ tfv t0
   
   [ill_formed_tabs_still_in]  Theorem
      
      ⊢ (∀tm n s n0 s0.
           (n0,s0) ∈ tfv tm ∧ (n,s) ∈ sfv s0 ⇒
           (n,s) ∈ tfv (tabs (n,s) i tm)) ∧
        ∀st n s n0 s0.
          (n0,s0) ∈ sfv st ∧ (n,s) ∈ sfv s0 ⇒ (n,s) ∈ sfv (sabs (n,s) i st)
   
   [inst_o_vmap]  Theorem
      
      ⊢ (∀t σ1 σ2.
           tfv t ⊆ FDOM σ1 ∧ tfv (tinst σ1 t) ⊆ FDOM σ2 ⇒
           tinst σ2 (tinst σ1 t) = tinst (o_vmap σ2 σ1) t) ∧
        ∀s σ1 σ2.
          sfv s ⊆ FDOM σ1 ∧ sfv (sinst σ1 s) ⊆ FDOM σ2 ⇒
          sinst σ2 (sinst σ1 s) = sinst (o_vmap σ2 σ1) s
   
   [is_bound_alt]  Theorem
      
      ⊢ is_bound t ⇔ ∃i. t = Bound i
   
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
          ∃σ. cstt σ ∧ no_bound σ ∧ tfv t1 ⊆ FDOM σ ∧ t2 = tinst σ t1
   
   [match_SOME_iff_inst']  Theorem
      
      ⊢ ∀t1 t2.
          IS_SOME (tmatch ∅ t1 t2 FEMPTY) ⇔
          ∃σ. cstt σ ∧ no_bound σ ∧ tfv t1 = FDOM σ ∧ t2 = tinst σ t1
   
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
   
   [mk_bmap_MAP]  Theorem
      
      ⊢ mk_bmap (MAP f l) = FMAP_MAP f (mk_bmap l)
   
   [no_bound_FUPDATE]  Theorem
      
      ⊢ no_bound f ∧ tbounds t = ∅ ⇒ no_bound (f |+ (x,t))
   
   [no_bound_not_bound]  Theorem
      
      ⊢ no_bound σ ∧ x ∈ FDOM σ ⇒ ¬is_bound (σ ' x)
   
   [no_bound_not_is_bound]  Theorem
      
      ⊢ no_bound σ ∧ x ∈ FDOM σ ⇒ ¬is_bound (σ ' x)
   
   [o_vmap_cstt]  Theorem
      
      ⊢ cstt σ1 ∧ cstt σ2 ∧ no_bound σ1 ∧ no_bound σ2 ∧ complete σ1 ∧
        (∀x. x ∈ FDOM σ1 ⇒ tfv (σ1 ' x) ⊆ FDOM σ2) ⇒
        cstt (o_vmap σ2 σ1)
   
   [o_vmap_no_bound]  Theorem
      
      ⊢ no_bound σ1 ∧ no_bound σ2 ⇒ no_bound (o_vmap σ2 σ1)
   
   [ok_abs_HD]  Theorem
      
      ⊢ ok_abs (s::sl) ⇒ sbounds s = ∅
   
   [ok_abs_abssl]  Theorem
      
      ⊢ (∀n1 s1 s0. MEM s0 l ∧ (n1,s1) ∈ sfv s0 ⇒ (n,s) ∉ sfv s1) ⇒
        ok_abs (abssl (n,s) i l) ⇒
        ok_abs l
   
   [sabs_sinst]  Theorem
      
      ⊢ ∀e an ast σ nn.
          sfv e ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧ (an,ast) ∉ FDOM σ ∧
          (∀x s. x ∈ sfv e ∪ sfv ast ∧ x ≠ (an,ast) ⇒ (nn,s) ∉ tfv (σ ' x)) ∧
          (∀n1 s1. (n1,s1) ∈ sfv e ⇒ (an,ast) ∉ sfv s1) ⇒
          sabs (nn,sinst σ ast) i
            (sinst (σ |+ ((an,ast),Var nn (sinst σ ast))) e) =
          sinst σ (sabs (an,ast) i e)
   
   [sbounds_St]  Theorem
      
      ⊢ sbounds (St n l) = ∅ ⇔ ∀t. MEM t l ⇒ tbounds t = ∅
   
   [sbounds_tbounds]  Theorem
      
      ⊢ (∀t n st. (n,st) ∈ tfv t ⇒ sbounds st ⊆ tbounds t) ∧
        ∀s n st. (n,st) ∈ sfv s ⇒ sbounds st ⊆ sbounds s
   
   [sfv_tfv]  Theorem
      
      ⊢ ∀t n s. ¬is_bound t ∧ (n,s) ∈ sfv (sort_of t) ⇒ (n,s) ∈ tfv t
   
   [shift_bmap_0]  Theorem
      
      ⊢ shift_bmap 0 bmap = bmap
   
   [shift_bmap_FEMPTY]  Theorem
      
      ⊢ shift_bmap i FEMPTY = FEMPTY
   
   [shift_bmap_FMAP_MAP_tabs]  Theorem
      
      ⊢ shift_bmap m (FMAP_MAP (tabs (n,s) i) bmap) =
        FMAP_MAP (tabs (n,s) (i + m)) (shift_bmap m bmap)
   
   [shift_bmap_SUM]  Theorem
      
      ⊢ shift_bmap a (shift_bmap b bmap) = shift_bmap (a + b) bmap
   
   [sinst_srpl]  Theorem
      
      ⊢ (∀tm i t σ.
           (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅) ∧
           (∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = ∅) ∧ tfv tm ⊆ FDOM σ ⇒
           tinst σ (trpl i t tm) = trpl i (tinst σ t) (tinst σ tm)) ∧
        ∀st i t σ.
          (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = ∅) ∧
          (∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = ∅) ∧ sfv st ⊆ FDOM σ ⇒
          sinst σ (srpl i t st) = srpl i (tinst σ t) (sinst σ st)
   
   [slabs_EL]  Theorem
      
      ⊢ ∀l n s m i.
          m < LENGTH l ⇒
          EL m (slabs (n,s) i l) = ssubst (n,s) (Bound (i + m)) (EL m l)
   
   [slabs_abssl]  Theorem
      
      ⊢ ∀l i.
          (∀n s st. MEM st l ∧ (n,s) ∈ sfv st ⇒ (n0,s0) ∉ sfv s) ⇒
          slabs (n0,s0) i l = abssl (n0,s0) i l
   
   [slabs_def]  Theorem
      
      ⊢ (∀s n i. slabs (n,s) i [] = []) ∧
        ∀t s n i h.
          slabs (n,s) i (h::t) =
          ssubst (n,s) (Bound i) h::slabs (n,s) (i + 1) t
   
   [slabs_id]  Theorem
      
      ⊢ ∀l i n s. (∀st. MEM st l ⇒ (n,s) ∉ sfv st) ⇒ slabs (n,s) i l = l
   
   [slabs_ind]  Theorem
      
      ⊢ ∀P. (∀n s i. P (n,s) i []) ∧
            (∀n s i h t. P (n,s) (i + 1) t ⇒ P (n,s) i (h::t)) ⇒
            ∀v v1 v2 v3. P (v,v1) v2 v3
   
   [slbounds_abssl]  Theorem
      
      ⊢ ∀n s m i l.
          m < LENGTH l ∧ (n,s) ∈ sfv (EL m l) ∧
          (∀n1 s1 st. MEM st l ∧ (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
          (∀n1 s1. (n1,s1) ∈ BIGUNION {sfv s0 | MEM s0 l} ⇒ sbounds s1 = ∅) ⇒
          slbounds (abssl (n,s) i l) = {i} ∪ slbounds l
   
   [slbounds_sbounds]  Theorem
      
      ⊢ ∀l i. i ∉ slbounds l ⇔ ∀m. m < LENGTH l ⇒ i + m ∉ sbounds (EL m l)
   
   [slbounds_slabs]  Theorem
      
      ⊢ ∀n s m i l.
          m < LENGTH l ∧ (n,s) ∈ sfv (EL m l) ∧
          (∀n1 s1. (n1,s1) ∈ BIGUNION {sfv s0 | MEM s0 l} ⇒ sbounds s1 = ∅) ⇒
          slbounds (slabs (n,s) i l) = {i} ∪ slbounds l
   
   [slbounds_specsl_DELETE]  Theorem
      
      ⊢ ∀sl i t.
          (∀n s st. MEM st sl ∧ (n,s) ∈ sfv st ⇒ sbounds s = ∅) ∧
          tbounds t = ∅ ⇒
          slbounds (specsl i t sl) = slbounds sl DELETE i
   
   [slprpl_EL]  Theorem
      
      ⊢ ∀l n bmap.
          n < LENGTH l ⇒
          EL n (slprpl bmap l) = sprpl (shift_bmap n bmap) (EL n l)
   
   [slprpl_FEMPTY]  Theorem
      
      ⊢ ∀l. slprpl FEMPTY l = l
   
   [sort_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'. St a0 a1 = St a0' a1' ⇔ a0 = a0' ∧ a1 = a1'
   
   [sort_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4 f5. ∃fn0 fn1 fn2.
          (∀a0 a1. fn0 (Var a0 a1) = f0 a0 a1 (fn1 a1)) ∧
          (∀a0 a1 a2. fn0 (Fn a0 a1 a2) = f1 a0 a1 a2 (fn1 a1) (fn2 a2)) ∧
          (∀a. fn0 (Bound a) = f2 a) ∧
          (∀a0 a1. fn1 (St a0 a1) = f3 a0 a1 (fn2 a1)) ∧ fn2 [] = f4 ∧
          ∀a0 a1. fn2 (a0::a1) = f5 a0 a1 (fn0 a0) (fn2 a1)
   
   [sort_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a0 a1. M' = St a0 a1 ⇒ f a0 a1 = f' a0 a1) ⇒
          sort_CASE M f = sort_CASE M' f'
   
   [sort_case_eq]  Theorem
      
      ⊢ sort_CASE x f = v ⇔ ∃s l. x = St s l ∧ f s l = v
   
   [sort_induction]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀s. P1 s ⇒ ∀s0. P0 (Var s0 s)) ∧
          (∀s l. P1 s ∧ P2 l ⇒ ∀s0. P0 (Fn s0 s l)) ∧ (∀n. P0 (Bound n)) ∧
          (∀l. P2 l ⇒ ∀s. P1 (St s l)) ∧ P2 [] ∧
          (∀t l. P0 t ∧ P2 l ⇒ P2 (t::l)) ⇒
          (∀t. P0 t) ∧ (∀s. P1 s) ∧ ∀l. P2 l
   
   [sort_nchotomy]  Theorem
      
      ⊢ ∀ss. ∃s l. ss = St s l
   
   [specsl_EL]  Theorem
      
      ⊢ ∀sl t i n.
          n < LENGTH sl ⇒ EL n (specsl i t sl) = srpl (i + n) t (EL n sl)
   
   [specsl_abssl]  Theorem
      
      ⊢ ∀l i n0 s0 new.
          (∀m. m < LENGTH l ⇒ i + m ∉ sbounds (EL m l)) ∧
          (∀n s st. MEM st l ∧ (n,s) ∈ sfv st ⇒ sbounds s = ∅) ∧
          (∀n s st. MEM st l ∧ (n,s) ∈ sfv st ⇒ (n0,s0) ∉ sfv s) ⇒
          specsl i new (abssl (n0,s0) i l) = MAP (ssubst (n0,s0) new) l
   
   [specsl_sbounds]  Theorem
      
      ⊢ ∀sl n t i.
          (∀n s st. (n,s) ∈ sfv st ∧ MEM st sl ⇒ sbounds s = ∅) ∧
          tbounds t = ∅ ∧ n < LENGTH sl ⇒
          sbounds (EL n (specsl i t sl)) = sbounds (EL n sl) DELETE (n + i)
   
   [specsl_sbounds_SUBSET]  Theorem
      
      ⊢ ∀sl n t i.
          (∀n s st. (n,s) ∈ sfv st ∧ MEM st sl ⇒ sbounds s = ∅) ∧
          tbounds t = ∅ ∧ n < LENGTH sl ⇒
          sbounds (EL n sl) ⊆ sbounds (EL n (specsl i t sl)) ∪ {n + i}
   
   [ssubst_sinst]  Theorem
      
      ⊢ ∀e an ast σ nn.
          sfv e ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧ (an,ast) ∉ FDOM σ ∧
          (∀x s. x ∈ sfv e ∪ sfv ast ∧ x ≠ (an,ast) ⇒ (nn,s) ∉ tfv (σ ' x)) ∧
          (∀n1 s1. (n1,s1) ∈ sfv e ⇒ (an,ast) ∉ sfv s1) ⇒
          ssubst (nn,sinst σ ast) (Bound i)
            (sinst (σ |+ ((an,ast),Var nn (sinst σ ast))) e) =
          sinst σ (ssubst (an,ast) (Bound i) e)
   
   [ssubtm_tsubtm]  Theorem
      
      ⊢ ∀t0 t. ¬is_bound t ∧ t0 ∈ ssubtm (sort_of t) ⇒ t0 ∈ tsubtm t
   
   [subtm_size_less]  Theorem
      
      ⊢ (∀t t0. t0 ∈ tsubtm t ⇒ term_size t0 ≤ term_size t) ∧
        ∀s t0. t0 ∈ ssubtm s ⇒ term_size t0 < sort_size s
   
   [tabs_def]  Theorem
      
      ⊢ (∀st s n m i.
           tabs (m,s) i (Var n st) =
           if m = n ∧ s = st then Bound i else Var n st) ∧
        (∀tl st s m i f.
           tabs (m,s) i (Fn f st tl) =
           Fn f (sabs (m,s) i st) (MAP (λa. tabs (m,s) i a) tl)) ∧
        (∀t s m i. tabs (m,s) t (Bound i) = Bound i) ∧
        ∀tl s n m i.
          sabs (m,s) i (St n tl) = St n (MAP (λa. tabs (m,s) i a) tl)
   
   [tabs_id]  Theorem
      
      ⊢ (∀t. (n,s) ∉ tfv t ⇒ tabs (n,s) i t = t) ∧
        ∀st. (n,s) ∉ sfv st ⇒ sabs (n,s) i st = st
   
   [tabs_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀m s i n st. P0 (m,s) i (Var n st)) ∧
          (∀m s i f st tl.
             (∀a. MEM a tl ⇒ P0 (m,s) i a) ∧ P1 (m,s) i st ⇒
             P0 (m,s) i (Fn f st tl)) ∧ (∀m s t i. P0 (m,s) t (Bound i)) ∧
          (∀m s i n tl.
             (∀a. MEM a tl ⇒ P0 (m,s) i a) ⇒ P1 (m,s) i (St n tl)) ⇒
          (∀v0 v1 v2. P0 v0 v1 v2) ∧ ∀v0 v1 v2. P1 v0 v1 v2
   
   [tabs_tbounds_in]  Theorem
      
      ⊢ (∀tm n s i.
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∈ tfv tm ⇒
           i ∈ tbounds (tabs (n,s) i tm)) ∧
        ∀st n s i.
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∈ sfv st ⇒
          i ∈ sbounds (sabs (n,s) i st)
   
   [tabs_tinst]  Theorem
      
      ⊢ ∀e an ast σ nn.
          tfv e ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧ (an,ast) ∉ FDOM σ ∧
          (∀x s. x ∈ tfv e ∪ sfv ast ∧ x ≠ (an,ast) ⇒ (nn,s) ∉ tfv (σ ' x)) ∧
          (∀n1 s1. (n1,s1) ∈ tfv e ⇒ (an,ast) ∉ sfv s1) ⇒
          tabs (nn,sinst σ ast) i
            (tinst (σ |+ ((an,ast),Var nn (sinst σ ast))) e) =
          tinst σ (tabs (an,ast) i e)
   
   [tabs_trpl]  Theorem
      
      ⊢ (∀tm i n s.
           (n,s) ∉ tfv tm ⇒ tabs (n,s) i (trpl i (Var n s) tm) = tm) ∧
        ∀st i n s. (n,s) ∉ sfv st ⇒ sabs (n,s) i (srpl i (Var n s) st) = st
   
   [tabs_tsubst]  Theorem
      
      ⊢ (∀tm n s i.
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ⇒
           tabs (n,s) i tm = tsubst (n,s) (Bound i) tm) ∧
        ∀st n s i.
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ⇒
          sabs (n,s) i st = ssubst (n,s) (Bound i) st
   
   [tbounds_EMPTY_tinst_no_bound]  Theorem
      
      ⊢ tbounds t = ∅ ∧ no_bound σ ⇒ tbounds (tinst σ t) = ∅
   
   [tbounds_Fn]  Theorem
      
      ⊢ tbounds (Fn s0 s l) = ∅ ⇔
        sbounds s = ∅ ∧ ∀t. MEM t l ⇒ tbounds t = ∅
   
   [tbounds_def]  Theorem
      
      ⊢ (∀i. tbounds (Bound i) = {i}) ∧
        (∀s n. tbounds (Var n s) = sbounds s) ∧
        (∀s n l.
           tbounds (Fn n s l) =
           BIGUNION (set (MAP (λa. tbounds a) l)) ∪ sbounds s) ∧
        ∀tl n. sbounds (St n tl) = BIGUNION (set (MAP (λa. tbounds a) tl))
   
   [tbounds_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀i. P0 (Bound i)) ∧ (∀n s. P1 s ⇒ P0 (Var n s)) ∧
          (∀n s l. (∀a. MEM a l ⇒ P0 a) ∧ P1 s ⇒ P0 (Fn n s l)) ∧
          (∀n tl. (∀a. MEM a tl ⇒ P0 a) ⇒ P1 (St n tl)) ⇒
          (∀v0. P0 v0) ∧ ∀v0. P1 v0
   
   [tbounds_tabs]  Theorem
      
      ⊢ (∀tm n s i.
           (n,s) ∈ tfv tm ∧ (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ sbounds s1 = ∅) ⇒
           tbounds (tabs (n,s) i tm) = {i} ∪ tbounds tm) ∧
        ∀st n s i.
          (n,s) ∈ sfv st ∧ (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ sbounds s1 = ∅) ⇒
          sbounds (sabs (n,s) i st) = {i} ∪ sbounds st
   
   [tbounds_tabs_SUBSET]  Theorem
      
      ⊢ (∀tm n s i.
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ sbounds s1 = ∅) ⇒
           tbounds tm ⊆ tbounds (tabs (n,s) i tm)) ∧
        ∀st n s i.
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ sbounds s1 = ∅) ⇒
          sbounds st ⊆ sbounds (sabs (n,s) i st)
   
   [tbounds_thm]  Theorem
      
      ⊢ tbounds (Bound i) = {i} ∧ tbounds (Var n s) = sbounds s ∧
        tbounds (Fn n s l) = BIGUNION {tbounds t | MEM t l} ∪ sbounds s ∧
        sbounds (St n tl) = BIGUNION {tbounds t | MEM t tl}
   
   [tbounds_tsubst]  Theorem
      
      ⊢ (∀tm n s i.
           (n,s) ∈ tfv tm ∧ (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ sbounds s1 = ∅) ⇒
           tbounds (tsubst (n,s) (Bound i) tm) = {i} ∪ tbounds tm) ∧
        ∀st n s i.
          (n,s) ∈ sfv st ∧ (∀n1 s1. (n1,s1) ∈ sfv st ⇒ sbounds s1 = ∅) ⇒
          sbounds (ssubst (n,s) (Bound i) st) = {i} ∪ sbounds st
   
   [tbounds_tsubst_SUBSET]  Theorem
      
      ⊢ (∀tm n s i.
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ sbounds s1 = ∅) ⇒
           tbounds tm ⊆ tbounds (tsubst (n,s) (Bound i) tm)) ∧
        ∀st n s i.
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ sbounds s1 = ∅) ⇒
          sbounds st ⊆ sbounds (ssubst (n,s) (Bound i) st)
   
   [term_11]  Theorem
      
      ⊢ (∀a0 a1 a0' a1'. Var a0 a1 = Var a0' a1' ⇔ a0 = a0' ∧ a1 = a1') ∧
        (∀a0 a1 a2 a0' a1' a2'.
           Fn a0 a1 a2 = Fn a0' a1' a2' ⇔ a0 = a0' ∧ a1 = a1' ∧ a2 = a2') ∧
        ∀a a'. Bound a = Bound a' ⇔ a = a'
   
   [term_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4 f5. ∃fn0 fn1 fn2.
          (∀a0 a1. fn0 (Var a0 a1) = f0 a0 a1 (fn1 a1)) ∧
          (∀a0 a1 a2. fn0 (Fn a0 a1 a2) = f1 a0 a1 a2 (fn1 a1) (fn2 a2)) ∧
          (∀a. fn0 (Bound a) = f2 a) ∧
          (∀a0 a1. fn1 (St a0 a1) = f3 a0 a1 (fn2 a1)) ∧ fn2 [] = f4 ∧
          ∀a0 a1. fn2 (a0::a1) = f5 a0 a1 (fn0 a0) (fn2 a1)
   
   [term_case_cong]  Theorem
      
      ⊢ ∀M M' f f1 f2.
          M = M' ∧ (∀a0 a1. M' = Var a0 a1 ⇒ f a0 a1 = f' a0 a1) ∧
          (∀a0 a1 a2. M' = Fn a0 a1 a2 ⇒ f1 a0 a1 a2 = f1' a0 a1 a2) ∧
          (∀a. M' = Bound a ⇒ f2 a = f2' a) ⇒
          term_CASE M f f1 f2 = term_CASE M' f' f1' f2'
   
   [term_case_eq]  Theorem
      
      ⊢ term_CASE x f f1 f2 = v ⇔
        (∃s0 s. x = Var s0 s ∧ f s0 s = v) ∨
        (∃s0 s l. x = Fn s0 s l ∧ f1 s0 s l = v) ∨
        ∃n. x = Bound n ∧ f2 n = v
   
   [term_distinct]  Theorem
      
      ⊢ (∀a2 a1' a1 a0' a0. Var a0 a1 ≠ Fn a0' a1' a2) ∧
        (∀a1 a0 a. Var a0 a1 ≠ Bound a) ∧
        ∀a2 a1 a0 a. Fn a0 a1 a2 ≠ Bound a
   
   [term_induction]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀s. P1 s ⇒ ∀s0. P0 (Var s0 s)) ∧
          (∀s l. P1 s ∧ P2 l ⇒ ∀s0. P0 (Fn s0 s l)) ∧ (∀n. P0 (Bound n)) ∧
          (∀l. P2 l ⇒ ∀s. P1 (St s l)) ∧ P2 [] ∧
          (∀t l. P0 t ∧ P2 l ⇒ P2 (t::l)) ⇒
          (∀t. P0 t) ∧ (∀s. P1 s) ∧ ∀l. P2 l
   
   [term_nchotomy]  Theorem
      
      ⊢ ∀tt.
          (∃s0 s. tt = Var s0 s) ∨ (∃s0 s l. tt = Fn s0 s l) ∨
          ∃n. tt = Bound n
   
   [term_size_eq]  Theorem
      
      ⊢ term1_size = list_size term_size
   
   [tfv_FINITE]  Theorem
      
      ⊢ (∀t. FINITE (tfv t)) ∧ ∀s. FINITE (sfv s)
   
   [tfv_def]  Theorem
      
      ⊢ (∀s n. tfv (Var n s) = {(n,s)} ∪ sfv s) ∧
        (∀tl s n.
           tfv (Fn n s tl) = BIGUNION (set (MAP (λa. tfv a) tl)) ∪ sfv s) ∧
        (∀v0. tfv (Bound v0) = ∅) ∧
        ∀tl n. sfv (St n tl) = BIGUNION (set (MAP (λa. tfv a) tl))
   
   [tfv_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀n s. P1 s ⇒ P0 (Var n s)) ∧
          (∀n s tl. (∀a. MEM a tl ⇒ P0 a) ∧ P1 s ⇒ P0 (Fn n s tl)) ∧
          (∀v0. P0 (Bound v0)) ∧
          (∀n tl. (∀a. MEM a tl ⇒ P0 a) ⇒ P1 (St n tl)) ⇒
          (∀v0. P0 v0) ∧ ∀v0. P1 v0
   
   [tfv_is_cont]  Theorem
      
      ⊢ (∀t. is_cont (tfv t)) ∧ ∀s. is_cont (sfv s)
   
   [tfv_sinst]  Theorem
      
      ⊢ (∀t σ.
           cstt σ ∧ tfv t ⊆ FDOM σ ∧ no_bound σ ⇒
           ∀n st.
             (n,st) ∈ tfv (tinst σ t) ⇔
             ∃n0 st0. (n0,st0) ∈ tfv t ∧ (n,st) ∈ tfv (σ ' (n0,st0))) ∧
        ∀s σ.
          cstt σ ∧ sfv s ⊆ FDOM σ ∧ no_bound σ ⇒
          ∀n st.
            (n,st) ∈ sfv (sinst σ s) ⇔
            ∃n0 st0. (n0,st0) ∈ sfv s ∧ (n,st) ∈ tfv (σ ' (n0,st0))
   
   [tfv_tabs]  Theorem
      
      ⊢ (∀tm n s.
           (∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (n,s) ∉ sfv s0) ∧ (n,s) ∈ tfv tm ⇒
           sfv s ∪ tfv (tabs (n,s) i tm) = tfv tm DELETE (n,s)) ∧
        ∀st n s.
          (∀n0 s0. (n0,s0) ∈ sfv st ⇒ (n,s) ∉ sfv s0) ∧ (n,s) ∈ sfv st ⇒
          sfv s ∪ sfv (sabs (n,s) i st) = sfv st DELETE (n,s)
   
   [tfv_tabs_SUBSET]  Theorem
      
      ⊢ (∀tm n s t.
           (∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (n,s) ∉ sfv s0) ⇒
           tfv (tabs (n,s) i tm) ⊆ tfv tm DELETE (n,s)) ∧
        ∀st n s t.
          (∀n0 s0. (n0,s0) ∈ sfv st ⇒ (n,s) ∉ sfv s0) ⇒
          sfv (sabs (n,s) i st) ⊆ sfv st DELETE (n,s)
   
   [tfv_thm]  Theorem
      
      ⊢ tfv (Var n s) = {(n,s)} ∪ sfv s ∧
        tfv (Fn n s tl) = BIGUNION {tfv t | MEM t tl} ∪ sfv s ∧
        tfv (Bound _0) = ∅ ∧ sfv (St n tl) = BIGUNION {tfv t | MEM t tl}
   
   [tfv_tinst_SUBSET_lemma]  Theorem
      
      ⊢ cstt σ ∧ no_bound σ ∧ (∀x. x ∈ FDOM σ ⇒ tfv (σ ' x) ⊆ s) ∧
        tfv t ⊆ FDOM σ ⇒
        tfv (tinst σ t) ⊆ s
   
   [tfv_tprpl]  Theorem
      
      ⊢ (∀tm bmap.
           (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅) ⇒
           tfv (tprpl bmap tm) =
           tfv tm ∪
           BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∩ tbounds tm}) ∧
        ∀st bmap.
          (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = ∅) ⇒
          sfv (sprpl bmap st) =
          sfv st ∪
          BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∩ sbounds st}
   
   [tfv_trpl]  Theorem
      
      ⊢ (∀t i new.
           i ∈ tbounds t ∧ (∀n0 s0. (n0,s0) ∈ tfv t ⇒ sbounds s0 = ∅) ⇒
           tfv (trpl i new t) = tfv new ∪ tfv t) ∧
        ∀s i new.
          i ∈ sbounds s ∧ (∀n0 s0. (n0,s0) ∈ sfv s ⇒ sbounds s0 = ∅) ⇒
          sfv (srpl i new s) = tfv new ∪ sfv s
   
   [tfv_trpl_SUBSET]  Theorem
      
      ⊢ (∀t i new.
           (∀n0 s0. (n0,s0) ∈ tfv t ⇒ sbounds s0 = ∅) ⇒
           tfv t ⊆ tfv (trpl i new t)) ∧
        ∀s i new.
          (∀n0 s0. (n0,s0) ∈ sfv s ⇒ sbounds s0 = ∅) ⇒
          sfv s ⊆ sfv (srpl i new s)
   
   [tfv_tshift]  Theorem
      
      ⊢ (∀t i. tfv (tshift i t) = tfv t) ∧ ∀s i. sfv (sshift i s) = sfv s
   
   [tfv_tsubst]  Theorem
      
      ⊢ (∀tm n s.
           (∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (n,s) ∉ sfv s0) ∧ (n,s) ∈ tfv tm ⇒
           sfv s ∪ tfv (tsubst (n,s) (Bound i) tm) = tfv tm DELETE (n,s)) ∧
        ∀st n s.
          (∀n0 s0. (n0,s0) ∈ sfv st ⇒ (n,s) ∉ sfv s0) ∧ (n,s) ∈ sfv st ⇒
          sfv s ∪ sfv (ssubst (n,s) (Bound i) st) = sfv st DELETE (n,s)
   
   [tfv_tsubst_SUBSET]  Theorem
      
      ⊢ (∀tm n s t.
           (∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (n,s) ∉ sfv s0) ⇒
           tfv (tsubst (n,s) t tm) ⊆ tfv tm DELETE (n,s) ∪ tfv t) ∧
        ∀st n s t.
          (∀n0 s0. (n0,s0) ∈ sfv st ⇒ (n,s) ∉ sfv s0) ⇒
          sfv (ssubst (n,s) t st) ⊆ sfv st DELETE (n,s) ∪ tfv t
   
   [tfv_tsubtm_closed]  Theorem
      
      ⊢ (∀tm n s t0. (n,s) ∈ tfv tm ∧ t0 ∈ ssubtm s ⇒ t0 ∈ tsubtm tm) ∧
        ∀st n s t0. (n,s) ∈ sfv st ∧ t0 ∈ ssubtm s ⇒ t0 ∈ ssubtm st
   
   [tinst_def]  Theorem
      
      ⊢ (∀σ s n.
           tinst σ (Var n s) =
           if (n,s) ∉ FDOM σ then Var n (sinst σ s) else σ ' (n,s)) ∧
        (∀σ tl s f.
           tinst σ (Fn f s tl) = Fn f (sinst σ s) (MAP (λa. tinst σ a) tl)) ∧
        (∀σ i. tinst σ (Bound i) = Bound i) ∧
        ∀σ tl n. sinst σ (St n tl) = St n (MAP (λa. tinst σ a) tl)
   
   [tinst_eq_cvmap]  Theorem
      
      ⊢ (∀tm.
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,sort_of t) ∉ sfv s1) ⇒
           tinst (TO_FMAP [((n,sort_of t),t)]) tm =
           tinst (cvmap (tfv tm) |+ ((n,sort_of t),t)) tm) ∧
        ∀st.
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,sort_of t) ∉ sfv s1) ⇒
          sinst (TO_FMAP [((n,sort_of t),t)]) st =
          sinst (cvmap (sfv st) |+ ((n,sort_of t),t)) st
   
   [tinst_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀σ n s. ((n,s) ∉ FDOM σ ⇒ P1 σ s) ⇒ P0 σ (Var n s)) ∧
          (∀σ f s tl. (∀a. MEM a tl ⇒ P0 σ a) ∧ P1 σ s ⇒ P0 σ (Fn f s tl)) ∧
          (∀σ i. P0 σ (Bound i)) ∧
          (∀σ n tl. (∀a. MEM a tl ⇒ P0 σ a) ⇒ P1 σ (St n tl)) ⇒
          (∀v0 v1. P0 v0 v1) ∧ ∀v0 v1. P1 v0 v1
   
   [tinst_subtm]  Theorem
      
      ⊢ (∀t σ n st.
           (n,st) ∈ FDOM σ ∩ tfv t ∧ cstt σ ∧ no_bound σ ⇒
           σ ' (n,st) ∈ tsubtm (tinst σ t)) ∧
        ∀s σ n st.
          (n,st) ∈ FDOM σ ∩ sfv s ∧ cstt σ ∧ no_bound σ ⇒
          σ ' (n,st) ∈ ssubtm (sinst σ s)
   
   [tinst_tabs]  Theorem
      
      ⊢ (∀tm i σ.
           cstt σ ∧ no_bound σ ∧ tfv tm DELETE (n,s) ⊆ FDOM σ ∧
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
           (∀n1 s1. (n1,s1) ∈ FDOM σ ⇒ (nn,sinst σ s) ∉ tfv (σ ' (n1,s1))) ∧
           (nn,sinst σ s) ∉ tfv tm ⇒
           tinst σ (tabs (n,s) i tm) =
           tabs (nn,sinst σ s) i
             (tinst (σ |+ ((n,s),Var nn (sinst σ s))) tm)) ∧
        ∀st i σ.
          cstt σ ∧ no_bound σ ∧ sfv st DELETE (n,s) ⊆ FDOM σ ∧
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
          (∀n1 s1. (n1,s1) ∈ FDOM σ ⇒ (nn,sinst σ s) ∉ tfv (σ ' (n1,s1))) ∧
          (nn,sinst σ s) ∉ sfv st ⇒
          sinst σ (sabs (n,s) i st) =
          sabs (nn,sinst σ s) i
            (sinst (σ |+ ((n,s),Var nn (sinst σ s))) st)
   
   [tinst_tsubst]  Theorem
      
      ⊢ (∀tm i σ.
           cstt σ ∧ no_bound σ ∧ tfv tm DELETE (n,s) ⊆ FDOM σ ∧
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
           (∀n1 s1. (n1,s1) ∈ FDOM σ ⇒ (nn,sinst σ s) ∉ tfv (σ ' (n1,s1))) ∧
           (nn,sinst σ s) ∉ tfv tm ⇒
           tinst σ (tsubst (n,s) (Bound i) tm) =
           tsubst (nn,sinst σ s) (Bound i)
             (tinst (σ |+ ((n,s),Var nn (sinst σ s))) tm)) ∧
        ∀st i σ.
          cstt σ ∧ no_bound σ ∧ sfv st DELETE (n,s) ⊆ FDOM σ ∧
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
          (∀n1 s1. (n1,s1) ∈ FDOM σ ⇒ (nn,sinst σ s) ∉ tfv (σ ' (n1,s1))) ∧
          (nn,sinst σ s) ∉ sfv st ⇒
          sinst σ (ssubst (n,s) (Bound i) st) =
          ssubst (nn,sinst σ s) (Bound i)
            (sinst (σ |+ ((n,s),Var nn (sinst σ s))) st)
   
   [tinst_vmap_id]  Theorem
      
      ⊢ (∀t σ.
           (∀n s. (n,s) ∈ FDOM σ ∩ tfv t ⇒ σ ' (n,s) = Var n s) ⇒
           tinst σ t = t) ∧
        ∀st σ.
          (∀n s. (n,s) ∈ FDOM σ ∩ sfv st ⇒ σ ' (n,s) = Var n s) ⇒
          sinst σ st = st
   
   [tlfv_is_cont]  Theorem
      
      ⊢ ∀l. is_cont (tlfv l)
   
   [tlmatch_EMPTY_TRANS_lemma]  Theorem
      
      ⊢ cstt σ1 ∧ cstt σ2 ∧ complete σ1 ∧ no_bound σ1 ∧ no_bound σ2 ∧
        (∀x. x ∈ FDOM σ1 ⇒ tfv (σ1 ' x) ⊆ FDOM σ2) ∧
        FDOM σ1 = BIGUNION {tfv t | MEM t farg} ⇒
        tlmatch ∅ farg (MAP (tinst σ2 ∘ tinst σ1) farg) FEMPTY =
        SOME (o_vmap σ2 σ1)
   
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
   
   [tlmatch_TRANS_o_vmap]  Theorem
      
      ⊢ tlmatch ∅ tl1 tl2 FEMPTY = SOME σ1 ∧
        tlmatch ∅ tl2 tl3 FEMPTY = SOME σ2 ⇒
        tlmatch ∅ tl1 tl3 FEMPTY = SOME (o_vmap σ2 σ1)
   
   [tlmatch_each]  Theorem
      
      ⊢ ∀tl1 tl2 f.
          complete f ∧ cstt f ∧ no_bound f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧
          LENGTH tl1 = LENGTH tl2 ⇒
          ∀σ. tlmatch ∅ tl1 tl2 f = SOME σ ⇔
              FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
              ∀n. n < LENGTH tl1 ⇒
                  tmatch ∅ (EL n tl1) (EL n tl2) f =
                  SOME (DRESTRICT σ (FDOM f ∪ tfv (EL n tl1)))
   
   [tlmatch_each_imp_tinst]  Theorem
      
      ⊢ ∀tl1 tl2 f.
          complete f ∧ cstt f ∧ no_bound f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧
          LENGTH tl1 = LENGTH tl2 ⇒
          ∀σ. tlmatch ∅ tl1 tl2 f = SOME σ ⇒
              FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
              ∀n. n < LENGTH tl1 ⇒ EL n tl2 = tinst σ (EL n tl1)
   
   [tlmatch_each_lemma]  Theorem
      
      ⊢ complete f ∧ cstt f ∧ no_bound f ∧ tmatch ∅ t1 t2 f = SOME σ ∧
        f ⊑ f1 ∧ complete f1 ∧ cstt f1 ∧ no_bound f1 ∧
        (∀x. x ∈ FDOM f1 ∧ x ∈ FDOM σ ⇒ f1 ' x = σ ' x) ⇒
        tmatch ∅ t1 t2 f1 = SOME (f1 ⊌ σ)
   
   [tlmatch_tinst_imp_SOME]  Theorem
      
      ⊢ ∀tl1 tl2 f.
          complete f ∧ cstt f ∧ no_bound f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧
          LENGTH tl1 = LENGTH tl2 ⇒
          ∀σ. f ⊑ σ ∧ cstt σ ∧ no_bound σ ∧
              FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
              (∀n. n < LENGTH tl1 ⇒ EL n tl2 = tinst σ (EL n tl1)) ⇒
              tlmatch ∅ tl1 tl2 f = SOME σ
   
   [tlmatch_tinst_imp_SOME']  Theorem
      
      ⊢ ∀tl1 tl2 f.
          complete f ∧ cstt f ∧ LENGTH tl1 = LENGTH tl2 ∧ no_bound f ⇒
          ∀σ. f ⊑ σ ∧ cstt σ ∧ no_bound σ ∧
              FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
              (∀n. n < LENGTH tl1 ⇒ EL n tl2 = tinst σ (EL n tl1)) ⇒
              tlmatch ∅ tl1 tl2 f = SOME σ
   
   [tm_induction2]  Theorem
      
      ⊢ ∀P. (∀s. (∀t. MEM t (stms s) ⇒ P t) ⇒ ∀s0. P (Var s0 s)) ∧
            (∀s l.
               (∀t. MEM t (stms s) ⇒ P t) ∧ (∀t. MEM t l ⇒ P t) ⇒
               ∀s0. P (Fn s0 s l)) ∧ (∀n. P (Bound n)) ⇒
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
      
      ⊢ ∀f. complete f ∧ cstt f ∧ no_bound f ⇒
            (tmatch ∅ t1 t2 f = SOME σ ⇔
             ∃σ0.
               no_bound σ0 ∧
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
      
      ⊢ cstt σ ∧ sfv s ⊆ tfv t ∧ tfv t ⊆ FDOM σ ∧ no_bound σ ⇒
        sfv (sinst σ s) ⊆ tfv (tinst σ t)
   
   [tmatch_def]  Theorem
      
      ⊢ (∀s n lcs f ct.
           tmatch lcs (Var n s) ct f =
           if tbounds ct ≠ ∅ then NONE
           else if (n,s) ∈ lcs then if Var n s = ct then SOME f else NONE
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
        (∀v8 v7 v6 v5 lcs f. tmatch lcs (Fn v5 v6 v7) (Bound v8) f = NONE) ∧
        (∀lcs j i f.
           tmatch lcs (Bound i) (Bound j) f =
           if i = j then SOME f else NONE) ∧
        (∀v9 v10 lcs i f. tmatch lcs (Bound i) (Var v9 v10) f = NONE) ∧
        (∀v13 v12 v11 lcs i f.
           tmatch lcs (Bound i) (Fn v11 v12 v13) f = NONE) ∧
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
             (¬(tbounds ct ≠ ∅) ∧ (n,s) ∉ lcs ∧ (n,s) ∉ FDOM f ⇒
              P1 lcs s (sort_of ct) f) ⇒
             P0 lcs (Var n s) ct f) ∧
          (∀lcs f1 s1 tl1 f2 s2 tl2 f.
             (∀σ0.
                f1 = f2 ∧ tlmatch lcs tl1 tl2 f = SOME σ0 ⇒ P1 lcs s1 s2 σ0) ∧
             (f1 = f2 ⇒ P2 lcs tl1 tl2 f) ⇒
             P0 lcs (Fn f1 s1 tl1) (Fn f2 s2 tl2) f) ∧
          (∀lcs v0 v1 v2 v3 v4 f. P0 lcs (Fn v0 v1 v2) (Var v3 v4) f) ∧
          (∀lcs v5 v6 v7 v8 f. P0 lcs (Fn v5 v6 v7) (Bound v8) f) ∧
          (∀lcs i j f. P0 lcs (Bound i) (Bound j) f) ∧
          (∀lcs i v9 v10 f. P0 lcs (Bound i) (Var v9 v10) f) ∧
          (∀lcs i v11 v12 v13 f. P0 lcs (Bound i) (Fn v11 v12 v13) f) ∧
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
   
   [tmatch_no_bound]  Theorem
      
      ⊢ (∀t1 t2 f σ. no_bound f ∧ tmatch ∅ t1 t2 f = SOME σ ⇒ no_bound σ) ∧
        (∀s1 s2 f σ. no_bound f ∧ smatch ∅ s1 s2 f = SOME σ ⇒ no_bound σ) ∧
        ∀tl1 tl2 f σ.
          no_bound f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒ no_bound σ
   
   [tprpl_FEMPTY]  Theorem
      
      ⊢ (∀t. tprpl FEMPTY t = t) ∧ ∀s. sprpl FEMPTY s = s
   
   [tprpl_FMAP_MAP_tabs]  Theorem
      
      ⊢ (∀tm i bmap.
           (n,s) ∉ tfv tm ⇒
           tprpl (FMAP_MAP (tabs (n,s) i) bmap) tm =
           tabs (n,s) i (tprpl bmap tm)) ∧
        ∀st i bmap.
          (n,s) ∉ sfv st ⇒
          sprpl (FMAP_MAP (tabs (n,s) i) bmap) st =
          sabs (n,s) i (sprpl bmap st)
   
   [tprpl_def]  Theorem
      
      ⊢ (∀s n bmap. tprpl bmap (Var n s) = Var n s) ∧
        (∀tl s f bmap.
           tprpl bmap (Fn f s tl) =
           Fn f (sprpl bmap s) (MAP (λa. tprpl bmap a) tl)) ∧
        (∀i bmap.
           tprpl bmap (Bound i) =
           if i ∈ FDOM bmap then bmap ' i else Bound i) ∧
        ∀tl n bmap. sprpl bmap (St n tl) = St n (MAP (λa. tprpl bmap a) tl)
   
   [tprpl_id]  Theorem
      
      ⊢ (∀t bmap. tbounds t ∩ FDOM bmap = ∅ ⇒ tprpl bmap t = t) ∧
        ∀s bmap. sbounds s ∩ FDOM bmap = ∅ ⇒ sprpl bmap s = s
   
   [tprpl_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀bmap n s. P0 bmap (Var n s)) ∧
          (∀bmap f s tl.
             (∀a. MEM a tl ⇒ P0 bmap a) ∧ P1 bmap s ⇒ P0 bmap (Fn f s tl)) ∧
          (∀bmap i. P0 bmap (Bound i)) ∧
          (∀bmap n tl. (∀a. MEM a tl ⇒ P0 bmap a) ⇒ P1 bmap (St n tl)) ⇒
          (∀v0 v1. P0 v0 v1) ∧ ∀v0 v1. P1 v0 v1
   
   [tprpl_mk_bmap_CONS]  Theorem
      
      ⊢ (∀t tm tl.
           tbounds tm = ∅ ⇒
           tprpl (mk_bmap (REVERSE tl ⧺ [tm])) t =
           tprpl (mk_bmap (REVERSE tl)) (trpl (LENGTH tl) tm t)) ∧
        ∀s tm tl.
          tbounds tm = ∅ ⇒
          sprpl (mk_bmap (REVERSE tl ⧺ [tm])) s =
          sprpl (mk_bmap (REVERSE tl)) (srpl (LENGTH tl) tm s)
   
   [tpsubtm_size_LESS]  Theorem
      
      ⊢ ∀t t0. t0 ∈ tpsubtm t ⇒ term_size t0 < term_size t
   
   [trpl_def]  Theorem
      
      ⊢ (∀new j i. trpl i new (Bound j) = if i = j then new else Bound j) ∧
        (∀s new n i. trpl i new (Var n s) = Var n s) ∧
        (∀tl s new i f.
           trpl i new (Fn f s tl) =
           Fn f (srpl i new s) (MAP (λa. trpl i new a) tl)) ∧
        ∀tl new n i.
          srpl i new (St n tl) = St n (MAP (λa. trpl i new a) tl)
   
   [trpl_eliminate]  Theorem
      
      ⊢ (∀tm i new.
           (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅) ∧ tbounds new = ∅ ⇒
           tbounds (trpl i new tm) = tbounds tm DELETE i) ∧
        ∀st i new.
          (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = ∅) ∧ tbounds new = ∅ ⇒
          sbounds (srpl i new st) = sbounds st DELETE i
   
   [trpl_eliminate0]  Theorem
      
      ⊢ (∀tm i new.
           (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅) ∧ Bound i ∉ tsubtm new ⇒
           Bound i ∉ tsubtm (trpl i new tm)) ∧
        ∀st i new.
          (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = ∅) ∧ Bound i ∉ tsubtm new ⇒
          Bound i ∉ ssubtm (srpl i new st)
   
   [trpl_id]  Theorem
      
      ⊢ (∀t i new. i ∉ tbounds t ⇒ trpl i new t = t) ∧
        ∀st i new. i ∉ sbounds st ⇒ srpl i new st = st
   
   [trpl_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀i new j. P0 i new (Bound j)) ∧
          (∀i new n s. P0 i new (Var n s)) ∧
          (∀i new f s tl.
             (∀a. MEM a tl ⇒ P0 i new a) ∧ P1 i new s ⇒
             P0 i new (Fn f s tl)) ∧
          (∀i new n tl. (∀a. MEM a tl ⇒ P0 i new a) ⇒ P1 i new (St n tl)) ⇒
          (∀v0 v1 v2. P0 v0 v1 v2) ∧ ∀v0 v1 v2. P1 v0 v1 v2
   
   [trpl_tabs]  Theorem
      
      ⊢ (∀tm i new n s.
           i ∉ tbounds tm ∧ (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
           (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅) ⇒
           trpl i new (tabs (n,s) i tm) = tsubst (n,s) new tm) ∧
        ∀st i new n s.
          i ∉ sbounds st ∧ (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
          (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = ∅) ⇒
          srpl i new (sabs (n,s) i st) = ssubst (n,s) new st
   
   [tshift_0]  Theorem
      
      ⊢ (∀t. tshift 0 t = t) ∧ ∀s. sshift 0 s = s
   
   [tshift_SUM]  Theorem
      
      ⊢ (∀t. tshift a (tshift b t) = tshift (a + b) t) ∧
        ∀s. sshift a (sshift b s) = sshift (a + b) s
   
   [tshift_def]  Theorem
      
      ⊢ (∀j i. tshift i (Bound j) = Bound (j + i)) ∧
        (∀s n i. tshift i (Var n s) = Var n s) ∧
        (∀s l i f.
           tshift i (Fn f s l) = Fn f (sshift i s) (MAP (λa. tshift i a) l)) ∧
        ∀n l i. sshift i (St n l) = St n (MAP (λa. tshift i a) l)
   
   [tshift_id]  Theorem
      
      ⊢ (∀tm n. tbounds tm = ∅ ⇒ tshift n tm = tm) ∧
        ∀st n. sbounds st = ∅ ⇒ sshift n st = st
   
   [tshift_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀i j. P0 i (Bound j)) ∧ (∀i n s. P0 i (Var n s)) ∧
          (∀i f s l. (∀a. MEM a l ⇒ P0 i a) ∧ P1 i s ⇒ P0 i (Fn f s l)) ∧
          (∀i n l. (∀a. MEM a l ⇒ P0 i a) ⇒ P1 i (St n l)) ⇒
          (∀v0 v1. P0 v0 v1) ∧ ∀v0 v1. P1 v0 v1
   
   [tshift_tabs]  Theorem
      
      ⊢ (∀tm m i.
           tshift m (tabs (n,s) i tm) = tabs (n,s) (i + m) (tshift m tm)) ∧
        ∀st m i.
          sshift m (sabs (n,s) i st) = sabs (n,s) (i + m) (sshift m st)
   
   [tsstt_back]  Theorem
      
      ⊢ (∀t t1 t2.
           t1 ∈ tsubtm t ∧ t2 ∉ tsubtm t ⇒ tsstt t2 t1 (tsstt t1 t2 t) = t) ∧
        ∀s t1 t2.
          t1 ∈ ssubtm s ∧ t2 ∉ ssubtm s ⇒ ssstt t2 t1 (ssstt t1 t2 s) = s
   
   [tsstt_def]  Theorem
      
      ⊢ (∀old new i.
           tsstt old new (Bound i) = if Bound i = old then new else Bound i) ∧
        (∀s old new n.
           tsstt old new (Var n s) =
           if Var n s = old then new else Var n (ssstt old new s)) ∧
        (∀tl st old new f.
           tsstt old new (Fn f st tl) =
           if Fn f st tl = old then new
           else Fn f (ssstt old new st) (MAP (λa. tsstt old new a) tl)) ∧
        ∀tl old new n.
          ssstt old new (St n tl) = St n (MAP (λa. tsstt old new a) tl)
   
   [tsstt_fix]  Theorem
      
      ⊢ ∀t1 t2. tsstt t1 t2 t1 = t2
   
   [tsstt_id]  Theorem
      
      ⊢ (∀t t1 t2. t1 ∉ tsubtm t ⇒ tsstt t1 t2 t = t) ∧
        ∀s t1 t2. t1 ∉ ssubtm s ⇒ ssstt t1 t2 s = s
   
   [tsstt_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀old new i. P0 old new (Bound i)) ∧
          (∀old new n s.
             (Var n s ≠ old ⇒ P1 old new s) ⇒ P0 old new (Var n s)) ∧
          (∀old new f st tl.
             (∀a. Fn f st tl ≠ old ∧ MEM a tl ⇒ P0 old new a) ∧
             (Fn f st tl ≠ old ⇒ P1 old new st) ⇒
             P0 old new (Fn f st tl)) ∧
          (∀old new n tl.
             (∀a. MEM a tl ⇒ P0 old new a) ⇒ P1 old new (St n tl)) ⇒
          (∀v0 v1 v2. P0 v0 v1 v2) ∧ ∀v0 v1 v2. P1 v0 v1 v2
   
   [tsstt_itself]  Theorem
      
      ⊢ (∀t t0. tsstt t0 t0 t = t) ∧ ∀s t0. ssstt t0 t0 s = s
   
   [tsstt_tsstt]  Theorem
      
      ⊢ (∀t t1 t2 t3.
           t1 ∈ tsubtm t ∧ t2 ∉ tsubtm t ⇒
           tsstt t2 t3 (tsstt t1 t2 t) = tsstt t1 t3 t) ∧
        ∀s t1 t2 t3.
          t1 ∈ ssubtm s ∧ t2 ∉ ssubtm s ⇒
          ssstt t2 t3 (ssstt t1 t2 s) = ssstt t1 t3 s
   
   [tsstt_tsstt1]  Theorem
      
      ⊢ (∀t t1 t2 t3.
           t2 ∉ tsubtm t ⇒ tsstt t2 t3 (tsstt t1 t2 t) = tsstt t1 t3 t) ∧
        ∀s t1 t2 t3.
          t2 ∉ ssubtm s ⇒ ssstt t2 t3 (ssstt t1 t2 s) = ssstt t1 t3 s
   
   [tsstt_tsubtm]  Theorem
      
      ⊢ (∀t t1 t2. t1 ∈ tsubtm t ⇒ t2 ∈ tsubtm (tsstt t1 t2 t)) ∧
        ∀s t1 t2. t1 ∈ ssubtm s ⇒ t2 ∈ ssubtm (ssstt t1 t2 s)
   
   [tsubst_def]  Theorem
      
      ⊢ (∀t st s n m.
           tsubst (m,s) t (Var n st) =
           if m = n ∧ s = st then t else Var n (ssubst (m,s) t st)) ∧
        (∀tl t st s m f.
           tsubst (m,s) t (Fn f st tl) =
           Fn f (ssubst (m,s) t st) (MAP (λa. tsubst (m,s) t a) tl)) ∧
        (∀t s m i. tsubst (m,s) t (Bound i) = Bound i) ∧
        ∀tl t s n m.
          ssubst (m,s) t (St n tl) = St n (MAP (λa. tsubst (m,s) t a) tl)
   
   [tsubst_eq_tinst]  Theorem
      
      ⊢ (∀t n s new. tsubst (n,s) new t = tinst (TO_FMAP [((n,s),new)]) t) ∧
        ∀st n s new. ssubst (n,s) new st = sinst (TO_FMAP [((n,s),new)]) st
   
   [tsubst_eq_tinst1]  Theorem
      
      ⊢ (∀n s new. tsubst (n,s) new = tinst (TO_FMAP [((n,s),new)])) ∧
        ∀n s new. ssubst (n,s) new = sinst (TO_FMAP [((n,s),new)])
   
   [tsubst_id]  Theorem
      
      ⊢ (∀t. (n,s) ∉ tfv t ⇒ tsubst (n,s) t1 t = t) ∧
        ∀st. (n,s) ∉ sfv st ⇒ ssubst (n,s) t1 st = st
   
   [tsubst_id']  Theorem
      
      ⊢ (n,s) ≠ (n1,s1) ∧ (n,s) ∉ sfv s1 ⇒
        tsubst (n,s) (Bound i) (Var n1 s1) = Var n1 s1
   
   [tsubst_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀m s t n st.
             (¬(m = n ∧ s = st) ⇒ P1 (m,s) t st) ⇒ P0 (m,s) t (Var n st)) ∧
          (∀m s t f st tl.
             (∀a. MEM a tl ⇒ P0 (m,s) t a) ∧ P1 (m,s) t st ⇒
             P0 (m,s) t (Fn f st tl)) ∧ (∀m s t i. P0 (m,s) t (Bound i)) ∧
          (∀m s t n tl.
             (∀a. MEM a tl ⇒ P0 (m,s) t a) ⇒ P1 (m,s) t (St n tl)) ⇒
          (∀v0 v1 v2. P0 v0 v1 v2) ∧ ∀v0 v1 v2. P1 v0 v1 v2
   
   [tsubst_tbounds_in]  Theorem
      
      ⊢ (∀tm n s i.
           (n,s) ∈ tfv tm ⇒ i ∈ tbounds (tsubst (n,s) (Bound i) tm)) ∧
        ∀st n s i. (n,s) ∈ sfv st ⇒ i ∈ sbounds (ssubst (n,s) (Bound i) st)
   
   [tsubst_tinst]  Theorem
      
      ⊢ ∀e an ast σ nn.
          tfv e ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧ (an,ast) ∉ FDOM σ ∧
          (∀x s. x ∈ tfv e ∪ sfv ast ∧ x ≠ (an,ast) ⇒ (nn,s) ∉ tfv (σ ' x)) ∧
          (∀n1 s1. (n1,s1) ∈ tfv e ⇒ (an,ast) ∉ sfv s1) ⇒
          tsubst (nn,sinst σ ast) (Bound i)
            (tinst (σ |+ ((an,ast),Var nn (sinst σ ast))) e) =
          tinst σ (tsubst (an,ast) (Bound i) e)
   
   [tsubst_tsstt]  Theorem
      
      ⊢ (∀tm n s new. tsubst (n,s) new tm = tsstt (Var n s) new tm) ∧
        ∀st n s new. ssubst (n,s) new st = ssstt (Var n s) new st
   
   [tsubtm_REFL]  Theorem
      
      ⊢ ∀t. t ∈ tsubtm t
   
   [tsubtm_def]  Theorem
      
      ⊢ (∀s n. tsubtm (Var n s) = Var n s INSERT ssubtm s) ∧
        (∀s l f.
           tsubtm (Fn f s l) =
           Fn f s l INSERT ssubtm s ∪ BIGUNION (set (MAP (λa. tsubtm a) l))) ∧
        (∀i. tsubtm (Bound i) = {Bound i}) ∧
        ∀n l. ssubtm (St n l) = BIGUNION (set (MAP (λa. tsubtm a) l))
   
   [tsubtm_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀n s. P1 s ⇒ P0 (Var n s)) ∧
          (∀f s l. (∀a. MEM a l ⇒ P0 a) ∧ P1 s ⇒ P0 (Fn f s l)) ∧
          (∀i. P0 (Bound i)) ∧ (∀n l. (∀a. MEM a l ⇒ P0 a) ⇒ P1 (St n l)) ⇒
          (∀v0. P0 v0) ∧ ∀v0. P1 v0
   
   [update_inst_lemma]  Theorem
      
      ⊢ v ∉ sfv s ∧ v ∉ FDOM σ ⇒ sinst σ s = sinst (σ |+ (v,t)) s
   
   [variant_NOT_fIN]  Theorem
      
      ⊢ ∀ns n. ¬fIN (variant ns n) ns
   
   [variant_def]  Theorem
      
      ⊢ ∀ns n.
          variant ns n = if fIN n ns then variant ns (STRCAT n "'") else n
   
   [variant_ind]  Theorem
      
      ⊢ ∀P. (∀ns n. (fIN n ns ⇒ P ns (STRCAT n "'")) ⇒ P ns n) ⇒
            ∀v v1. P v v1
   
   [variant_var_NOTIN]  Theorem
      
      ⊢ ∀vs n s. FINITE vs ⇒ (variant (fromSet (IMAGE FST vs)) n,s) ∉ vs
   
   [vmap_fix_FEMPTY]  Theorem
      
      ⊢ vmap_fix FEMPTY vs
   
   [vsort_tfv_closed]  Theorem
      
      ⊢ (∀h n s v. (n,s) ∈ tfv h ∧ v ∈ sfv s ⇒ v ∈ tfv h) ∧
        ∀st n s v. (n,s) ∈ sfv st ∧ v ∈ sfv s ⇒ v ∈ sfv st
   
   [wfabsap_LENGTH]  Theorem
      
      ⊢ ∀tl sl. wfabsap Σf sl tl ⇒ LENGTH sl = LENGTH tl
   
   [wfabsap_def]  Theorem
      
      ⊢ (∀Σf. wfabsap Σf [] [] ⇔ T) ∧
        (∀Σf tl t sl s.
           wfabsap Σf (s::sl) (t::tl) ⇔
           (∀n0 s0 st. MEM st sl ∧ (n0,s0) ∈ sfv st ⇒ sbounds s0 = ∅) ∧
           wft Σf t ∧ s = sort_of t ∧ wfs Σf s ∧
           wfabsap Σf (specsl 0 t sl) tl) ∧
        (∀Σf sl s. wfabsap Σf (s::sl) [] ⇔ F) ∧
        ∀Σf tl t. wfabsap Σf [] (t::tl) ⇔ F
   
   [wfabsap_ind]  Theorem
      
      ⊢ ∀P. (∀Σf. P Σf [] []) ∧
            (∀Σf s sl t tl. P Σf (specsl 0 t sl) tl ⇒ P Σf (s::sl) (t::tl)) ∧
            (∀Σf s sl. P Σf (s::sl) []) ∧ (∀Σf t tl. P Σf [] (t::tl)) ⇒
            ∀v v1 v2. P v v1 v2
   
   [wfabsap_ok_abs]  Theorem
      
      ⊢ ∀tl sl. wfabsap Σf sl tl ⇒ ok_abs sl
   
   [wfabsap_sfv_SUBSET]  Theorem
      
      ⊢ ∀tl sl.
          wfabsap Σf sl tl ⇒
          BIGUNION {sfv s | MEM s sl} ⊆ BIGUNION {tfv t | MEM t tl}
   
   [wfabsap_sfv_sbounds]  Theorem
      
      ⊢ wfabsap Σf sl tl ⇒
        ∀n0 s0 st. MEM st sl ∧ (n0,s0) ∈ sfv st ⇒ sbounds s0 = ∅
   
   [wfabsap_sinst_tinst]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {{(n,s)} ∪ sfv s | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀tl sl.
          cstt σ ∧ BIGUNION {tfv t | MEM t tl} ⊆ FDOM σ ∧ wfcod Σf σ ∧
          wfabsap Σf sl tl ⇒
          wfabsap Σf (MAP (sinst σ) sl) (MAP (tinst σ) tl)
   
   [wfabsap_slbounds]  Theorem
      
      ⊢ ∀tl sl. wfabsap Σf sl tl ⇒ slbounds sl = ∅
   
   [wfabsap_wfs]  Theorem
      
      ⊢ ∀tl sl.
          wfabsap Σf sl tl ⇒ ∀st n s. MEM st sl ∧ (n,s) ∈ sfv st ⇒ wfs Σf s
   
   [wfabsap_wft]  Theorem
      
      ⊢ ∀tl sl t. wfabsap Σf sl tl ∧ MEM t tl ⇒ wft Σf t
   
   [wfcod_no_bound]  Theorem
      
      ⊢ wfcod Σf σ ⇒ no_bound σ
   
   [wfcod_no_bound0]  Theorem
      
      ⊢ wfcod Σf σ ⇒ ∀x. x ∈ FDOM σ ⇒ tbounds (σ ' x) = ∅
   
   [wft_def]  Theorem
      
      ⊢ (∀Σf s n. wft Σf (Var n s) ⇔ wfs Σf s) ∧
        (∀Σf tl s f.
           wft Σf (Fn f s tl) ⇔
           wfs Σf s ∧ (∀t. MEM t tl ⇒ wft Σf t) ∧ isfsym Σf f ∧
           IS_SOME (tlmatch ∅ (MAP Var' (fsymin Σf f)) tl FEMPTY) ∧
           sinst (THE (tlmatch ∅ (MAP Var' (fsymin Σf f)) tl FEMPTY))
             (fsymout Σf f) =
           s) ∧ (∀Σf i. wft Σf (Bound i) ⇔ F) ∧
        ∀Σf tl n. wfs Σf (St n tl) ⇔ EVERY (λa. wft Σf a) tl
   
   [wft_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀Σf n s. P1 Σf s ⇒ P0 Σf (Var n s)) ∧
          (∀Σf f s tl.
             (∀t. MEM t tl ⇒ P0 Σf t) ∧ P1 Σf s ⇒ P0 Σf (Fn f s tl)) ∧
          (∀Σf i. P0 Σf (Bound i)) ∧
          (∀Σf n tl. (∀a. MEM a tl ⇒ P0 Σf a) ⇒ P1 Σf (St n tl)) ⇒
          (∀v0 v1. P0 v0 v1) ∧ ∀v0 v1. P1 v0 v1
   
   [wft_no_bound]  Theorem
      
      ⊢ (∀t. wft Σf t ⇒ tbounds t = ∅) ∧ ∀s. wfs Σf s ⇒ sbounds s = ∅
   
   [wft_tbounds]  Theorem
      
      ⊢ (∀t. wft Σf t ⇒ tbounds t = ∅) ∧ ∀s. wfs Σf s ⇒ sbounds s = ∅
   
   [wft_tinst]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        (∀t. wft Σf t ⇒
             ∀σ. cstt σ ∧ wfcod Σf σ ∧ tfv t ⊆ FDOM σ ⇒ wft Σf (tinst σ t)) ∧
        ∀s. wfs Σf s ⇒
            ∀σ. cstt σ ∧ wfcod Σf σ ∧ sfv s ⊆ FDOM σ ⇒ wfs Σf (sinst σ s)
   
   [wft_tsubtm]  Theorem
      
      ⊢ (∀tm. wft Σf tm ⇒ ∀t0. t0 ∈ tsubtm tm ⇒ wft Σf t0) ∧
        ∀st. wfs Σf st ⇒ ∀t0. t0 ∈ ssubtm st ⇒ wft Σf t0
   
   [wft_wfs]  Theorem
      
      ⊢ (∀tm. wft Σf tm ⇒ ∀n s. (n,s) ∈ tfv tm ⇒ wfs Σf s) ∧
        ∀st. wfs Σf st ⇒ ∀n s. (n,s) ∈ sfv st ⇒ wfs Σf s
   
   [wfvmap_cont_DRESTRICT]  Theorem
      
      ⊢ cstt σ ∧ complete σ ∧ is_cont s ⇒ cstt (DRESTRICT σ s)
   
   
*)
end
