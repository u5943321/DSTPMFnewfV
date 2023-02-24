signature fsytxTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val EQ_def : thm
    val FALLL_def : thm
    val Uof_def : thm
    val abst_def : thm
    val dest_eq_def_primitive : thm
    val fVars_def : thm
    val fVinst_def : thm
    val fVslfv_def : thm
    val fabs_def : thm
    val fabsl_def : thm
    val fbounds_def : thm
    val ffv_def : thm
    val finst_def : thm
    val form_TY_DEF : thm
    val form_case_def : thm
    val form_size_def : thm
    val fprpl_def : thm
    val frename_def : thm
    val frpl_def : thm
    val gcont_def : thm
    val has_eq : thm
    val inst_eff_def : thm
    val is_EQ_def : thm
    val ispsym_def : thm
    val mk_FALL_def : thm
    val ofFMAP_def : thm
    val plainfV_def : thm
    val presname_def : thm
    val psymin_def : thm
    val rnmap_def : thm
    val slfv_def : thm
    val sname_def : thm
    val srename_def : thm
    val substb_def : thm
    val trename_def : thm
    val tsname_def : thm
    val v2twbmap_def : thm
    val vinst_fVar_def : thm
    val vl2sl0_def : thm
    val vl2sl_def : thm
    val vsname_def : thm
    val wffVmap_def : thm
    val wff_def : thm
    val wfsig_def : thm
  
  (*  Theorems  *)
    val BIGUNION_IMAGE_sbounds_ffv : thm
    val BIGUNION_IMAGE_sbounds_tfv : thm
    val BIGUNION_is_cont : thm
    val EL_specslwtl : thm
    val FAPPLY_rnmap : thm
    val FAPPLY_rnmap_SUBSET : thm
    val FAPPLY_v2twbmap : thm
    val FDOM_rnmap : thm
    val FDOM_v2twbmap : thm
    val FINITE_BIGUNION_tfv : thm
    val FINITE_lemma : thm
    val IN_fVslfv : thm
    val IN_slfv : thm
    val IN_tfv_trename : thm
    val LENGTH_specslwtl : thm
    val MEM_fVsl_SUBSET_fVslfv : thm
    val NOTIN_fVslfv : thm
    val NOTIN_frename : thm
    val NOTIN_trename : thm
    val TO_FMAP_SING : thm
    val Uof_EMPTY : thm
    val Uof_INSERT : thm
    val Uof_SUBSET : thm
    val Uof_SUBSET_MONO : thm
    val Uof_Sing : thm
    val Uof_UNION : thm
    val abssl_MAP_srename : thm
    val absvl_def : thm
    val absvl_ind : thm
    val cstt_EXT : thm
    val cstt_rnmap : thm
    val datatype_form : thm
    val dest_eq_def : thm
    val dest_eq_ind : thm
    val fVars_finst : thm
    val fVslfv_SUBSET_ffv : thm
    val fVslfv_alt : thm
    val fabs_fbounds_in : thm
    val fabs_frename : thm
    val fabs_frpl : thm
    val fabs_id : thm
    val fbounds_fabs : thm
    val fbounds_fabs_SUBSET : thm
    val fbounds_fabs_fVslfv : thm
    val fbounds_thm : thm
    val ffv_EQ : thm
    val ffv_FALLL : thm
    val ffv_FINITE : thm
    val ffv_fabs : thm
    val ffv_fabs_SUBSET : thm
    val ffv_fabs_fVslfv : thm
    val ffv_finst : thm
    val ffv_fprpl : thm
    val ffv_frename : thm
    val ffv_is_cont : thm
    val ffv_mk_FALL : thm
    val ffv_mk_FALL_fVslfv : thm
    val ffv_thm : thm
    val finst_EQ : thm
    val finst_TO_FMAP_id : thm
    val finst_eq_cvmap : thm
    val finst_fabs : thm
    val finst_vmap_id : thm
    val fmap_ffv_finst_eq : thm
    val fmap_ffv_finst_eq1 : thm
    val form_11 : thm
    val form_Axiom : thm
    val form_case_cong : thm
    val form_case_eq : thm
    val form_distinct : thm
    val form_induction : thm
    val form_nchotomy : thm
    val fprpl_FEMPTY : thm
    val fprpl_FMAP_MAP_fabs_IN : thm
    val fprpl_mk_bmap_CONS : thm
    val fprpl_mk_bmap_abs : thm
    val frename_FALLL : thm
    val frename_alt : thm
    val frename_eq : thm
    val frename_finst : thm
    val frename_finst_ffv : thm
    val frename_fix : thm
    val frename_fprpl : thm
    val fresh_name_ex : thm
    val frpl_FALLL : thm
    val frpl_fabs : thm
    val gcont_EMPTY : thm
    val gcont_FINITE : thm
    val gcont_SING : thm
    val gcont_UNION : thm
    val gcont_is_cont : thm
    val gcont_of_cont : thm
    val ill_formed_fabs_still_in : thm
    val inst_eff_tinst : thm
    val mk_FALLL_def : thm
    val mk_FALLL_ind : thm
    val mk_FALL_rename_eq : thm
    val mk_bmap_NIL : thm
    val no_subrename : thm
    val ok_abs_rename : thm
    val presname_DRESTRICT : thm
    val presname_FUPDATE : thm
    val presname_cvmap : thm
    val presname_rnmap : thm
    val sfv_ffv : thm
    val shift_bmap_0_I : thm
    val shift_bmap_SING : thm
    val slprpl_FMAP_MAP_abssl_IN : thm
    val slprpl_mk_bmap_CONS : thm
    val slprpl_trename : thm
    val specslwtl : thm
    val specslwtl_ind : thm
    val tabs_trename : thm
    val tbounds_trename : thm
    val tfv_tprpl_SUBSET : thm
    val tfv_trename : thm
    val tfv_trpl_SUBSET1 : thm
    val tinst_cvmap_UPDATE : thm
    val tprpl_FMAP_MAP_tabs_IN : thm
    val tprpl_FUNION : thm
    val tprpl_mk_bmap_CONS : thm
    val tprpl_wvar : thm
    val trename_alt : thm
    val trename_back : thm
    val trename_fix : thm
    val trename_shift_bmap : thm
    val trename_tinst : thm
    val trename_tinst_tfv : thm
    val trename_tprpl : thm
    val trename_tshift : thm
    val trpl_tprpl : thm
    val tsname_tinst : thm
    val tsname_trename : thm
    val wfabsap0_def : thm
    val wfabsap0_ind : thm
    val wfabsap0_specslwtl : thm
    val wfabsap0_wft : thm
    val wfabsap_wfabsap0 : thm
    val wfcod_rnmap_BIGUNION : thm
    val wfcod_rnmap_SUBSET : thm
    val wfcod_rnmap_cont : thm
    val wfcod_rnmap_ffv : thm
    val wfcod_rnmap_gcont : thm
    val wfcod_rnmap_tfv : thm
    val wff_EQ : thm
    val wff_FALL : thm
    val wff_FALLL_ffv_SUBSET : thm
    val wff_FALLL_no_vbound : thm
    val wff_False : thm
    val wff_IMP : thm
    val wff_Pred : thm
    val wff_cases : thm
    val wff_fVar : thm
    val wff_fVar_subst_lemma : thm
    val wff_fbounds : thm
    val wff_finst : thm
    val wff_frename : thm
    val wff_ind : thm
    val wff_no_vbound : thm
    val wff_rules : thm
    val wff_spec : thm
    val wff_strongind : thm
    val wff_wfcod_cvmap_ffv : thm
    val wff_wfs : thm
    val wft_no_vbound : thm
    val wft_not_bound : thm
    val wft_trename : thm
    val wft_trename0 : thm
  
  val fsytx_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [tmsytx] Parent theory of "fsytx"
   
   [EQ_def]  Definition
      
      ⊢ ∀t1 t2. EQ t1 t2 = Pred "=" [t1; t2]
   
   [FALLL_def]  Definition
      
      ⊢ (∀ϕ. FALLL [] ϕ = ϕ) ∧ ∀h t ϕ. FALLL (h::t) ϕ = FALL h (FALLL t ϕ)
   
   [Uof_def]  Definition
      
      ⊢ ∀f s. Uof f s = BIGUNION {f e | e ∈ s}
   
   [abst_def]  Definition
      
      ⊢ ∀v. abst v = fabs v 0
   
   [dest_eq_def_primitive]  Definition
      
      ⊢ dest_eq =
        WFREC (@R. WF R)
          (λdest_eq a.
               case a of
                 False => ARB
               | Pred "" v1 => ARB
               | Pred "=" [] => ARB
               | Pred "=" [t1] => ARB
               | Pred "=" [t1; t2] => I (t1,t2)
               | Pred "=" (t1::t2::v31::v32) => ARB
               | Pred (STRING #"=" (STRING v22 v23)) v1 => ARB
               | Pred (STRING v19 v17) v1 => ARB
               | IMP v2 v3 => ARB
               | FALL v6 v7 => ARB
               | fVar v10 v11 v12 => ARB)
   
   [fVars_def]  Definition
      
      ⊢ (∀v0 v1. fVars (Pred v0 v1) = ∅) ∧
        (∀f1 f2. fVars (IMP f1 f2) = fVars f1 ∪ fVars f2) ∧
        (∀s b. fVars (FALL s b) = fVars b) ∧ fVars False = ∅ ∧
        ∀P sl tl. fVars (fVar P sl tl) = {(P,sl)}
   
   [fVinst_def]  Definition
      
      ⊢ (∀fσ. fVinst fσ False = False) ∧
        (∀fσ p tl. fVinst fσ (Pred p tl) = Pred p tl) ∧
        (∀fσ f1 f2.
           fVinst fσ (IMP f1 f2) = IMP (fVinst fσ f1) (fVinst fσ f2)) ∧
        (∀fσ s ϕ. fVinst fσ (FALL s ϕ) = FALL s (fVinst fσ ϕ)) ∧
        ∀fσ P sl tl.
          fVinst fσ (fVar P sl tl) =
          if (P,sl) ∈ FDOM fσ then
            fprpl (mk_bmap (REVERSE tl)) (fσ ' (P,sl))
          else fVar P sl tl
   
   [fVslfv_def]  Definition
      
      ⊢ ∀f. fVslfv f = Uof (slfv ∘ SND) (fVars f)
   
   [fabs_def]  Definition
      
      ⊢ (∀v0 v1. fabs v0 v1 False = False) ∧
        (∀v i p tl. fabs v i (Pred p tl) = Pred p (MAP (tabs v i) tl)) ∧
        (∀v i p vl tl.
           fabs v i (fVar p vl tl) = fVar p vl (MAP (tabs v i) tl)) ∧
        (∀v i f1 f2. fabs v i (IMP f1 f2) = IMP (fabs v i f1) (fabs v i f2)) ∧
        ∀v i s b.
          fabs v i (FALL s b) = FALL (sabs v i s) (fabs v (i + 1) b)
   
   [fabsl_def]  Definition
      
      ⊢ (∀i b. fabsl [] i b = b) ∧
        ∀h t i b. fabsl (h::t) i b = fabsl t (i + 1) (fabs h i b)
   
   [fbounds_def]  Definition
      
      ⊢ fbounds False = ∅ ∧
        (∀P sl tl. fbounds (fVar P sl tl) = BIGUNION (set (MAP tbounds tl))) ∧
        (∀p tl. fbounds (Pred p tl) = BIGUNION (set (MAP tbounds tl))) ∧
        (∀f1 f2. fbounds (IMP f1 f2) = fbounds f1 ∪ fbounds f2) ∧
        ∀s b.
          fbounds (FALL s b) = sbounds s ∪ IMAGE PRE (fbounds b DELETE 0)
   
   [ffv_def]  Definition
      
      ⊢ ffv False = ∅ ∧
        (∀p tl. ffv (Pred p tl) = BIGUNION (set (MAP tfv tl))) ∧
        (∀p sl tl.
           ffv (fVar p sl tl) =
           BIGUNION (set (MAP sfv sl)) ∪ BIGUNION (set (MAP tfv tl))) ∧
        (∀s f. ffv (FALL s f) = sfv s ∪ ffv f) ∧
        ∀f1 f2. ffv (IMP f1 f2) = ffv f1 ∪ ffv f2
   
   [finst_def]  Definition
      
      ⊢ (∀σ. finst σ False = False) ∧
        (∀σ p tl. finst σ (Pred p tl) = Pred p (MAP (tinst σ) tl)) ∧
        (∀σ f1 f2. finst σ (IMP f1 f2) = IMP (finst σ f1) (finst σ f2)) ∧
        (∀σ p sl tl.
           finst σ (fVar p sl tl) =
           fVar p (MAP (sinst σ) sl) (MAP (tinst σ) tl)) ∧
        ∀σ s f. finst σ (FALL s f) = FALL (sinst σ s) (finst σ f)
   
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
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC (SUC 0)))
                                (ARB,ARB,a0,ARB)
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('form') a1) ∨
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
        (∀a0 a1 v f f1 f2 f3.
           form_CASE (FALL a0 a1) v f f1 f2 f3 = f2 a0 a1) ∧
        ∀a0 a1 a2 v f f1 f2 f3.
          form_CASE (fVar a0 a1 a2) v f f1 f2 f3 = f3 a0 a1 a2
   
   [form_size_def]  Definition
      
      ⊢ form_size False = 0 ∧
        (∀a0 a1.
           form_size (Pred a0 a1) =
           1 + (list_size char_size a0 + list_size term_size a1)) ∧
        (∀a0 a1. form_size (IMP a0 a1) = 1 + (form_size a0 + form_size a1)) ∧
        (∀a0 a1. form_size (FALL a0 a1) = 1 + (sort_size a0 + form_size a1)) ∧
        ∀a0 a1 a2.
          form_size (fVar a0 a1 a2) =
          1 +
          (list_size char_size a0 +
           (list_size sort_size a1 + list_size term_size a2))
   
   [fprpl_def]  Definition
      
      ⊢ (∀bmap. fprpl bmap False = False) ∧
        (∀bmap f1 f2.
           fprpl bmap (IMP f1 f2) = IMP (fprpl bmap f1) (fprpl bmap f2)) ∧
        (∀bmap p tl. fprpl bmap (Pred p tl) = Pred p (MAP (tprpl bmap) tl)) ∧
        (∀bmap p sl tl.
           fprpl bmap (fVar p sl tl) = fVar p sl (MAP (tprpl bmap) tl)) ∧
        ∀bmap s b.
          fprpl bmap (FALL s b) =
          FALL (sprpl bmap s) (fprpl (shift_bmap 1 bmap) b)
   
   [frename_def]  Definition
      
      ⊢ ∀n s nn f.
          frename (n,s) nn f = finst (TO_FMAP [((n,s),Var nn s)]) f
   
   [frpl_def]  Definition
      
      ⊢ (∀v0 v1. frpl v0 v1 False = False) ∧
        (∀i t p tl. frpl i t (Pred p tl) = Pred p (MAP (trpl i t) tl)) ∧
        (∀i t p sl tl.
           frpl i t (fVar p sl tl) = fVar p sl (MAP (trpl i t) tl)) ∧
        (∀i t f1 f2. frpl i t (IMP f1 f2) = IMP (frpl i t f1) (frpl i t f2)) ∧
        ∀i t s b.
          frpl i t (FALL s b) = FALL (srpl i t s) (frpl (i + 1) t b)
   
   [gcont_def]  Definition
      
      ⊢ ∀vs. gcont vs = vs ∪ BIGUNION {sfv s | (∃n. (n,s) ∈ vs)}
   
   [has_eq]  Definition
      
      ⊢ ∀Σe s. has_eq Σe s ⇔ s ∈ Σe
   
   [inst_eff_def]  Definition
      
      ⊢ ∀σ n s.
          inst_eff σ (n,s) =
          if (n,s) ∈ FDOM σ then σ ' (n,s) else Var n (sinst σ s)
   
   [is_EQ_def]  Definition
      
      ⊢ ∀f. is_EQ f ⇔ ∃t1 t2. f = EQ t1 t2
   
   [ispsym_def]  Definition
      
      ⊢ ∀Σp p. ispsym Σp p ⇔ p ∈ FDOM Σp
   
   [mk_FALL_def]  Definition
      
      ⊢ ∀n s b. mk_FALL n s b = FALL s (abst (n,s) b)
   
   [ofFMAP_def]  Definition
      
      ⊢ ∀f fmap s.
          ofFMAP f fmap s = BIGUNION {f (fmap ' a) | a | a ∈ FDOM fmap ∩ s}
   
   [plainfV_def]  Definition
      
      ⊢ ∀P sl.
          plainfV (P,sl) =
          fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
   
   [presname_def]  Definition
      
      ⊢ ∀σ. presname σ ⇔
            ∀v. v ∈ FDOM σ ⇒ ¬is_bound (σ ' v) ∧ tsname (σ ' v) = vsname v
   
   [psymin_def]  Definition
      
      ⊢ ∀Σp p. psymin Σp p = Σp ' p
   
   [rnmap_def]  Definition
      
      ⊢ ∀n s nn vs.
          rnmap (n,s) nn vs =
          FUN_FMAP (λ(n1,s1). trename (n,s) nn (Var n1 s1)) vs
   
   [slfv_def]  Definition
      
      ⊢ ∀sl. slfv sl = Uof sfv (set sl)
   
   [sname_def]  Definition
      
      ⊢ ∀n v0. sname (St n v0) = n
   
   [srename_def]  Definition
      
      ⊢ ∀n s nn. srename (n,s) nn = sinst (TO_FMAP [((n,s),Var nn s)])
   
   [substb_def]  Definition
      
      ⊢ ∀t f. substb t f = frpl 0 t f
   
   [trename_def]  Definition
      
      ⊢ ∀n s nn. trename (n,s) nn = tinst (TO_FMAP [((n,s),Var nn s)])
   
   [tsname_def]  Definition
      
      ⊢ tsname = sname ∘ sort_of
   
   [v2twbmap_def]  Definition
      
      ⊢ ∀b2v bmap.
          v2twbmap b2v bmap =
          FUN_FMAP (λv. bmap ' (CHOICE {i | i ∈ FDOM b2v ∧ b2v ' i = v}))
            (FRANGE b2v)
   
   [vinst_fVar_def]  Definition
      
      ⊢ ∀vσ P sl. vinst_fVar vσ (P,sl) = (P,MAP (sinst vσ) sl)
   
   [vl2sl0_def]  Definition
      
      ⊢ vl2sl0 [] = [] ∧ ∀v vs. vl2sl0 (v::vs) = v::absvl 0 v (vl2sl0 vs)
   
   [vl2sl_def]  Definition
      
      ⊢ ∀vl. vl2sl vl = MAP SND (vl2sl0 vl)
   
   [vsname_def]  Definition
      
      ⊢ ∀n s. vsname (n,s) = sname s
   
   [wffVmap_def]  Definition
      
      ⊢ ∀Σ ε.
          wffVmap Σ ε ⇔
          ∀P sl. (P,sl) ∈ FDOM ε ⇒ wff Σ (FALLL sl (ε ' (P,sl)))
   
   [wff_def]  Definition
      
      ⊢ wff =
        (λa0 a1.
             ∀wff'.
               (∀a0 a1.
                  (∃Σe Σf Σp. a0 = (Σf,Σp,Σe) ∧ a1 = False) ∨
                  (∃t1 t2 Σe Σf Σp.
                     a0 = (Σf,Σp,Σe) ∧ a1 = EQ t1 t2 ∧ wft Σf t1 ∧
                     wft Σf t2 ∧ sort_of t1 = sort_of t2 ∧
                     has_eq Σe (tsname t2)) ∨
                  (∃p tl Σe Σf Σp.
                     a0 = (Σf,Σp,Σe) ∧ a1 = Pred p tl ∧
                     (∀t. MEM t tl ⇒ wft Σf t) ∧ ispsym Σp p ∧
                     IS_SOME (tlmatch ∅ (MAP Var' (Σp ' p)) tl FEMPTY)) ∨
                  (∃f1 f2 Σe Σf Σp.
                     a0 = (Σf,Σp,Σe) ∧ a1 = IMP f1 f2 ∧
                     wff' (Σf,Σp,Σe) f1 ∧ wff' (Σf,Σp,Σe) f2) ∨
                  (∃P sl tl Σe Σf Σp.
                     a0 = (Σf,Σp,Σe) ∧ a1 = fVar P sl tl ∧ wfabsap Σf sl tl) ∨
                  (∃Σe Σf Σp f n s.
                     a0 = (Σf,Σp,Σe) ∧ a1 = mk_FALL n s f ∧
                     wff' (Σf,Σp,Σe) f ∧ wfs Σf s ∧ (n,s) ∉ fVslfv f ∧
                     ∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
                  wff' a0 a1) ⇒
               wff' a0 a1)
   
   [wfsig_def]  Definition
      
      ⊢ ∀Σf Σp Σe.
          wfsig (Σf,Σp,Σe) ⇔
          (∀fsym.
             isfsym Σf fsym ⇒
             sfv (fsymout Σf fsym) ⊆
             BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧
          ¬ispsym Σp "="
   
   [BIGUNION_IMAGE_sbounds_ffv]  Theorem
      
      ⊢ ∀f. BIGUNION (IMAGE (sbounds ∘ SND) (ffv (frename (n,s) nn f))) =
            BIGUNION (IMAGE (sbounds ∘ SND) (ffv f))
   
   [BIGUNION_IMAGE_sbounds_tfv]  Theorem
      
      ⊢ (∀tm.
           BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn tm))) =
           BIGUNION (IMAGE (sbounds ∘ SND) (tfv tm))) ∧
        ∀st.
          BIGUNION (IMAGE (sbounds ∘ SND) (sfv (srename (n,s) nn st))) =
          BIGUNION (IMAGE (sbounds ∘ SND) (sfv st))
   
   [BIGUNION_is_cont]  Theorem
      
      ⊢ (∀s. s ∈ ss ⇒ is_cont s) ⇒ is_cont (BIGUNION ss)
   
   [EL_specslwtl]  Theorem
      
      ⊢ ∀n1 n tl sl.
          LENGTH tl = n1 ∧ n < LENGTH sl ∧ LENGTH sl = LENGTH tl ∧
          (∀t. MEM t tl ⇒ tbounds t = ∅) ⇒
          EL n (specslwtl tl sl) =
          (EL n tl,sprpl (mk_bmap (REVERSE (TAKE n tl))) (EL n sl))
   
   [FAPPLY_rnmap]  Theorem
      
      ⊢ ∀vs n1 s1.
          FINITE vs ∧ (n1,s1) ∈ vs ⇒
          rnmap (n,s) nn vs ' (n1,s1) = trename (n,s) nn (Var n1 s1)
   
   [FAPPLY_rnmap_SUBSET]  Theorem
      
      ⊢ FINITE vs ∧ ss ⊆ vs ⇒
        ∀n1 s1.
          (n1,s1) ∈ ss ⇒
          rnmap (n,s) nn ss ' (n1,s1) = rnmap (n,s) nn vs ' (n1,s1)
   
   [FAPPLY_v2twbmap]  Theorem
      
      ⊢ INJ ($' b2v) (FDOM b2v) (FRANGE b2v) ∧ FDOM b2v = FDOM bmap ⇒
        ∀i. i ∈ FDOM b2v ⇒ v2twbmap b2v bmap ' (b2v ' i) = bmap ' i
   
   [FDOM_rnmap]  Theorem
      
      ⊢ ∀vs. FINITE vs ⇒ FDOM (rnmap (n,s) nn vs) = vs
   
   [FDOM_v2twbmap]  Theorem
      
      ⊢ FDOM (v2twbmap b2v bmap) = FRANGE b2v
   
   [FINITE_BIGUNION_tfv]  Theorem
      
      ⊢ FINITE (BIGUNION {tfv t | MEM t tl})
   
   [FINITE_lemma]  Theorem
      
      ⊢ FINITE {f t | MEM t l}
   
   [IN_fVslfv]  Theorem
      
      ⊢ v ∈ fVslfv f ⇔ ∃P sl s. (P,sl) ∈ fVars f ∧ MEM s sl ∧ v ∈ sfv s
   
   [IN_slfv]  Theorem
      
      ⊢ (n,s) ∈ slfv sl ⇔ ∃s0. MEM s0 sl ∧ (n,s) ∈ sfv s0
   
   [IN_tfv_trename]  Theorem
      
      ⊢ (∀tm n s nn. (n,s) ∈ tfv tm ⇒ (nn,s) ∈ tfv (trename (n,s) nn tm)) ∧
        ∀st n s nn. (n,s) ∈ sfv st ⇒ (nn,s) ∈ sfv (srename (n,s) nn st)
   
   [LENGTH_specslwtl]  Theorem
      
      ⊢ ∀n tl sl.
          LENGTH tl = n ∧ LENGTH sl = n ⇒ LENGTH (specslwtl tl sl) = n
   
   [MEM_fVsl_SUBSET_fVslfv]  Theorem
      
      ⊢ ∀P sl s. (P,sl) ∈ fVars f ∧ MEM s sl ⇒ sfv s ⊆ fVslfv f
   
   [NOTIN_fVslfv]  Theorem
      
      ⊢ v ∉ fVslfv f ⇔ ∀P sl s. (P,sl) ∈ fVars f ∧ MEM s sl ⇒ v ∉ sfv s
   
   [NOTIN_frename]  Theorem
      
      ⊢ ∀f. nn ≠ n ⇒ (n,s) ∉ ffv (frename (n,s) nn f)
   
   [NOTIN_trename]  Theorem
      
      ⊢ (∀tm. nn ≠ n ⇒ (n,s) ∉ tfv (trename (n,s) nn tm)) ∧
        ∀st. nn ≠ n ⇒ (n,s) ∉ sfv (srename (n,s) nn st)
   
   [TO_FMAP_SING]  Theorem
      
      ⊢ TO_FMAP [(a,b)] ' a = b
   
   [Uof_EMPTY]  Theorem
      
      ⊢ Uof f ∅ = ∅
   
   [Uof_INSERT]  Theorem
      
      ⊢ Uof f (a INSERT s) = f a ∪ Uof f s
   
   [Uof_SUBSET]  Theorem
      
      ⊢ Uof f A ⊆ B ⇔ ∀a. a ∈ A ⇒ f a ⊆ B
   
   [Uof_SUBSET_MONO]  Theorem
      
      ⊢ s1 ⊆ s2 ⇒ Uof f s1 ⊆ Uof f s2
   
   [Uof_Sing]  Theorem
      
      ⊢ Uof f {x} = f x
   
   [Uof_UNION]  Theorem
      
      ⊢ Uof f (A ∪ B) = Uof f A ∪ Uof f B
   
   [abssl_MAP_srename]  Theorem
      
      ⊢ ∀l i.
          (∀n1 s1 st. MEM st l ∧ (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
          (∀st. MEM st l ⇒ (nn,s) ∉ sfv st) ⇒
          abssl (n,s) i l = abssl (nn,s) i (MAP (srename (n,s) nn) l)
   
   [absvl_def]  Theorem
      
      ⊢ (∀v i. absvl i v [] = []) ∧
        ∀v t s n i.
          absvl i v ((n,s)::t) = (n,sabs v i s)::absvl (i + 1) v t
   
   [absvl_ind]  Theorem
      
      ⊢ ∀P. (∀i v. P i v []) ∧
            (∀i v n s t. P (i + 1) v t ⇒ P i v ((n,s)::t)) ⇒
            ∀v v1 v2. P v v1 v2
   
   [cstt_EXT]  Theorem
      
      ⊢ cstt σ ⇒
        ∀vs.
          FINITE vs ∧ FDOM σ ⊆ vs ⇒
          ∃σ1.
            FDOM σ1 = gcont vs ∧ complete σ1 ∧ cstt σ1 ∧
            ∀v. v ∈ vs ⇒ inst_eff σ1 v = inst_eff σ v
   
   [cstt_rnmap]  Theorem
      
      ⊢ ∀vs. FINITE vs ∧ is_cont vs ⇒ cstt (rnmap (n,s) nn vs)
   
   [datatype_form]  Theorem
      
      ⊢ DATATYPE (form False Pred IMP FALL fVar)
   
   [dest_eq_def]  Theorem
      
      ⊢ dest_eq (Pred "=" [t1; t2]) =
        if #"=" = #"=" then
          case "" of
            "" =>
              (case [t1; t2] of
                 [] => ARB
               | [t1] => ARB
               | [t1; t2] => (t1,t2)
               | t1::t2::v31::v32 => ARB)
          | STRING v22 v23 => ARB
        else ARB
   
   [dest_eq_ind]  Theorem
      
      ⊢ ∀P. (∀t1 t2. P (Pred "=" [t1; t2])) ∧ P False ∧
            (∀v18. P (Pred "" v18)) ∧ P (Pred "=" []) ∧
            (∀v30. P (Pred "=" [v30])) ∧
            (∀v36 v35 v33 v34. P (Pred "=" (v36::v35::v33::v34))) ∧
            (∀v24 v25 v37. P (Pred (STRING #"=" (STRING v24 v25)) v37)) ∧
            (∀v38 v39 v40. P (Pred (STRING v38 v39) v40)) ∧
            (∀v4 v5. P (IMP v4 v5)) ∧ (∀v8 v9. P (FALL v8 v9)) ∧
            (∀v13 v14 v15. P (fVar v13 v14 v15)) ⇒
            ∀v. P v
   
   [fVars_finst]  Theorem
      
      ⊢ ∀f. fVars (finst vσ f) = IMAGE (vinst_fVar vσ) (fVars f)
   
   [fVslfv_SUBSET_ffv]  Theorem
      
      ⊢ ∀f. fVslfv f ⊆ ffv f
   
   [fVslfv_alt]  Theorem
      
      ⊢ fVslfv False = ∅ ∧ fVslfv (IMP f1 f2) = fVslfv f1 ∪ fVslfv f2 ∧
        fVslfv (FALL s b) = fVslfv b ∧ fVslfv (Pred p tl) = ∅ ∧
        fVslfv (fVar P sl tl) = slfv sl
   
   [fabs_fbounds_in]  Theorem
      
      ⊢ ∀f n s i.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∉ fVslfv f ∧
          (n,s) ∈ ffv f ⇒
          i ∈ fbounds (fabs (n,s) i f)
   
   [fabs_frename]  Theorem
      
      ⊢ ∀f i.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (nn,s) ∉ ffv f ∧
          (n,s) ∉ fVslfv f ⇒
          fabs (n,s) i f = fabs (nn,s) i (frename (n,s) nn f)
   
   [fabs_frpl]  Theorem
      
      ⊢ ∀f i n s. (n,s) ∉ ffv f ⇒ fabs (n,s) i (frpl i (Var n s) f) = f
   
   [fabs_id]  Theorem
      
      ⊢ ∀f n s i. (n,s) ∉ ffv f ⇒ fabs (n,s) i f = f
   
   [fbounds_fabs]  Theorem
      
      ⊢ ∀f i n s.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∈ ffv f ∧
          (n,s) ∉ fVslfv f ∧ (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = ∅) ⇒
          fbounds (fabs (n,s) i f) = {i} ∪ fbounds f
   
   [fbounds_fabs_SUBSET]  Theorem
      
      ⊢ ∀f n s i.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = ∅) ⇒
          fbounds f ⊆ fbounds (fabs (n,s) i f)
   
   [fbounds_fabs_fVslfv]  Theorem
      
      ⊢ ∀f i n s.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∈ ffv f ∧
          (n,s) ∉ fVslfv f ∧ (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = ∅) ⇒
          fbounds (fabs (n,s) i f) = {i} ∪ fbounds f
   
   [fbounds_thm]  Theorem
      
      ⊢ fbounds False = ∅ ∧
        fbounds (fVar P sl tl) = BIGUNION {tbounds t | MEM t tl} ∧
        fbounds (Pred p tl) = BIGUNION {tbounds t | MEM t tl} ∧
        fbounds (IMP f1 f2) = fbounds f1 ∪ fbounds f2 ∧
        fbounds (FALL s b) = sbounds s ∪ IMAGE PRE (fbounds b DELETE 0)
   
   [ffv_EQ]  Theorem
      
      ⊢ ffv (EQ t1 t2) = tfv t1 ∪ tfv t2
   
   [ffv_FALLL]  Theorem
      
      ⊢ ∀sl f. ffv (FALLL sl f) = BIGUNION {sfv s | MEM s sl} ∪ ffv f
   
   [ffv_FINITE]  Theorem
      
      ⊢ ∀f. FINITE (ffv f)
   
   [ffv_fabs]  Theorem
      
      ⊢ ∀fm i n s.
          (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ∧
          (∀P sl s0. (P,sl) ∈ fVars fm ∧ MEM s0 sl ⇒ (n,s) ∉ sfv s0) ∧
          (n,s) ∈ ffv fm ⇒
          sfv s ∪ ffv (fabs (n,s) i fm) = ffv fm DELETE (n,s)
   
   [ffv_fabs_SUBSET]  Theorem
      
      ⊢ ∀fm i n s.
          (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ∧ (n,s) ∉ fVslfv fm ⇒
          ffv (fabs (n,s) i fm) ⊆ ffv fm DELETE (n,s)
   
   [ffv_fabs_fVslfv]  Theorem
      
      ⊢ ∀fm i n s.
          (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ∧ (n,s) ∉ fVslfv fm ∧
          (n,s) ∈ ffv fm ⇒
          sfv s ∪ ffv (fabs (n,s) i fm) = ffv fm DELETE (n,s)
   
   [ffv_finst]  Theorem
      
      ⊢ ∀f σ.
          cstt σ ∧ ffv f ⊆ FDOM σ ∧ no_bound σ ⇒
          ∀n st.
            (n,st) ∈ ffv (finst σ f) ⇔
            ∃n0 st0. (n0,st0) ∈ ffv f ∧ (n,st) ∈ tfv (σ ' (n0,st0))
   
   [ffv_fprpl]  Theorem
      
      ⊢ ∀ϕ bmap.
          (∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅) ⇒
          ffv (fprpl bmap ϕ) =
          ffv ϕ ∪ BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∩ fbounds ϕ}
   
   [ffv_frename]  Theorem
      
      ⊢ ∀f. (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ∧
            (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (nn,s) ∉ ffv f ∧
            (n,s) ∈ ffv f ⇒
            ffv (frename (n,s) nn f) = ffv f DELETE (n,s) ∪ {(nn,s)}
   
   [ffv_is_cont]  Theorem
      
      ⊢ ∀f. is_cont (ffv f)
   
   [ffv_mk_FALL]  Theorem
      
      ⊢ ∀f n s.
          (∀n0 s0. (n0,s0) ∈ ffv f ⇒ (n,s) ∉ sfv s0) ∧
          (∀P sl s0. (P,sl) ∈ fVars f ∧ MEM s0 sl ⇒ (n,s) ∉ sfv s0) ⇒
          ffv (mk_FALL n s f) = ffv f ∪ sfv s DELETE (n,s)
   
   [ffv_mk_FALL_fVslfv]  Theorem
      
      ⊢ ∀f n s.
          (∀n0 s0. (n0,s0) ∈ ffv f ⇒ (n,s) ∉ sfv s0) ∧ (n,s) ∉ fVslfv f ⇒
          ffv (mk_FALL n s f) = ffv f ∪ sfv s DELETE (n,s)
   
   [ffv_thm]  Theorem
      
      ⊢ ffv False = ∅ ∧ ffv (Pred p tl) = BIGUNION {tfv t | MEM t tl} ∧
        ffv (fVar p sl tl) =
        BIGUNION {sfv s | MEM s sl} ∪ BIGUNION {tfv t | MEM t tl} ∧
        ffv (FALL s f) = sfv s ∪ ffv f ∧ ffv (IMP f1 f2) = ffv f1 ∪ ffv f2
   
   [finst_EQ]  Theorem
      
      ⊢ finst σ (EQ t1 t2) = EQ (tinst σ t1) (tinst σ t2)
   
   [finst_TO_FMAP_id]  Theorem
      
      ⊢ finst (TO_FMAP [((n,s),Var n s)]) f = f
   
   [finst_eq_cvmap]  Theorem
      
      ⊢ ∀f vs.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,sort_of t) ∉ sfv s1) ∧ FINITE vs ∧
          ffv f ⊆ vs ⇒
          finst (TO_FMAP [((n,sort_of t),t)]) f =
          finst (cvmap vs |+ ((n,sort_of t),t)) f
   
   [finst_fabs]  Theorem
      
      ⊢ ∀f an ast σ nn i.
          ffv f ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧ (an,ast) ∉ FDOM σ ∧
          (∀x s. x ∈ ffv f ∪ sfv ast ∧ x ≠ (an,ast) ⇒ (nn,s) ∉ tfv (σ ' x)) ∧
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (an,ast) ∉ sfv s1) ∧
          (∀P sl s0. (P,sl) ∈ fVars f ∧ MEM s0 sl ⇒ (an,ast) ∉ sfv s0) ⇒
          fabs (nn,sinst σ ast) i
            (finst (σ |+ ((an,ast),Var nn (sinst σ ast))) f) =
          finst σ (fabs (an,ast) i f)
   
   [finst_vmap_id]  Theorem
      
      ⊢ ∀f. (∀n s. (n,s) ∈ FDOM σ ∩ ffv f ⇒ σ ' (n,s) = Var n s) ⇒
            finst σ f = f
   
   [fmap_ffv_finst_eq]  Theorem
      
      ⊢ ∀f σ1 σ2.
          ffv f ⊆ FDOM σ1 ∧ ffv f ⊆ FDOM σ2 ∧
          (∀x. x ∈ ffv f ⇒ σ1 ' x = σ2 ' x) ⇒
          finst σ1 f = finst σ2 f
   
   [fmap_ffv_finst_eq1]  Theorem
      
      ⊢ ∀f σ1 σ2.
          DRESTRICT σ1 (ffv f) = DRESTRICT σ2 (ffv f) ⇒
          finst σ1 f = finst σ2 f
   
   [form_11]  Theorem
      
      ⊢ (∀a0 a1 a0' a1'. Pred a0 a1 = Pred a0' a1' ⇔ a0 = a0' ∧ a1 = a1') ∧
        (∀a0 a1 a0' a1'. IMP a0 a1 = IMP a0' a1' ⇔ a0 = a0' ∧ a1 = a1') ∧
        (∀a0 a1 a0' a1'. FALL a0 a1 = FALL a0' a1' ⇔ a0 = a0' ∧ a1 = a1') ∧
        ∀a0 a1 a2 a0' a1' a2'.
          fVar a0 a1 a2 = fVar a0' a1' a2' ⇔ a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
   
   [form_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4. ∃fn.
          fn False = f0 ∧ (∀a0 a1. fn (Pred a0 a1) = f1 a0 a1) ∧
          (∀a0 a1. fn (IMP a0 a1) = f2 a0 a1 (fn a0) (fn a1)) ∧
          (∀a0 a1. fn (FALL a0 a1) = f3 a0 a1 (fn a1)) ∧
          ∀a0 a1 a2. fn (fVar a0 a1 a2) = f4 a0 a1 a2
   
   [form_case_cong]  Theorem
      
      ⊢ ∀M M' v f f1 f2 f3.
          M = M' ∧ (M' = False ⇒ v = v') ∧
          (∀a0 a1. M' = Pred a0 a1 ⇒ f a0 a1 = f' a0 a1) ∧
          (∀a0 a1. M' = IMP a0 a1 ⇒ f1 a0 a1 = f1' a0 a1) ∧
          (∀a0 a1. M' = FALL a0 a1 ⇒ f2 a0 a1 = f2' a0 a1) ∧
          (∀a0 a1 a2. M' = fVar a0 a1 a2 ⇒ f3 a0 a1 a2 = f3' a0 a1 a2) ⇒
          form_CASE M v f f1 f2 f3 = form_CASE M' v' f' f1' f2' f3'
   
   [form_case_eq]  Theorem
      
      ⊢ form_CASE x v f f1 f2 f3 = v' ⇔
        x = False ∧ v = v' ∨ (∃s l. x = Pred s l ∧ f s l = v') ∨
        (∃f' f0. x = IMP f' f0 ∧ f1 f' f0 = v') ∨
        (∃s f'. x = FALL s f' ∧ f2 s f' = v') ∨
        ∃s l l0. x = fVar s l l0 ∧ f3 s l l0 = v'
   
   [form_distinct]  Theorem
      
      ⊢ (∀a1 a0. False ≠ Pred a0 a1) ∧ (∀a1 a0. False ≠ IMP a0 a1) ∧
        (∀a1 a0. False ≠ FALL a0 a1) ∧ (∀a2 a1 a0. False ≠ fVar a0 a1 a2) ∧
        (∀a1' a1 a0' a0. Pred a0 a1 ≠ IMP a0' a1') ∧
        (∀a1' a1 a0' a0. Pred a0 a1 ≠ FALL a0' a1') ∧
        (∀a2 a1' a1 a0' a0. Pred a0 a1 ≠ fVar a0' a1' a2) ∧
        (∀a1' a1 a0' a0. IMP a0 a1 ≠ FALL a0' a1') ∧
        (∀a2 a1' a1 a0' a0. IMP a0 a1 ≠ fVar a0' a1' a2) ∧
        ∀a2 a1' a1 a0' a0. FALL a0 a1 ≠ fVar a0' a1' a2
   
   [form_induction]  Theorem
      
      ⊢ ∀P. P False ∧ (∀s l. P (Pred s l)) ∧
            (∀f f0. P f ∧ P f0 ⇒ P (IMP f f0)) ∧
            (∀f. P f ⇒ ∀s. P (FALL s f)) ∧ (∀s l l0. P (fVar s l l0)) ⇒
            ∀f. P f
   
   [form_nchotomy]  Theorem
      
      ⊢ ∀ff.
          ff = False ∨ (∃s l. ff = Pred s l) ∨ (∃f f0. ff = IMP f f0) ∨
          (∃s f. ff = FALL s f) ∨ ∃s l l0. ff = fVar s l l0
   
   [fprpl_FEMPTY]  Theorem
      
      ⊢ ∀ϕ. fprpl FEMPTY ϕ = ϕ
   
   [fprpl_FMAP_MAP_fabs_IN]  Theorem
      
      ⊢ ∀ϕ i n s bmap.
          (nn,s) ∉ ffv ϕ ∧ (∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
          (∀b n1 s1.
             b ∈ FDOM bmap ∧ (n1,s1) ∈ tfv (bmap ' b) ⇒ (n,s) ∉ sfv s1) ∧
          n ≠ nn ⇒
          fprpl (FMAP_MAP (tabs (n,s) i) bmap) ϕ =
          frename (nn,s) n (fabs (n,s) i (fprpl bmap (frename (n,s) nn ϕ)))
   
   [fprpl_mk_bmap_CONS]  Theorem
      
      ⊢ tbounds tm = ∅ ⇒
        fprpl (mk_bmap (REVERSE tl ⧺ [tm])) ϕ =
        fprpl (mk_bmap (REVERSE tl)) (frpl (LENGTH tl) tm ϕ)
   
   [fprpl_mk_bmap_abs]  Theorem
      
      ⊢ ∀ϕ i bmap.
          (n,s) ∉ ffv ϕ ⇒
          fprpl (FMAP_MAP (tabs (n,s) i) bmap) ϕ =
          fabs (n,s) i (fprpl bmap ϕ)
   
   [frename_FALLL]  Theorem
      
      ⊢ ∀sl ϕ.
          frename (n,s) nn (FALLL sl ϕ) =
          FALLL (MAP (srename (n,s) nn) sl) (frename (n,s) nn ϕ)
   
   [frename_alt]  Theorem
      
      ⊢ frename (n,s) nn False = False ∧
        frename (n,s) nn (IMP f1 f2) =
        IMP (frename (n,s) nn f1) (frename (n,s) nn f2) ∧
        frename (n,s) nn (fVar p sl tl) =
        fVar p (MAP (srename (n,s) nn) sl) (MAP (trename (n,s) nn) tl) ∧
        frename (n,s) nn (Pred p tl) = Pred p (MAP (trename (n,s) nn) tl) ∧
        frename (n,s) nn (FALL st f) =
        FALL (srename (n,s) nn st) (frename (n,s) nn f)
   
   [frename_eq]  Theorem
      
      ⊢ frename (n,s) nn (EQ t1 t2) =
        EQ (trename (n,s) nn t1) (trename (n,s) nn t2)
   
   [frename_finst]  Theorem
      
      ⊢ ∀f n s nn vs.
          FINITE vs ∧ ffv f ⊆ vs ⇒
          frename (n,s) nn f = finst (rnmap (n,s) nn vs) f
   
   [frename_finst_ffv]  Theorem
      
      ⊢ frename (n,s) nn f = finst (rnmap (n,s) nn (ffv f)) f
   
   [frename_fix]  Theorem
      
      ⊢ ∀f n s. (n,s) ∉ ffv f ⇒ frename (n,s) nn f = f
   
   [frename_fprpl]  Theorem
      
      ⊢ ∀ϕ l0 n s nn bmap.
          frename (n,s) nn (fprpl bmap ϕ) =
          fprpl (FMAP_MAP (trename (n,s) nn) bmap) (frename (n,s) nn ϕ)
   
   [fresh_name_ex]  Theorem
      
      ⊢ ∀vs. FINITE vs ⇒ ∃nn. ∀s. (nn,s) ∉ vs
   
   [frpl_FALLL]  Theorem
      
      ⊢ ∀sl tm ϕ i.
          frpl i tm (FALLL sl ϕ) =
          FALLL (specsl i tm sl) (frpl (i + LENGTH sl) tm ϕ)
   
   [frpl_fabs]  Theorem
      
      ⊢ ∀f i n s.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = ∅) ∧ i ∉ fbounds f ∧
          (n,s) ∉ fVslfv f ⇒
          frpl i new (fabs (n,s) i f) = finst (TO_FMAP [((n,s),new)]) f
   
   [gcont_EMPTY]  Theorem
      
      ⊢ gcont ∅ = ∅
   
   [gcont_FINITE]  Theorem
      
      ⊢ ∀vs. FINITE vs ⇒ FINITE (gcont vs)
   
   [gcont_SING]  Theorem
      
      ⊢ gcont {(n,s)} = tfv (Var n s)
   
   [gcont_UNION]  Theorem
      
      ⊢ gcont (A ∪ B) = gcont A ∪ gcont B
   
   [gcont_is_cont]  Theorem
      
      ⊢ ∀vs. is_cont (gcont vs)
   
   [gcont_of_cont]  Theorem
      
      ⊢ ∀ct. is_cont ct ⇒ gcont ct = ct
   
   [ill_formed_fabs_still_in]  Theorem
      
      ⊢ ∀f n s n0 s0 i.
          (n0,s0) ∈ ffv f ∧ (n,s) ∈ sfv s0 ⇒ (n,s) ∈ ffv (fabs (n,s) i f)
   
   [inst_eff_tinst]  Theorem
      
      ⊢ (∀tm σ1 σ2.
           (∀n s. (n,s) ∈ tfv tm ⇒ inst_eff σ1 (n,s) = inst_eff σ2 (n,s)) ⇒
           tinst σ1 tm = tinst σ2 tm) ∧
        ∀st σ1 σ2.
          (∀n s. (n,s) ∈ sfv st ⇒ inst_eff σ1 (n,s) = inst_eff σ2 (n,s)) ⇒
          sinst σ1 st = sinst σ2 st
   
   [mk_FALLL_def]  Theorem
      
      ⊢ (∀b. mk_FALLL [] b = b) ∧
        ∀vl s n b. mk_FALLL ((n,s)::vl) b = mk_FALL n s (mk_FALLL vl b)
   
   [mk_FALLL_ind]  Theorem
      
      ⊢ ∀P. (∀b. P [] b) ∧ (∀n s vl b. P vl b ⇒ P ((n,s)::vl) b) ⇒
            ∀v v1. P v v1
   
   [mk_FALL_rename_eq]  Theorem
      
      ⊢ ∀f. (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∉ fVslfv f ∧
            (nn,s) ∉ ffv f ⇒
            mk_FALL n s f = mk_FALL nn s (frename (n,s) nn f)
   
   [mk_bmap_NIL]  Theorem
      
      ⊢ mk_bmap [] = FEMPTY
   
   [no_subrename]  Theorem
      
      ⊢ ∀n0 s0. (n0,s0) ∈ sfv s ⇒ trename (n,s) nn (Var n0 s0) = Var n0 s0
   
   [ok_abs_rename]  Theorem
      
      ⊢ ok_abs (MAP (srename (n,s) nn) l) ⇔ ok_abs l
   
   [presname_DRESTRICT]  Theorem
      
      ⊢ presname σ ⇒ presname (DRESTRICT σ s)
   
   [presname_FUPDATE]  Theorem
      
      ⊢ presname σ ⇒
        ∀v t. ¬is_bound t ∧ vsname v = tsname t ⇒ presname (σ |+ (v,t))
   
   [presname_cvmap]  Theorem
      
      ⊢ ∀vs. FINITE vs ⇒ presname (cvmap vs)
   
   [presname_rnmap]  Theorem
      
      ⊢ ∀vs. FINITE vs ⇒ presname (rnmap (n,s) nn vs)
   
   [sfv_ffv]  Theorem
      
      ⊢ ∀f. (n,s) ∈ ffv f ⇒ sfv s ⊆ ffv f
   
   [shift_bmap_0_I]  Theorem
      
      ⊢ shift_bmap 0 = I
   
   [shift_bmap_SING]  Theorem
      
      ⊢ tbounds h = ∅ ⇒ shift_bmap n (mk_bmap [h]) ' n = h
   
   [slprpl_FMAP_MAP_abssl_IN]  Theorem
      
      ⊢ ∀sl i n s nn bmap.
          (∀st. MEM st sl ⇒ (nn,s) ∉ sfv st) ∧
          (∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
          (∀b n1 s1.
             b ∈ FDOM bmap ∧ (n1,s1) ∈ tfv (bmap ' b) ⇒ (n,s) ∉ sfv s1) ∧
          n ≠ nn ⇒
          slprpl (FMAP_MAP (tabs (n,s) i) bmap) sl =
          MAP (srename (nn,s) n)
            (abssl (n,s) i (slprpl bmap (MAP (srename (n,s) nn) sl)))
   
   [slprpl_mk_bmap_CONS]  Theorem
      
      ⊢ ∀l tl tm n.
          tbounds tm = ∅ ⇒
          slprpl (shift_bmap n (mk_bmap (REVERSE tl ⧺ [tm]))) l =
          slprpl (shift_bmap n (mk_bmap (REVERSE tl)))
            (specsl (n + LENGTH tl) tm l)
   
   [slprpl_trename]  Theorem
      
      ⊢ ∀l n s nn bmap.
          MAP (srename (n,s) nn) (slprpl bmap l) =
          slprpl (FMAP_MAP (trename (n,s) nn) bmap)
            (MAP (srename (n,s) nn) l)
   
   [specslwtl]  Theorem
      
      ⊢ specslwtl [] [] = [] ∧
        ∀tl t sl s.
          specslwtl (t::tl) (s::sl) = (t,s)::specslwtl tl (specsl 0 t sl)
   
   [specslwtl_ind]  Theorem
      
      ⊢ ∀P. P [] [] ∧
            (∀t tl s sl. P tl (specsl 0 t sl) ⇒ P (t::tl) (s::sl)) ∧
            (∀v6 v7. P [] (v6::v7)) ∧ (∀v10 v11. P (v10::v11) []) ⇒
            ∀v v1. P v v1
   
   [tabs_trename]  Theorem
      
      ⊢ (∀tm.
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧ (nn,s) ∉ tfv tm ⇒
           tabs (n,s) i tm = tabs (nn,s) i (trename (n,s) nn tm)) ∧
        ∀st.
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧ (nn,s) ∉ sfv st ⇒
          sabs (n,s) i st = sabs (nn,s) i (srename (n,s) nn st)
   
   [tbounds_trename]  Theorem
      
      ⊢ (∀tm n s nn. tbounds (trename (n,s) nn tm) = tbounds tm) ∧
        ∀st n s nn. sbounds (srename (n,s) nn st) = sbounds st
   
   [tfv_tprpl_SUBSET]  Theorem
      
      ⊢ (∀t i new. tfv t ⊆ tfv (tprpl bmap t)) ∧
        ∀s i new. sfv s ⊆ sfv (sprpl bmap s)
   
   [tfv_trename]  Theorem
      
      ⊢ (∀tm n s nn.
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∈ tfv tm ⇒
           tfv (trename (n,s) nn tm) = tfv tm DELETE (n,s) ∪ {(nn,s)}) ∧
        ∀st n s nn.
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∈ sfv st ⇒
          sfv (srename (n,s) nn st) = sfv st DELETE (n,s) ∪ {(nn,s)}
   
   [tfv_trpl_SUBSET1]  Theorem
      
      ⊢ (∀t i new. tfv t ⊆ tfv (trpl i new t)) ∧
        ∀s i new. sfv s ⊆ sfv (srpl i new s)
   
   [tinst_cvmap_UPDATE]  Theorem
      
      ⊢ (∀tm vs n s.
           (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,sort_of t) ∉ sfv s1) ∧
           FINITE vs ∧ tfv tm ⊆ vs ⇒
           tinst (cvmap vs |+ ((n,sort_of t),t)) tm =
           tinst (TO_FMAP [((n,sort_of t),t)]) tm) ∧
        ∀st vs n s.
          (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,sort_of t) ∉ sfv s1) ∧ FINITE vs ∧
          sfv st ⊆ vs ⇒
          sinst (cvmap vs |+ ((n,sort_of t),t)) st =
          sinst (TO_FMAP [((n,sort_of t),t)]) st
   
   [tprpl_FMAP_MAP_tabs_IN]  Theorem
      
      ⊢ (∀tm i n s nn bmap.
           (nn,s) ∉ tfv tm ∧
           (∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
           (∀b n1 s1.
              b ∈ FDOM bmap ∧ (n1,s1) ∈ tfv (bmap ' b) ⇒ (n,s) ∉ sfv s1) ∧
           n ≠ nn ⇒
           tprpl (FMAP_MAP (tabs (n,s) i) bmap) tm =
           trename (nn,s) n
             (tabs (n,s) i (tprpl bmap (trename (n,s) nn tm)))) ∧
        ∀st i n s nn bmap.
          (nn,s) ∉ sfv st ∧ (∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
          (∀b n1 s1.
             b ∈ FDOM bmap ∧ (n1,s1) ∈ tfv (bmap ' b) ⇒ (n,s) ∉ sfv s1) ∧
          n ≠ nn ⇒
          sprpl (FMAP_MAP (tabs (n,s) i) bmap) st =
          srename (nn,s) n
            (sabs (n,s) i (sprpl bmap (srename (n,s) nn st)))
   
   [tprpl_FUNION]  Theorem
      
      ⊢ (∀tm bmap1 bmap2.
           (∀i. i ∈ FDOM bmap2 ∩ tbounds tm ⇒ tbounds (bmap2 ' i) = ∅) ∧
           FDOM bmap1 ∩ FDOM bmap2 = ∅ ⇒
           tprpl bmap1 (tprpl bmap2 tm) = tprpl (bmap1 ⊌ bmap2) tm) ∧
        ∀st bmap1 bmap2.
          (∀i. i ∈ FDOM bmap2 ∩ sbounds st ⇒ tbounds (bmap2 ' i) = ∅) ∧
          FDOM bmap1 ∩ FDOM bmap2 = ∅ ⇒
          sprpl bmap1 (sprpl bmap2 st) = sprpl (bmap1 ⊌ bmap2) st
   
   [tprpl_mk_bmap_CONS]  Theorem
      
      ⊢ (∀t tm tl n.
           tbounds tm = ∅ ⇒
           tprpl (shift_bmap n (mk_bmap (REVERSE tl ⧺ [tm]))) t =
           tprpl (shift_bmap n (mk_bmap (REVERSE tl)))
             (trpl (LENGTH tl + n) tm t)) ∧
        ∀s tm tl n.
          tbounds tm = ∅ ⇒
          sprpl (shift_bmap n (mk_bmap (REVERSE tl ⧺ [tm]))) s =
          sprpl (shift_bmap n (mk_bmap (REVERSE tl)))
            (srpl (LENGTH tl + n) tm s)
   
   [tprpl_wvar]  Theorem
      
      ⊢ (∀tm bmap b2v.
           INJ ($' b2v) (FDOM b2v) (FRANGE b2v) ∧ FDOM bmap = FDOM b2v ∧
           (∀i. i ∈ FDOM b2v ⇒ tfv (Var' (b2v ' i)) ∩ tfv tm = ∅) ⇒
           tprpl bmap tm =
           tinst (v2twbmap b2v bmap) (tprpl (FMAP_MAP Var' b2v) tm)) ∧
        ∀st bmap b2v.
          INJ ($' b2v) (FDOM b2v) (FRANGE b2v) ∧ FDOM bmap = FDOM b2v ∧
          (∀i. i ∈ FDOM b2v ⇒ tfv (Var' (b2v ' i)) ∩ sfv st = ∅) ⇒
          sprpl bmap st =
          sinst (v2twbmap b2v bmap) (sprpl (FMAP_MAP Var' b2v) st)
   
   [trename_alt]  Theorem
      
      ⊢ trename (n,s) nn (Var n0 s0) =
        (if n0 = n ∧ s0 = s then Var nn s else Var n0 (srename (n,s) nn s0)) ∧
        trename (n,s) nn (Fn f st tl) =
        Fn f (srename (n,s) nn st) (MAP (trename (n,s) nn) tl) ∧
        trename (n,s) nn (Bound i) = Bound i ∧
        srename (n,s) nn (St sn tl) = St sn (MAP (trename (n,s) nn) tl)
   
   [trename_back]  Theorem
      
      ⊢ (∀tm n s nn.
           (nn,s) ∉ tfv tm ⇒ trename (nn,s) n (trename (n,s) nn tm) = tm) ∧
        ∀st n s nn.
          (nn,s) ∉ sfv st ⇒ srename (nn,s) n (srename (n,s) nn st) = st
   
   [trename_fix]  Theorem
      
      ⊢ (∀tm n s nn. (n,s) ∉ tfv tm ⇒ trename (n,s) nn tm = tm) ∧
        ∀st n s nn. (n,s) ∉ sfv st ⇒ srename (n,s) nn st = st
   
   [trename_shift_bmap]  Theorem
      
      ⊢ FMAP_MAP (trename (n,s) nn) (shift_bmap i bmap) =
        shift_bmap i (FMAP_MAP (trename (n,s) nn) bmap)
   
   [trename_tinst]  Theorem
      
      ⊢ (∀tm n s nn vs.
           FINITE vs ∧ tfv tm ⊆ vs ⇒
           trename (n,s) nn tm = tinst (rnmap (n,s) nn vs) tm) ∧
        ∀st n s nn vs.
          FINITE vs ∧ sfv st ⊆ vs ⇒
          srename (n,s) nn st = sinst (rnmap (n,s) nn vs) st
   
   [trename_tinst_tfv]  Theorem
      
      ⊢ (∀tm. trename (n,s) nn tm = tinst (rnmap (n,s) nn (tfv tm)) tm) ∧
        ∀st. srename (n,s) nn st = sinst (rnmap (n,s) nn (sfv st)) st
   
   [trename_tprpl]  Theorem
      
      ⊢ (∀tm l0 n s nn bmap.
           trename (n,s) nn (tprpl bmap tm) =
           tprpl (FMAP_MAP (trename (n,s) nn) bmap) (trename (n,s) nn tm)) ∧
        ∀st l0 n s nn bmap.
          srename (n,s) nn (sprpl bmap st) =
          sprpl (FMAP_MAP (trename (n,s) nn) bmap) (srename (n,s) nn st)
   
   [trename_tshift]  Theorem
      
      ⊢ (∀tm i n s nn.
           trename (n,s) nn (tshift i tm) = tshift i (trename (n,s) nn tm)) ∧
        ∀st i n s nn.
          srename (n,s) nn (sshift i st) = sshift i (srename (n,s) nn st)
   
   [trpl_tprpl]  Theorem
      
      ⊢ (∀tm n t.
           tbounds t = ∅ ⇒
           trpl n t tm = tprpl (shift_bmap n (mk_bmap [t])) tm) ∧
        ∀st n t.
          tbounds t = ∅ ⇒
          srpl n t st = sprpl (shift_bmap n (mk_bmap [t])) st
   
   [tsname_tinst]  Theorem
      
      ⊢ (∀t. ¬is_bound t ∧ presname σ ⇒ tsname (tinst σ t) = tsname t) ∧
        ∀s. presname σ ⇒ sname (sinst σ s) = sname s
   
   [tsname_trename]  Theorem
      
      ⊢ ∀t. ¬is_bound t ⇒ tsname (trename (n,s) nn t) = tsname t
   
   [wfabsap0_def]  Theorem
      
      ⊢ (∀Σf. wfabsap0 Σf [] [] ⇔ T) ∧
        (∀Σf tl t sl s.
           wfabsap0 Σf (s::sl) (t::tl) ⇔
           wft Σf t ∧ s = sort_of t ∧ wfs Σf s ∧
           wfabsap0 Σf (specsl 0 t sl) tl) ∧
        (∀Σf sl s. wfabsap0 Σf (s::sl) [] ⇔ F) ∧
        ∀Σf tl t. wfabsap0 Σf [] (t::tl) ⇔ F
   
   [wfabsap0_ind]  Theorem
      
      ⊢ ∀P. (∀Σf. P Σf [] []) ∧
            (∀Σf s sl t tl. P Σf (specsl 0 t sl) tl ⇒ P Σf (s::sl) (t::tl)) ∧
            (∀Σf s sl. P Σf (s::sl) []) ∧ (∀Σf t tl. P Σf [] (t::tl)) ⇒
            ∀v v1 v2. P v v1 v2
   
   [wfabsap0_specslwtl]  Theorem
      
      ⊢ ∀tl sl.
          wfabsap0 Σ sl tl ⇔
          LENGTH sl = LENGTH tl ∧
          (let
             sl1 = specslwtl tl sl
           in
             ∀t s. MEM (t,s) sl1 ⇒ wft Σ t ∧ wfs Σ s ∧ sort_of t = s)
   
   [wfabsap0_wft]  Theorem
      
      ⊢ ∀tl sl t. wfabsap0 Σf sl tl ∧ MEM t tl ⇒ wft Σf t
   
   [wfabsap_wfabsap0]  Theorem
      
      ⊢ ∀n sl tl. LENGTH sl = n ⇒ wfabsap0 Σ sl tl ⇒ wfabsap Σ sl tl
   
   [wfcod_rnmap_BIGUNION]  Theorem
      
      ⊢ (∀vs. vs ∈ ss ⇒ wfcod Σf (rnmap (n,s) nn vs)) ∧
        FINITE (BIGUNION ss) ⇒
        wfcod Σf (rnmap (n,s) nn (BIGUNION ss))
   
   [wfcod_rnmap_SUBSET]  Theorem
      
      ⊢ FINITE vs ∧ wfcod Σf (rnmap (n,s) nn vs) ⇒
        ∀ss. ss ⊆ vs ⇒ wfcod Σf (rnmap (n,s) nn ss)
   
   [wfcod_rnmap_cont]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀vs.
          FINITE vs ⇒
          is_cont vs ⇒
          (∀n1 s1. (n1,s1) ∈ vs ⇒ wfs Σf s1) ⇒
          wfcod Σf (rnmap (n,s) nn vs)
   
   [wfcod_rnmap_ffv]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀f. wff (Σf,Σp,Σe) f ⇒ ∀n s ss. wfcod Σf (rnmap (n,s) nn (ffv f))
   
   [wfcod_rnmap_gcont]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀vs.
          FINITE vs ⇒
          (∀n1 s1. (n1,s1) ∈ vs ⇒ wfs Σf s1) ⇒
          wfcod Σf (rnmap (n,s) nn (gcont vs))
   
   [wfcod_rnmap_tfv]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        (∀tm. wft Σf tm ⇒ ∀n s ss. wfcod Σf (rnmap (n,s) nn (tfv tm))) ∧
        ∀st. wfs Σf st ⇒ ∀n s ss. wfcod Σf (rnmap (n,s) nn (sfv st))
   
   [wff_EQ]  Theorem
      
      ⊢ wfsig (Σf,Σp,Σe) ⇒
        (wff (Σf,Σp,Σe) (EQ t1 t2) ⇔
         wft Σf t1 ∧ wft Σf t2 ∧ sort_of t1 = sort_of t2 ∧
         has_eq Σe (tsname t2))
   
   [wff_FALL]  Theorem
      
      ⊢ ∀s b.
          wff (Σf,Σp,Σe) (FALL s b) ⇔
          ∃f n.
            wff (Σf,Σp,Σe) f ∧ wfs Σf s ∧ (n,s) ∉ fVslfv f ∧
            (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
            FALL s b = mk_FALL n s f
   
   [wff_FALLL_ffv_SUBSET]  Theorem
      
      ⊢ ∀sl. ffv ϕ ⊆ ffv (FALLL sl ϕ)
   
   [wff_FALLL_no_vbound]  Theorem
      
      ⊢ ∀sl. wff Σ (FALLL sl ϕ) ⇒ ∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅
   
   [wff_False]  Theorem
      
      ⊢ ∀Σe Σf Σp. wff (Σf,Σp,Σe) False
   
   [wff_IMP]  Theorem
      
      ⊢ ∀f1 f2 Σe Σf Σp.
          wff (Σf,Σp,Σe) f1 ∧ wff (Σf,Σp,Σe) f2 ⇒
          wff (Σf,Σp,Σe) (IMP f1 f2)
   
   [wff_Pred]  Theorem
      
      ⊢ ∀p tl Σe Σf Σp.
          (∀t. MEM t tl ⇒ wft Σf t) ∧ ispsym Σp p ∧
          IS_SOME (tlmatch ∅ (MAP Var' (Σp ' p)) tl FEMPTY) ⇒
          wff (Σf,Σp,Σe) (Pred p tl)
   
   [wff_cases]  Theorem
      
      ⊢ ∀a0 a1.
          wff a0 a1 ⇔
          (∃Σe Σf Σp. a0 = (Σf,Σp,Σe) ∧ a1 = False) ∨
          (∃t1 t2 Σe Σf Σp.
             a0 = (Σf,Σp,Σe) ∧ a1 = EQ t1 t2 ∧ wft Σf t1 ∧ wft Σf t2 ∧
             sort_of t1 = sort_of t2 ∧ has_eq Σe (tsname t2)) ∨
          (∃p tl Σe Σf Σp.
             a0 = (Σf,Σp,Σe) ∧ a1 = Pred p tl ∧ (∀t. MEM t tl ⇒ wft Σf t) ∧
             ispsym Σp p ∧
             IS_SOME (tlmatch ∅ (MAP Var' (Σp ' p)) tl FEMPTY)) ∨
          (∃f1 f2 Σe Σf Σp.
             a0 = (Σf,Σp,Σe) ∧ a1 = IMP f1 f2 ∧ wff (Σf,Σp,Σe) f1 ∧
             wff (Σf,Σp,Σe) f2) ∨
          (∃P sl tl Σe Σf Σp.
             a0 = (Σf,Σp,Σe) ∧ a1 = fVar P sl tl ∧ wfabsap Σf sl tl) ∨
          ∃Σe Σf Σp f n s.
            a0 = (Σf,Σp,Σe) ∧ a1 = mk_FALL n s f ∧ wff (Σf,Σp,Σe) f ∧
            wfs Σf s ∧ (n,s) ∉ fVslfv f ∧
            ∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1
   
   [wff_fVar]  Theorem
      
      ⊢ ∀P sl tl Σe Σf Σp. wfabsap Σf sl tl ⇒ wff (Σf,Σp,Σe) (fVar P sl tl)
   
   [wff_fVar_subst_lemma]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀tl sl ϕ.
          wfabsap Σf sl tl ∧ wff (Σf,Σp,Σe) (FALLL sl ϕ) ⇒
          wff (Σf,Σp,Σe) (fprpl (mk_bmap (REVERSE tl)) ϕ)
   
   [wff_fbounds]  Theorem
      
      ⊢ ∀f. wff Σf f ⇒ fbounds f = ∅
   
   [wff_finst]  Theorem
      
      ⊢ ∀f. wff (Σf,Σp,Σe) f ⇒
            (∀fsym.
               isfsym Σf fsym ⇒
               sfv (fsymout Σf fsym) ⊆
               BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
            ∀σ. cstt σ ∧ wfcod Σf σ ∧ ffv f ⊆ FDOM σ ∧ presname σ ⇒
                wff (Σf,Σp,Σe) (finst σ f)
   
   [wff_frename]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀f. wff (Σf,Σp,Σe) f ⇒ ∀n s nn. wff (Σf,Σp,Σe) (frename (n,s) nn f)
   
   [wff_ind]  Theorem
      
      ⊢ ∀wff'.
          (∀Σe Σf Σp. wff' (Σf,Σp,Σe) False) ∧
          (∀t1 t2 Σe Σf Σp.
             wft Σf t1 ∧ wft Σf t2 ∧ sort_of t1 = sort_of t2 ∧
             has_eq Σe (tsname t2) ⇒
             wff' (Σf,Σp,Σe) (EQ t1 t2)) ∧
          (∀p tl Σe Σf Σp.
             (∀t. MEM t tl ⇒ wft Σf t) ∧ ispsym Σp p ∧
             IS_SOME (tlmatch ∅ (MAP Var' (Σp ' p)) tl FEMPTY) ⇒
             wff' (Σf,Σp,Σe) (Pred p tl)) ∧
          (∀f1 f2 Σe Σf Σp.
             wff' (Σf,Σp,Σe) f1 ∧ wff' (Σf,Σp,Σe) f2 ⇒
             wff' (Σf,Σp,Σe) (IMP f1 f2)) ∧
          (∀P sl tl Σe Σf Σp.
             wfabsap Σf sl tl ⇒ wff' (Σf,Σp,Σe) (fVar P sl tl)) ∧
          (∀Σe Σf Σp f n s.
             wff' (Σf,Σp,Σe) f ∧ wfs Σf s ∧ (n,s) ∉ fVslfv f ∧
             (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
             wff' (Σf,Σp,Σe) (mk_FALL n s f)) ⇒
          ∀a0 a1. wff a0 a1 ⇒ wff' a0 a1
   
   [wff_no_vbound]  Theorem
      
      ⊢ ∀f. wff Σf f ⇒ ∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅
   
   [wff_rules]  Theorem
      
      ⊢ (∀Σe Σf Σp. wff (Σf,Σp,Σe) False) ∧
        (∀t1 t2 Σe Σf Σp.
           wft Σf t1 ∧ wft Σf t2 ∧ sort_of t1 = sort_of t2 ∧
           has_eq Σe (tsname t2) ⇒
           wff (Σf,Σp,Σe) (EQ t1 t2)) ∧
        (∀p tl Σe Σf Σp.
           (∀t. MEM t tl ⇒ wft Σf t) ∧ ispsym Σp p ∧
           IS_SOME (tlmatch ∅ (MAP Var' (Σp ' p)) tl FEMPTY) ⇒
           wff (Σf,Σp,Σe) (Pred p tl)) ∧
        (∀f1 f2 Σe Σf Σp.
           wff (Σf,Σp,Σe) f1 ∧ wff (Σf,Σp,Σe) f2 ⇒
           wff (Σf,Σp,Σe) (IMP f1 f2)) ∧
        (∀P sl tl Σe Σf Σp.
           wfabsap Σf sl tl ⇒ wff (Σf,Σp,Σe) (fVar P sl tl)) ∧
        ∀Σe Σf Σp f n s.
          wff (Σf,Σp,Σe) f ∧ wfs Σf s ∧ (n,s) ∉ fVslfv f ∧
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
          wff (Σf,Σp,Σe) (mk_FALL n s f)
   
   [wff_spec]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧
        wff (Σf,Σp,Σe) (FALL s ϕ) ⇒
        ∀t. wft Σf t ∧ sort_of t = s ⇒ wff (Σf,Σp,Σe) (substb t ϕ)
   
   [wff_strongind]  Theorem
      
      ⊢ ∀wff'.
          (∀Σe Σf Σp. wff' (Σf,Σp,Σe) False) ∧
          (∀t1 t2 Σe Σf Σp.
             wft Σf t1 ∧ wft Σf t2 ∧ sort_of t1 = sort_of t2 ∧
             has_eq Σe (tsname t2) ⇒
             wff' (Σf,Σp,Σe) (EQ t1 t2)) ∧
          (∀p tl Σe Σf Σp.
             (∀t. MEM t tl ⇒ wft Σf t) ∧ ispsym Σp p ∧
             IS_SOME (tlmatch ∅ (MAP Var' (Σp ' p)) tl FEMPTY) ⇒
             wff' (Σf,Σp,Σe) (Pred p tl)) ∧
          (∀f1 f2 Σe Σf Σp.
             wff (Σf,Σp,Σe) f1 ∧ wff' (Σf,Σp,Σe) f1 ∧ wff (Σf,Σp,Σe) f2 ∧
             wff' (Σf,Σp,Σe) f2 ⇒
             wff' (Σf,Σp,Σe) (IMP f1 f2)) ∧
          (∀P sl tl Σe Σf Σp.
             wfabsap Σf sl tl ⇒ wff' (Σf,Σp,Σe) (fVar P sl tl)) ∧
          (∀Σe Σf Σp f n s.
             wff (Σf,Σp,Σe) f ∧ wff' (Σf,Σp,Σe) f ∧ wfs Σf s ∧
             (n,s) ∉ fVslfv f ∧ (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
             wff' (Σf,Σp,Σe) (mk_FALL n s f)) ⇒
          ∀a0 a1. wff a0 a1 ⇒ wff' a0 a1
   
   [wff_wfcod_cvmap_ffv]  Theorem
      
      ⊢ wff (Σf,Σp,Σe) f ⇒ wfcod Σf (cvmap (ffv f))
   
   [wff_wfs]  Theorem
      
      ⊢ ∀f. wff (Σf,Σp,Σe) f ⇒ ∀n s. (n,s) ∈ ffv f ⇒ wfs Σf s
   
   [wft_no_vbound]  Theorem
      
      ⊢ (∀tm. wft Σf tm ⇒ ∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅) ∧
        ∀st. wfs Σf st ⇒ ∀n s. (n,s) ∈ sfv st ⇒ sbounds s = ∅
   
   [wft_not_bound]  Theorem
      
      ⊢ wft Σ t ⇒ ¬is_bound t
   
   [wft_trename]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        (∀tm. wft Σf tm ⇒ ∀n s ss. wft Σf (trename (n,s) nn tm)) ∧
        ∀st. wfs Σf st ⇒ ∀n s ss. wfs Σf (srename (n,s) nn st)
   
   [wft_trename0]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        (∀tm.
           wft Σf tm ⇒
           ∀n s ss.
             wft Σf (trename (n,s) nn tm) ∧
             wfcod Σf (rnmap (n,s) nn (tfv tm))) ∧
        ∀st.
          wfs Σf st ⇒
          ∀n s ss.
            wfs Σf (srename (n,s) nn st) ∧
            wfcod Σf (rnmap (n,s) nn (sfv st))
   
   
*)
end
