signature Pf0DrvTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val Pf0Drv_def : thm
    val Pf0_def : thm
    val UCI_def : thm
    val UCIth_def : thm
    val ax2th_def : thm
    val fVrnwinst_def : thm
    val uniqify_def : thm
    val wfaths_def : thm
    val wfsigaths_def : thm
  
  (*  Theorems  *)
    val EL_specslwtl : thm
    val FAPPLY_fVmap_fVrn1 : thm
    val FAPPLY_fVrnwinst : thm
    val FAPPLY_mk_bmap_REVERSE_Lofeqthl : thm
    val FAPPLY_mk_bmap_REVERSE_Rofeqthl : thm
    val FAPPLY_o_fVmap1' : thm
    val FAPPLY_plainfV_bmap : thm
    val FAPPLY_vinst_fVmap1 : thm
    val FAPPLY_vinst_fVmap_fVmap_fVrn : thm
    val FAPPLY_vinst_fVmap_fVmap_fVrn1 : thm
    val FDOM_fVrnwinst : thm
    val IMAGE_Uof : thm
    val IMAGE_eq_lemma : thm
    val IMAGE_fVrn_fVars : thm
    val IMAGE_fVrn_fVrwinst_vinst_fVar : thm
    val IMAGE_vinst_fVar_fVars : thm
    val IN_cont_FAPPLY_SUBSET_cont_vinst : thm
    val IN_thfVars : thm
    val Pf0Drv_add_assum : thm
    val Pf0Drv_add_cont : thm
    val Pf0Drv_add_cont0 : thm
    val Pf0Drv_add_cont1 : thm
    val Pf0Drv_assum_SUBSET : thm
    val Pf0Drv_assum_ffv_SUBSET : thm
    val Pf0Drv_assume : thm
    val Pf0Drv_cfm : thm
    val Pf0Drv_concl_ffv_SUBSET : thm
    val Pf0Drv_cont_SUBSET : thm
    val Pf0Drv_cont_SUBSET_cong : thm
    val Pf0Drv_cont_wf : thm
    val Pf0Drv_cont_wf' : thm
    val Pf0Drv_disch : thm
    val Pf0Drv_double_neg : thm
    val Pf0Drv_ffv_SUBSET_cont : thm
    val Pf0Drv_gen : thm
    val Pf0Drv_mp : thm
    val Pf0Drv_undisch : thm
    val Pf0Drv_wff : thm
    val Pf0Drv_wff1 : thm
    val Pf0_ALLE : thm
    val Pf0_ALLI : thm
    val Pf0_AX : thm
    val Pf0_add_cont1 : thm
    val Pf0_assume : thm
    val Pf0_cases : thm
    val Pf0_cfm : thm
    val Pf0_cong : thm
    val Pf0_cont_is_cont : thm
    val Pf0_disch : thm
    val Pf0_double_neg : thm
    val Pf0_ffv_SUBSET_wff : thm
    val Pf0_fromBot : thm
    val Pf0_ind : thm
    val Pf0_mp : thm
    val Pf0_refl : thm
    val Pf0_rules : thm
    val Pf0_strongind : thm
    val Pf0_sym : thm
    val Pf0_trans : thm
    val Pf0_vinsth : thm
    val Pf0_wff : thm
    val Pf2Pf0_fVinsth_lemma : thm
    val Pf2Pf0_vinst_lemma : thm
    val PfDrv_assum_wff : thm
    val PfDrv_concl_wff : thm
    val PfDrv_cont_FINITE : thm
    val PfDrv_cont_is_cont : thm
    val PfDrv_fVinsth : thm
    val PfDrv_slfv_SUBSET_cont : thm
    val PfDrv_uniqify : thm
    val PfDrv_vinsth : thm
    val Pf_assum_FINITE : thm
    val SUBSET_thfVars : thm
    val Uof_FINITE_lemma : thm
    val Uof_IMAGE : thm
    val Uof_concl_assum_SUBSET_cont : thm
    val Uof_fVars_finst_ffVrn : thm
    val Uof_ffv_uniqify : thm
    val cfVmap_DRESTRICT : thm
    val cfVmap_o_fVmap : thm
    val cont_assum_concl : thm
    val cont_fVinsth : thm
    val cont_uniqify : thm
    val cont_vinsth : thm
    val ex_SUBSET_ofFMAP : thm
    val fVars_FAPPLY_SUBSET_thfVars_fVinsth : thm
    val fVars_FINITE : thm
    val fVinst_cfVmap_is_cfm : thm
    val fVinst_o_Vmap_finst_ffVrn : thm
    val fVinst_plainfV : thm
    val fVinst_subset_lemma : thm
    val fVinst_subset_lemma0 : thm
    val fVinsth_DRESTRICT : thm
    val fVrn_fVrwinst : thm
    val ffVrn_eq : thm
    val ffVrn_eq1 : thm
    val ffv_SUBSET_cont_fVinsth : thm
    val ffv_assum_SUBSET_cont_fVinsth : thm
    val ffv_ffVinst_SUBSET_cont_fVinsth : thm
    val ffv_finst_ffVrn : thm
    val fprpl_fix : thm
    val gen_precise_maps_ex : thm
    val insth_uniqify_fVinsth : thm
    val is_cfm_EQ : thm
    val is_cfm_IFF : thm
    val is_cfm_NEG : thm
    val is_cfm_fabs : thm
    val is_cfm_finst : thm
    val is_cfm_fprpl : thm
    val is_cfm_frpl : thm
    val main_fVinst_case : thm
    val mk_bmap_BIGUNION : thm
    val ofFMAP_DRESTRICT : thm
    val ofFMAP_FINITE : thm
    val ofFMAP_IMAGE : thm
    val ofFMAP_SUBSET : thm
    val ofFMAP_SUBSET_UNION_lemma : thm
    val ofFMAP_Uof : thm
    val ofFMAP_Uof_SUBSET_lemma : thm
    val ofFMAP_Uof_SUBSET_lemma2 : thm
    val ofFMAP_as_IMAGE : thm
    val ofFMAP_differ_2_SUBSET_lemma : thm
    val ofFMAP_fVars_SUBSET_fVars_fVinst : thm
    val ofFMAP_fVars_rn2fVmap : thm
    val ofFMAP_ffv_is_cont : thm
    val ofFMAP_ffv_o_fVmap : thm
    val ofFMAP_tfv_is_cont : thm
    val precise_maps_ex : thm
    val sfv_vinst_cont_SUBSET_MONO : thm
    val shift_bmap_SING : thm
    val slfv_SUBSET_ffv : thm
    val specslwtl : thm
    val specslwtl_ind : thm
    val thfVars_FAPPLY_IN_cont : thm
    val thfVars_slfv_cont_fVinsth : thm
    val thfVars_uniqify : thm
    val thfVars_vinsth : thm
    val tprpl_FUNION : thm
    val tprpl_fix : thm
    val trpl_tprpl : thm
    val uniqifn_DRESTRICT : thm
    val uniqifn_INJ : thm
    val uniqify_DRESTRICT : thm
    val vinst_case_SUBSET_lemma : thm
    val vinst_cont_DRESTRICT : thm
    val vinst_cont_UNION : thm
    val vinst_cont_is_cont : thm
    val vinst_cont_wf : thm
    val vinst_fVar_fVrn_eq_eq : thm
    val vinsth_DRESTRICT : thm
    val vinsth_DRESTRICT1 : thm
    val vinsth_case_SUBSET : thm
    val vinsth_case_precise_maps_ex : thm
    val wfabsap0_def : thm
    val wfabsap0_ind : thm
    val wfabsap0_specslwtl : thm
    val wfcfVmap_DRESTRICT : thm
    val wfcod_o_vmap : thm
    val wffVmap_fVar_subfm_LENGTH : thm
    val wffVmap_ofFMAP_var_wf : thm
    val wfvmap_DRESTRICT : thm
  
  val Pf0Drv_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [PfDrv] Parent theory of "Pf0Drv"
   
   [Pf0Drv_def]  Definition
      
      ⊢ ∀Σ aths th. Pf0Drv Σ aths th ⇔ ∃pf0. Pf0 Σ aths pf0 ∧ MEM th pf0
   
   [Pf0_def]  Definition
      
      ⊢ Pf0 =
        (λΣ aths a0.
             ∀Pf0'.
               (∀a0.
                  (∃ath. a0 = [ath] ∧ ath ∈ aths) ∨
                  (∃b sl Pf0s eqths.
                     a0 =
                     FLAT (map2list (LENGTH sl − 1) Pf0s) ⧺
                     [fcong (map2list (LENGTH sl − 1) eqths) sl b] ∧
                     sl ≠ [] ∧
                     (∀n. n < LENGTH sl ⇒
                          is_EQ (concl (eqths n)) ∧ Pf0' (Pf0s n) ∧
                          MEM (eqths n) (Pf0s n) ∧
                          sort_of (Leq (concl (eqths n))) = EL n sl) ∧
                     (∀s. MEM s sl ⇒ wfs (FST Σ) s) ∧ wff Σ (FALLL sl b) ∧
                     is_cfm b) ∨
                  (∃pf th vσ.
                     a0 = pf ⧺ [vinsth vσ th] ∧ Pf0' pf ∧ MEM th pf ∧
                     wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ) ∨
                  (∃Γ A pf x s f.
                     a0 = pf ⧺ [gen (x,s) (Γ,A,f)] ∧ Pf0' pf ∧
                     MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
                     (x,s) ∉ genavds (Γ,A,f)) ∨
                  (∃Γ A pf s f t.
                     a0 = pf ⧺ [spec t (Γ,A,FALL s f)] ∧ Pf0' pf ∧
                     MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧ sort_of t = s) ∨
                  (∃Γ A pf f.
                     a0 = pf ⧺ [(Γ,A,f)] ∧ Pf0' pf ∧
                     MEM (Γ,A ∪ {NEG f},False) pf) ∨
                  (∃Γ A pf f.
                     a0 = pf ⧺ [(Γ ∪ ffv f,A,f)] ∧ Pf0' pf ∧
                     MEM (Γ,A,False) pf ∧ wff Σ f ∧ is_cfm f) ∨
                  (∃c. a0 = [assume c] ∧ wff Σ c ∧ is_cfm c) ∨
                  (∃Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
                     a0 = pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)] ∧ Pf0' pf1 ∧
                     Pf0' pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
                     MEM (Γ2,A2,f1) pf2) ∨
                  (∃pf th a.
                     a0 = pf ⧺ [disch a th] ∧ Pf0' pf ∧ MEM th pf ∧
                     wff Σ a ∧ is_cfm a) ∨
                  (∃t. a0 = [refl t] ∧ wft (FST Σ) t ∧
                       tsname t ∈ SND (SND Σ)) ∨
                  (∃Γ A pf t1 t2.
                     a0 = pf ⧺ [(Γ,A,EQ t2 t1)] ∧ Pf0' pf ∧
                     MEM (Γ,A,EQ t1 t2) pf) ∨
                  (∃Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
                     a0 = pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)] ∧
                     Pf0' pf1 ∧ Pf0' pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
                     MEM (Γ2,A2,EQ t2 t3) pf2) ∨
                  (∃s pf th n.
                     a0 = pf ⧺ [add_cont1 (n,s) th] ∧ Pf0' pf ∧ MEM th pf ∧
                     wfs (FST Σ) s) ⇒
                  Pf0' a0) ⇒
               Pf0' a0)
   
   [UCI_def]  Definition
      
      ⊢ ∀Σ f.
          UCI Σ f =
          {instf fσ vσ (ffVrn uσ f) |
           (fσ,vσ,uσ) |
           uniqifn uσ (fVars f) ∧
           IMAGE (λ(P,sl). (P,MAP (sinst vσ) sl)) (fVars f) ⊆ FDOM fσ ∧
           wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧ ffv f ⊆ FDOM vσ}
   
   [UCIth_def]  Definition
      
      ⊢ ∀Σ th.
          UCIth Σ th =
          {insth fσ vσ (uniqify uσ th) |
           (fσ,vσ,uσ) |
           uniqifn uσ (thfVars th) ∧
           IMAGE (λ(P,sl). (P,MAP (sinst vσ) sl)) (thfVars th) ⊆ FDOM fσ ∧
           wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧ cont th ⊆ FDOM vσ}
   
   [ax2th_def]  Definition
      
      ⊢ ∀ax. ax2th ax = (ffv ax,∅,ax)
   
   [fVrnwinst_def]  Definition
      
      ⊢ ∀vσ uσ1 hσ uσ2.
          fVrwinst vσ uσ1 hσ uσ2 =
          FUN_FMAP
            (λ(P,sl).
                 uσ1 '
                 (vinst_fVar vσ
                    (CHOICE
                       {(P0,sl0) |
                        (P,sl) =
                        vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P0,sl0)) ∧
                        (P0,sl0) ∈ FDOM uσ2})))
            (IMAGE (vinst_fVar (o_vmap hσ vσ) ∘ fVrn uσ2) (FDOM uσ2))
   
   [uniqify_def]  Definition
      
      ⊢ ∀uσ Γ A f. uniqify uσ (Γ,A,f) = (Γ,IMAGE (ffVrn uσ) A,ffVrn uσ f)
   
   [wfaths_def]  Definition
      
      ⊢ ∀Σf Σp Σe aths.
          wfaths (Σf,Σp,Σe) aths ⇔
          ∀Γ A f.
            (Γ,A,f) ∈ aths ⇒
            wff (Σf,Σp,Σe) f ∧ is_cfm f ∧
            (∀a. a ∈ A ⇒ wff (Σf,Σp,Σe) a ∧ is_cfm a) ∧
            (∀n s. (n,s) ∈ Γ ⇒ wfs Σf s) ∧ Uof ffv ({f} ∪ A) ⊆ Γ
   
   [wfsigaths_def]  Definition
      
      ⊢ ∀Σ aths. wfsigaths Σ aths ⇔ wfsig Σ ∧ wfaths Σ aths
   
   [EL_specslwtl]  Theorem
      
      ⊢ ∀n1 n tl sl.
          LENGTH tl = n1 ∧ n < LENGTH sl ∧ LENGTH sl = LENGTH tl ∧
          (∀t. MEM t tl ⇒ tbounds t = ∅) ⇒
          EL n (specslwtl tl sl) =
          (EL n tl,sprpl (mk_bmap (REVERSE (TAKE n tl))) (EL n sl))
   
   [FAPPLY_fVmap_fVrn1]  Theorem
      
      ⊢ ∀uσ σ.
          uniqifn uσ (FDOM σ) ⇒
          ∀fv. fv ∈ FDOM σ ⇒ fVmap_fVrn σ uσ ' (fVrn uσ fv) = σ ' fv
   
   [FAPPLY_fVrnwinst]  Theorem
      
      ⊢ uniqifn uσ2 (FDOM uσ2) ∧ (P,sl) ∈ FDOM uσ2 ⇒
        fVrwinst vσ uσ1 hσ uσ2 '
        (vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P,sl))) =
        uσ1 ' (vinst_fVar vσ (P,sl))
   
   [FAPPLY_mk_bmap_REVERSE_Lofeqthl]  Theorem
      
      ⊢ i ≤ n ⇒
        mk_bmap (REVERSE (Lofeqthl (map2list n eqths))) ' i =
        Leq (concl (eqths (n − i)))
   
   [FAPPLY_mk_bmap_REVERSE_Rofeqthl]  Theorem
      
      ⊢ i ≤ n ⇒
        mk_bmap (REVERSE (Rofeqthl (map2list n eqths))) ' i =
        Req (concl (eqths (n − i)))
   
   [FAPPLY_o_fVmap1']  Theorem
      
      ⊢ fv ∈ FDOM σ1 ⇒ o_fVmap σ2 σ1 ' fv = fVinst σ2 (σ1 ' fv)
   
   [FAPPLY_plainfV_bmap]  Theorem
      
      ⊢ ∀i. i < LENGTH r ⇒
            mk_bmap (REVERSE (MAP Bound (REVERSE (COUNT_LIST (LENGTH r))))) '
            i =
            Bound i
   
   [FAPPLY_vinst_fVmap1]  Theorem
      
      ⊢ ∀fv fσ vσ.
          fv ∈ FDOM fσ ∧ alluniq (FDOM fσ) ⇒
          vinst_fVmap vσ fσ ' (vinst_fVar vσ fv) = finst vσ (fσ ' fv)
   
   [FAPPLY_vinst_fVmap_fVmap_fVrn]  Theorem
      
      ⊢ (P,sl) ∈ FDOM σ ∧ (P,sl) ∈ FDOM uσf ∧ uniqifn uσf (FDOM σ) ⇒
        vinst_fVmap vσ (fVmap_fVrn σ uσf) '
        (vinst_fVar vσ (fVrn uσf (P,sl))) =
        finst vσ (σ ' (P,sl))
   
   [FAPPLY_vinst_fVmap_fVmap_fVrn1]  Theorem
      
      ⊢ ∀uσf vσ σ.
          fv ∈ FDOM σ ∧ fv ∈ FDOM uσf ∧ uniqifn uσf (FDOM σ) ⇒
          vinst_fVmap vσ (fVmap_fVrn σ uσf) ' (vinst_fVar vσ (fVrn uσf fv)) =
          finst vσ (σ ' fv)
   
   [FDOM_fVrnwinst]  Theorem
      
      ⊢ FDOM (fVrwinst vσ uσ1 hσ uσ2) =
        IMAGE (vinst_fVar (o_vmap hσ vσ) ∘ fVrn uσ2) (FDOM uσ2)
   
   [IMAGE_Uof]  Theorem
      
      ⊢ IMAGE f (Uof g s) = Uof (IMAGE f ∘ g) s
   
   [IMAGE_eq_lemma]  Theorem
      
      ⊢ (∀a. a ∈ A ⇒ f1 a = f2 a) ⇒ IMAGE f1 A = IMAGE f2 A
   
   [IMAGE_fVrn_fVars]  Theorem
      
      ⊢ IMAGE (fVrn uσf) ∘ fVars = fVars ∘ ffVrn uσf
   
   [IMAGE_fVrn_fVrwinst_vinst_fVar]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs th ∧ wfvmap (FST Σ) vσ ∧
        uniqifn uσ2 (thfVars th) ∧ uniqifn uσ1 (FDOM uσ1) ∧
        IMAGE (vinst_fVar vσ) (thfVars th) = FDOM uσ1 ∧
        FDOM uσ2 = thfVars th ∧ cont th = FDOM vσ ∧
        cont (vinsth vσ th) = FDOM hσ ⇒
        IMAGE
          (fVrn (fVrwinst vσ uσ1 hσ uσ2) ∘ vinst_fVar (o_vmap hσ vσ) ∘
           fVrn uσ2) (FDOM uσ2) ⊆
        IMAGE (vinst_fVar hσ) (IMAGE (fVrn uσ1) (FDOM uσ1))
   
   [IMAGE_vinst_fVar_fVars]  Theorem
      
      ⊢ IMAGE (vinst_fVar vσ) ∘ fVars = fVars ∘ finst vσ
   
   [IN_cont_FAPPLY_SUBSET_cont_vinst]  Theorem
      
      ⊢ x ∈ cont th ∧ x ∈ FDOM vσ ⇒ tfv (vσ ' x) ⊆ cont (vinsth vσ th)
   
   [IN_thfVars]  Theorem
      
      ⊢ ∀fv. fv ∈ thfVars (Γ,A,f) ⇔ ∃a. (a = f ∨ a ∈ A) ∧ fv ∈ fVars a
   
   [Pf0Drv_add_assum]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ ∀s th.
          FINITE s ⇒
          wfsigaths Σ aths ∧ (∀ϕ. ϕ ∈ s ⇒ wff Σ ϕ ∧ is_cfm ϕ) ∧
          Pf0Drv Σ aths th ⇒
          Pf0Drv Σ aths (add_assum s th)
   
   [Pf0Drv_add_cont]  Theorem
      
      ⊢ FINITE ct ∧ is_cont ct ⇒
        (∀n s. (n,s) ∈ ct ⇒ wfs (FST Σ) s) ∧ Pf0Drv Σ aths th ⇒
        Pf0Drv Σ aths (add_cont ct th)
   
   [Pf0Drv_add_cont0]  Theorem
      
      ⊢ ∀vs.
          FINITE vs ⇒
          (∀n s. (n,s) ∈ vs ⇒ wfs (FST Σ) s) ∧ Pf0Drv Σ aths th ⇒
          Pf0Drv Σ aths (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) vs) th)
   
   [Pf0Drv_add_cont1]  Theorem
      
      ⊢ Pf0Drv Σ aths th ⇒
        ∀n s. wfs (FST Σ) s ⇒ Pf0Drv Σ aths (add_cont1 (n,s) th)
   
   [Pf0Drv_assum_SUBSET]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaths Σ aths ∧ Pf0Drv Σ aths (Γ,A0,f) ∧ FINITE A ∧ A0 ⊆ A ∧
        (∀a. a ∈ A ⇒ wff Σ a ∧ is_cfm a) ⇒
        Pf0Drv Σ aths (Γ ∪ Uof ffv A,A,f)
   
   [Pf0Drv_assum_ffv_SUBSET]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaths Σ axs ⇒
        ∀Γ A f. Pf0Drv Σ axs (Γ,A,f) ⇒ ∀a. a ∈ A ⇒ ffv a ⊆ Γ
   
   [Pf0Drv_assume]  Theorem
      
      ⊢ ∀Σ aths c. wff Σ c ∧ is_cfm c ⇒ Pf0Drv Σ aths (assume c)
   
   [Pf0Drv_cfm]  Theorem
      
      ⊢ wfaths Σ aths ⇒
        ∀Γ A f. Pf0Drv Σ aths (Γ,A,f) ⇒ is_cfm f ∧ ∀a. a ∈ A ⇒ is_cfm a
   
   [Pf0Drv_concl_ffv_SUBSET]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaths Σ axs ⇒ ∀Γ A f. Pf0Drv Σ axs (Γ,A,f) ⇒ ffv f ⊆ Γ
   
   [Pf0Drv_cont_SUBSET]  Theorem
      
      ⊢ Pf0Drv Σ aths (Γ0,A,f) ∧ FINITE Γ ∧ Γ0 ⊆ Γ ∧ is_cont Γ ∧
        (∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s) ⇒
        Pf0Drv Σ aths (Γ,A,f)
   
   [Pf0Drv_cont_SUBSET_cong]  Theorem
      
      ⊢ Pf0Drv Σ aths (Γ0,A,f) ∧ FINITE Γ ∧ Γ0 ⊆ Γ ∧ is_cont Γ ∧
        (∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s) ∧ A = A' ∧ f = f' ⇒
        Pf0Drv Σ aths (Γ,A',f')
   
   [Pf0Drv_cont_wf]  Theorem
      
      ⊢ (∀Γ A f. (Γ,A,f) ∈ aths ⇒ ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s) ⇒
        ∀pf.
          Pf0 (Σf,Σp,Σe) aths pf ⇒
          ∀Γ A f. MEM (Γ,A,f) pf ⇒ ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s
   
   [Pf0Drv_cont_wf']  Theorem
      
      ⊢ (∀Γ A f. (Γ,A,f) ∈ aths ⇒ ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s) ⇒
        ∀Γ A f. Pf0Drv (Σf,Σp,Σe) aths (Γ,A,f) ⇒ ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s
   
   [Pf0Drv_disch]  Theorem
      
      ⊢ Pf0Drv Σ aths (Γ,A,f) ∧ wff Σ a ∧ is_cfm a ⇒
        Pf0Drv Σ aths (disch a (Γ,A,f))
   
   [Pf0Drv_double_neg]  Theorem
      
      ⊢ Pf0Drv Σ aths (Γ,A ∪ {NEG f},False) ⇒ Pf0Drv Σ aths (Γ,A,f)
   
   [Pf0Drv_ffv_SUBSET_cont]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaths Σ axs ⇒
        ∀Γ A f. Pf0Drv Σ axs (Γ,A,f) ⇒ Uof ffv ({f} ∪ A) ⊆ Γ
   
   [Pf0Drv_gen]  Theorem
      
      ⊢ Pf0Drv Σ aths (Γ,A,f) ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
        (x,s) ∉ genavds (Γ,A,f) ⇒
        Pf0Drv Σ aths (gen (x,s) (Γ,A,f))
   
   [Pf0Drv_mp]  Theorem
      
      ⊢ Pf0Drv Σ aths (Γ1,A1,IMP ϕ ψ) ∧ Pf0Drv Σ aths (Γ2,A2,ϕ) ⇒
        Pf0Drv Σ aths (Γ1 ∪ Γ2,A1 ∪ A2,ψ)
   
   [Pf0Drv_undisch]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaths Σ aths ⇒
        Pf0Drv Σ aths (Γ,A,IMP f1 f2) ⇒
        Pf0Drv Σ aths (Γ,A ∪ {f1},f2)
   
   [Pf0Drv_wff]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaths Σ axs ⇒
        ∀th.
          Pf0Drv Σ axs th ⇒ wff Σ (concl th) ∧ ∀a. a ∈ assum th ⇒ wff Σ a
   
   [Pf0Drv_wff1]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaths Σ aths ⇒
        ∀Γ A f. Pf0Drv Σ aths (Γ,A,f) ⇒ wff Σ f ∧ ∀a. a ∈ A ⇒ wff Σ a
   
   [Pf0_ALLE]  Theorem
      
      ⊢ ∀Σ aths Γ A pf s f t.
          Pf0 Σ aths pf ∧ MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧
          sort_of t = s ⇒
          Pf0 Σ aths (pf ⧺ [spec t (Γ,A,FALL s f)])
   
   [Pf0_ALLI]  Theorem
      
      ⊢ ∀Σ aths Γ A pf x s f.
          Pf0 Σ aths pf ∧ MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
          (x,s) ∉ genavds (Γ,A,f) ⇒
          Pf0 Σ aths (pf ⧺ [gen (x,s) (Γ,A,f)])
   
   [Pf0_AX]  Theorem
      
      ⊢ ∀Σ aths ath. ath ∈ aths ⇒ Pf0 Σ aths [ath]
   
   [Pf0_add_cont1]  Theorem
      
      ⊢ ∀Σ aths s pf th n.
          Pf0 Σ aths pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
          Pf0 Σ aths (pf ⧺ [add_cont1 (n,s) th])
   
   [Pf0_assume]  Theorem
      
      ⊢ ∀Σ aths c. wff Σ c ∧ is_cfm c ⇒ Pf0 Σ aths [assume c]
   
   [Pf0_cases]  Theorem
      
      ⊢ ∀Σ aths a0.
          Pf0 Σ aths a0 ⇔
          (∃ath. a0 = [ath] ∧ ath ∈ aths) ∨
          (∃b sl Pf0s eqths.
             a0 =
             FLAT (map2list (LENGTH sl − 1) Pf0s) ⧺
             [fcong (map2list (LENGTH sl − 1) eqths) sl b] ∧ sl ≠ [] ∧
             (∀n. n < LENGTH sl ⇒
                  is_EQ (concl (eqths n)) ∧ Pf0 Σ aths (Pf0s n) ∧
                  MEM (eqths n) (Pf0s n) ∧
                  sort_of (Leq (concl (eqths n))) = EL n sl) ∧
             (∀s. MEM s sl ⇒ wfs (FST Σ) s) ∧ wff Σ (FALLL sl b) ∧ is_cfm b) ∨
          (∃pf th vσ.
             a0 = pf ⧺ [vinsth vσ th] ∧ Pf0 Σ aths pf ∧ MEM th pf ∧
             wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ) ∨
          (∃Γ A pf x s f.
             a0 = pf ⧺ [gen (x,s) (Γ,A,f)] ∧ Pf0 Σ aths pf ∧
             MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
             (x,s) ∉ genavds (Γ,A,f)) ∨
          (∃Γ A pf s f t.
             a0 = pf ⧺ [spec t (Γ,A,FALL s f)] ∧ Pf0 Σ aths pf ∧
             MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧ sort_of t = s) ∨
          (∃Γ A pf f.
             a0 = pf ⧺ [(Γ,A,f)] ∧ Pf0 Σ aths pf ∧
             MEM (Γ,A ∪ {NEG f},False) pf) ∨
          (∃Γ A pf f.
             a0 = pf ⧺ [(Γ ∪ ffv f,A,f)] ∧ Pf0 Σ aths pf ∧
             MEM (Γ,A,False) pf ∧ wff Σ f ∧ is_cfm f) ∨
          (∃c. a0 = [assume c] ∧ wff Σ c ∧ is_cfm c) ∨
          (∃Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
             a0 = pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)] ∧ Pf0 Σ aths pf1 ∧
             Pf0 Σ aths pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
             MEM (Γ2,A2,f1) pf2) ∨
          (∃pf th a.
             a0 = pf ⧺ [disch a th] ∧ Pf0 Σ aths pf ∧ MEM th pf ∧ wff Σ a ∧
             is_cfm a) ∨
          (∃t. a0 = [refl t] ∧ wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ)) ∨
          (∃Γ A pf t1 t2.
             a0 = pf ⧺ [(Γ,A,EQ t2 t1)] ∧ Pf0 Σ aths pf ∧
             MEM (Γ,A,EQ t1 t2) pf) ∨
          (∃Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
             a0 = pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)] ∧
             Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
             MEM (Γ2,A2,EQ t2 t3) pf2) ∨
          ∃s pf th n.
            a0 = pf ⧺ [add_cont1 (n,s) th] ∧ Pf0 Σ aths pf ∧ MEM th pf ∧
            wfs (FST Σ) s
   
   [Pf0_cfm]  Theorem
      
      ⊢ wfaths (Σf,Σp,Σe) aths ⇒
        ∀pf.
          Pf0 (Σf,Σp,Σe) aths pf ⇒
          ∀Γ A f. MEM (Γ,A,f) pf ⇒ is_cfm f ∧ ∀a. a ∈ A ⇒ is_cfm a
   
   [Pf0_cong]  Theorem
      
      ⊢ ∀Σ aths b sl Pf0s eqths.
          sl ≠ [] ∧
          (∀n. n < LENGTH sl ⇒
               is_EQ (concl (eqths n)) ∧ Pf0 Σ aths (Pf0s n) ∧
               MEM (eqths n) (Pf0s n) ∧
               sort_of (Leq (concl (eqths n))) = EL n sl) ∧
          (∀s. MEM s sl ⇒ wfs (FST Σ) s) ∧ wff Σ (FALLL sl b) ∧ is_cfm b ⇒
          Pf0 Σ aths
            (FLAT (map2list (LENGTH sl − 1) Pf0s) ⧺
             [fcong (map2list (LENGTH sl − 1) eqths) sl b])
   
   [Pf0_cont_is_cont]  Theorem
      
      ⊢ (∀th. th ∈ aths ⇒ is_cont (cont th)) ⇒
        ∀pf. Pf0 Σ aths pf ⇒ ∀Γ A f. MEM (Γ,A,f) pf ⇒ is_cont Γ
   
   [Pf0_disch]  Theorem
      
      ⊢ ∀Σ aths pf th a.
          Pf0 Σ aths pf ∧ MEM th pf ∧ wff Σ a ∧ is_cfm a ⇒
          Pf0 Σ aths (pf ⧺ [disch a th])
   
   [Pf0_double_neg]  Theorem
      
      ⊢ ∀Σ aths Γ A pf f.
          Pf0 Σ aths pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒
          Pf0 Σ aths (pf ⧺ [(Γ,A,f)])
   
   [Pf0_ffv_SUBSET_wff]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsig (Σf,Σp,Σe) ∧ wfaths (Σf,Σp,Σe) aths ⇒
        ∀pf.
          Pf0 (Σf,Σp,Σe) aths pf ⇒
          ∀Γ A f.
            MEM (Γ,A,f) pf ⇒
            Uof ffv ({f} ∪ A) ⊆ Γ ∧ wff (Σf,Σp,Σe) f ∧
            ∀a. a ∈ A ⇒ wff (Σf,Σp,Σe) a
   
   [Pf0_fromBot]  Theorem
      
      ⊢ ∀Σ aths Γ A pf f.
          Pf0 Σ aths pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ∧ is_cfm f ⇒
          Pf0 Σ aths (pf ⧺ [(Γ ∪ ffv f,A,f)])
   
   [Pf0_ind]  Theorem
      
      ⊢ ∀Σ aths Pf0'.
          (∀ath. ath ∈ aths ⇒ Pf0' [ath]) ∧
          (∀b sl Pf0s eqths.
             sl ≠ [] ∧
             (∀n. n < LENGTH sl ⇒
                  is_EQ (concl (eqths n)) ∧ Pf0' (Pf0s n) ∧
                  MEM (eqths n) (Pf0s n) ∧
                  sort_of (Leq (concl (eqths n))) = EL n sl) ∧
             (∀s. MEM s sl ⇒ wfs (FST Σ) s) ∧ wff Σ (FALLL sl b) ∧ is_cfm b ⇒
             Pf0'
               (FLAT (map2list (LENGTH sl − 1) Pf0s) ⧺
                [fcong (map2list (LENGTH sl − 1) eqths) sl b])) ∧
          (∀pf th vσ.
             Pf0' pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ ⇒
             Pf0' (pf ⧺ [vinsth vσ th])) ∧
          (∀Γ A pf x s f.
             Pf0' pf ∧ MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
             (x,s) ∉ genavds (Γ,A,f) ⇒
             Pf0' (pf ⧺ [gen (x,s) (Γ,A,f)])) ∧
          (∀Γ A pf s f t.
             Pf0' pf ∧ MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧
             sort_of t = s ⇒
             Pf0' (pf ⧺ [spec t (Γ,A,FALL s f)])) ∧
          (∀Γ A pf f.
             Pf0' pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒ Pf0' (pf ⧺ [(Γ,A,f)])) ∧
          (∀Γ A pf f.
             Pf0' pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ∧ is_cfm f ⇒
             Pf0' (pf ⧺ [(Γ ∪ ffv f,A,f)])) ∧
          (∀c. wff Σ c ∧ is_cfm c ⇒ Pf0' [assume c]) ∧
          (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
             Pf0' pf1 ∧ Pf0' pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
             MEM (Γ2,A2,f1) pf2 ⇒
             Pf0' (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)])) ∧
          (∀pf th a.
             Pf0' pf ∧ MEM th pf ∧ wff Σ a ∧ is_cfm a ⇒
             Pf0' (pf ⧺ [disch a th])) ∧
          (∀t. wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ) ⇒ Pf0' [refl t]) ∧
          (∀Γ A pf t1 t2.
             Pf0' pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒ Pf0' (pf ⧺ [(Γ,A,EQ t2 t1)])) ∧
          (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
             Pf0' pf1 ∧ Pf0' pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
             MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
             Pf0' (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
          (∀s pf th n.
             Pf0' pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
             Pf0' (pf ⧺ [add_cont1 (n,s) th])) ⇒
          ∀a0. Pf0 Σ aths a0 ⇒ Pf0' a0
   
   [Pf0_mp]  Theorem
      
      ⊢ ∀Σ aths Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
          Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
          MEM (Γ2,A2,f1) pf2 ⇒
          Pf0 Σ aths (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)])
   
   [Pf0_refl]  Theorem
      
      ⊢ ∀Σ aths t.
          wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ) ⇒ Pf0 Σ aths [refl t]
   
   [Pf0_rules]  Theorem
      
      ⊢ ∀Σ aths.
          (∀ath. ath ∈ aths ⇒ Pf0 Σ aths [ath]) ∧
          (∀b sl Pf0s eqths.
             sl ≠ [] ∧
             (∀n. n < LENGTH sl ⇒
                  is_EQ (concl (eqths n)) ∧ Pf0 Σ aths (Pf0s n) ∧
                  MEM (eqths n) (Pf0s n) ∧
                  sort_of (Leq (concl (eqths n))) = EL n sl) ∧
             (∀s. MEM s sl ⇒ wfs (FST Σ) s) ∧ wff Σ (FALLL sl b) ∧ is_cfm b ⇒
             Pf0 Σ aths
               (FLAT (map2list (LENGTH sl − 1) Pf0s) ⧺
                [fcong (map2list (LENGTH sl − 1) eqths) sl b])) ∧
          (∀pf th vσ.
             Pf0 Σ aths pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧
             cont th ⊆ FDOM vσ ⇒
             Pf0 Σ aths (pf ⧺ [vinsth vσ th])) ∧
          (∀Γ A pf x s f.
             Pf0 Σ aths pf ∧ MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
             (x,s) ∉ genavds (Γ,A,f) ⇒
             Pf0 Σ aths (pf ⧺ [gen (x,s) (Γ,A,f)])) ∧
          (∀Γ A pf s f t.
             Pf0 Σ aths pf ∧ MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧
             sort_of t = s ⇒
             Pf0 Σ aths (pf ⧺ [spec t (Γ,A,FALL s f)])) ∧
          (∀Γ A pf f.
             Pf0 Σ aths pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒
             Pf0 Σ aths (pf ⧺ [(Γ,A,f)])) ∧
          (∀Γ A pf f.
             Pf0 Σ aths pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ∧ is_cfm f ⇒
             Pf0 Σ aths (pf ⧺ [(Γ ∪ ffv f,A,f)])) ∧
          (∀c. wff Σ c ∧ is_cfm c ⇒ Pf0 Σ aths [assume c]) ∧
          (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
             Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
             MEM (Γ2,A2,f1) pf2 ⇒
             Pf0 Σ aths (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)])) ∧
          (∀pf th a.
             Pf0 Σ aths pf ∧ MEM th pf ∧ wff Σ a ∧ is_cfm a ⇒
             Pf0 Σ aths (pf ⧺ [disch a th])) ∧
          (∀t. wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ) ⇒ Pf0 Σ aths [refl t]) ∧
          (∀Γ A pf t1 t2.
             Pf0 Σ aths pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
             Pf0 Σ aths (pf ⧺ [(Γ,A,EQ t2 t1)])) ∧
          (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
             Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
             MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
             Pf0 Σ aths (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
          ∀s pf th n.
            Pf0 Σ aths pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
            Pf0 Σ aths (pf ⧺ [add_cont1 (n,s) th])
   
   [Pf0_strongind]  Theorem
      
      ⊢ ∀Σ aths Pf0'.
          (∀ath. ath ∈ aths ⇒ Pf0' [ath]) ∧
          (∀b sl Pf0s eqths.
             sl ≠ [] ∧
             (∀n. n < LENGTH sl ⇒
                  is_EQ (concl (eqths n)) ∧ Pf0 Σ aths (Pf0s n) ∧
                  Pf0' (Pf0s n) ∧ MEM (eqths n) (Pf0s n) ∧
                  sort_of (Leq (concl (eqths n))) = EL n sl) ∧
             (∀s. MEM s sl ⇒ wfs (FST Σ) s) ∧ wff Σ (FALLL sl b) ∧ is_cfm b ⇒
             Pf0'
               (FLAT (map2list (LENGTH sl − 1) Pf0s) ⧺
                [fcong (map2list (LENGTH sl − 1) eqths) sl b])) ∧
          (∀pf th vσ.
             Pf0 Σ aths pf ∧ Pf0' pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧
             cont th ⊆ FDOM vσ ⇒
             Pf0' (pf ⧺ [vinsth vσ th])) ∧
          (∀Γ A pf x s f.
             Pf0 Σ aths pf ∧ Pf0' pf ∧ MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧
             sfv s ⊆ Γ ∧ (x,s) ∉ genavds (Γ,A,f) ⇒
             Pf0' (pf ⧺ [gen (x,s) (Γ,A,f)])) ∧
          (∀Γ A pf s f t.
             Pf0 Σ aths pf ∧ Pf0' pf ∧ MEM (Γ,A,FALL s f) pf ∧
             wft (FST Σ) t ∧ sort_of t = s ⇒
             Pf0' (pf ⧺ [spec t (Γ,A,FALL s f)])) ∧
          (∀Γ A pf f.
             Pf0 Σ aths pf ∧ Pf0' pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒
             Pf0' (pf ⧺ [(Γ,A,f)])) ∧
          (∀Γ A pf f.
             Pf0 Σ aths pf ∧ Pf0' pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ∧
             is_cfm f ⇒
             Pf0' (pf ⧺ [(Γ ∪ ffv f,A,f)])) ∧
          (∀c. wff Σ c ∧ is_cfm c ⇒ Pf0' [assume c]) ∧
          (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
             Pf0 Σ aths pf1 ∧ Pf0' pf1 ∧ Pf0 Σ aths pf2 ∧ Pf0' pf2 ∧
             MEM (Γ1,A1,IMP f1 f2) pf1 ∧ MEM (Γ2,A2,f1) pf2 ⇒
             Pf0' (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)])) ∧
          (∀pf th a.
             Pf0 Σ aths pf ∧ Pf0' pf ∧ MEM th pf ∧ wff Σ a ∧ is_cfm a ⇒
             Pf0' (pf ⧺ [disch a th])) ∧
          (∀t. wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ) ⇒ Pf0' [refl t]) ∧
          (∀Γ A pf t1 t2.
             Pf0 Σ aths pf ∧ Pf0' pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
             Pf0' (pf ⧺ [(Γ,A,EQ t2 t1)])) ∧
          (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
             Pf0 Σ aths pf1 ∧ Pf0' pf1 ∧ Pf0 Σ aths pf2 ∧ Pf0' pf2 ∧
             MEM (Γ1,A1,EQ t1 t2) pf1 ∧ MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
             Pf0' (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
          (∀s pf th n.
             Pf0 Σ aths pf ∧ Pf0' pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
             Pf0' (pf ⧺ [add_cont1 (n,s) th])) ⇒
          ∀a0. Pf0 Σ aths a0 ⇒ Pf0' a0
   
   [Pf0_sym]  Theorem
      
      ⊢ ∀Σ aths Γ A pf t1 t2.
          Pf0 Σ aths pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
          Pf0 Σ aths (pf ⧺ [(Γ,A,EQ t2 t1)])
   
   [Pf0_trans]  Theorem
      
      ⊢ ∀Σ aths Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
          Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
          MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
          Pf0 Σ aths (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])
   
   [Pf0_vinsth]  Theorem
      
      ⊢ ∀Σ aths pf th vσ.
          Pf0 Σ aths pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ ⇒
          Pf0 Σ aths (pf ⧺ [vinsth vσ th])
   
   [Pf0_wff]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaths Σ axs ⇒
        ∀pf.
          Pf0 Σ axs pf ⇒
          ∀Γ A f. MEM (Γ,A,f) pf ⇒ wff Σ f ∧ ∀a. a ∈ A ⇒ wff Σ a
   
   [Pf2Pf0_fVinsth_lemma]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ ∀uσ.
          wffsig Σf ∧ wff (Σf,Σp,Σe) f ∧ uniqifn uσf (FDOM fσ) ∧
          wffVmap (Σf,Σp,Σe) fσ ∧ fVars f ⊆ FDOM fσ ∧
          wfcfVmap (Σf,Σp,Σe) σ ∧ wfvmap Σf vσ ∧
          ffv f ∪ ffv (fVinst fσ f) ⊆ FDOM vσ ⇒
          fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))) =
          fVinst
            (o_fVmap σ
               (vinst_fVmap vσ
                  (fVmap_fVrn
                     (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
            (finst vσ (ffVrn uσf f))
   
   [Pf2Pf0_vinst_lemma]  Theorem
      
      ⊢ ∀f. uniqifn uσ2 (FDOM uσ2) ∧ fVars f ⊆ FDOM uσ2 ∧
            IMAGE (vinst_fVar vσ) (fVars f) ⊆ FDOM uσ1 ∧ ffv f ⊆ FDOM vσ ∧
            ffv (finst vσ f) ⊆ FDOM hσ ⇒
            finst hσ (ffVrn uσ1 (finst vσ f)) =
            ffVrn (fVrwinst vσ uσ1 hσ uσ2)
              (finst (o_vmap hσ vσ) (ffVrn uσ2 f))
   
   [PfDrv_assum_wff]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒ ∀th. PfDrv Σ axs (Γ,A,f) ⇒ ∀a. a ∈ A ⇒ wff Σ a
   
   [PfDrv_concl_wff]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒ ∀th. PfDrv Σ axs (Γ,A,f) ⇒ wff Σ f
   
   [PfDrv_cont_FINITE]  Theorem
      
      ⊢ ∀pf. Pf Σ axs pf ⇒ ∀th. MEM th pf ⇒ FINITE (cont th)
   
   [PfDrv_cont_is_cont]  Theorem
      
      ⊢ ∀th. PfDrv Σ axs th ⇒ is_cont (cont th)
   
   [PfDrv_fVinsth]  Theorem
      
      ⊢ ∀th.
          PfDrv Σ axs th ∧ wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ⇒
          PfDrv Σ axs (fVinsth fσ th)
   
   [PfDrv_slfv_SUBSET_cont]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ,A,f) ⇒ Uof fVslfv ({f} ∪ A) ⊆ Γ
   
   [PfDrv_uniqify]  Theorem
      
      [oracles: cheat] [axioms: ] []
      ⊢ PfDrv Σ axs th ⇒ ∀uσ. PfDrv Σ axs (uniqify uσ th)
   
   [PfDrv_vinsth]  Theorem
      
      ⊢ ∀Σ axs th vσ.
          PfDrv Σ axs th ∧ wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ ⇒
          PfDrv Σ axs (vinsth vσ th)
   
   [Pf_assum_FINITE]  Theorem
      
      ⊢ ∀pf. Pf Σ axs pf ⇒ ∀Γ A f. MEM (Γ,A,f) pf ⇒ FINITE A
   
   [SUBSET_thfVars]  Theorem
      
      ⊢ fVars f ⊆ thfVars (Γ,A,f) ∧ ∀a. a ∈ A ⇒ fVars a ⊆ thfVars (Γ,A,f)
   
   [Uof_FINITE_lemma]  Theorem
      
      ⊢ FINITE A ∧ (∀a. a ∈ A ⇒ FINITE (f a)) ⇒ FINITE (Uof f A)
   
   [Uof_IMAGE]  Theorem
      
      ⊢ Uof f (IMAGE g s) = Uof (f ∘ g) s
   
   [Uof_concl_assum_SUBSET_cont]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs th ⇒
        Uof ffv ({concl th} ∪ assum th) ⊆ cont th
   
   [Uof_fVars_finst_ffVrn]  Theorem
      
      ⊢ Uof (fVars ∘ finst vσ ∘ ffVrn uσf) A =
        Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) ∘ fVars) A
   
   [Uof_ffv_uniqify]  Theorem
      
      ⊢ Uof ffv ({concl (uniqify uσ th)} ∪ assum (uniqify uσ th)) =
        Uof ffv ({concl th} ∪ assum th)
   
   [cfVmap_DRESTRICT]  Theorem
      
      ⊢ cfVmap σ ⇒ cfVmap (DRESTRICT σ s)
   
   [cfVmap_o_fVmap]  Theorem
      
      ⊢ cfVmap cσ ∧ ofFMAP fVars σ (FDOM σ) ⊆ FDOM cσ ⇒
        cfVmap (o_fVmap cσ σ)
   
   [cont_assum_concl]  Theorem
      
      ⊢ (cont th,assum th,concl th) = th
   
   [cont_fVinsth]  Theorem
      
      ⊢ cont th ⊆ cont (fVinsth fσ th)
   
   [cont_uniqify]  Theorem
      
      ⊢ cont (uniqify σ th) = cont th
   
   [cont_vinsth]  Theorem
      
      ⊢ cont (vinsth vσ th) = vinst_cont vσ (cont th)
   
   [ex_SUBSET_ofFMAP]  Theorem
      
      ⊢ ∀a. a ∈ A ∧ a ∈ FDOM σ ∧ X ⊆ f (σ ' a) ⇒ X ⊆ ofFMAP f σ A
   
   [fVars_FAPPLY_SUBSET_thfVars_fVinsth]  Theorem
      
      ⊢ fv ∈ thfVars th ∧ fv ∈ FDOM fσ ⇒
        fVars (fσ ' fv) ⊆ thfVars (fVinsth fσ th)
   
   [fVars_FINITE]  Theorem
      
      ⊢ ∀f. FINITE (fVars f)
   
   [fVinst_cfVmap_is_cfm]  Theorem
      
      ⊢ ∀f σ. cfVmap σ ∧ fVars f ⊆ FDOM σ ⇒ is_cfm (fVinst σ f)
   
   [fVinst_o_Vmap_finst_ffVrn]  Theorem
      
      ⊢ insth
          (o_fVmap σ
             (vinst_fVmap vσ
                (fVmap_fVrn
                   (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
          vσ (uniqify uσf (Γ,A,f)) =
        (vinst_cont vσ Γ ∪
         (ofFMAP ffv
            (o_fVmap σ
               (vinst_fVmap vσ
                  (fVmap_fVrn
                     (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
            (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) ∪
          ofFMAP ffv
            (o_fVmap σ
               (vinst_fVmap vσ
                  (fVmap_fVrn
                     (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
            (Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) ∘ fVars) A)),
         IMAGE
           (instf
              (o_fVmap σ
                 (vinst_fVmap vσ
                    (fVmap_fVrn
                       (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
              vσ ∘ ffVrn uσf) A,
         fVinst
           (o_fVmap σ
              (vinst_fVmap vσ
                 (fVmap_fVrn
                    (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
           (finst vσ (ffVrn uσf f)))
   
   [fVinst_plainfV]  Theorem
      
      ⊢ fv ∈ FDOM fσ ⇒ fVinst fσ (plainfV fv) = fσ ' fv
   
   [fVinst_subset_lemma]  Theorem
      
      ⊢ PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ∧ wffVmap Σ fσ ∧ wffVmap Σ σ ∧
        wfvmap (FST Σ) vσ ∧
        (∀fv. fv ∈ Uof fVars ({f} ∪ A) ⇒ ffv (fσ ' fv) ⊆ FDOM vσ) ∧
        uniqifn uσf (FDOM fσ) ∧ Uof fVars ({f} ∪ A) ⊆ FDOM fσ ⇒
        vinst_cont vσ Γ ∪
        (ofFMAP ffv
           (o_fVmap σ
              (vinst_fVmap vσ
                 (fVmap_fVrn
                    (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
           (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) ∪
         ofFMAP ffv
           (o_fVmap σ
              (vinst_fVmap vσ
                 (fVmap_fVrn
                    (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
           (Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) ∘ fVars) A)) ⊆
        vinst_cont vσ
          (Γ ∪ (ofFMAP ffv fσ (fVars f) ∪ ofFMAP ffv fσ (Uof fVars A))) ∪
        (ofFMAP ffv σ
           (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f)))) ∪
         ofFMAP ffv σ
           (Uof (IMAGE (vinst_fVar vσ) ∘ fVars)
              (IMAGE (ffVrn uσ ∘ fVinst fσ) A)))
   
   [fVinst_subset_lemma0]  Theorem
      
      ⊢ wffVmap Σ fσ ∧ wffVmap Σ σ ∧ wfvmap (FST Σ) vσ ∧
        (∀fv. fv ∈ fVars f ⇒ ffv (fσ ' fv) ⊆ FDOM vσ) ∧
        uniqifn uσf (FDOM fσ) ∧ fVars f ⊆ FDOM fσ ⇒
        Uof ffv
          (IMAGE
             (fVinst σ ∘
              $'
                (vinst_fVmap vσ
                   (fVmap_fVrn
                      (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
             (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f))) ⊆
        vinst_cont vσ (ffv f) ∪ vinst_cont vσ (ofFMAP ffv fσ (fVars f)) ∪
        ofFMAP ffv σ
          (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f))))
   
   [fVinsth_DRESTRICT]  Theorem
      
      ⊢ fVinsth (DRESTRICT fσ (thfVars th)) th = fVinsth fσ th
   
   [fVrn_fVrwinst]  Theorem
      
      ⊢ (P,sl) ∈ FDOM uσ2 ∧ uniqifn uσ2 (FDOM uσ2) ⇒
        fVrn (fVrwinst vσ uσ1 hσ uσ2)
          (vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P,sl))) =
        (uσ1 ' (vinst_fVar vσ (P,sl)),MAP (sinst (o_vmap hσ vσ)) sl)
   
   [ffVrn_eq]  Theorem
      
      ⊢ ∀f σ1 σ2.
          DRESTRICT σ1 (fVars f) = DRESTRICT σ2 (fVars f) ⇒
          ffVrn σ1 f = ffVrn σ2 f
   
   [ffVrn_eq1]  Theorem
      
      ⊢ ∀f σ1 σ2.
          FDOM σ1 ∩ fVars f = FDOM σ2 ∩ fVars f ∧
          (∀fv. fv ∈ fVars f ⇒ σ1 ' fv = σ2 ' fv) ⇒
          ffVrn σ1 f = ffVrn σ2 f
   
   [ffv_SUBSET_cont_fVinsth]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ,A,f) ⇒
        ffv f ⊆ cont (fVinsth fσ (Γ,A,f))
   
   [ffv_assum_SUBSET_cont_fVinsth]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ,A,f) ⇒
        ∀a. a ∈ A ⇒ ffv a ⊆ cont (fVinsth fσ (Γ,A,f))
   
   [ffv_ffVinst_SUBSET_cont_fVinsth]  Theorem
      
      ⊢ PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ∧ wffVmap Σ fσ ∧
        thfVars (Γ,A,f) ⊆ FDOM fσ ⇒
        ffv f ∪ ffv (fVinst fσ f) ⊆ cont (fVinsth fσ (Γ,A,f))
   
   [ffv_finst_ffVrn]  Theorem
      
      ⊢ ffv (finst σ (ffVrn uσ f)) = ffv (finst σ f)
   
   [fprpl_fix]  Theorem
      
      ⊢ ∀f bmap.
          (∀i. i ∈ FDOM bmap ⇒ bmap ' i = Bound i) ⇒ fprpl bmap f = f
   
   [gen_precise_maps_ex]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ Pf Σ axs pf ∧ MEM th pf ∧ wfvmap (FST Σ) hσ ∧
        wfcfVmap Σ fσ ∧ thfVars (vinsth hσ (uniqify uσ th)) ⊆ FDOM fσ ∧
        cont th ⊆ FDOM hσ ∧ uniqifn uσ (thfVars th) ⇒
        ∃uσ1 hσ1 fσ1.
          wfvmap (FST Σ) hσ1 ∧ wfcfVmap Σ fσ1 ∧
          thfVars (vinsth hσ1 (uniqify uσ1 th)) = FDOM fσ1 ∧
          cont th = FDOM hσ1 ∧ uniqifn uσ1 (thfVars th) ∧
          thfVars th = FDOM uσ1 ∧
          insth fσ hσ (uniqify uσ th) = insth fσ1 hσ1 (uniqify uσ1 th)
   
   [insth_uniqify_fVinsth]  Theorem
      
      ⊢ insth σ vσ (uniqify uσ (fVinsth fσ (Γ,A,f))) =
        (vinst_cont vσ
           (Γ ∪ (ofFMAP ffv fσ (fVars f) ∪ ofFMAP ffv fσ (Uof fVars A))) ∪
         (ofFMAP ffv σ
            (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f)))) ∪
          ofFMAP ffv σ
            (Uof (IMAGE (vinst_fVar vσ) ∘ fVars)
               (IMAGE (ffVrn uσ ∘ fVinst fσ) A))),
         IMAGE (fVinst σ ∘ finst vσ ∘ ffVrn uσ ∘ fVinst fσ) A,
         fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))))
   
   [is_cfm_EQ]  Theorem
      
      ⊢ is_cfm (EQ t1 t2)
   
   [is_cfm_IFF]  Theorem
      
      ⊢ is_cfm (IFF f1 f2) ⇔ is_cfm f1 ∧ is_cfm f2
   
   [is_cfm_NEG]  Theorem
      
      ⊢ ∀f. is_cfm (NEG f) ⇔ is_cfm f
   
   [is_cfm_fabs]  Theorem
      
      ⊢ ∀f i. is_cfm (fabs v i f) ⇔ is_cfm f
   
   [is_cfm_finst]  Theorem
      
      ⊢ is_cfm (finst σ f) ⇔ is_cfm f
   
   [is_cfm_fprpl]  Theorem
      
      ⊢ ∀f bmap. is_cfm (fprpl bmap f) ⇔ is_cfm f
   
   [is_cfm_frpl]  Theorem
      
      ⊢ ∀f i. is_cfm (frpl i v f) ⇔ is_cfm f
   
   [main_fVinst_case]  Theorem
      
      [oracles: DISK_THM, cheat] [axioms: ] []
      ⊢ wfsigaxs Σ axs ∧ Pf Σ axs pf ∧
        Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ⇒
        (∀th.
           MEM th pf ⇒
           ∀vσ fσ uσ.
             wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
             thfVars (vinsth vσ (uniqify uσ th)) ⊆ FDOM fσ ∧
             cont th ⊆ FDOM vσ ∧ uniqifn uσ (thfVars th) ⇒
             Pf0Drv Σ aths (insth fσ vσ (uniqify uσ th))) ∧ MEM th pf ∧
        wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ∧
        Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ∧ wfvmap (FST Σ) vσ ∧
        wfcfVmap Σ fσ' ∧
        thfVars (vinsth vσ (uniqify uσ (fVinsth fσ th))) ⊆ FDOM fσ' ∧
        cont (fVinsth fσ th) ⊆ FDOM vσ ∧
        uniqifn uσ (thfVars (fVinsth fσ th)) ⇒
        Pf0Drv Σ aths (insth fσ' vσ (uniqify uσ (fVinsth fσ th)))
   
   [mk_bmap_BIGUNION]  Theorem
      
      ⊢ ∀l ϕ.
          BIGUNION
            {tfv (mk_bmap l ' i) | i | i ∈ count (LENGTH l) ∩ fbounds ϕ} ⊆
          Uof tfv (set l)
   
   [ofFMAP_DRESTRICT]  Theorem
      
      ⊢ s ⊆ A ⇒ ofFMAP f (DRESTRICT σ A) s = ofFMAP f σ s
   
   [ofFMAP_FINITE]  Theorem
      
      ⊢ FINITE A ∧ (∀a. a ∈ A ∧ a ∈ FDOM σ ⇒ FINITE (f (σ ' a))) ⇒
        FINITE (ofFMAP f σ A)
   
   [ofFMAP_IMAGE]  Theorem
      
      ⊢ ofFMAP f σ (IMAGE g s) = Uof (f ∘ $' σ) (FDOM σ ∩ IMAGE g s)
   
   [ofFMAP_SUBSET]  Theorem
      
      ⊢ ofFMAP f σ A ⊆ B ⇔ ∀a. a ∈ A ∧ a ∈ FDOM σ ⇒ f (σ ' a) ⊆ B
   
   [ofFMAP_SUBSET_UNION_lemma]  Theorem
      
      ⊢ ofFMAP f σ1 A ⊆ ofFMAP g σ2 C ∧ ofFMAP f σ1 B ⊆ ofFMAP g σ2 D ⇒
        ofFMAP f σ1 (A ∪ B) ⊆ ofFMAP g σ2 (C ∪ D)
   
   [ofFMAP_Uof]  Theorem
      
      ⊢ ofFMAP f σ s = Uof f (IMAGE ($' σ) (FDOM σ ∩ s))
   
   [ofFMAP_Uof_SUBSET_lemma]  Theorem
      
      ⊢ (∀a. a ∈ A ⇒ ofFMAP f σ (g a) ⊆ B) ⇒ ofFMAP f σ (Uof g A) ⊆ B
   
   [ofFMAP_Uof_SUBSET_lemma2]  Theorem
      
      ⊢ (∀a. a ∈ s1 ⇒ ∃b. b ∈ s2 ∧ ofFMAP f σ1 (g a) ⊆ ofFMAP f σ2 (g b)) ⇒
        ofFMAP f σ1 (Uof g s1) ⊆ ofFMAP f σ2 (Uof g s2)
   
   [ofFMAP_as_IMAGE]  Theorem
      
      ⊢ ofFMAP f σ s = BIGUNION (IMAGE (f ∘ $' σ) (FDOM σ ∩ s))
   
   [ofFMAP_differ_2_SUBSET_lemma]  Theorem
      
      ⊢ (∀a. a ∈ A ∧ a ∈ FDOM σ1 ⇒
             ∃b. b ∈ B ∧ b ∈ FDOM σ2 ∧ σ1 ' a = σ2 ' b) ⇒
        ofFMAP f σ1 A ⊆ ofFMAP f σ2 B
   
   [ofFMAP_fVars_SUBSET_fVars_fVinst]  Theorem
      
      ⊢ ∀f. ofFMAP fVars σ (fVars f) ⊆ fVars (fVinst σ f)
   
   [ofFMAP_fVars_rn2fVmap]  Theorem
      
      ⊢ ofFMAP fVars (rn2fVmap uσ) A = IMAGE (fVrn uσ) (FDOM uσ ∩ A)
   
   [ofFMAP_ffv_is_cont]  Theorem
      
      ⊢ is_cont (ofFMAP ffv σ A)
   
   [ofFMAP_ffv_o_fVmap]  Theorem
      
      ⊢ ofFMAP ffv (o_fVmap σ2 σ1) s ⊆
        Uof ffv (IMAGE (fVinst σ2 ∘ $' σ1) (s ∩ FDOM σ1)) ∪
        Uof ffv (IMAGE ($' σ2) (s ∩ (FDOM σ2 DIFF FDOM σ1)))
   
   [ofFMAP_tfv_is_cont]  Theorem
      
      ⊢ is_cont (ofFMAP tfv σ A)
   
   [precise_maps_ex]  Theorem
      
      ⊢ ∀th fσ uσ vσ σ.
          PfDrv Σ axs th ∧ wfsigaxs Σ axs ⇒
          wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ∧ wfvmap (FST Σ) vσ ∧
          wfcfVmap Σ σ ∧
          thfVars (vinsth vσ (uniqify uσ (fVinsth fσ th))) ⊆ FDOM σ ∧
          cont (fVinsth fσ th) ⊆ FDOM vσ ∧
          uniqifn uσ (thfVars (fVinsth fσ th)) ⇒
          ∃fσ1 uσ1 vσ1 σ1.
            wffVmap Σ fσ1 ∧ thfVars th = FDOM fσ1 ∧ wfvmap (FST Σ) vσ1 ∧
            wfcfVmap Σ σ1 ∧
            thfVars (vinsth vσ1 (uniqify uσ1 (fVinsth fσ1 th))) = FDOM σ1 ∧
            cont (fVinsth fσ1 th) = FDOM vσ1 ∧
            uniqifn uσ1 (thfVars (fVinsth fσ1 th)) ∧
            thfVars (fVinsth fσ1 th) = FDOM uσ1 ∧
            insth σ vσ (uniqify uσ (fVinsth fσ th)) =
            insth σ1 vσ1 (uniqify uσ1 (fVinsth fσ1 th))
   
   [sfv_vinst_cont_SUBSET_MONO]  Theorem
      
      ⊢ wfvmap Σ vσ ∧ sfv s ⊆ ct ∧ ct ⊆ FDOM vσ ⇒
        sfv (sinst vσ s) ⊆ vinst_cont vσ ct
   
   [shift_bmap_SING]  Theorem
      
      ⊢ tbounds h = ∅ ⇒ shift_bmap n (mk_bmap [h]) ' n = h
   
   [slfv_SUBSET_ffv]  Theorem
      
      ⊢ (P,sl) ∈ fVars f ⇒ slfv sl ⊆ ffv f
   
   [specslwtl]  Theorem
      
      ⊢ specslwtl [] [] = [] ∧
        ∀tl t sl s.
          specslwtl (t::tl) (s::sl) = (t,s)::specslwtl tl (specsl 0 t sl)
   
   [specslwtl_ind]  Theorem
      
      ⊢ ∀P. P [] [] ∧
            (∀t tl s sl. P tl (specsl 0 t sl) ⇒ P (t::tl) (s::sl)) ∧
            (∀v6 v7. P [] (v6::v7)) ∧ (∀v10 v11. P (v10::v11) []) ⇒
            ∀v v1. P v v1
   
   [thfVars_FAPPLY_IN_cont]  Theorem
      
      ⊢ fv ∈ thfVars th ∧ fv ∈ FDOM fσ ⇒
        ffv (fσ ' fv) ⊆ cont (fVinsth fσ th)
   
   [thfVars_slfv_cont_fVinsth]  Theorem
      
      ⊢ PfDrv Σ axs th ∧ wfsigaxs Σ axs ∧ (P,sl) ∈ thfVars th ⇒
        slfv sl ⊆ cont (fVinsth fσ th)
   
   [thfVars_uniqify]  Theorem
      
      ⊢ thfVars (uniqify uσf th) = IMAGE (fVrn uσf) (thfVars th)
   
   [thfVars_vinsth]  Theorem
      
      ⊢ thfVars (vinsth vσ th) = IMAGE (vinst_fVar vσ) (thfVars th)
   
   [tprpl_FUNION]  Theorem
      
      ⊢ (∀tm bmap1 bmap2.
           (∀i. i ∈ FDOM bmap2 ∩ tbounds tm ⇒ tbounds (bmap2 ' i) = ∅) ∧
           FDOM bmap1 ∩ FDOM bmap2 = ∅ ⇒
           tprpl bmap1 (tprpl bmap2 tm) = tprpl (bmap1 ⊌ bmap2) tm) ∧
        ∀st bmap1 bmap2.
          (∀i. i ∈ FDOM bmap2 ∩ sbounds st ⇒ tbounds (bmap2 ' i) = ∅) ∧
          FDOM bmap1 ∩ FDOM bmap2 = ∅ ⇒
          sprpl bmap1 (sprpl bmap2 st) = sprpl (bmap1 ⊌ bmap2) st
   
   [tprpl_fix]  Theorem
      
      ⊢ (∀t bmap.
           (∀i. i ∈ FDOM bmap ⇒ bmap ' i = Bound i) ⇒ tprpl bmap t = t) ∧
        ∀s bmap.
          (∀i. i ∈ FDOM bmap ⇒ bmap ' i = Bound i) ⇒ sprpl bmap s = s
   
   [trpl_tprpl]  Theorem
      
      ⊢ (∀tm n t.
           tbounds t = ∅ ⇒
           trpl n t tm = tprpl (shift_bmap n (mk_bmap [t])) tm) ∧
        ∀st n t.
          tbounds t = ∅ ⇒
          srpl n t st = sprpl (shift_bmap n (mk_bmap [t])) st
   
   [uniqifn_DRESTRICT]  Theorem
      
      ⊢ uniqifn uσ A ⇒ uniqifn (DRESTRICT uσ A) A
   
   [uniqifn_INJ]  Theorem
      
      ⊢ uniqifn σ s ∧ fv1 ∈ s ∧ fv2 ∈ s ∧ σ ' fv1 = σ ' fv2 ⇒ fv1 = fv2
   
   [uniqify_DRESTRICT]  Theorem
      
      ⊢ thfVars th ⊆ s ⇒ uniqify (DRESTRICT uσ s) th = uniqify uσ th
   
   [vinst_case_SUBSET_lemma]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ,A,f) ∧ wfvmap (FST Σ) vσ ∧
        cont (Γ,A,f) = FDOM vσ ∧ wfvmap (FST Σ) hσ ∧ wfcfVmap Σ fσ ∧
        thfVars
          (vinst_cont hσ (vinst_cont vσ Γ),
           IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A)),
           finst hσ (ffVrn uσ1 (finst vσ f))) =
        FDOM fσ ∧
        cont (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM hσ ∧
        uniqifn uσ1 (FDOM uσ1) ∧
        thfVars (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM uσ1 ∧
        uniqifn uσ2 (thfVars (Γ,A,f)) ∧ FDOM uσ2 = thfVars (Γ,A,f) ⇒
        ∀a. a = f ∨ a ∈ A ⇒
            ofFMAP ffv (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
              (fVars (finst (o_vmap hσ vσ) (ffVrn uσ2 a))) ⊆
            ofFMAP ffv fσ (fVars (finst hσ (ffVrn uσ1 (finst vσ a))))
   
   [vinst_cont_DRESTRICT]  Theorem
      
      ⊢ Γ ⊆ s ∧ s ⊆ FDOM vσ ⇒
        vinst_cont (DRESTRICT vσ s) Γ = vinst_cont vσ Γ
   
   [vinst_cont_UNION]  Theorem
      
      ⊢ vinst_cont vσ (A ∪ B) = vinst_cont vσ A ∪ vinst_cont vσ B
   
   [vinst_cont_is_cont]  Theorem
      
      ⊢ is_cont (vinst_cont vσ ct)
   
   [vinst_cont_wf]  Theorem
      
      ⊢ (∀n s. (n,s) ∈ ct ⇒ wfs Σf s) ∧ wfcod Σf vσ ⇒
        ∀n s. (n,s) ∈ vinst_cont vσ ct ⇒ wfs Σf s
   
   [vinst_fVar_fVrn_eq_eq]  Theorem
      
      ⊢ uniqifn uσf s ∧ x1 ∈ s ∧ x2 ∈ s ⇒
        ∀vσ.
          vinst_fVar vσ (fVrn uσf x1) = vinst_fVar vσ (fVrn uσf x2) ⇒
          x1 = x2
   
   [vinsth_DRESTRICT]  Theorem
      
      ⊢ Uof ffv ({f} ∪ A) ⊆ s ∧ Γ ⊆ s ∧ s ⊆ FDOM vσ ⇒
        vinsth (DRESTRICT vσ s) (Γ,A,f) = vinsth vσ (Γ,A,f)
   
   [vinsth_DRESTRICT1]  Theorem
      
      ⊢ Uof ffv ({concl th} ∪ assum th) ⊆ s ∧ cont th ⊆ s ∧ s ⊆ FDOM vσ ⇒
        vinsth (DRESTRICT vσ s) th = vinsth vσ th
   
   [vinsth_case_SUBSET]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ,A,f) ∧ wfvmap (FST Σ) vσ ∧
        cont (Γ,A,f) = FDOM vσ ∧ wfvmap (FST Σ) hσ ∧ wfcfVmap Σ fσ ∧
        thfVars
          (vinst_cont hσ (vinst_cont vσ Γ),
           IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A)),
           finst hσ (ffVrn uσ1 (finst vσ f))) =
        FDOM fσ ∧
        cont (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM hσ ∧
        uniqifn uσ1 (FDOM uσ1) ∧
        thfVars (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM uσ1 ∧
        uniqifn uσ2 (thfVars (Γ,A,f)) ∧ FDOM uσ2 = thfVars (Γ,A,f) ⇒
        vinst_cont (o_vmap hσ vσ) Γ ∪
        ofFMAP ffv (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
          (Uof fVars
             ({finst (o_vmap hσ vσ) (ffVrn uσ2 f)} ∪
              IMAGE (finst (o_vmap hσ vσ)) (IMAGE (ffVrn uσ2) A))) ⊆
        vinst_cont hσ (vinst_cont vσ Γ) ∪
        ofFMAP ffv fσ
          (Uof fVars
             ({finst hσ (ffVrn uσ1 (finst vσ f))} ∪
              IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A))))
   
   [vinsth_case_precise_maps_ex]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ Pf Σ axs pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧
        cont th ⊆ FDOM vσ ∧ wfvmap (FST Σ) hσ ∧ wfcfVmap Σ fσ ∧
        thfVars (vinsth hσ (uniqify uσ (vinsth vσ th))) ⊆ FDOM fσ ∧
        cont (vinsth vσ th) ⊆ FDOM hσ ∧ uniqifn uσ (thfVars (vinsth vσ th)) ⇒
        ∃vσ1 uσ1 hσ1 fσ1.
          wfvmap (FST Σ) vσ1 ∧ cont th = FDOM vσ1 ∧ wfvmap (FST Σ) hσ1 ∧
          wfcfVmap Σ fσ1 ∧
          thfVars (vinsth hσ1 (uniqify uσ1 (vinsth vσ1 th))) = FDOM fσ1 ∧
          cont (vinsth vσ1 th) = FDOM hσ1 ∧
          uniqifn uσ1 (thfVars (vinsth vσ1 th)) ∧
          thfVars (vinsth vσ1 th) = FDOM uσ1 ∧
          insth fσ hσ (uniqify uσ (vinsth vσ th)) =
          insth fσ1 hσ1 (uniqify uσ1 (vinsth vσ1 th))
   
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
   
   [wfcfVmap_DRESTRICT]  Theorem
      
      ⊢ wfcfVmap Σ σ ⇒ wfcfVmap Σ (DRESTRICT σ s)
   
   [wfcod_o_vmap]  Theorem
      
      ⊢ wfcod Σ σ1 ∧ wfcod Σ σ2 ∧ cstt σ2 ∧ wffsig Σ ∧
        (∀x. x ∈ FDOM σ1 ⇒ tfv (σ1 ' x) ⊆ FDOM σ2) ⇒
        wfcod Σ (o_vmap σ2 σ1)
   
   [wffVmap_fVar_subfm_LENGTH]  Theorem
      
      ⊢ wffVmap Σ σ ⇒
        ∀fv.
          fv ∈ FDOM σ ⇒
          ∀P sl tl. fVar P sl tl ∈ subfm (σ ' fv) ⇒ LENGTH sl = LENGTH tl
   
   [wffVmap_ofFMAP_var_wf]  Theorem
      
      ⊢ wffVmap (Σf,Σp,Σe) σ ⇒ ∀n s A. (n,s) ∈ ofFMAP ffv σ A ⇒ wfs Σf s
   
   [wfvmap_DRESTRICT]  Theorem
      
      ⊢ wfvmap Σ vσ ⇒
        ∀s. s ⊆ FDOM vσ ∧ is_cont s ⇒ wfvmap Σ (DRESTRICT vσ s)
   
   
*)
end
