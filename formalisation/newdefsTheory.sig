signature newdefsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val CONJ_def : thm
    val DISJ_def : thm
    val EX_def : thm
    val IFF_def : thm
    val Lofeqths_def : thm
    val NEG_def : thm
    val Rofeqths_def : thm
    val True_def : thm
    val absapLs_def : thm
    val add_assum_def : thm
    val add_cont1_def : thm
    val add_cont_def : thm
    val alluniq_def : thm
    val assum_def : thm
    val assume_def : thm
    val cfVmap_def : thm
    val concl_def : thm
    val cont_def : thm
    val disch_def : thm
    val fVcong_def : thm
    val fVinsth_def : thm
    val fVmap_fVrn_def : thm
    val fVrn_def : thm
    val fcong_def : thm
    val ffVrn_def : thm
    val gen_def : thm
    val genavds_def : thm
    val instf_def : thm
    val insth_def : thm
    val is_cfm_def : thm
    val is_cth : thm
    val map2list : thm
    val o_fVmap_def : thm
    val plainfV_def : thm
    val refl_def : thm
    val rn2fVmap_def : thm
    val subfm_def : thm
    val sym_def_primitive : thm
    val thfVars_def : thm
    val undisch_def_primitive : thm
    val uniqifn_def : thm
    val vinst_bmap_def : thm
    val vinst_cont_def : thm
    val vinst_fVmap_def : thm
    val vinsth_def : thm
    val vsfv_def : thm
    val wfcfVmap_def : thm
    val wffsig_def : thm
    val wfvmap_def : thm
  
  (*  Theorems  *)
    val BIGUNION_IMAGE_Uof : thm
    val EL_map2list : thm
    val EMPTY_is_cont : thm
    val FALLL_components : thm
    val FALLL_fbounds : thm
    val FAPPLY_fVmap_fVrn : thm
    val FAPPLY_o_fVmap : thm
    val FAPPLY_o_fVmap1 : thm
    val FAPPLY_o_fVmap2 : thm
    val FAPPLY_rn2fVmap : thm
    val FAPPLY_vinst_bmap : thm
    val FAPPLY_vinst_fVmap : thm
    val FDOM_fVmap_fVrn : thm
    val FDOM_o_fVmap : thm
    val FDOM_rn2fVmap : thm
    val FDOM_vinst_bmap : thm
    val FDOM_vinst_fVmap : thm
    val IN_Uof : thm
    val IN_Uof_Uof : thm
    val IN_genavds : thm
    val IN_slfv' : thm
    val IN_vsfv : thm
    val LENGTH_LRofeqthl : thm
    val LENGTH_map2list : thm
    val MAP_tprpl_mk_bmap_REVERSE : thm
    val MEM_Lofeqthl_map2list : thm
    val MEM_Rofeqthl_map2list : thm
    val MEM_map2list : thm
    val NOTIN_genavds : thm
    val Uof_lemma_classic : thm
    val absapLs_fabs : thm
    val add_assum_EMPTY : thm
    val add_cont1_add_cont : thm
    val add_cont_EMPTY : thm
    val add_cont_UNION : thm
    val alluniq_EMPTY : thm
    val cont_decompose : thm
    val dest_eq_EQ : thm
    val fVar_FALLL_inc : thm
    val fVar_prpl_o_fVmap : thm
    val fVar_prpl_o_fVmap1 : thm
    val fVar_subfm_IN_absapLs : thm
    val fVars_ffVrn : thm
    val fVars_vinst : thm
    val fVinst_FALLL : thm
    val fVinst_ffVrn : thm
    val fVinst_fprpl : thm
    val fVslfv_fabs : thm
    val ffVrn_fVinst : thm
    val ffv_IFF : thm
    val ffv_NEG : thm
    val ffv_ffVrn : thm
    val ffv_finst_alt : thm
    val ffv_finst_wfvmap : thm
    val ffv_frpl : thm
    val ffv_frpl_SUBSET : thm
    val finst_FALLL : thm
    val finst_fprpl : thm
    val finst_o_vmap : thm
    val frpl_fprpl : thm
    val frpl_id : thm
    val instf_fVinst : thm
    val instf_fVinst_finst : thm
    val insth_instf : thm
    val is_cont_DELETE : thm
    val map2list_compute : thm
    val ofFMAP_SUBSET_MONO : thm
    val ofFMAP_SUBSET_ffv_fVinst : thm
    val shift_bmap_vinst_bmap : thm
    val spec_def : thm
    val spec_ind : thm
    val sym_def : thm
    val sym_ind : thm
    val tinst_tprpl : thm
    val trpl_tprpl : thm
    val tshift_tinst : thm
    val undisch_def : thm
    val undisch_ind : thm
    val uniqifn_FDOM_SUBSET : thm
    val uniqifn_SUBSET : thm
    val uniqifn_alluniq : thm
    val uniqifn_alluniq0 : thm
    val uniqifn_ex : thm
    val vinst_bmap_alt : thm
    val vinst_cont_EMPTY : thm
    val vinst_cont_UNION : thm
    val wfabsap_Lofeqthl_sl_NONNIL : thm
    val wffVmap_DRESTRICT : thm
    val wffVmap_fVmap_fVrn : thm
    val wffVmap_o_fVmap : thm
    val wffVmap_vinst_fVmap : thm
    val wff_FALL_alt : thm
    val wff_IMP : thm
    val wff_absapLs_eq : thm
    val wff_subfm_fVar_LENGTH : thm
    val wfvmap_IN_ofMAP_wfs : thm
    val wfvmap_presname : thm
  
  val newdefs_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [fVinst] Parent theory of "newdefs"
   
   [CONJ_def]  Definition
      
      ⊢ ∀f1 f2. CONJ f1 f2 = NEG (IMP f1 (NEG f2))
   
   [DISJ_def]  Definition
      
      ⊢ ∀f1 f2. DISJ f1 f2 = IMP (NEG f1) f2
   
   [EX_def]  Definition
      
      ⊢ ∀s b. EX s b = NEG (FALL s (NEG b))
   
   [IFF_def]  Definition
      
      ⊢ ∀f1 f2. IFF f1 f2 = CONJ (IMP f1 f2) (IMP f2 f1)
   
   [Lofeqths_def]  Definition
      
      ⊢ ∀eqthl. Lofeqthl eqthl = MAP (FST ∘ dest_eq ∘ concl) eqthl
   
   [NEG_def]  Definition
      
      ⊢ ∀f. NEG f = IMP f False
   
   [Rofeqths_def]  Definition
      
      ⊢ ∀eqthl. Rofeqthl eqthl = MAP (SND ∘ dest_eq ∘ concl) eqthl
   
   [True_def]  Definition
      
      ⊢ True = NEG False
   
   [absapLs_def]  Definition
      
      ⊢ absapLs False = ∅ ∧ (∀v0 v1. absapLs (Pred v0 v1) = ∅) ∧
        (∀f1 f2. absapLs (IMP f1 f2) = absapLs f1 ∪ absapLs f2) ∧
        (∀s b. absapLs (FALL s b) = absapLs b) ∧
        ∀P sl tl. absapLs (fVar P sl tl) = {(LENGTH sl,LENGTH tl)}
   
   [add_assum_def]  Definition
      
      ⊢ ∀s Γ A f. add_assum s (Γ,A,f) = (Γ ∪ Uof ffv s,A ∪ s,f)
   
   [add_cont1_def]  Definition
      
      ⊢ ∀n s Γ A f. add_cont1 (n,s) (Γ,A,f) = ({(n,s)} ∪ sfv s ∪ Γ,A,f)
   
   [add_cont_def]  Definition
      
      ⊢ ∀ct Γ A f. add_cont ct (Γ,A,f) = (ct ∪ Γ,A,f)
   
   [alluniq_def]  Definition
      
      ⊢ ∀fVs.
          alluniq fVs ⇔
          ∀P1 P2 sl1 sl2.
            (P1,sl1) ∈ fVs ∧ (P2,sl2) ∈ fVs ∧ sl1 ≠ sl2 ⇒ P1 ≠ P2
   
   [assum_def]  Definition
      
      ⊢ ∀Γ A f. assum (Γ,A,f) = A
   
   [assume_def]  Definition
      
      ⊢ ∀f. assume f = (ffv f,{f},f)
   
   [cfVmap_def]  Definition
      
      ⊢ ∀σ. cfVmap σ ⇔ ∀P sl. (P,sl) ∈ FDOM σ ⇒ is_cfm (σ ' (P,sl))
   
   [concl_def]  Definition
      
      ⊢ ∀Γ A f. concl (Γ,A,f) = f
   
   [cont_def]  Definition
      
      ⊢ ∀Γ A f. cont (Γ,A,f) = Γ
   
   [disch_def]  Definition
      
      ⊢ ∀a Γ A f. disch a (Γ,A,f) = (Γ ∪ ffv a,A DELETE a,IMP a f)
   
   [fVcong_def]  Definition
      
      ⊢ ∀eqthl P sl.
          fVcong eqthl P sl =
          (Uof cont (set eqthl),Uof assum (set eqthl),
           IFF (fVar P sl (Lofeqthl eqthl)) (fVar P sl (Rofeqthl eqthl)))
   
   [fVinsth_def]  Definition
      
      ⊢ ∀σf ct asm f.
          fVinsth σf (ct,asm,f) =
          (ct ∪ ofFMAP ffv σf (Uof fVars ({f} ∪ asm)),
           IMAGE (fVinst σf) asm,fVinst σf f)
   
   [fVmap_fVrn_def]  Definition
      
      ⊢ ∀σ uσ.
          fVmap_fVrn σ uσ =
          FUN_FMAP
            (λ(P,sl).
                 σ '
                 (CHOICE {(P0,sl) | uσ ' (P0,sl) = P ∧ (P0,sl) ∈ FDOM σ}))
            (IMAGE (fVrn uσ) (FDOM σ))
   
   [fVrn_def]  Definition
      
      ⊢ ∀uσ P sl.
          fVrn uσ (P,sl) =
          if (P,sl) ∈ FDOM uσ then (uσ ' (P,sl),sl) else (P,sl)
   
   [fcong_def]  Definition
      
      ⊢ ∀eqthl sl b.
          fcong eqthl sl b =
          (Uof cont (set eqthl) ∪ ffv b,Uof assum (set eqthl),
           IFF (fprpl (mk_bmap (REVERSE (Lofeqthl eqthl))) b)
             (fprpl (mk_bmap (REVERSE (Rofeqthl eqthl))) b))
   
   [ffVrn_def]  Definition
      
      ⊢ (∀uσ P sl tl.
           ffVrn uσ (fVar P sl tl) =
           if (P,sl) ∈ FDOM uσ then fVar (uσ ' (P,sl)) sl tl
           else fVar P sl tl) ∧
        (∀uσ f1 f2. ffVrn uσ (IMP f1 f2) = IMP (ffVrn uσ f1) (ffVrn uσ f2)) ∧
        (∀uσ s b. ffVrn uσ (FALL s b) = FALL s (ffVrn uσ b)) ∧
        (∀uσ p tl. ffVrn uσ (Pred p tl) = Pred p tl) ∧
        ∀uσ. ffVrn uσ False = False
   
   [gen_def]  Definition
      
      ⊢ ∀n s Γ A f. gen (n,s) (Γ,A,f) = (Γ DELETE (n,s),A,mk_FALL n s f)
   
   [genavds_def]  Definition
      
      ⊢ ∀th.
          genavds th =
          Uof (sfv ∘ SND) (cont th) ∪ Uof ffv (assum th) ∪
          Uof (slfv ∘ SND) (Uof fVars ({concl th} ∪ assum th))
   
   [instf_def]  Definition
      
      ⊢ ∀σf σv f. instf σf σv f = fVinst σf (finst σv f)
   
   [insth_def]  Definition
      
      ⊢ ∀σf σv th. insth σf σv th = fVinsth σf (vinsth σv th)
   
   [is_cfm_def]  Definition
      
      ⊢ (is_cfm False ⇔ T) ∧
        (∀f1 f2. is_cfm (IMP f1 f2) ⇔ is_cfm f1 ∧ is_cfm f2) ∧
        (∀v0 v1 v2. is_cfm (fVar v0 v1 v2) ⇔ F) ∧
        (∀v3 v4. is_cfm (Pred v3 v4) ⇔ T) ∧
        ∀s b. is_cfm (FALL s b) ⇔ is_cfm b
   
   [is_cth]  Definition
      
      ⊢ ∀Γ A f. is_cth (Γ,A,f) ⇔ is_cfm f ∧ ∀a. a ∈ A ⇒ is_cfm f
   
   [map2list]  Definition
      
      ⊢ (∀f. map2list 0 f = [f 0]) ∧
        ∀n f. map2list (SUC n) f = map2list n f ⧺ [f (n + 1)]
   
   [o_fVmap_def]  Definition
      
      ⊢ ∀σ2 σ1.
          o_fVmap σ2 σ1 =
          FUN_FMAP
            (λ(P,sl).
                 if (P,sl) ∈ FDOM σ1 then fVinst σ2 (σ1 ' (P,sl))
                 else σ2 ' (P,sl)) (FDOM σ1 ∪ FDOM σ2)
   
   [plainfV_def]  Definition
      
      ⊢ ∀P sl.
          plainfV (P,sl) =
          fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
   
   [refl_def]  Definition
      
      ⊢ ∀t. refl t = (tfv t,∅,EQ t t)
   
   [rn2fVmap_def]  Definition
      
      ⊢ ∀uσ. rn2fVmap uσ = FUN_FMAP (λfV. plainfV (fVrn uσ fV)) (FDOM uσ)
   
   [subfm_def]  Definition
      
      ⊢ subfm False = {False} ∧
        (∀f1 f2. subfm (IMP f1 f2) = {IMP f1 f2} ∪ subfm f1 ∪ subfm f2) ∧
        (∀p tl. subfm (Pred p tl) = {Pred p tl}) ∧
        (∀P sl tl. subfm (fVar P sl tl) = {fVar P sl tl}) ∧
        ∀s b. subfm (FALL s b) = {FALL s b} ∪ subfm b
   
   [sym_def_primitive]  Definition
      
      ⊢ sym =
        WFREC (@R. WF R)
          (λsym a.
               case a of
                 (Γ,A,False) => ARB
               | (Γ,A,Pred "" v5) => ARB
               | (Γ,A,Pred "=" []) => ARB
               | (Γ,A,Pred "=" [t1]) => ARB
               | (Γ,A,Pred "=" [t1; t2]) => I (Γ,A,Pred "=" [t2; t1])
               | (Γ,A,Pred "=" (t1::t2::v43::v44)) => ARB
               | (Γ,A,Pred (STRING #"=" (STRING v30 v31)) v5) => ARB
               | (Γ,A,Pred (STRING v27 v23) v5) => ARB
               | (Γ,A,IMP v6 v7) => ARB
               | (Γ,A,FALL v10 v11) => ARB
               | (Γ,A,fVar v14 v15 v16) => ARB)
   
   [thfVars_def]  Definition
      
      ⊢ ∀ct asm f. thfVars (ct,asm,f) = Uof fVars ({f} ∪ asm)
   
   [undisch_def_primitive]  Definition
      
      ⊢ undisch =
        WFREC (@R. WF R)
          (λundisch a.
               case a of
                 (Γ,A,False) => ARB
               | (Γ,A,Pred v4 v5) => ARB
               | (Γ,A,IMP f1 f2) => I (Γ,A ∪ {f1},f2)
               | (Γ,A,FALL v10 v11) => ARB
               | (Γ,A,fVar v14 v15 v16) => ARB)
   
   [uniqifn_def]  Definition
      
      ⊢ ∀uσ fVs.
          uniqifn uσ fVs ⇔
          fVs ⊆ FDOM uσ ∧
          ∀P1 P2 sl1 sl2.
            (P1,sl1) ∈ fVs ∧ (P2,sl2) ∈ fVs ∧ (P1,sl1) ≠ (P2,sl2) ⇒
            uσ ' (P1,sl1) ≠ uσ ' (P2,sl2)
   
   [vinst_bmap_def]  Definition
      
      ⊢ ∀σ bmap.
          vinst_bmap σ bmap = FUN_FMAP (λi. tinst σ (bmap ' i)) (FDOM bmap)
   
   [vinst_cont_def]  Definition
      
      ⊢ ∀σ Γ. vinst_cont σ Γ = ofFMAP tfv σ Γ
   
   [vinst_fVmap_def]  Definition
      
      ⊢ ∀vσ fσ.
          vinst_fVmap vσ fσ =
          FUN_FMAP
            (λ(P,sl).
                 finst vσ
                   (fσ '
                    (CHOICE
                       {(P0,sl0) |
                        vinst_fVar vσ (P0,sl0) = (P,sl) ∧
                        (P0,sl0) ∈ FDOM fσ})))
            (IMAGE (vinst_fVar vσ) (FDOM fσ))
   
   [vinsth_def]  Definition
      
      ⊢ ∀σ Γ A f.
          vinsth σ (Γ,A,f) = (vinst_cont σ Γ,IMAGE (finst σ) A,finst σ f)
   
   [vsfv_def]  Definition
      
      ⊢ ∀vs. vsfv vs = Uof (sfv ∘ SND) vs
   
   [wfcfVmap_def]  Definition
      
      ⊢ ∀Σ fσ. wfcfVmap Σ fσ ⇔ wffVmap Σ fσ ∧ cfVmap fσ
   
   [wffsig_def]  Definition
      
      ⊢ ∀Σf.
          wffsig Σf ⇔
          ∀fsym.
            isfsym Σf fsym ⇒
            sfv (fsymout Σf fsym) ⊆
            BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}
   
   [wfvmap_def]  Definition
      
      ⊢ ∀Σ vσ. wfvmap Σ vσ ⇔ cstt vσ ∧ wfcod Σ vσ
   
   [BIGUNION_IMAGE_Uof]  Theorem
      
      ⊢ BIGUNION (IMAGE f s) = Uof f s
   
   [EL_map2list]  Theorem
      
      ⊢ ∀n m. m ≤ n ⇒ EL m (map2list n f) = f m
   
   [EMPTY_is_cont]  Theorem
      
      ⊢ is_cont ∅
   
   [FALLL_components]  Theorem
      
      ⊢ ∀sl b1 b2. FALLL sl b1 = FALLL sl b2 ⇒ b1 = b2
   
   [FALLL_fbounds]  Theorem
      
      ⊢ wffsig Σf ⇒
        ∀n sl b.
          LENGTH sl = n ⇒
          wff (Σf,Σg,Σe) (FALLL sl b) ⇒
          fbounds b ⊆ count (LENGTH sl)
   
   [FAPPLY_fVmap_fVrn]  Theorem
      
      ⊢ uniqifn uσ (FDOM σ) ⇒
        ∀P sl.
          (P,sl) ∈ FDOM σ ⇒ fVmap_fVrn σ uσ ' (uσ ' (P,sl),sl) = σ ' (P,sl)
   
   [FAPPLY_o_fVmap]  Theorem
      
      ⊢ (P,sl) ∈ FDOM σ1 ∪ FDOM σ2 ⇒
        o_fVmap σ2 σ1 ' (P,sl) =
        if (P,sl) ∈ FDOM σ1 then fVinst σ2 (σ1 ' (P,sl)) else σ2 ' (P,sl)
   
   [FAPPLY_o_fVmap1]  Theorem
      
      ⊢ (P,sl) ∈ FDOM σ1 ⇒ o_fVmap σ2 σ1 ' (P,sl) = fVinst σ2 (σ1 ' (P,sl))
   
   [FAPPLY_o_fVmap2]  Theorem
      
      ⊢ (P,sl) ∉ FDOM σ1 ∧ (P,sl) ∈ FDOM σ2 ⇒
        o_fVmap σ2 σ1 ' (P,sl) = σ2 ' (P,sl)
   
   [FAPPLY_rn2fVmap]  Theorem
      
      ⊢ fV ∈ FDOM uσ ⇒ rn2fVmap uσ ' fV = plainfV (fVrn uσ fV)
   
   [FAPPLY_vinst_bmap]  Theorem
      
      ⊢ i ∈ FDOM bmap ⇒ vinst_bmap σ bmap ' i = tinst σ (bmap ' i)
   
   [FAPPLY_vinst_fVmap]  Theorem
      
      ⊢ ∀P sl.
          (P,sl) ∈ FDOM fσ ∧ alluniq (FDOM fσ) ⇒
          vinst_fVmap vσ fσ ' (vinst_fVar vσ (P,sl)) =
          finst vσ (fσ ' (P,sl))
   
   [FDOM_fVmap_fVrn]  Theorem
      
      ⊢ FDOM (fVmap_fVrn σ uσ) = IMAGE (fVrn uσ) (FDOM σ)
   
   [FDOM_o_fVmap]  Theorem
      
      ⊢ FDOM (o_fVmap σ2 σ1) = FDOM σ1 ∪ FDOM σ2
   
   [FDOM_rn2fVmap]  Theorem
      
      ⊢ FDOM (rn2fVmap uσ) = FDOM uσ
   
   [FDOM_vinst_bmap]  Theorem
      
      ⊢ FDOM (vinst_bmap σ bmap) = FDOM bmap
   
   [FDOM_vinst_fVmap]  Theorem
      
      ⊢ FDOM (vinst_fVmap vσ fσ) = IMAGE (vinst_fVar vσ) (FDOM fσ)
   
   [IN_Uof]  Theorem
      
      ⊢ x ∈ Uof f A ⇔ ∃a. a ∈ A ∧ x ∈ f a
   
   [IN_Uof_Uof]  Theorem
      
      ⊢ x ∈ Uof f1 (Uof f2 A) ⇔ ∃a e. a ∈ A ∧ e ∈ f2 a ∧ x ∈ f1 e
   
   [IN_genavds]  Theorem
      
      ⊢ ∀x th.
          x ∈ genavds (Γ,A,f) ⇔
          (∃n s. (n,s) ∈ Γ ∧ x ∈ sfv s) ∨ (∃a. a ∈ A ∧ x ∈ ffv a) ∨
          ∃P sl s f0.
            (f0 = f ∨ f0 ∈ A) ∧ (P,sl) ∈ fVars f0 ∧ MEM s sl ∧ x ∈ sfv s
   
   [IN_slfv']  Theorem
      
      ⊢ v ∈ slfv sl ⇔ ∃s0. MEM s0 sl ∧ v ∈ sfv s0
   
   [IN_vsfv]  Theorem
      
      ⊢ x ∈ vsfv vs ⇔ ∃n s. (n,s) ∈ vs ∧ x ∈ sfv s
   
   [LENGTH_LRofeqthl]  Theorem
      
      ⊢ LENGTH (Lofeqthl l) = LENGTH l ∧ LENGTH (Rofeqthl l) = LENGTH l
   
   [LENGTH_map2list]  Theorem
      
      ⊢ ∀n. LENGTH (map2list n f) = n + 1
   
   [MAP_tprpl_mk_bmap_REVERSE]  Theorem
      
      ⊢ MAP (tprpl (mk_bmap (REVERSE l0)) ∘ Bound)
          (REVERSE (COUNT_LIST (LENGTH l0))) =
        l0
   
   [MEM_Lofeqthl_map2list]  Theorem
      
      ⊢ (∀n0. n0 ≤ n ⇒ is_EQ (concl (eqths n0))) ⇒
        (MEM t (Lofeqthl (map2list n eqths)) ⇔
         ∃n0 Γ A t1 t2. n0 ≤ n ∧ eqths n0 = (Γ,A,EQ t1 t2) ∧ t = t1)
   
   [MEM_Rofeqthl_map2list]  Theorem
      
      ⊢ (∀n0. n0 ≤ n ⇒ is_EQ (concl (eqths n0))) ⇒
        (MEM t (Rofeqthl (map2list n eqths)) ⇔
         ∃n0 Γ A t1 t2. n0 ≤ n ∧ eqths n0 = (Γ,A,EQ t1 t2) ∧ t = t2)
   
   [MEM_map2list]  Theorem
      
      ⊢ MEM th (map2list n eqths) ⇔ ∃n0. n0 ≤ n ∧ th = eqths n0
   
   [NOTIN_genavds]  Theorem
      
      ⊢ ∀x th.
          x ∉ genavds (Γ,A,f) ⇔
          (∀n s. (n,s) ∈ Γ ⇒ x ∉ sfv s) ∧ (∀a. a ∈ A ⇒ x ∉ ffv a) ∧
          ∀P sl s f0.
            (f0 = f ∨ f0 ∈ A) ∧ (P,sl) ∈ fVars f0 ∧ MEM s sl ⇒ x ∉ sfv s
   
   [Uof_lemma_classic]  Theorem
      
      ⊢ Uof ffv ({False} ∪ (A ∪ {NEG f})) = Uof ffv ({f} ∪ A)
   
   [absapLs_fabs]  Theorem
      
      ⊢ ∀f i v. absapLs (fabs v i f) = absapLs f
   
   [add_assum_EMPTY]  Theorem
      
      ⊢ add_assum ∅ th = th
   
   [add_cont1_add_cont]  Theorem
      
      ⊢ add_cont1 (n,s) = add_cont ({(n,s)} ∪ sfv s)
   
   [add_cont_EMPTY]  Theorem
      
      ⊢ add_cont ∅ th = th
   
   [add_cont_UNION]  Theorem
      
      ⊢ add_cont (c1 ∪ c2) th = add_cont c1 (add_cont c2 th)
   
   [alluniq_EMPTY]  Theorem
      
      ⊢ alluniq ∅
   
   [cont_decompose]  Theorem
      
      ⊢ ∀ct.
          FINITE ct ∧ is_cont ct ⇒
          (let
             s = IMAGE (λ(n,s). {(n,s)} ∪ sfv s) ct
           in
             FINITE s ∧ BIGUNION s = ct ∧ ∀ct0. ct0 ∈ s ⇒ is_cont ct0)
   
   [dest_eq_EQ]  Theorem
      
      ⊢ dest_eq (EQ t1 t2) = (t1,t2)
   
   [fVar_FALLL_inc]  Theorem
      
      ⊢ ∀l b f. f ∈ subfm b ⇒ f ∈ subfm (FALLL l b)
   
   [fVar_prpl_o_fVmap]  Theorem
      
      ⊢ ∀f σ1 σ2.
          wffsig Σf ∧ wffVmap (Σf,Σg,Σe) σ1 ∧ wffVmap (Σf,Σg,Σe) σ2 ⇒
          fVinst σ2 (fVinst σ1 f) = fVinst (o_fVmap σ2 σ1) f
   
   [fVar_prpl_o_fVmap1]  Theorem
      
      ⊢ ∀f σ1 σ2.
          wffsig Σf ∧
          (∀P sl.
             (P,sl) ∈ fVars f ∩ FDOM σ1 ⇒
             wff (Σf,Σp,Σe) (FALLL sl (σ1 ' (P,sl)))) ∧
          wffVmap (Σf,Σg,Σe) σ2 ⇒
          fVinst σ2 (fVinst σ1 f) = fVinst (o_fVmap σ2 σ1) f
   
   [fVar_subfm_IN_absapLs]  Theorem
      
      ⊢ ∀f P sl tl.
          fVar P sl tl ∈ subfm f ⇒ (LENGTH sl,LENGTH tl) ∈ absapLs f
   
   [fVars_ffVrn]  Theorem
      
      ⊢ ∀f. fVars (ffVrn uσ f) = IMAGE (fVrn uσ) (fVars f)
   
   [fVars_vinst]  Theorem
      
      ⊢ ∀f. fVars (finst vσ f) = IMAGE (vinst_fVar vσ) (fVars f)
   
   [fVinst_FALLL]  Theorem
      
      ⊢ ∀sl b. fVinst σ (FALLL sl b) = FALLL sl (fVinst σ b)
   
   [fVinst_ffVrn]  Theorem
      
      ⊢ uniqifn uσ (FDOM σ) ⇒
        ∀f. fVars f ⊆ FDOM σ ⇒
            fVinst (fVmap_fVrn σ uσ) (ffVrn uσ f) = fVinst σ f
   
   [fVinst_fprpl]  Theorem
      
      ⊢ ∀ϕ σ bmap.
          wffVmap (Σf,Σg,Σe) σ ∧ wffsig Σf ∧
          (∀P sl tl. fVar P sl tl ∈ subfm ϕ ⇒ LENGTH sl = LENGTH tl) ⇒
          fVinst σ (fprpl bmap ϕ) = fprpl bmap (fVinst σ ϕ)
   
   [fVslfv_fabs]  Theorem
      
      ⊢ fVslfv (fabs v i f) = fVslfv f
   
   [ffVrn_fVinst]  Theorem
      
      ⊢ ∀f. (∀P sl tl. fVar P sl tl ∈ subfm f ⇒ LENGTH sl = LENGTH tl) ⇒
            ffVrn uσ f = fVinst (rn2fVmap uσ) f
   
   [ffv_IFF]  Theorem
      
      ⊢ ffv (IFF f1 f2) = ffv f1 ∪ ffv f2
   
   [ffv_NEG]  Theorem
      
      ⊢ ffv (NEG f) = ffv f
   
   [ffv_ffVrn]  Theorem
      
      ⊢ ffv (ffVrn uσf f) = ffv f
   
   [ffv_finst_alt]  Theorem
      
      ⊢ cstt σ ∧ ffv f ⊆ FDOM σ ∧ no_bound σ ⇒
        ffv (finst σ f) = ofFMAP tfv σ (ffv f)
   
   [ffv_finst_wfvmap]  Theorem
      
      ⊢ ∀f σ Σ.
          wfvmap Σ σ ∧ ffv f ⊆ FDOM σ ⇒
          ∀n st.
            (n,st) ∈ ffv (finst σ f) ⇔
            ∃n0 st0. (n0,st0) ∈ ffv f ∧ (n,st) ∈ tfv (σ ' (n0,st0))
   
   [ffv_frpl]  Theorem
      
      ⊢ tbounds new = ∅ ∧ (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ∧
        i ∈ fbounds f ⇒
        ffv (frpl i new f) = ffv f ∪ tfv new
   
   [ffv_frpl_SUBSET]  Theorem
      
      ⊢ tbounds new = ∅ ∧ (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ⇒
        ffv (frpl i new f) ⊆ ffv f ∪ tfv new
   
   [finst_FALLL]  Theorem
      
      ⊢ ∀sl b.
          finst vσ (FALLL sl b) = FALLL (MAP (sinst vσ) sl) (finst vσ b)
   
   [finst_fprpl]  Theorem
      
      ⊢ ∀f bmap σ.
          ffv f ⊆ FDOM σ ∧ (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ∧
          (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
          finst σ (fprpl bmap f) = fprpl (vinst_bmap σ bmap) (finst σ f)
   
   [finst_o_vmap]  Theorem
      
      ⊢ ∀f σ1 σ2.
          ffv f ⊆ FDOM σ1 ∧ ffv (finst σ1 f) ⊆ FDOM σ2 ⇒
          finst σ2 (finst σ1 f) = finst (o_vmap σ2 σ1) f
   
   [frpl_fprpl]  Theorem
      
      ⊢ ∀f i new.
          tbounds new = ∅ ⇒ frpl i new f = fprpl (TO_FMAP [(i,new)]) f
   
   [frpl_id]  Theorem
      
      ⊢ ∀f i. i ∉ fbounds f ⇒ frpl i new f = f
   
   [instf_fVinst]  Theorem
      
      ⊢ ∀f. fVars f ⊆ FDOM σ ∧ ffv (fVinst σ f) ⊆ FDOM vσ ∧ wffVmap Σ σ ∧
            alluniq (FDOM σ) ∧ (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ∧
            (∀n s. (n,s) ∈ FDOM vσ ⇒ tbounds (vσ ' (n,s)) = ∅) ⇒
            finst vσ (fVinst σ f) = instf (vinst_fVmap vσ σ) vσ f
   
   [instf_fVinst_finst]  Theorem
      
      ⊢ instf fσ vσ = fVinst fσ ∘ finst vσ
   
   [insth_instf]  Theorem
      
      ⊢ insth fσ vσ (Γ,A,f) =
        (vinst_cont vσ Γ ∪
         ofFMAP ffv fσ (Uof (IMAGE (vinst_fVar vσ) ∘ fVars) ({f} ∪ A)),
         IMAGE (instf fσ vσ) A,instf fσ vσ f)
   
   [is_cont_DELETE]  Theorem
      
      ⊢ is_cont ct ∧ (∀n s. (n,s) ∈ ct ⇒ v ∉ sfv s) ⇒ is_cont (ct DELETE v)
   
   [map2list_compute]  Theorem
      
      ⊢ (∀f. map2list 0 f = [f 0]) ∧
        (∀n f.
           map2list (NUMERAL (BIT1 n)) f =
           map2list (NUMERAL (BIT1 n) − 1) f ⧺
           [f (NUMERAL (BIT1 n) − 1 + 1)]) ∧
        ∀n f.
          map2list (NUMERAL (BIT2 n)) f =
          map2list (NUMERAL (BIT1 n)) f ⧺ [f (NUMERAL (BIT1 n) + 1)]
   
   [ofFMAP_SUBSET_MONO]  Theorem
      
      ⊢ s1 ⊆ s2 ⇒ ofFMAP f σ s1 ⊆ ofFMAP f σ s2
   
   [ofFMAP_SUBSET_ffv_fVinst]  Theorem
      
      ⊢ ∀f. (∀fv.
               fv ∈ FDOM σ ∩ fVars f ⇒
               ∀n s. (n,s) ∈ ffv (σ ' fv) ⇒ sbounds s = ∅) ⇒
            ofFMAP ffv σ (fVars f) ⊆ ffv (fVinst σ f)
   
   [shift_bmap_vinst_bmap]  Theorem
      
      ⊢ (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
        shift_bmap n (vinst_bmap σ bmap) = vinst_bmap σ (shift_bmap n bmap)
   
   [spec_def]  Theorem
      
      ⊢ spec t (Γ,A,FALL s b) = (Γ ∪ tfv t,A,substb t b)
   
   [spec_ind]  Theorem
      
      ⊢ ∀P. (∀t Γ A s b. P t (Γ,A,FALL s b)) ∧
            (∀v24 v23 v22. P v24 (v23,v22,False)) ∧
            (∀v27 v26 v25 v8 v9. P v27 (v26,v25,Pred v8 v9)) ∧
            (∀v30 v29 v28 v12 v13. P v30 (v29,v28,IMP v12 v13)) ∧
            (∀v33 v32 v31 v19 v20 v21. P v33 (v32,v31,fVar v19 v20 v21)) ⇒
            ∀v v1 v2 v3. P v (v1,v2,v3)
   
   [sym_def]  Theorem
      
      ⊢ sym (Γ,A,Pred "=" [t1; t2]) =
        if #"=" = #"=" then
          case "" of
            "" =>
              (case [t1; t2] of
                 [] => ARB
               | [t1] => ARB
               | [t1; t2] => (Γ,A,Pred "=" [t2; t1])
               | t1::t2::v43::v44 => ARB)
          | STRING v30 v31 => ARB
        else ARB
   
   [sym_ind]  Theorem
      
      ⊢ ∀P. (∀Γ A t1 t2. P (Γ,A,Pred "=" [t1; t2])) ∧
            (∀v21 v20. P (v21,v20,False)) ∧
            (∀v26 v25 v24. P (v26,v25,Pred "" v24)) ∧
            (∀v37 v36. P (v37,v36,Pred "=" [])) ∧
            (∀v42 v41 v40. P (v42,v41,Pred "=" [v40])) ∧
            (∀v50 v49 v48 v47 v45 v46.
               P (v50,v49,Pred "=" (v48::v47::v45::v46))) ∧
            (∀v53 v52 v32 v33 v51.
               P (v53,v52,Pred (STRING #"=" (STRING v32 v33)) v51)) ∧
            (∀v58 v57 v54 v55 v56. P (v58,v57,Pred (STRING v54 v55) v56)) ∧
            (∀v60 v59 v8 v9. P (v60,v59,IMP v8 v9)) ∧
            (∀v62 v61 v12 v13. P (v62,v61,FALL v12 v13)) ∧
            (∀v64 v63 v17 v18 v19. P (v64,v63,fVar v17 v18 v19)) ⇒
            ∀v v1 v2. P (v,v1,v2)
   
   [tinst_tprpl]  Theorem
      
      ⊢ (∀tm bmap σ.
           tfv tm ⊆ FDOM σ ∧ (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅) ∧
           (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
           tinst σ (tprpl bmap tm) = tprpl (vinst_bmap σ bmap) (tinst σ tm)) ∧
        ∀st bmap σ.
          sfv st ⊆ FDOM σ ∧ (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = ∅) ∧
          (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
          sinst σ (sprpl bmap st) = sprpl (vinst_bmap σ bmap) (sinst σ st)
   
   [trpl_tprpl]  Theorem
      
      ⊢ (∀tm i new. trpl i new tm = tprpl (TO_FMAP [(i,new)]) tm) ∧
        ∀st i new. srpl i new st = sprpl (TO_FMAP [(i,new)]) st
   
   [tshift_tinst]  Theorem
      
      ⊢ (∀tm.
           (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
           tshift n (tinst σ tm) = tinst σ (tshift n tm)) ∧
        ∀st.
          (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
          sshift n (sinst σ st) = sinst σ (sshift n st)
   
   [undisch_def]  Theorem
      
      ⊢ undisch (Γ,A,IMP f1 f2) = (Γ,A ∪ {f1},f2)
   
   [undisch_ind]  Theorem
      
      ⊢ ∀P. (∀Γ A f1 f2. P (Γ,A,IMP f1 f2)) ∧
            (∀v21 v20. P (v21,v20,False)) ∧
            (∀v23 v22 v6 v7. P (v23,v22,Pred v6 v7)) ∧
            (∀v25 v24 v12 v13. P (v25,v24,FALL v12 v13)) ∧
            (∀v27 v26 v17 v18 v19. P (v27,v26,fVar v17 v18 v19)) ⇒
            ∀v v1 v2. P (v,v1,v2)
   
   [uniqifn_FDOM_SUBSET]  Theorem
      
      ⊢ uniqifn uσ fVs ⇒ fVs ⊆ FDOM uσ
   
   [uniqifn_SUBSET]  Theorem
      
      ⊢ uniqifn uσ A ∧ B ⊆ A ⇒ uniqifn uσ B
   
   [uniqifn_alluniq]  Theorem
      
      ⊢ ∀f. uniqifn uσ (fVars f) ⇒ alluniq (fVars (ffVrn uσ f))
   
   [uniqifn_alluniq0]  Theorem
      
      ⊢ ∀s. uniqifn uσ s ⇒ alluniq (IMAGE (fVrn uσ) s)
   
   [uniqifn_ex]  Theorem
      
      ⊢ ∀fVs. FINITE fVs ⇒ ∃uσ. uniqifn uσ fVs ∧ FDOM uσ = fVs
   
   [vinst_bmap_alt]  Theorem
      
      ⊢ vinst_bmap vσ bmap = FMAP_MAP (tinst vσ) bmap
   
   [vinst_cont_EMPTY]  Theorem
      
      ⊢ vinst_cont σv ∅ = ∅
   
   [vinst_cont_UNION]  Theorem
      
      ⊢ vinst_cont σ (s1 ∪ s2) = vinst_cont σ s1 ∪ vinst_cont σ s2
   
   [wfabsap_Lofeqthl_sl_NONNIL]  Theorem
      
      ⊢ wfabsap Σf sl (Lofeqthl (map2list f l)) ⇒ sl ≠ []
   
   [wffVmap_DRESTRICT]  Theorem
      
      ⊢ wffVmap Σ σ ⇒ ∀s. wffVmap Σ (DRESTRICT σ s)
   
   [wffVmap_fVmap_fVrn]  Theorem
      
      ⊢ ∀σ. wffVmap Σ σ ∧ uniqifn uσ (FDOM σ) ⇒ wffVmap Σ (fVmap_fVrn σ uσ)
   
   [wffVmap_o_fVmap]  Theorem
      
      ⊢ ∀σ1 σ2.
          wffsig Σf ∧ wffVmap (Σf,Σp,Σe) σ1 ∧ wffVmap (Σf,Σp,Σe) σ2 ⇒
          wffVmap (Σf,Σp,Σe) (o_fVmap σ2 σ1)
   
   [wffVmap_vinst_fVmap]  Theorem
      
      ⊢ ∀σ. wffsig (FST Σ) ∧ wffVmap Σ σ ∧ alluniq (FDOM σ) ∧
            wfvmap (FST Σ) vσ ∧ presname vσ ∧
            BIGUNION
              {ffv (σ ' (P,sl)) ∪ slfv sl | (P,sl) | (P,sl) ∈ FDOM σ} ⊆
            FDOM vσ ⇒
            wffVmap Σ (vinst_fVmap vσ σ)
   
   [wff_FALL_alt]  Theorem
      
      ⊢ ∀f. wff (Σf,Σp,Σe) f ⇒
            ∀s b.
              f = FALL s b ⇒
              ∀nn.
                (nn,s) ∉ ffv b ⇒
                FALL s b = mk_FALL nn s (substb (Var nn s) b)
   
   [wff_IMP]  Theorem
      
      ⊢ wff Σ (IMP f1 f2) ⇔ wff Σ f1 ∧ wff Σ f2
   
   [wff_absapLs_eq]  Theorem
      
      ⊢ ∀f. wff Σ f ⇒ ∀n1 n2. (n1,n2) ∈ absapLs f ⇒ n1 = n2
   
   [wff_subfm_fVar_LENGTH]  Theorem
      
      ⊢ ∀f. wff Σ f ⇒
            ∀P sl tl. fVar P sl tl ∈ subfm f ⇒ LENGTH sl = LENGTH tl
   
   [wfvmap_IN_ofMAP_wfs]  Theorem
      
      ⊢ wfvmap Σf vσ ∧ (n,s) ∈ ofFMAP tfv vσ vs ⇒ wfs Σf s
   
   [wfvmap_presname]  Theorem
      
      ⊢ wfvmap Σ vσ ⇒ presname vσ
   
   
*)
end
