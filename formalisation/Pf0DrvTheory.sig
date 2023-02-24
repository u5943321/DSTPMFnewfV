signature Pf0DrvTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val Pf0Drv_def : thm
    val Pf0_def : thm
    val wfaths_def : thm
    val wfsigaths_def : thm
  
  (*  Theorems  *)
    val FAPPLY_mk_bmap_REVERSE_Lofeqthl : thm
    val FAPPLY_mk_bmap_REVERSE_Rofeqthl : thm
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
    val is_cfm_EQ : thm
    val is_cfm_IFF : thm
    val is_cfm_NEG : thm
    val is_cfm_fabs : thm
    val is_cfm_finst : thm
    val is_cfm_fprpl : thm
    val is_cfm_frpl : thm
    val mk_bmap_BIGUNION : thm
  
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
   
   [FAPPLY_mk_bmap_REVERSE_Lofeqthl]  Theorem
      
      ⊢ i ≤ n ⇒
        mk_bmap (REVERSE (Lofeqthl (map2list n eqths))) ' i =
        Leq (concl (eqths (n − i)))
   
   [FAPPLY_mk_bmap_REVERSE_Rofeqthl]  Theorem
      
      ⊢ i ≤ n ⇒
        mk_bmap (REVERSE (Rofeqthl (map2list n eqths))) ' i =
        Req (concl (eqths (n − i)))
   
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
   
   [mk_bmap_BIGUNION]  Theorem
      
      ⊢ ∀l ϕ.
          BIGUNION
            {tfv (mk_bmap l ' i) | i | i ∈ count (LENGTH l) ∩ fbounds ϕ} ⊆
          Uof tfv (set l)
   
   
*)
end
