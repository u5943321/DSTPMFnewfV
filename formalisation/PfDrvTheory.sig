signature PfDrvTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val Leq_def : thm
    val PfDrv_def : thm
    val Pf_def : thm
    val Req_def : thm
    val wfsigaxs_def : thm
  
  (*  Theorems  *)
    val Leq_Req_EQ : thm
    val PfDrv_EX_E : thm
    val PfDrv_add_assum : thm
    val PfDrv_add_cont : thm
    val PfDrv_add_cont0 : thm
    val PfDrv_add_cont1 : thm
    val PfDrv_assum_SUBSET : thm
    val PfDrv_assum_ffv_SUBSET : thm
    val PfDrv_assume : thm
    val PfDrv_concl_ffv_SUBSET : thm
    val PfDrv_cont_SUBSET : thm
    val PfDrv_cont_wf : thm
    val PfDrv_cont_wf' : thm
    val PfDrv_contrapos : thm
    val PfDrv_contrapos0 : thm
    val PfDrv_disch : thm
    val PfDrv_double_neg : thm
    val PfDrv_ffv_SUBSET_cont : thm
    val PfDrv_gen : thm
    val PfDrv_mp : thm
    val PfDrv_undisch : thm
    val PfDrv_wff : thm
    val PfDrv_wff1 : thm
    val Pf_ALLE : thm
    val Pf_ALLI : thm
    val Pf_AX : thm
    val Pf_add_cont1 : thm
    val Pf_assume : thm
    val Pf_cases : thm
    val Pf_cont_is_cont : thm
    val Pf_disch : thm
    val Pf_double_neg : thm
    val Pf_fVcong : thm
    val Pf_fVinsth : thm
    val Pf_ffv_SUBSET_wff : thm
    val Pf_fromBot : thm
    val Pf_ind : thm
    val Pf_mp : thm
    val Pf_refl : thm
    val Pf_rules : thm
    val Pf_strongind : thm
    val Pf_sym : thm
    val Pf_trans : thm
    val Pf_vinsth : thm
    val Pf_wff : thm
    val Uof_sfv_SUBSET_cont : thm
    val fVars_NEG : thm
    val fVars_frpl : thm
    val fVslfv_False : thm
    val fVslfv_IMP : thm
    val ffv_EX : thm
    val is_EQ_wff_Leq_Req : thm
    val wfabsap_wfs : thm
    val wff_FALL_EX : thm
    val wff_False' : thm
    val wff_IFF : thm
    val wff_NEG : thm
    val wff_fVar' : thm
  
  val PfDrv_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [newdefs] Parent theory of "PfDrv"
   
   [Leq_def]  Definition
      
      ⊢ Leq = FST ∘ dest_eq
   
   [PfDrv_def]  Definition
      
      ⊢ ∀Σ axs th. PfDrv Σ axs th ⇔ ∃pf. Pf Σ axs pf ∧ MEM th pf
   
   [Pf_def]  Definition
      
      ⊢ Pf =
        (λΣ axs a0.
             ∀Pf'.
               (∀a0.
                  (∃ax. a0 = [(ffv ax,∅,ax)] ∧ ax ∈ axs) ∨
                  (∃P sl Pfs eqths.
                     a0 =
                     FLAT (map2list (LENGTH sl − 1) Pfs) ⧺
                     [fVcong (map2list (LENGTH sl − 1) eqths) P sl] ∧
                     sl ≠ [] ∧
                     (∀n. n < LENGTH sl ⇒
                          is_EQ (concl (eqths n)) ∧ Pf' (Pfs n) ∧
                          MEM (eqths n) (Pfs n) ∧
                          sort_of (Leq (concl (eqths n))) = EL n sl) ∧
                     ∀s. MEM s sl ⇒ wfs (FST Σ) s) ∨
                  (∃pf th fσ.
                     a0 = pf ⧺ [fVinsth fσ th] ∧ Pf' pf ∧ MEM th pf ∧
                     wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ) ∨
                  (∃pf th vσ.
                     a0 = pf ⧺ [vinsth vσ th] ∧ Pf' pf ∧ MEM th pf ∧
                     wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ) ∨
                  (∃Γ A pf x s f.
                     a0 = pf ⧺ [gen (x,s) (Γ,A,f)] ∧ Pf' pf ∧
                     MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
                     (x,s) ∉ genavds (Γ,A,f)) ∨
                  (∃Γ A pf s f t.
                     a0 = pf ⧺ [spec t (Γ,A,FALL s f)] ∧ Pf' pf ∧
                     MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧ sort_of t = s) ∨
                  (∃Γ A pf f.
                     a0 = pf ⧺ [(Γ,A,f)] ∧ Pf' pf ∧
                     MEM (Γ,A ∪ {NEG f},False) pf) ∨
                  (∃Γ A pf f.
                     a0 = pf ⧺ [(Γ ∪ ffv f,A,f)] ∧ Pf' pf ∧
                     MEM (Γ,A,False) pf ∧ wff Σ f) ∨
                  (∃c. a0 = [assume c] ∧ wff Σ c) ∨
                  (∃Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
                     a0 = pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)] ∧ Pf' pf1 ∧
                     Pf' pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
                     MEM (Γ2,A2,f1) pf2) ∨
                  (∃pf th a.
                     a0 = pf ⧺ [disch a th] ∧ Pf' pf ∧ MEM th pf ∧ wff Σ a) ∨
                  (∃t. a0 = [refl t] ∧ wft (FST Σ) t ∧
                       tsname t ∈ SND (SND Σ)) ∨
                  (∃Γ A pf t1 t2.
                     a0 = pf ⧺ [(Γ,A,EQ t2 t1)] ∧ Pf' pf ∧
                     MEM (Γ,A,EQ t1 t2) pf) ∨
                  (∃Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
                     a0 = pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)] ∧
                     Pf' pf1 ∧ Pf' pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
                     MEM (Γ2,A2,EQ t2 t3) pf2) ∨
                  (∃s pf th n.
                     a0 = pf ⧺ [add_cont1 (n,s) th] ∧ Pf' pf ∧ MEM th pf ∧
                     wfs (FST Σ) s) ⇒
                  Pf' a0) ⇒
               Pf' a0)
   
   [Req_def]  Definition
      
      ⊢ Req = SND ∘ dest_eq
   
   [wfsigaxs_def]  Definition
      
      ⊢ ∀Σf Σp Σe axs.
          wfsigaxs (Σf,Σp,Σe) axs ⇔
          wfsig (Σf,Σp,Σe) ∧ ∀ax. ax ∈ axs ⇒ wff (Σf,Σp,Σe) ax
   
   [Leq_Req_EQ]  Theorem
      
      ⊢ Leq (EQ t1 t2) = t1 ∧ Req (EQ t1 t2) = t2
   
   [PfDrv_EX_E]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (G1,A1,EX s b) ∧ (a,s) ∉ ffv b ∧
        (a,s) ∉ G2 ∧ substb (Var a s) b ∉ A2 ∧
        PfDrv Σ axs (G2 ∪ {(a,s)},A2 ∪ {substb (Var a s) b},f) ∧
        (a,s) ∉ Uof (sfv ∘ SND) G2 ∧ (a,s) ∉ Uof ffv (A2 ∪ {f}) ∧
        (a,s) ∉ Uof (slfv ∘ SND) (Uof fVars (A2 ∪ {f})) ⇒
        PfDrv Σ axs (G1 ∪ G2,A1 ∪ A2,f)
   
   [PfDrv_add_assum]  Theorem
      
      ⊢ ∀s th.
          FINITE s ⇒
          wfsigaxs Σ axs ∧ (∀ϕ. ϕ ∈ s ⇒ wff Σ ϕ) ∧ PfDrv Σ axs th ⇒
          PfDrv Σ axs (add_assum s th)
   
   [PfDrv_add_cont]  Theorem
      
      ⊢ FINITE ct ∧ is_cont ct ⇒
        (∀n s. (n,s) ∈ ct ⇒ wfs (FST Σ) s) ∧ PfDrv Σ axs th ⇒
        PfDrv Σ axs (add_cont ct th)
   
   [PfDrv_add_cont0]  Theorem
      
      ⊢ ∀vs.
          FINITE vs ⇒
          (∀n s. (n,s) ∈ vs ⇒ wfs (FST Σ) s) ∧ PfDrv Σ axs th ⇒
          PfDrv Σ axs (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) vs) th)
   
   [PfDrv_add_cont1]  Theorem
      
      ⊢ PfDrv Σ axs th ⇒
        ∀n s. wfs (FST Σ) s ⇒ PfDrv Σ axs (add_cont1 (n,s) th)
   
   [PfDrv_assum_SUBSET]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ,A0,f) ∧ FINITE A ∧ A0 ⊆ A ∧
        (∀a. a ∈ A ⇒ wff Σ a) ⇒
        PfDrv Σ axs (Γ ∪ Uof ffv A,A,f)
   
   [PfDrv_assum_ffv_SUBSET]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒
        ∀Γ A f. PfDrv Σ axs (Γ,A,f) ⇒ ∀a. a ∈ A ⇒ ffv a ⊆ Γ
   
   [PfDrv_assume]  Theorem
      
      ⊢ ∀Σ axs c. wff Σ c ⇒ PfDrv Σ axs (assume c)
   
   [PfDrv_concl_ffv_SUBSET]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒ ∀Γ A f. PfDrv Σ axs (Γ,A,f) ⇒ ffv f ⊆ Γ
   
   [PfDrv_cont_SUBSET]  Theorem
      
      ⊢ PfDrv Σ axs (Γ0,A,f) ∧ FINITE Γ ∧ Γ0 ⊆ Γ ∧ is_cont Γ ∧
        (∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s) ⇒
        PfDrv Σ axs (Γ,A,f)
   
   [PfDrv_cont_wf]  Theorem
      
      ⊢ (∀ax. ax ∈ axs ⇒ wff (Σf,Σp,Σe) ax) ⇒
        ∀pf.
          Pf (Σf,Σp,Σe) axs pf ⇒
          ∀Γ A f. MEM (Γ,A,f) pf ⇒ ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s
   
   [PfDrv_cont_wf']  Theorem
      
      ⊢ (∀ax. ax ∈ axs ⇒ wff (Σf,Σp,Σe) ax) ⇒
        ∀Γ A f. PfDrv (Σf,Σp,Σe) axs (Γ,A,f) ⇒ ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s
   
   [PfDrv_contrapos]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ1,A1,IMP ϕ ψ) ⇒
        PfDrv Σ axs (Γ1,A1,IMP (NEG ψ) (NEG ϕ))
   
   [PfDrv_contrapos0]  Theorem
      
      ⊢ wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ1,A1,IMP ϕ ψ) ⇒
        PfDrv Σ axs (Γ1,A1 DELETE ϕ DELETE NEG ψ,IMP (NEG ψ) (NEG ϕ))
   
   [PfDrv_disch]  Theorem
      
      ⊢ PfDrv Σ axs (Γ,A,f) ∧ wff Σ a ⇒ PfDrv Σ axs (disch a (Γ,A,f))
   
   [PfDrv_double_neg]  Theorem
      
      ⊢ PfDrv Σ axs (Γ,A ∪ {NEG f},False) ⇒ PfDrv Σ axs (Γ,A,f)
   
   [PfDrv_ffv_SUBSET_cont]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒
        ∀Γ A f. PfDrv Σ axs (Γ,A,f) ⇒ Uof ffv ({f} ∪ A) ⊆ Γ
   
   [PfDrv_gen]  Theorem
      
      ⊢ PfDrv Σ axs (Γ,A,f) ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
        (x,s) ∉ genavds (Γ,A,f) ⇒
        PfDrv Σ axs (gen (x,s) (Γ,A,f))
   
   [PfDrv_mp]  Theorem
      
      ⊢ PfDrv Σ axs (Γ1,A1,IMP ϕ ψ) ∧ PfDrv Σ axs (Γ2,A2,ϕ) ⇒
        PfDrv Σ axs (Γ1 ∪ Γ2,A1 ∪ A2,ψ)
   
   [PfDrv_undisch]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒
        PfDrv Σ axs (Γ,A,IMP f1 f2) ⇒
        PfDrv Σ axs (Γ,A ∪ {f1},f2)
   
   [PfDrv_wff]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒
        ∀th. PfDrv Σ axs th ⇒ wff Σ (concl th) ∧ ∀a. a ∈ assum th ⇒ wff Σ a
   
   [PfDrv_wff1]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒
        ∀Γ A f. PfDrv Σ axs (Γ,A,f) ⇒ wff Σ f ∧ ∀a. a ∈ A ⇒ wff Σ a
   
   [Pf_ALLE]  Theorem
      
      ⊢ ∀Σ axs Γ A pf s f t.
          Pf Σ axs pf ∧ MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧
          sort_of t = s ⇒
          Pf Σ axs (pf ⧺ [spec t (Γ,A,FALL s f)])
   
   [Pf_ALLI]  Theorem
      
      ⊢ ∀Σ axs Γ A pf x s f.
          Pf Σ axs pf ∧ MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
          (x,s) ∉ genavds (Γ,A,f) ⇒
          Pf Σ axs (pf ⧺ [gen (x,s) (Γ,A,f)])
   
   [Pf_AX]  Theorem
      
      ⊢ ∀Σ axs ax. ax ∈ axs ⇒ Pf Σ axs [(ffv ax,∅,ax)]
   
   [Pf_add_cont1]  Theorem
      
      ⊢ ∀Σ axs s pf th n.
          Pf Σ axs pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
          Pf Σ axs (pf ⧺ [add_cont1 (n,s) th])
   
   [Pf_assume]  Theorem
      
      ⊢ ∀Σ axs c. wff Σ c ⇒ Pf Σ axs [assume c]
   
   [Pf_cases]  Theorem
      
      ⊢ ∀Σ axs a0.
          Pf Σ axs a0 ⇔
          (∃ax. a0 = [(ffv ax,∅,ax)] ∧ ax ∈ axs) ∨
          (∃P sl Pfs eqths.
             a0 =
             FLAT (map2list (LENGTH sl − 1) Pfs) ⧺
             [fVcong (map2list (LENGTH sl − 1) eqths) P sl] ∧ sl ≠ [] ∧
             (∀n. n < LENGTH sl ⇒
                  is_EQ (concl (eqths n)) ∧ Pf Σ axs (Pfs n) ∧
                  MEM (eqths n) (Pfs n) ∧
                  sort_of (Leq (concl (eqths n))) = EL n sl) ∧
             ∀s. MEM s sl ⇒ wfs (FST Σ) s) ∨
          (∃pf th fσ.
             a0 = pf ⧺ [fVinsth fσ th] ∧ Pf Σ axs pf ∧ MEM th pf ∧
             wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ) ∨
          (∃pf th vσ.
             a0 = pf ⧺ [vinsth vσ th] ∧ Pf Σ axs pf ∧ MEM th pf ∧
             wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ) ∨
          (∃Γ A pf x s f.
             a0 = pf ⧺ [gen (x,s) (Γ,A,f)] ∧ Pf Σ axs pf ∧ MEM (Γ,A,f) pf ∧
             wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧ (x,s) ∉ genavds (Γ,A,f)) ∨
          (∃Γ A pf s f t.
             a0 = pf ⧺ [spec t (Γ,A,FALL s f)] ∧ Pf Σ axs pf ∧
             MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧ sort_of t = s) ∨
          (∃Γ A pf f.
             a0 = pf ⧺ [(Γ,A,f)] ∧ Pf Σ axs pf ∧
             MEM (Γ,A ∪ {NEG f},False) pf) ∨
          (∃Γ A pf f.
             a0 = pf ⧺ [(Γ ∪ ffv f,A,f)] ∧ Pf Σ axs pf ∧
             MEM (Γ,A,False) pf ∧ wff Σ f) ∨
          (∃c. a0 = [assume c] ∧ wff Σ c) ∨
          (∃Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
             a0 = pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)] ∧ Pf Σ axs pf1 ∧
             Pf Σ axs pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧ MEM (Γ2,A2,f1) pf2) ∨
          (∃pf th a.
             a0 = pf ⧺ [disch a th] ∧ Pf Σ axs pf ∧ MEM th pf ∧ wff Σ a) ∨
          (∃t. a0 = [refl t] ∧ wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ)) ∨
          (∃Γ A pf t1 t2.
             a0 = pf ⧺ [(Γ,A,EQ t2 t1)] ∧ Pf Σ axs pf ∧
             MEM (Γ,A,EQ t1 t2) pf) ∨
          (∃Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
             a0 = pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)] ∧ Pf Σ axs pf1 ∧
             Pf Σ axs pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
             MEM (Γ2,A2,EQ t2 t3) pf2) ∨
          ∃s pf th n.
            a0 = pf ⧺ [add_cont1 (n,s) th] ∧ Pf Σ axs pf ∧ MEM th pf ∧
            wfs (FST Σ) s
   
   [Pf_cont_is_cont]  Theorem
      
      ⊢ ∀pf. Pf Σ axs pf ⇒ ∀Γ A f. MEM (Γ,A,f) pf ⇒ is_cont Γ
   
   [Pf_disch]  Theorem
      
      ⊢ ∀Σ axs pf th a.
          Pf Σ axs pf ∧ MEM th pf ∧ wff Σ a ⇒ Pf Σ axs (pf ⧺ [disch a th])
   
   [Pf_double_neg]  Theorem
      
      ⊢ ∀Σ axs Γ A pf f.
          Pf Σ axs pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒
          Pf Σ axs (pf ⧺ [(Γ,A,f)])
   
   [Pf_fVcong]  Theorem
      
      ⊢ ∀Σ axs P sl Pfs eqths.
          sl ≠ [] ∧
          (∀n. n < LENGTH sl ⇒
               is_EQ (concl (eqths n)) ∧ Pf Σ axs (Pfs n) ∧
               MEM (eqths n) (Pfs n) ∧
               sort_of (Leq (concl (eqths n))) = EL n sl) ∧
          (∀s. MEM s sl ⇒ wfs (FST Σ) s) ⇒
          Pf Σ axs
            (FLAT (map2list (LENGTH sl − 1) Pfs) ⧺
             [fVcong (map2list (LENGTH sl − 1) eqths) P sl])
   
   [Pf_fVinsth]  Theorem
      
      ⊢ ∀Σ axs pf th fσ.
          Pf Σ axs pf ∧ MEM th pf ∧ wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ⇒
          Pf Σ axs (pf ⧺ [fVinsth fσ th])
   
   [Pf_ffv_SUBSET_wff]  Theorem
      
      ⊢ wfsig (Σf,Σp,Σe) ∧ (∀ax. ax ∈ axs ⇒ wff (Σf,Σp,Σe) ax) ⇒
        ∀pf.
          Pf (Σf,Σp,Σe) axs pf ⇒
          ∀Γ A f.
            MEM (Γ,A,f) pf ⇒
            Uof ffv ({f} ∪ A) ⊆ Γ ∧ wff (Σf,Σp,Σe) f ∧
            ∀a. a ∈ A ⇒ wff (Σf,Σp,Σe) a
   
   [Pf_fromBot]  Theorem
      
      ⊢ ∀Σ axs Γ A pf f.
          Pf Σ axs pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ⇒
          Pf Σ axs (pf ⧺ [(Γ ∪ ffv f,A,f)])
   
   [Pf_ind]  Theorem
      
      ⊢ ∀Σ axs Pf'.
          (∀ax. ax ∈ axs ⇒ Pf' [(ffv ax,∅,ax)]) ∧
          (∀P sl Pfs eqths.
             sl ≠ [] ∧
             (∀n. n < LENGTH sl ⇒
                  is_EQ (concl (eqths n)) ∧ Pf' (Pfs n) ∧
                  MEM (eqths n) (Pfs n) ∧
                  sort_of (Leq (concl (eqths n))) = EL n sl) ∧
             (∀s. MEM s sl ⇒ wfs (FST Σ) s) ⇒
             Pf'
               (FLAT (map2list (LENGTH sl − 1) Pfs) ⧺
                [fVcong (map2list (LENGTH sl − 1) eqths) P sl])) ∧
          (∀pf th fσ.
             Pf' pf ∧ MEM th pf ∧ wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ⇒
             Pf' (pf ⧺ [fVinsth fσ th])) ∧
          (∀pf th vσ.
             Pf' pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ ⇒
             Pf' (pf ⧺ [vinsth vσ th])) ∧
          (∀Γ A pf x s f.
             Pf' pf ∧ MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
             (x,s) ∉ genavds (Γ,A,f) ⇒
             Pf' (pf ⧺ [gen (x,s) (Γ,A,f)])) ∧
          (∀Γ A pf s f t.
             Pf' pf ∧ MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧ sort_of t = s ⇒
             Pf' (pf ⧺ [spec t (Γ,A,FALL s f)])) ∧
          (∀Γ A pf f.
             Pf' pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒ Pf' (pf ⧺ [(Γ,A,f)])) ∧
          (∀Γ A pf f.
             Pf' pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ⇒
             Pf' (pf ⧺ [(Γ ∪ ffv f,A,f)])) ∧
          (∀c. wff Σ c ⇒ Pf' [assume c]) ∧
          (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
             Pf' pf1 ∧ Pf' pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
             MEM (Γ2,A2,f1) pf2 ⇒
             Pf' (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)])) ∧
          (∀pf th a. Pf' pf ∧ MEM th pf ∧ wff Σ a ⇒ Pf' (pf ⧺ [disch a th])) ∧
          (∀t. wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ) ⇒ Pf' [refl t]) ∧
          (∀Γ A pf t1 t2.
             Pf' pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒ Pf' (pf ⧺ [(Γ,A,EQ t2 t1)])) ∧
          (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
             Pf' pf1 ∧ Pf' pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
             MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
             Pf' (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
          (∀s pf th n.
             Pf' pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
             Pf' (pf ⧺ [add_cont1 (n,s) th])) ⇒
          ∀a0. Pf Σ axs a0 ⇒ Pf' a0
   
   [Pf_mp]  Theorem
      
      ⊢ ∀Σ axs Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
          Pf Σ axs pf1 ∧ Pf Σ axs pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
          MEM (Γ2,A2,f1) pf2 ⇒
          Pf Σ axs (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)])
   
   [Pf_refl]  Theorem
      
      ⊢ ∀Σ axs t.
          wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ) ⇒ Pf Σ axs [refl t]
   
   [Pf_rules]  Theorem
      
      ⊢ ∀Σ axs.
          (∀ax. ax ∈ axs ⇒ Pf Σ axs [(ffv ax,∅,ax)]) ∧
          (∀P sl Pfs eqths.
             sl ≠ [] ∧
             (∀n. n < LENGTH sl ⇒
                  is_EQ (concl (eqths n)) ∧ Pf Σ axs (Pfs n) ∧
                  MEM (eqths n) (Pfs n) ∧
                  sort_of (Leq (concl (eqths n))) = EL n sl) ∧
             (∀s. MEM s sl ⇒ wfs (FST Σ) s) ⇒
             Pf Σ axs
               (FLAT (map2list (LENGTH sl − 1) Pfs) ⧺
                [fVcong (map2list (LENGTH sl − 1) eqths) P sl])) ∧
          (∀pf th fσ.
             Pf Σ axs pf ∧ MEM th pf ∧ wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ⇒
             Pf Σ axs (pf ⧺ [fVinsth fσ th])) ∧
          (∀pf th vσ.
             Pf Σ axs pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧
             cont th ⊆ FDOM vσ ⇒
             Pf Σ axs (pf ⧺ [vinsth vσ th])) ∧
          (∀Γ A pf x s f.
             Pf Σ axs pf ∧ MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
             (x,s) ∉ genavds (Γ,A,f) ⇒
             Pf Σ axs (pf ⧺ [gen (x,s) (Γ,A,f)])) ∧
          (∀Γ A pf s f t.
             Pf Σ axs pf ∧ MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧
             sort_of t = s ⇒
             Pf Σ axs (pf ⧺ [spec t (Γ,A,FALL s f)])) ∧
          (∀Γ A pf f.
             Pf Σ axs pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒
             Pf Σ axs (pf ⧺ [(Γ,A,f)])) ∧
          (∀Γ A pf f.
             Pf Σ axs pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ⇒
             Pf Σ axs (pf ⧺ [(Γ ∪ ffv f,A,f)])) ∧
          (∀c. wff Σ c ⇒ Pf Σ axs [assume c]) ∧
          (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
             Pf Σ axs pf1 ∧ Pf Σ axs pf2 ∧ MEM (Γ1,A1,IMP f1 f2) pf1 ∧
             MEM (Γ2,A2,f1) pf2 ⇒
             Pf Σ axs (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)])) ∧
          (∀pf th a.
             Pf Σ axs pf ∧ MEM th pf ∧ wff Σ a ⇒
             Pf Σ axs (pf ⧺ [disch a th])) ∧
          (∀t. wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ) ⇒ Pf Σ axs [refl t]) ∧
          (∀Γ A pf t1 t2.
             Pf Σ axs pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
             Pf Σ axs (pf ⧺ [(Γ,A,EQ t2 t1)])) ∧
          (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
             Pf Σ axs pf1 ∧ Pf Σ axs pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
             MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
             Pf Σ axs (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
          ∀s pf th n.
            Pf Σ axs pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
            Pf Σ axs (pf ⧺ [add_cont1 (n,s) th])
   
   [Pf_strongind]  Theorem
      
      ⊢ ∀Σ axs Pf'.
          (∀ax. ax ∈ axs ⇒ Pf' [(ffv ax,∅,ax)]) ∧
          (∀P sl Pfs eqths.
             sl ≠ [] ∧
             (∀n. n < LENGTH sl ⇒
                  is_EQ (concl (eqths n)) ∧ Pf Σ axs (Pfs n) ∧
                  Pf' (Pfs n) ∧ MEM (eqths n) (Pfs n) ∧
                  sort_of (Leq (concl (eqths n))) = EL n sl) ∧
             (∀s. MEM s sl ⇒ wfs (FST Σ) s) ⇒
             Pf'
               (FLAT (map2list (LENGTH sl − 1) Pfs) ⧺
                [fVcong (map2list (LENGTH sl − 1) eqths) P sl])) ∧
          (∀pf th fσ.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM th pf ∧ wffVmap Σ fσ ∧
             thfVars th ⊆ FDOM fσ ⇒
             Pf' (pf ⧺ [fVinsth fσ th])) ∧
          (∀pf th vσ.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧
             cont th ⊆ FDOM vσ ⇒
             Pf' (pf ⧺ [vinsth vσ th])) ∧
          (∀Γ A pf x s f.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM (Γ,A,f) pf ∧ wfs (FST Σ) s ∧
             sfv s ⊆ Γ ∧ (x,s) ∉ genavds (Γ,A,f) ⇒
             Pf' (pf ⧺ [gen (x,s) (Γ,A,f)])) ∧
          (∀Γ A pf s f t.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM (Γ,A,FALL s f) pf ∧ wft (FST Σ) t ∧
             sort_of t = s ⇒
             Pf' (pf ⧺ [spec t (Γ,A,FALL s f)])) ∧
          (∀Γ A pf f.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒
             Pf' (pf ⧺ [(Γ,A,f)])) ∧
          (∀Γ A pf f.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ⇒
             Pf' (pf ⧺ [(Γ ∪ ffv f,A,f)])) ∧
          (∀c. wff Σ c ⇒ Pf' [assume c]) ∧
          (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
             Pf Σ axs pf1 ∧ Pf' pf1 ∧ Pf Σ axs pf2 ∧ Pf' pf2 ∧
             MEM (Γ1,A1,IMP f1 f2) pf1 ∧ MEM (Γ2,A2,f1) pf2 ⇒
             Pf' (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,f2)])) ∧
          (∀pf th a.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM th pf ∧ wff Σ a ⇒
             Pf' (pf ⧺ [disch a th])) ∧
          (∀t. wft (FST Σ) t ∧ tsname t ∈ SND (SND Σ) ⇒ Pf' [refl t]) ∧
          (∀Γ A pf t1 t2.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
             Pf' (pf ⧺ [(Γ,A,EQ t2 t1)])) ∧
          (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
             Pf Σ axs pf1 ∧ Pf' pf1 ∧ Pf Σ axs pf2 ∧ Pf' pf2 ∧
             MEM (Γ1,A1,EQ t1 t2) pf1 ∧ MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
             Pf' (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
          (∀s pf th n.
             Pf Σ axs pf ∧ Pf' pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
             Pf' (pf ⧺ [add_cont1 (n,s) th])) ⇒
          ∀a0. Pf Σ axs a0 ⇒ Pf' a0
   
   [Pf_sym]  Theorem
      
      ⊢ ∀Σ axs Γ A pf t1 t2.
          Pf Σ axs pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
          Pf Σ axs (pf ⧺ [(Γ,A,EQ t2 t1)])
   
   [Pf_trans]  Theorem
      
      ⊢ ∀Σ axs Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
          Pf Σ axs pf1 ∧ Pf Σ axs pf2 ∧ MEM (Γ1,A1,EQ t1 t2) pf1 ∧
          MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
          Pf Σ axs (pf1 ⧺ pf2 ⧺ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])
   
   [Pf_vinsth]  Theorem
      
      ⊢ ∀Σ axs pf th vσ.
          Pf Σ axs pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧ cont th ⊆ FDOM vσ ⇒
          Pf Σ axs (pf ⧺ [vinsth vσ th])
   
   [Pf_wff]  Theorem
      
      ⊢ wfsigaxs Σ axs ⇒
        ∀pf.
          Pf Σ axs pf ⇒
          ∀Γ A f. MEM (Γ,A,f) pf ⇒ wff Σ f ∧ ∀a. a ∈ A ⇒ wff Σ a
   
   [Uof_sfv_SUBSET_cont]  Theorem
      
      ⊢ ∀ct. is_cont ct ⇒ Uof (sfv ∘ SND) ct ⊆ ct
   
   [fVars_NEG]  Theorem
      
      ⊢ ∀f. fVars (NEG f) = fVars f
   
   [fVars_frpl]  Theorem
      
      ⊢ ∀f i. fVars (frpl i v f) = fVars f
   
   [fVslfv_False]  Theorem
      
      ⊢ fVslfv False = ∅
   
   [fVslfv_IMP]  Theorem
      
      ⊢ fVslfv (IMP f1 f2) = fVslfv f1 ∪ fVslfv f2
   
   [ffv_EX]  Theorem
      
      ⊢ ffv (EX s b) = sfv s ∪ ffv b
   
   [is_EQ_wff_Leq_Req]  Theorem
      
      ⊢ wfsig Σ ∧ is_EQ f ∧ wff Σ f ⇒ sort_of (Leq f) = sort_of (Req f)
   
   [wfabsap_wfs]  Theorem
      
      ⊢ ∀tl sl.
          (∀s. MEM s sl ⇒ wfs Σf s) ∧ (∀t. MEM t tl ⇒ wft Σf t) ∧
          LENGTH tl = LENGTH sl ∧
          (∀n. n < LENGTH sl ⇒ sort_of (EL n tl) = EL n sl) ⇒
          wfabsap Σf sl tl
   
   [wff_FALL_EX]  Theorem
      
      ⊢ wff Σ (FALL s b) ⇔ wff Σ (EX s b)
   
   [wff_False']  Theorem
      
      ⊢ wff Σ False
   
   [wff_IFF]  Theorem
      
      ⊢ wff Σ (IFF f1 f2) ⇔ wff Σ f1 ∧ wff Σ f2
   
   [wff_NEG]  Theorem
      
      ⊢ wff Σ (NEG f) ⇔ wff Σ f
   
   [wff_fVar']  Theorem
      
      ⊢ ∀P sl tl. wfabsap (FST Σ) sl tl ⇒ wff Σ (fVar P sl tl)
   
   
*)
end
