signature fVinstTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val Leq_def : thm
    val Req_def : thm
    val bmap_eff_def : thm
    val bmap_equiv_def : thm
    val fVmap_eff_def : thm
    val fVmap_rename_def : thm
    val shift_bmap'_def : thm
  
  (*  Theorems  *)
    val FAPPLY_fVmap_rename : thm
    val FAPPLY_shift_bmap' : thm
    val FDOM_fVmap_rename : thm
    val FDOM_shift_bmap' : thm
    val bmap_eff_fprpl : thm
    val bmap_eff_shift_bmap : thm
    val bmap_eff_slprpl : thm
    val bmap_eff_tprpl : thm
    val fVar_prpl_eq_lemma : thm
    val fVar_prpl_fabs1 : thm
    val fVars_DRESTRICT_fVinst_eq : thm
    val fVars_DRESTRICT_fVinst_eq0 : thm
    val fVars_DRESTRICT_fVinst_eq1 : thm
    val fVars_fVinst : thm
    val fVars_fabs : thm
    val fVars_fprpl : thm
    val fVinst_EQ : thm
    val fVinst_fabs : thm
    val fVinst_id : thm
    val fVmap_no_bound_lemma : thm
    val ffv_fVinst : thm
    val fprpl_FMAP_MAP : thm
    val ofFMAP_EMPTY : thm
    val ofFMAP_FDOM : thm
    val ofFMAP_Sing : thm
    val ofFMAP_Sing_EMPTY : thm
    val ofFMAP_UNION : thm
    val ok_abs_slprpl : thm
    val ok_abs_slprpl_fix : thm
    val sbounds_frename_EMPTY : thm
    val shift_bmap'_FMAP_MAP : thm
    val shift_bmap_equiv : thm
    val shift_bmap_shift_bmap'_bmap_eff : thm
    val shift_bmap_shift_bmap'_equiv : thm
    val slprpl_id : thm
    val tprpl_FMAP_MAP_tprpl : thm
    val tprpl_shift_bmap'_tshift : thm
    val tprpl_shift_bmap_shift_bmap' : thm
    val wffVmap_fVmap_rename : thm
    val wffVmap_no_vbound : thm
    val wff_fVinst : thm
  
  val fVinst_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [fm] Parent theory of "fVinst"
   
   [Leq_def]  Definition
      
      ⊢ Leq = FST ∘ dest_eq
   
   [Req_def]  Definition
      
      ⊢ Req = SND ∘ dest_eq
   
   [bmap_eff_def]  Definition
      
      ⊢ ∀bmap i.
          bmap_eff bmap i = if i ∈ FDOM bmap then bmap ' i else Bound i
   
   [bmap_equiv_def]  Definition
      
      ⊢ ∀bmap1 bmap2.
          bmap_equiv bmap1 bmap2 ⇔ ∀i. bmap_eff bmap1 i = bmap_eff bmap2 i
   
   [fVmap_eff_def]  Definition
      
      ⊢ ∀σ P sl.
          fVmap_eff σ (P,sl) =
          if (P,sl) ∈ FDOM σ then σ ' (P,sl)
          else fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
   
   [fVmap_rename_def]  Definition
      
      ⊢ ∀n s nn σ.
          fVmap_rename (n,s) nn σ =
          FUN_FMAP (λ(P,sl). frename (n,s) nn (σ ' (P,sl))) (FDOM σ)
   
   [shift_bmap'_def]  Definition
      
      ⊢ ∀i bmap.
          shift_bmap' i bmap =
          FUN_FMAP
            (λn. if i ≤ n then tshift i (bmap ' (n − i)) else Bound n)
            (count i ∪ IMAGE ($+ i) (FDOM bmap))
   
   [FAPPLY_fVmap_rename]  Theorem
      
      ⊢ (P,sl) ∈ FDOM σ ⇒
        fVmap_rename (n,s) nn σ ' (P,sl) = frename (n,s) nn (σ ' (P,sl))
   
   [FAPPLY_shift_bmap']  Theorem
      
      ⊢ ∀x. (x ∈ FDOM bmap ⇒
             shift_bmap' i bmap ' (i + x) = tshift i (bmap ' x)) ∧
            ∀x. x < i ⇒ shift_bmap' i bmap ' x = Bound x
   
   [FDOM_fVmap_rename]  Theorem
      
      ⊢ FDOM (fVmap_rename (n,s) nn σ) = FDOM σ
   
   [FDOM_shift_bmap']  Theorem
      
      ⊢ FDOM (shift_bmap' i bmap) = count i ∪ IMAGE ($+ i) (FDOM bmap)
   
   [bmap_eff_fprpl]  Theorem
      
      ⊢ ∀f bmap1 bmap2.
          bmap_equiv bmap1 bmap2 ⇒ fprpl bmap1 f = fprpl bmap2 f
   
   [bmap_eff_shift_bmap]  Theorem
      
      ⊢ bmap_eff (shift_bmap n bmap) i =
        if ∃a. i = n + a ∧ a ∈ FDOM bmap then tshift n (bmap ' (i − n))
        else Bound i
   
   [bmap_eff_slprpl]  Theorem
      
      ⊢ ∀sl bmap1 bmap2.
          bmap_equiv bmap1 bmap2 ⇒ slprpl bmap1 sl = slprpl bmap2 sl
   
   [bmap_eff_tprpl]  Theorem
      
      ⊢ (∀tm bmap1 bmap2.
           bmap_equiv bmap1 bmap2 ⇒ tprpl bmap1 tm = tprpl bmap2 tm) ∧
        ∀st bmap1 bmap2.
          bmap_equiv bmap1 bmap2 ⇒ sprpl bmap1 st = sprpl bmap2 st
   
   [fVar_prpl_eq_lemma]  Theorem
      
      ⊢ MAP (tprpl (mk_bmap (REVERSE l0)) ∘ Bound)
          (REVERSE (COUNT_LIST (LENGTH l0))) =
        l0
   
   [fVar_prpl_fabs1]  Theorem
      
      ⊢ ∀f i σ.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∉ fVslfv f ∧
          (∀P sl. (P,sl) ∈ FDOM σ ∩ fVars f ⇒ (n,s) ∉ ffv (σ ' (P,sl))) ⇒
          fVinst σ (fabs (n,s) i f) = fabs (n,s) i (fVinst σ f)
   
   [fVars_DRESTRICT_fVinst_eq]  Theorem
      
      ⊢ ∀f σ. fVinst (DRESTRICT σ (fVars f)) f = fVinst σ f
   
   [fVars_DRESTRICT_fVinst_eq0]  Theorem
      
      ⊢ ∀f σ1 σ2.
          FDOM σ1 ∩ fVars f = FDOM σ2 ∩ fVars f ∧
          (∀fv. fv ∈ FDOM σ1 ∩ fVars f ⇒ σ1 ' fv = σ2 ' fv) ⇒
          fVinst σ1 f = fVinst σ2 f
   
   [fVars_DRESTRICT_fVinst_eq1]  Theorem
      
      ⊢ ∀f σ s. fVars f ⊆ s ⇒ fVinst σ f = fVinst (DRESTRICT σ s) f
   
   [fVars_fVinst]  Theorem
      
      ⊢ ∀f σ.
          fVars f ∪ fVars (fVinst σ f) = fVars f ∪ ofFMAP fVars σ (fVars f)
   
   [fVars_fabs]  Theorem
      
      ⊢ ∀f v i. fVars (fabs v i f) = fVars f
   
   [fVars_fprpl]  Theorem
      
      ⊢ ∀f bmap. fVars (fprpl bmap f) = fVars f
   
   [fVinst_EQ]  Theorem
      
      ⊢ fVinst σ (EQ t1 t2) = EQ t1 t2
   
   [fVinst_fabs]  Theorem
      
      ⊢ ∀f i.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∉ fVslfv f ∧
          (∀P sl.
             (P,sl) ∈ fVars f ∩ FDOM σ ⇒
             (nn,s) ∉ ffv (σ ' (P,sl)) ∧
             ∀st. MEM st sl ⇒ (n,s) ∉ sfv st ∧ (nn,s) ∉ sfv st) ∧
          (nn,s) ∉ ffv f ∧ nn ≠ n ⇒
          fVinst σ (fabs (n,s) i f) =
          frename (nn,s) n
            (fabs (n,s) i (fVinst (fVmap_rename (n,s) nn σ) f))
   
   [fVinst_id]  Theorem
      
      ⊢ ∀f ε. FDOM ε ∩ fVars f = ∅ ⇒ fVinst ε f = f
   
   [fVmap_no_bound_lemma]  Theorem
      
      ⊢ (∀P sl. (P,sl) ∈ FDOM σ ⇒ wff (Σf,Σp) (FALLL sl (σ ' (P,sl)))) ⇒
        ∀P sl n s.
          (P,sl) ∈ FDOM σ ⇒ (n,s) ∈ ffv (σ ' (P,sl)) ⇒ sbounds s = ∅
   
   [ffv_fVinst]  Theorem
      
      ⊢ ∀f σ.
          (∀P sl n s.
             (P,sl) ∈ FDOM σ ∩ fVars f ⇒
             (n,s) ∈ ffv (σ ' (P,sl)) ⇒
             sbounds s = ∅) ⇒
          ffv f ∪ ffv (fVinst σ f) =
          ffv f ∪ ofFMAP ffv σ (FDOM σ ∩ fVars f)
   
   [fprpl_FMAP_MAP]  Theorem
      
      ⊢ ∀f bmap bmap0.
          fbounds f ⊆ FDOM bmap0 ⇒
          fprpl (FMAP_MAP (tprpl bmap) bmap0) f =
          fprpl bmap (fprpl bmap0 f)
   
   [ofFMAP_EMPTY]  Theorem
      
      ⊢ ofFMAP f1 f2 ∅ = ∅
   
   [ofFMAP_FDOM]  Theorem
      
      ⊢ ofFMAP f σ (FDOM σ ∩ A) = ofFMAP f σ A
   
   [ofFMAP_Sing]  Theorem
      
      ⊢ x ∈ FDOM σ ⇒ ofFMAP f σ {x} = f (σ ' x)
   
   [ofFMAP_Sing_EMPTY]  Theorem
      
      ⊢ x ∉ FDOM σ ⇒ ofFMAP f σ {x} = ∅
   
   [ofFMAP_UNION]  Theorem
      
      ⊢ ofFMAP f σ (s1 ∪ s2) = ofFMAP f σ s1 ∪ ofFMAP f σ s2
   
   [ok_abs_slprpl]  Theorem
      
      ⊢ ∀l bmap. ok_abs l ⇒ slprpl bmap l = l
   
   [ok_abs_slprpl_fix]  Theorem
      
      ⊢ ok_abs l ⇒ slbounds l = ∅
   
   [sbounds_frename_EMPTY]  Theorem
      
      ⊢ (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ⇒
        ∀n s. (n,s) ∈ ffv (frename (n0,s0) nn f) ⇒ sbounds s = ∅
   
   [shift_bmap'_FMAP_MAP]  Theorem
      
      ⊢ ∀n bmap bmap0.
          FMAP_MAP (tprpl (shift_bmap' n bmap)) (shift_bmap' n bmap0) =
          shift_bmap' n (FMAP_MAP (tprpl bmap) bmap0)
   
   [shift_bmap_equiv]  Theorem
      
      ⊢ bmap_equiv bmap1 bmap2 ⇒
        ∀n. bmap_equiv (shift_bmap n bmap1) (shift_bmap n bmap2)
   
   [shift_bmap_shift_bmap'_bmap_eff]  Theorem
      
      ⊢ ∀n i bmap.
          bmap_eff (shift_bmap n bmap) i = bmap_eff (shift_bmap' n bmap) i
   
   [shift_bmap_shift_bmap'_equiv]  Theorem
      
      ⊢ bmap_equiv (shift_bmap' n bmap) (shift_bmap n bmap)
   
   [slprpl_id]  Theorem
      
      ⊢ ∀l. slbounds l = ∅ ⇒ ∀bmap. slprpl bmap l = l
   
   [tprpl_FMAP_MAP_tprpl]  Theorem
      
      ⊢ (∀tm bmap0 bmap.
           tbounds tm ⊆ FDOM bmap0 ⇒
           tprpl (FMAP_MAP (tprpl bmap) bmap0) tm =
           tprpl bmap (tprpl bmap0 tm)) ∧
        ∀st bmap0 bmap.
          sbounds st ⊆ FDOM bmap0 ⇒
          sprpl (FMAP_MAP (tprpl bmap) bmap0) st =
          sprpl bmap (sprpl bmap0 st)
   
   [tprpl_shift_bmap'_tshift]  Theorem
      
      ⊢ (∀tm n bmap.
           tprpl (shift_bmap' n bmap) (tshift n tm) =
           tshift n (tprpl bmap tm)) ∧
        ∀st n bmap.
          sprpl (shift_bmap' n bmap) (sshift n st) =
          sshift n (sprpl bmap st)
   
   [tprpl_shift_bmap_shift_bmap']  Theorem
      
      ⊢ (∀tm i bmap.
           tprpl (shift_bmap i bmap) tm = tprpl (shift_bmap' i bmap) tm) ∧
        ∀st i bmap.
          sprpl (shift_bmap i bmap) st = sprpl (shift_bmap' i bmap) st
   
   [wffVmap_fVmap_rename]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧
        wffVmap (Σf,Σp,Σe) σ ∧
        (∀P sl s0. (P,sl) ∈ FDOM σ ∧ MEM s0 sl ⇒ (n,s) ∉ sfv s0) ⇒
        wffVmap (Σf,Σp,Σe) (fVmap_rename (n,s) nn σ)
   
   [wffVmap_no_vbound]  Theorem
      
      ⊢ ∀σ. wffVmap Σ σ ⇒
            ∀P sl.
              (P,sl) ∈ FDOM σ ⇒
              ∀n s. (n,s) ∈ ffv (σ ' (P,sl)) ⇒ sbounds s = ∅
   
   [wff_fVinst]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀f. wff (Σf,Σp,Σe) f ⇒
            ∀σ. wffVmap (Σf,Σp,Σe) σ ⇒ wff (Σf,Σp,Σe) (fVinst σ f)
   
   
*)
end
