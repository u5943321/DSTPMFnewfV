signature renameTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val gcont_def : thm
    val rnmap_def : thm
  
  (*  Theorems  *)
    val BIGUNION_IMAGE_sbounds_ffv : thm
    val BIGUNION_IMAGE_sbounds_tfv : thm
    val BIGUNION_is_cont : thm
    val FAPPLY_rnmap : thm
    val FAPPLY_rnmap_SUBSET : thm
    val FDOM_rnmap : thm
    val FINITE_BIGUNION_tfv : thm
    val FINITE_lemma : thm
    val IN_tfv_trename : thm
    val NOTIN_frename : thm
    val NOTIN_trename : thm
    val cstt_rnmap : thm
    val fVar_subst_fabs : thm
    val ffv_FALLL : thm
    val ffv_fabs_SUBSET : thm
    val fprpl_FMAP_MAP_fabs_IN : thm
    val frename_FALLL : thm
    val frename_alt : thm
    val frename_finst : thm
    val frename_finst_ffv : thm
    val frename_fix : thm
    val fresh_name_ex : thm
    val gcont_EMPTY : thm
    val gcont_FINITE : thm
    val gcont_SING : thm
    val gcont_UNION : thm
    val gcont_is_cont : thm
    val gcont_of_cont : thm
    val mk_FALL_rename_eq : thm
    val no_subrename : thm
    val slprpl_FMAP_MAP_abssl_IN : thm
    val tprpl_FMAP_MAP_tabs_IN : thm
    val trename_alt : thm
    val trename_back : thm
    val trename_tinst : thm
    val trename_tinst_tfv : thm
    val wfcod_rnmap_BIGUNION : thm
    val wfcod_rnmap_SUBSET : thm
    val wfcod_rnmap_cont : thm
    val wfcod_rnmap_ffv : thm
    val wfcod_rnmap_gcont : thm
    val wfcod_rnmap_tfv : thm
    val wff_fVar_subst : thm
    val wff_frename : thm
    val wft_trename : thm
    val wft_trename0 : thm
  
  val rename_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [fsytx] Parent theory of "rename"
   
   [gcont_def]  Definition
      
      ⊢ ∀vs. gcont vs = vs ∪ BIGUNION {sfv s | (∃n. (n,s) ∈ vs)}
   
   [rnmap_def]  Definition
      
      ⊢ ∀n s nn vs.
          rnmap (n,s) nn vs =
          FUN_FMAP (λ(n1,s1). trename (n,s) nn (Var n1 s1)) vs
   
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
   
   [FAPPLY_rnmap]  Theorem
      
      ⊢ ∀vs n1 s1.
          FINITE vs ∧ (n1,s1) ∈ vs ⇒
          rnmap (n,s) nn vs ' (n1,s1) = trename (n,s) nn (Var n1 s1)
   
   [FAPPLY_rnmap_SUBSET]  Theorem
      
      ⊢ FINITE vs ∧ ss ⊆ vs ⇒
        ∀n1 s1.
          (n1,s1) ∈ ss ⇒
          rnmap (n,s) nn ss ' (n1,s1) = rnmap (n,s) nn vs ' (n1,s1)
   
   [FDOM_rnmap]  Theorem
      
      ⊢ ∀vs. FINITE vs ⇒ FDOM (rnmap (n,s) nn vs) = vs
   
   [FINITE_BIGUNION_tfv]  Theorem
      
      ⊢ FINITE (BIGUNION {tfv t | MEM t tl})
   
   [FINITE_lemma]  Theorem
      
      ⊢ FINITE {f t | MEM t l}
   
   [IN_tfv_trename]  Theorem
      
      ⊢ (∀tm n s nn. (n,s) ∈ tfv tm ⇒ (nn,s) ∈ tfv (trename (n,s) nn tm)) ∧
        ∀st n s nn. (n,s) ∈ sfv st ⇒ (nn,s) ∈ sfv (srename (n,s) nn st)
   
   [NOTIN_frename]  Theorem
      
      ⊢ ∀f. nn ≠ n ⇒ (n,s) ∉ ffv (frename (n,s) nn f)
   
   [NOTIN_trename]  Theorem
      
      ⊢ (∀tm. nn ≠ n ⇒ (n,s) ∉ tfv (trename (n,s) nn tm)) ∧
        ∀st. nn ≠ n ⇒ (n,s) ∉ sfv (srename (n,s) nn st)
   
   [cstt_rnmap]  Theorem
      
      ⊢ ∀vs. FINITE vs ∧ is_cont vs ⇒ cstt (rnmap (n,s) nn vs)
   
   [fVar_subst_fabs]  Theorem
      
      ⊢ ∀f i.
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
          (P,sl) ∈ freefVars f ∧ (∀st. MEM st sl ⇒ (n,s) ∉ sfv st) ∧
          (nn,s) ∉ ffv ϕ ∧ (∀st. MEM st sl ⇒ (nn,s) ∉ sfv st) ∧
          (nn,s) ∉ ffv f ∧ nn ≠ n ⇒
          fVar_subst (P,sl,ϕ) (fabs (n,s) i f) =
          frename (nn,s) n
            (fabs (n,s) i (fVar_subst (P,sl,frename (n,s) nn ϕ) f))
   
   [ffv_FALLL]  Theorem
      
      ⊢ ∀sl f. ffv (FALLL sl f) = BIGUNION {sfv s | MEM s sl} ∪ ffv f
   
   [ffv_fabs_SUBSET]  Theorem
      
      ⊢ ∀fm i n s.
          (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ⇒
          ffv (fabs (n,s) i fm) ⊆ ffv fm DELETE (n,s)
   
   [fprpl_FMAP_MAP_fabs_IN]  Theorem
      
      ⊢ ∀ϕ i n s bmap.
          (nn,s) ∉ ffv ϕ ∧ (∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
          (∀b n1 s1.
             b ∈ FDOM bmap ∧ (n1,s1) ∈ tfv (bmap ' b) ⇒ (n,s) ∉ sfv s1) ∧
          n ≠ nn ⇒
          fprpl (FMAP_MAP (tabs (n,s) i) bmap) ϕ =
          frename (nn,s) n (fabs (n,s) i (fprpl bmap (frename (n,s) nn ϕ)))
   
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
   
   [frename_finst]  Theorem
      
      ⊢ ∀f n s nn vs.
          FINITE vs ∧ ffv f ⊆ vs ⇒
          frename (n,s) nn f = finst (rnmap (n,s) nn vs) f
   
   [frename_finst_ffv]  Theorem
      
      ⊢ frename (n,s) nn f = finst (rnmap (n,s) nn (ffv f)) f
   
   [frename_fix]  Theorem
      
      ⊢ ∀f n s. (n,s) ∉ ffv f ⇒ frename (n,s) nn f = f
   
   [fresh_name_ex]  Theorem
      
      ⊢ ∀vs. FINITE vs ⇒ ∃nn. ∀s. (nn,s) ∉ vs
   
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
   
   [mk_FALL_rename_eq]  Theorem
      
      ⊢ ∀f. (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (nn,s) ∉ ffv f ⇒
            mk_FALL n s f = mk_FALL nn s (frename (n,s) nn f)
   
   [no_subrename]  Theorem
      
      ⊢ ∀n0 s0. (n0,s0) ∈ sfv s ⇒ trename (n,s) nn (Var n0 s0) = Var n0 s0
   
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
        ∀f. wff (Σf,Σp) f ⇒ ∀n s ss. wfcod Σf (rnmap (n,s) nn (ffv f))
   
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
   
   [wff_fVar_subst]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀f. wff (Σf,Σp) f ⇒
            ∀P sl ϕ.
              wff (Σf,Σp) (FALLL sl ϕ) ⇒
              wff (Σf,Σp) (fVar_subst (P,sl,ϕ) f)
   
   [wff_frename]  Theorem
      
      ⊢ (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
        ∀f. wff (Σf,Σp) f ⇒ ∀n s nn. wff (Σf,Σp) (frename (n,s) nn f)
   
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
