open HolKernel Parse boolLib bossLib;
open finite_setTheory;
open finite_mapTheory;
open pred_setTheory;
val _ = new_theory "fsytx";



Datatype:
  form = False
       | Pred string (term list)
       | IMP form form
       | FALL sort form
       | fVar string (sort list) (term list)
End

val form_size_def = DB.fetch "-" "form_size_def"    
val _ = export_rewrites ["form_size_def"]
        

Definition ispsym_def:
  ispsym Σp p ⇔ p ∈ FDOM Σp
End


Definition psymin_def:
  psymin Σp p = Σp ' p
End



Definition ffv_def[simp]:
  ffv False = {} ∧
  ffv (Pred p tl) = BIGUNION (set (MAP tfv tl)) ∧
  ffv (fVar p sl tl) = BIGUNION (set (MAP sfv sl)) ∪ BIGUNION (set (MAP tfv tl)) ∧
  ffv (FALL s f) = sfv s ∪ ffv f ∧
  ffv (IMP f1 f2) = ffv f1 ∪ ffv f2
End


Theorem ffv_thm[simp]:
  ffv False = {} ∧
  ffv (Pred p tl) = BIGUNION {tfv t | MEM t tl} ∧
  ffv (fVar p sl tl) = BIGUNION {sfv s | MEM s sl} ∪  BIGUNION {tfv t | MEM t tl} ∧
  ffv (FALL s f) = sfv s ∪ ffv f ∧
  ffv (IMP f1 f2) = ffv f1 ∪ ffv f2
Proof
simp[ffv_def,PULL_EXISTS] >> simp[Once EXTENSION,PULL_EXISTS,MEM_MAP,LIST_TO_SET_MAP,IMAGE_DEF,EXTENSION]
QED


Definition subst_def:
  subst _ _ False = False ∧
  subst t i (Pred p tl) =
  Pred p (MAP (treplace i t) tl) ∧
  subst t i (fVar p sl tl) =
  fVar p (slreplace i t sl) (MAP (treplace i t) tl) ∧
  subst t i (IMP f1 f2) =
  IMP (subst t i f1) (subst t i f2) ∧
  subst t i (FALL s b) =
  FALL (sreplace i t s) (subst t (i + 1) b)
End

Definition subst_bound_def:
  subst_bound t f = subst t 0 f
End  



(*new *)
Definition abs_def:
  abs _ _ False = False ∧
  abs v i (Pred p tl) =
  Pred p (MAP (tsubst v (Bound i)) tl) ∧
  abs v i (fVar p vl tl) =
  fVar p (slabs v i vl)
         (MAP (tsubst v (Bound i)) tl) ∧
  abs v i (IMP f1 f2) =
  IMP (abs v i f1) (abs v i f2) ∧
  abs v i (FALL s b) =
  FALL (ssubst v (Bound i) s) (abs v (i + 1) b)
End     


Definition abstract_def:
  abstract v = abs v 0
End

Definition mk_FALL_def:
mk_FALL n s b = FALL s (abstract (n,s) b)
End        

Definition fbounds_def:
fbounds False = {} ∧
fbounds (fVar P sl tl) = 
(slbounds sl) ∪
BIGUNION (set (MAP tbounds tl)) ∧
fbounds (Pred p tl) = BIGUNION (set (MAP tbounds tl)) ∧
fbounds (IMP f1 f2) = fbounds f1 ∪ fbounds f2 ∧
fbounds (FALL s b) =
sbounds s ∪ IMAGE PRE (fbounds b DELETE 0) 
End



Theorem fbounds_thm:
fbounds False = {} ∧
fbounds (fVar P sl tl) = 
(slbounds sl) ∪ BIGUNION {tbounds t | MEM t tl} ∧
fbounds (Pred p tl) = BIGUNION {tbounds t | MEM t tl} ∧
fbounds (IMP f1 f2) = fbounds f1 ∪ fbounds f2 ∧
fbounds (FALL s b) =
sbounds s ∪ IMAGE PRE (fbounds b DELETE 0) 
Proof
simp[fbounds_def,PULL_EXISTS] >> simp[Once EXTENSION,PULL_EXISTS,MEM_MAP,LIST_TO_SET_MAP,IMAGE_DEF,EXTENSION]
QED 
        
   
Inductive wff:
[~False:]
(wff (Σf,Σp) False) ∧
[~Pred:]
  ((∀t. MEM t tl ⇒ wft Σf t) ∧
ispsym Σp p ∧
IS_SOME
(tlmatch {} (MAP (UNCURRY Var) (Σp ' p)) tl FEMPTY) ⇒
wff (Σf,Σp) (Pred p tl)) ∧
[~IMP:]
  (wff (Σf,Σp) f1 ∧ wff (Σf,Σp) f2 ⇒
  wff (Σf,Σp) (IMP f1 f2)) ∧
[~fVar:]
  (wfabsap Σf sl tl ⇒
  wff (Σf,Σp) (fVar P sl tl)) ∧
[~FALL:]
 (∀f n s.
  wff (Σf,Σp) f ∧ wfs Σf s ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
  wff (Σf,Σp) (mk_FALL n s f))
End

                
Definition finst_def[simp]:
  finst σ False = False ∧
  finst σ (Pred p tl) = Pred p (MAP (tinst σ) tl) ∧
  finst σ (IMP f1 f2) = IMP (finst σ f1) (finst σ f2) ∧
  (finst σ (fVar p sl tl) =
  fVar p (MAP (sinst σ) sl)
  (MAP (tinst σ) tl)) ∧
  finst σ (FALL s f) =
    FALL (sinst σ s) (finst σ f)
End                
                

Theorem ffv_is_cont:
 ∀f.  is_cont (ffv f)
Proof
Induct_on ‘f’ >> rw[ffv_thm,is_cont_def] (* 6 *)
>- (rw[SUBSET_DEF,PULL_EXISTS] >> qexists ‘t’ >> simp[] >>
   metis_tac[vsort_tfv_closed])
>- (gs[is_cont_def] >>
   first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF])
>- (gs[is_cont_def] >>
   first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF])
>- (qspecl_then [‘s’] assume_tac $ cj 2 tfv_is_cont >>
   gs[is_cont_def] >>
   first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (gs[is_cont_def] >>
   first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF])
>- (qspecl_then [‘s''’] assume_tac $ cj 2 tfv_is_cont >>
   gs[is_cont_def] >>
   first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
qspecl_then [‘t’] assume_tac $ cj 1 tfv_is_cont >>
gs[is_cont_def] >>
first_x_assum $ drule_then assume_tac >>
gs[SUBSET_DEF] >> metis_tac[]   
QED



Theorem fmap_ffv_finst_eq:
  (∀f σ1 σ2.
     ffv f ⊆ FDOM σ1 ∧ ffv f ⊆ FDOM σ2 ∧
     (∀x. x ∈ ffv f ⇒ σ1 ' x = σ2 ' x) ⇒
     finst σ1 f = finst σ2 f)
Proof
  Induct_on ‘f’ >> gs[finst_def] (* 3 *)
  >- (rw[MAP_EQ_f] >>
     irule $ cj 1 fmap_fv_inst_eq_alt >>
     gs[SUBSET_DEF,MEM_MAP] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
     rw[] >>
     irule $ cj 2 fmap_fv_inst_eq_alt >>
     gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]) >>
  rw[MAP_EQ_f] (* 2 *)
  >- (irule $ cj 2 fmap_fv_inst_eq_alt >>
     gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]) >>
  irule $ cj 1 fmap_fv_inst_eq_alt >>
  gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]
QED  


Theorem fmap_ffv_finst_eq1:
  (∀f σ1 σ2.
     DRESTRICT σ1 (ffv f) = DRESTRICT σ2 (ffv f) ⇒
     finst σ1 f = finst σ2 f)
Proof
  Induct_on ‘f’ >> gs[finst_def] (* 3 *)
  >- (rw[MAP_EQ_f] >>
     irule $ cj 1 fmap_fv_inst_eq >>
      irule DRESTRICT_SUBSET >> first_x_assum $ irule_at Any >>      
     gs[SUBSET_DEF,MEM_MAP] >> metis_tac[])
  >- (rw[] >> first_x_assum irule >> irule DRESTRICT_SUBSET >>
      first_x_assum $ irule_at Any >>   gs[SUBSET_DEF,MEM_MAP] >> metis_tac[])
  >- (rw[] (* 2 *)
     >- (irule $ cj 2 fmap_fv_inst_eq >>
        irule DRESTRICT_SUBSET >> first_x_assum $ irule_at Any >>      
        gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]) >>
     first_x_assum irule >>
     irule DRESTRICT_SUBSET >> first_x_assum $ irule_at Any >>      
     gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]) >>
  rw[MAP_EQ_f]
  >- (irule $ cj 2 fmap_fv_inst_eq >>
      irule DRESTRICT_SUBSET >> first_x_assum $ irule_at Any >>      
      gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]) >>
  irule $ cj 1 fmap_fv_inst_eq >>
  irule DRESTRICT_SUBSET >> first_x_assum $ irule_at Any >>      
  gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]      
QED  


Theorem abs_id:
∀f n s i. (n,s) ∉ ffv f ⇒ abs (n,s) i f = f
Proof
Induct_on ‘f’ (* 5 *)
>- rw[abs_def]
>- (rw[abs_def,MAP_fix] >>
   metis_tac[tsubst_id])
>- rw[abs_def]
>- (rw[abs_def] >> metis_tac[tsubst_id]) >>
rw[abs_def,MAP_fix] (* 2 *)
>- (irule LIST_EQ >> simp[LENGTH_slabs] >> rw[] >>
   drule_then assume_tac slabs_EL >>simp[] >>
   irule $ cj 2 tsubst_id >>
   metis_tac[MEM_EL]) >>
metis_tac[tsubst_id]
QED


Theorem ffv_abs:
∀fm i n s.
 (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ∧
 (n,s) ∈ ffv fm ⇒
 sfv s ∪ ffv (abs (n,s) i fm) =
 ffv fm DELETE (n,s)
Proof
Induct_on ‘fm’ (* 5 *)
>- rw[ffv_def,abs_def]
>- (rw[ffv_thm,abs_def] >> gs[MEM_MAP,PULL_EXISTS] >>
   rename [‘(n,s) ∈ tfv t’] >>
    ‘BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l)} =
    (BIGUNION {tfv t1 | (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∈ tfv y)}) ∪
    (BIGUNION {tfv t1 | (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∉ tfv y)})’
    by (rw[EXTENSION] >> metis_tac[]) >>
    qabbrev_tac ‘BU =  BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l)}’ >>
    qabbrev_tac ‘BU1 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∈ tfv y)}’ >>
    qabbrev_tac ‘BU2 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∉ tfv y)}’ >>
    simp[] >>
    ‘BU2 = BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y}’
     by
      (rw[Abbr‘BU2’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
      (* 2 *)
      >> (‘(tsubst (n,s) (Bound i) y) = y’
          suffices_by metis_tac[] >>
         irule $ cj 1 tsubst_id >> simp[])) >>
    simp[UNION_ASSOC] >>
   ‘sfv s ∪ BU1 =
     BIGUNION {sfv s0 ∪ tfv t1 |
     (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧ s0 = s}’
     by (rw[Abbr‘BU1’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv t1 |
           (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧
           s0 = s} =
      BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
            MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >> simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} =
      BIGUNION
          {tfv y DELETE (n0,s0) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by
        (‘∀y n0 s0. MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n ⇒
          sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) =
          tfv y DELETE (n0,s0)’
         suffices_by
          (strip_tac >> AP_TERM_TAC >> 
          rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
          metis_tac[]) >>
         rw[] >>
         irule $ cj 1 tfv_tsubst >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {tfv y DELETE (n0,s0) | MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} ∪
        BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} =
     BIGUNION {tfv y | MEM y l} DELETE (n,s)’
      by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
         >>  metis_tac[]) >>
     simp[])
>- (rw[ffv_thm,abs_def] (* 2 *)   
   >- (Cases_on ‘(n,s) ∈ ffv fm'’ (* 2 *)
      >- (‘sfv s ∪ (ffv (abs (n,s) i fm) ∪ ffv (abs (n,s) i fm')) = (sfv s ∪ ffv (abs (n,s) i fm)) ∪ (sfv s ∪ ffv (abs (n,s) i fm'))’ by (rw[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘sfv s ∪ ffv (abs (n,s) i fm) = ffv fm DELETE (n,s) ∧
       sfv s ∪ ffv (abs (n,s) i fm') = ffv fm' DELETE (n,s)’
       by metis_tac[] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
      rw[UNION_ASSOC] >>
      ‘sfv s ∪ ffv (abs (n,s) i fm) = ffv fm DELETE (n,s)’
       by metis_tac[] >>
      ‘(abs (n,s) i fm') = fm'’
       by metis_tac[abs_id] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
  Cases_on ‘(n,s) ∈ ffv fm’ (* 2 *)
  >- (‘sfv s ∪ (ffv (abs (n,s) i fm) ∪ ffv (abs (n,s) i fm')) = (sfv s ∪ ffv (abs (n,s) i fm)) ∪ (sfv s ∪ ffv (abs (n,s) i fm'))’ by (rw[EXTENSION] >> metis_tac[]) >>
    simp[] >>
    ‘sfv s ∪ ffv (abs (n,s) i fm) = ffv fm DELETE (n,s) ∧
     sfv s ∪ ffv (abs (n,s) i fm') = ffv fm' DELETE (n,s)’
      by metis_tac[] >>
    simp[] >> rw[EXTENSION] >> metis_tac[]) >>
  rw[UNION_ASSOC] >>
  ‘sfv s ∪ ffv (abs (n,s) i fm') = ffv fm' DELETE (n,s)’
    by metis_tac[] >>
  ‘(abs (n,s) i fm) = fm’
   by metis_tac[abs_id] >>
  simp[] >>
   ‘sfv s ∪ ffv fm ∪ ffv (abs (n,s) i fm') =
   sfv s ∪ ffv (abs (n,s) i fm') ∪ ffv fm’
    by (rw[EXTENSION] >> metis_tac[]) >> simp[] >>
   rw[EXTENSION] >> metis_tac[])
>- (rw[ffv_thm,abs_def] (* 2 *)
   >- (Cases_on ‘(n,s') ∈ ffv fm’ (* 2 *) >-
      (‘sfv s' ∪ (sfv (ssubst (n,s') (Bound i) s) ∪ ffv (abs (n,s') (i+1) fm)) =
      (sfv s' ∪ (sfv (ssubst (n,s') (Bound i) s)) ∪ (sfv s' ∪ ffv (abs (n,s') (i+1) fm)))’
       by (rw[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘sfv s' ∪
        (sfv (ssubst (n,s') (Bound i) s)) =
       sfv s DELETE (n,s')’ by metis_tac[tfv_tsubst] >>
      simp[] >>
      ‘(sfv s' ∪ ffv (abs (n,s') (i+1) fm)) =
      ffv fm DELETE (n,s')’ by metis_tac[] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
      ‘abs (n,s') (i + 1) fm = fm’ by metis_tac[abs_id] >>
      simp[] >> rw[UNION_ASSOC]>>
      ‘sfv s' ∪ sfv (ssubst (n,s') (Bound i) s) =
      sfv s DELETE (n,s')’  by metis_tac[tfv_tsubst] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
   (Cases_on ‘(n,s') ∈ sfv s’ (* 2 *) >-
      (‘sfv s' ∪ (sfv (ssubst (n,s') (Bound i) s) ∪ ffv (abs (n,s') (i+1) fm)) =
      (sfv s' ∪ (sfv (ssubst (n,s') (Bound i) s)) ∪ (sfv s' ∪ ffv (abs (n,s') (i+1) fm)))’
       by (rw[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘sfv s' ∪
        (sfv (ssubst (n,s') (Bound i) s)) =
       sfv s DELETE (n,s')’ by metis_tac[tfv_tsubst] >>
      simp[] >>
      ‘(sfv s' ∪ ffv (abs (n,s') (i+1) fm)) =
      ffv fm DELETE (n,s')’ by metis_tac[] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
      ‘ssubst (n,s') (Bound i) s = s’
       by metis_tac[tsubst_id] >>
      simp[] >> rw[UNION_ASSOC]>>
      ‘sfv s' ∪ sfv s ∪ ffv (abs (n,s') (i + 1) fm) =
        sfv s ∪ (sfv s' ∪ ffv (abs (n,s') (i + 1) fm)) ’
        by (rw[EXTENSION] >> metis_tac[]) >> simp[] >>
      ‘sfv s' ∪ ffv (abs (n,s') (i + 1) fm) =
      ffv fm DELETE (n,s')’  by metis_tac[] >>
      simp[] >> rw[EXTENSION] >> metis_tac[])) >>
(*fVar case*)      
rw[ffv_thm,abs_def] >> gs[MEM_MAP,PULL_EXISTS] >-
(rename [‘(n,st) ∈ sfv s’,‘ MEM s sl’] >>
‘{sfv s | MEM s (slabs (n,st) i sl)} =
 {sfv (ssubst (n,st) (Bound (i + m)) (EL m sl)) | m | m < LENGTH sl}’
 by (simp[Once EXTENSION] >> rw[EQ_IMP_THM] (* 2 *)
    >- (gs[MEM_EL] >> qexistsl [‘n''’] >>
       gs[LENGTH_slabs] >> AP_TERM_TAC >>
       metis_tac[slabs_EL]) >>
    qexists ‘EL m (slabs (n,st) i sl)’ >>
    gs[MEM_EL,LENGTH_slabs,PULL_EXISTS] >> qexists ‘m’ >> simp[] >>
    AP_TERM_TAC >> metis_tac[slabs_EL]) >>
‘sfv st ∪
 BIGUNION {sfv s | MEM s (slabs (n,st) i sl)}
 = BIGUNION {sfv s | MEM s sl} DELETE (n,st)’
 by
 (simp[] >> rw[Once EXTENSION,PULL_EXISTS] >>
  rw[EQ_IMP_THM] (* 3 *)
  >- (qexists ‘s’ >> simp[] >>
      metis_tac[vsort_tfv_closed])
  >- (Cases_on ‘(n,st) ∈ sfv (EL m sl)’ (* 2 *)
      >- (‘sfv st ∪ sfv (ssubst (n,st) (Bound (i+ m)) (EL m sl)) =
           sfv (EL m sl) DELETE (n,st)’
            by (irule $ cj 2 tfv_tsubst >> metis_tac[MEM_EL]) >>
          ‘x ∈ sfv st ∪ sfv (ssubst (n,st) (Bound (i+m)) (EL m sl))’
            by rw[UNION_DEF] >>
          gs[EXTENSION] >> metis_tac[MEM_EL]) >>
      ‘ssubst (n,st) (Bound (i+m)) (EL m sl) = (EL m sl)’
        by (irule $ cj 2 tsubst_id >> simp[]) >>
      metis_tac[MEM_EL]) >>
  gvs[MEM_EL] >> rename [‘x ∈ sfv (EL n1 sl)’] >> 
  Cases_on ‘(n,st) ∈ sfv (EL n1 sl)’ (* 2 *)
  >- (‘sfv st ∪ sfv (ssubst (n,st) (Bound (i+n1)) (EL n1 sl)) =
       sfv (EL n1 sl) DELETE (n,st)’
        by (irule $ cj 2 tfv_tsubst >> metis_tac[MEM_EL]) >>
      ‘x ∈ sfv (EL n1 sl) DELETE (n,st)’ by simp[] >>
      qpat_x_assum ‘sfv st ∪ sfv (ssubst (n,st) (Bound (i + n1)) (EL n1 sl)) =
        sfv (EL n1 sl) DELETE (n,st)’ (assume_tac o GSYM) >>
      pop_assum SUBST_ALL_TAC >>
      gs[UNION_DEF] >> metis_tac[MEM_EL]) >>
  ‘ssubst (n,st) (Bound (i+n1)) (EL n1 sl)= (EL n1 sl)’
    by (irule $ cj 2 tsubst_id >> simp[]) >>
  metis_tac[MEM_EL]) >>
 Cases_on ‘∃t. MEM t l0 ∧ (n,st) ∈ tfv t’ (* 2 *)
>-(‘sfv st ∪
    BIGUNION {tfv t | (∃y. t = tsubst (n,st) (Bound i) y ∧ MEM y l0)} = BIGUNION {tfv t | MEM t l0} DELETE (n,st)’
     by
     (rw[Once EXTENSION,PULL_EXISTS] >>
      rw[EQ_IMP_THM] (* 3 *)
      >- (qexists ‘t’ >> simp[] >>
          metis_tac[vsort_tfv_closed])
      >- (Cases_on ‘(n,st) ∈ tfv y’ (* 2 *)
          >- (‘sfv st ∪ tfv (tsubst (n,st) (Bound i) y) =
               tfv y DELETE (n,st)’
                by (irule $ cj 1 tfv_tsubst >> metis_tac[]) >>
              ‘x ∈ sfv st ∪ tfv (tsubst (n,st) (Bound i) y)’
                by rw[UNION_DEF] >>
              gs[EXTENSION] >> metis_tac[]) >>
          ‘tsubst (n,st) (Bound i) y = y’
            by (irule $ cj 1 tsubst_id >> simp[]) >>
          metis_tac[]) >>
      rename [‘x ∈ tfv y’] >>
      Cases_on ‘(n,st) ∈ tfv y’ (* 2 *)
      >- (‘sfv st ∪ tfv (tsubst (n,st) (Bound i) y) =
           tfv y DELETE (n,st)’
            by (irule $ cj 1 tfv_tsubst >> metis_tac[]) >>
          ‘x ∈ tfv y DELETE (n,st)’ by simp[] >>
          qpat_x_assum ‘sfv st ∪ tfv (tsubst (n,st) (Bound i) y) = tfv y DELETE (n,st)’ (assume_tac o GSYM) >>
          pop_assum SUBST_ALL_TAC >>
          gs[UNION_DEF] >> metis_tac[]) >>
      ‘tsubst (n,st) (Bound i) y = y’
        by (irule $ cj 1 tsubst_id >> simp[]) >>
      metis_tac[]) >> simp[] >>
   gs[EXTENSION] >> metis_tac[]) >>
simp[UNION_ASSOC] >>
‘BIGUNION {tfv t | (∃y. t = tsubst (n,st) (Bound i) y ∧ MEM y l0)} =  BIGUNION {tfv t | MEM t l0}’ 
  by (AP_TERM_TAC >> rw[Once EXTENSION] >>
      ‘∀y. MEM y l0 ⇒ tsubst (n,st) (Bound i) y = y’
        suffices_by  metis_tac[] >>
      rw[] >> metis_tac[tsubst_id]) >>
simp[] >> gs[EXTENSION] >> metis_tac[]) >>
(*last subgoal*)
rename [‘(n,s) ∈ tfv t’,‘ (slabs (n,s) i sl)’] >>
‘{sfv st | MEM st (slabs (n,s) i sl)} =
 {sfv (ssubst (n,s) (Bound (i + m)) (EL m sl)) | m | m < LENGTH sl}’
 by (simp[Once EXTENSION] >> rw[EQ_IMP_THM] (* 2 *)
    >- (gs[MEM_EL] >> qexistsl [‘n''’] >>
       gs[LENGTH_slabs] >> AP_TERM_TAC >>
       metis_tac[slabs_EL]) >>
    qexists ‘EL m (slabs (n,s) i sl)’ >>
    gs[MEM_EL,LENGTH_slabs,PULL_EXISTS] >> qexists ‘m’ >> simp[] >>
    AP_TERM_TAC >> metis_tac[slabs_EL]) >>
‘sfv s ∪
 BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l0)} = BIGUNION {tfv t | MEM t l0}  DELETE (n,s)’
  by
  (rw[Once EXTENSION,PULL_EXISTS] >>
   rw[EQ_IMP_THM] (* 3 *)
   >- (qexists ‘t’ >> simp[] >>
       metis_tac[vsort_tfv_closed] )
   >- (Cases_on ‘(n,s) ∈ tfv y’ (* 2 *)
       >- (‘sfv s ∪ tfv (tsubst (n,s) (Bound i) y) =
            tfv y DELETE (n,s)’
             by (irule $ cj 1 tfv_tsubst >> metis_tac[]) >>
           ‘x ∈ sfv s ∪ tfv (tsubst (n,s) (Bound i) y) ’
             by rw[UNION_DEF] >>
           gs[EXTENSION] >> metis_tac[]) >>
       ‘tsubst (n,s) (Bound i) y = y’
         by (irule $ cj 1 tsubst_id >> simp[]) >>
       metis_tac[]) >>
   rename [‘x ∈ tfv y’] >>
   Cases_on ‘(n,s) ∈ tfv y’ (* 2 *)
   >- (‘sfv s ∪ tfv (tsubst (n,s) (Bound i) y) =
        tfv y DELETE (n,s)’
         by (irule $ cj 1 tfv_tsubst >> metis_tac[]) >>
       ‘x ∈ tfv y DELETE (n,s)’ by simp[] >>
       qpat_x_assum ‘sfv s ∪ tfv (tsubst (n,s) (Bound i) y) = tfv y DELETE (n,s)’ (assume_tac o GSYM) >>
       pop_assum SUBST_ALL_TAC >>
       gs[UNION_DEF] >> metis_tac[]) >>
   ‘tsubst (n,s) (Bound i) y = y’
     by (irule $ cj 1 tsubst_id >> simp[]) >>
   metis_tac[]) >>
Cases_on ‘∃s1. MEM s1 sl ∧ (n,s) ∈ sfv s1’ (* 2 *)
>- (‘sfv s ∪
    BIGUNION {sfv s' | MEM s' (slabs (n,s) i sl)} = BIGUNION {sfv s | MEM s sl} DELETE (n,s)’
     by
     (gs[] >> rw[Once EXTENSION,PULL_EXISTS] >>
      rw[EQ_IMP_THM] (* 3 *)
      >- (qexists ‘s1’ >> simp[] >>
          metis_tac[vsort_tfv_closed])
      >- (Cases_on ‘(n,s) ∈ sfv (EL m sl)’ (* 2 *)
          >- (‘sfv s ∪ sfv (ssubst (n,s) (Bound (i+ m)) (EL m sl)) =
               sfv (EL m sl) DELETE (n,s)’
                by (irule $ cj 2 tfv_tsubst >> metis_tac[MEM_EL]) >>
              ‘x ∈ sfv s ∪ sfv (ssubst (n,s) (Bound (i+m)) (EL m sl))’
                by rw[UNION_DEF] >>
              gs[EXTENSION] >> metis_tac[MEM_EL]) >>
          ‘ssubst (n,s) (Bound (i+m)) (EL m sl) = (EL m sl)’
            by (irule $ cj 2 tsubst_id >> simp[]) >>
          metis_tac[MEM_EL]) >>
      gvs[MEM_EL] >> rename [‘x ∈ sfv (EL n1 sl)’] >> 
      Cases_on ‘(n,s) ∈ sfv (EL n1 sl)’ (* 2 *)
      >- (‘sfv s ∪ sfv (ssubst (n,s) (Bound (i+n1)) (EL n1 sl)) =
           sfv (EL n1 sl) DELETE (n,s)’
            by (irule $ cj 2 tfv_tsubst >> metis_tac[MEM_EL]) >>
          ‘x ∈ sfv (EL n1 sl) DELETE (n,s)’ by simp[] >>
          qpat_x_assum ‘sfv s ∪ sfv (ssubst (n,s) (Bound (i + n1)) (EL n1 sl)) =
        sfv (EL n1 sl) DELETE (n,s)’ (assume_tac o GSYM) >>
          pop_assum SUBST_ALL_TAC >>
          gs[UNION_DEF] >> metis_tac[MEM_EL]) >>
      ‘ssubst (n,s) (Bound (i+n1)) (EL n1 sl)= (EL n1 sl)’
        by (irule $ cj 2 tsubst_id >> simp[]) >>
      metis_tac[MEM_EL]) >> 
     simp[] >> gs[EXTENSION] >> metis_tac[]) >>
(*last subgoal*) 
 ‘BIGUNION  {sfv s' | MEM s' (slabs (n,s) i sl)} = BIGUNION {sfv s | MEM s sl}’ 
     by (AP_TERM_TAC >> rw[Once EXTENSION] >>
         rw[MEM_EL,PULL_EXISTS,LENGTH_slabs] >> rw[EQ_IMP_THM] (* 2 *)
         >- (drule_then assume_tac slabs_EL >> simp[] >>
            qexists ‘n'’ >> simp[] >> AP_TERM_TAC >>
            irule $ cj 2 tsubst_id >> metis_tac[MEM_EL]) >> 
         drule_then assume_tac slabs_EL >> simp[] >>
         qexists ‘n'’ >> simp[] >> AP_TERM_TAC >>
         rw[Once EQ_SYM_EQ] >>
         irule $ cj 2 tsubst_id >> metis_tac[MEM_EL]) >> 
simp[] >> gs[EXTENSION] >> metis_tac[]
QED
                     
    
Theorem ffv_mk_FALL:
∀f n s.
(∀n0 s0. (n0,s0) ∈ ffv f ⇒ (n,s) ∉ sfv s0) ⇒
ffv (mk_FALL n s f) = (ffv f ∪ sfv s) DELETE (n,s)
Proof
rw[ffv_thm,mk_FALL_def,abstract_def] >>
Cases_on ‘(n,s) ∈ ffv f’ (*2 *)
>- (drule_all_then assume_tac ffv_abs >> simp[] >>
   ‘sfv s  ⊆ ffv f DELETE (n,s)’
     suffices_by (gs[EXTENSION] >> gs[SUBSET_DEF] >>
                 metis_tac[]) >>
   gs[SUBSET_DEF,EXTENSION] >>  metis_tac[]) >>
‘(abs (n,s) 0 f) = f’ by metis_tac[abs_id] >>
simp[] >>
rw[EXTENSION] >> metis_tac[tm_tree_WF]
QED

Theorem finst_abstract:
∀f an ast σ nn i.
  ffv f ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧
  (an,ast) ∉ FDOM σ ∧
  (∀x s. x ∈ ffv f ∪ sfv ast ∧ x ≠ (an,ast) ⇒
   (nn,s) ∉ tfv (σ ' x)) ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (an,ast) ∉ sfv s1) ⇒ 
  abs (nn,sinst σ ast) i
          (finst (σ |+ ((an,ast),Var nn (sinst σ ast))) f) =
  finst σ (abs (an,ast) i f)
Proof
 Induct_on ‘f’
 >- rw[abstract_def,finst_def,abs_def]
 >- (rw[abstract_def,finst_def,abs_def,
        MAP_MAP_o,MAP_EQ_f] >>
    irule tsubst_tinst >> simp[] >>
    gs[SUBSET_DEF] >> metis_tac[])
 >- (rw[abstract_def,abs_def] (* 2 *) >>
    simp[GSYM abstract_def] >>
    first_x_assum irule >>
    gs[SUBSET_DEF] >> metis_tac[])
 >- (rw[abstract_def,abs_def] (* 2 *)
    >- (irule ssubst_sinst >>
       gs[SUBSET_DEF] >> metis_tac[]) >>
    first_x_assum irule >>
    gs[SUBSET_DEF] >> metis_tac[]) >>
 rw[abstract_def,finst_def,abs_def,
    MAP_MAP_o,MAP_EQ_f] (* 2 *)
 >- (irule MAP_sinst_slabs >> gs[SUBSET_DEF] >> metis_tac[]) >>
 irule tsubst_tinst >> simp[] >>
 gs[SUBSET_DEF] >> metis_tac[]
QED         



Theorem ffv_finst:
(∀f σ.
        cstt σ ∧ ffv f ⊆ FDOM σ ∧ no_bound σ ⇒
        ∀n st.
          (n,st) ∈ ffv (finst σ f) ⇔
          ∃n0 st0. (n0,st0) ∈ ffv f ∧ (n,st) ∈ tfv (σ ' (n0,st0)))        
Proof
Induct_on ‘f’ (* 5 *)
>- rw[ffv_thm]
>- (rw[ffv_thm,MEM_MAP,PULL_EXISTS] >>
   eq_tac >> rw[] (* 2 *)
   >- (drule $ cj 1 tfv_sinst >> rw[] >>
      ‘tfv y ⊆ FDOM σ ’ by (gs[SUBSET_DEF] >> metis_tac[])>>
      first_x_assum $ drule_then assume_tac >> gs[] >>
      metis_tac[]) >>
   drule $ cj 1 tfv_sinst >> rw[] >>
   ‘tfv t ⊆ FDOM σ ’ by (gs[SUBSET_DEF] >> metis_tac[])>>
   metis_tac[])
>- (rw[ffv_thm] >> metis_tac[])
>- (rw[ffv_thm] >> eq_tac >> rw[] (* 4 *)
   >- (drule $ cj 2 tfv_sinst >> rw[] >>
      first_x_assum $ drule_then assume_tac >>
      gs[] >> metis_tac[])
   >- (first_x_assum $ drule_all_then assume_tac >>
      metis_tac[])
   >- (disj1_tac >> metis_tac[tfv_sinst]) >>
   disj2_tac >> metis_tac[]) >>
rw[ffv_thm,MEM_MAP,PULL_EXISTS] >>
   eq_tac >> rw[] (* 4 *)
   >- (drule $ cj 2 tfv_sinst >> rw[] >>
      ‘sfv y ⊆ FDOM σ ’ by (gs[SUBSET_DEF] >> metis_tac[])>>
      first_x_assum $ drule_then assume_tac >> gs[] >>
      metis_tac[]) 
   >- (drule $ cj 1 tfv_sinst >> rw[] >>
      ‘tfv y ⊆ FDOM σ ’ by (gs[SUBSET_DEF] >> metis_tac[])>>
      metis_tac[])
   >- (disj1_tac >>
      drule $ cj 2 tfv_sinst >> rw[] >>
      ‘sfv s' ⊆ FDOM σ ’ by (gs[SUBSET_DEF] >> metis_tac[])>>
      first_x_assum $ drule_then assume_tac >> gs[] >>
      metis_tac[]) >>
   drule $ cj 1 tfv_sinst >> rw[] >>
   ‘tfv t ⊆ FDOM σ ’ by (gs[SUBSET_DEF] >> metis_tac[])>>
   metis_tac[]
QED   


Theorem ffv_FINITE[simp]:
 ∀f. FINITE (ffv f)
Proof
 Induct_on ‘f’ >> simp[ffv_thm,MEM_MAP,PULL_EXISTS] (* 2 *)
 >- (‘∀l. {tfv t | MEM t l} = IMAGE tfv (set l)’  suffices_by simp[] >>
 simp[EXTENSION]) >>
 (‘∀l l0. {tfv t | MEM t l0} = IMAGE tfv (set l0) ∧
          {sfv s | MEM s l} = IMAGE sfv (set l)’  suffices_by simp[] >>
 simp[EXTENSION])
QED


Theorem wff_finst:
  ∀f. wff (Σf,Σp) f ⇒
  (∀fsym. isfsym Σf fsym ⇒ sfv (fsymout Σf fsym) ⊆ BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
  ∀σ. cstt σ ∧ wfcod Σf σ ∧ ffv f ⊆ FDOM σ ⇒
  wff (Σf,Σp) (finst σ f)
Proof
  Induct_on ‘wff’ >> simp[] >> rw[] (* 5 *)
  >- metis_tac[wff_rules]
  >- (irule $ cj 2 wff_rules >> simp[MEM_MAP] >>
     rw[] (* 2 *)
     >- (first_x_assum drule >>
        rw[] >> irule $ cj 1 wft_tinst >>
        rw[] >> gs[SUBSET_DEF,MEM_MAP] >>
        metis_tac[]) >>
     irule IS_SOME_tlmatch_inst >> simp[] >>
     metis_tac[])
  >- (irule $ cj 3 wff_rules >> rw[])
  >- (irule $ cj 4 wff_rules >>
     irule wfabsap_sinst_tinst >> metis_tac[]) >>
  first_x_assum drule >> rw[] >>
  rw[mk_FALL_def] >>
  ‘∃σ1. cstt σ1 ∧ wfcod Σf σ1 ∧ ffv (mk_FALL n s f) = FDOM σ1 ∧
  (wff (Σf,Σp) (FALL (sinst σ1 s) (finst σ1 (abstract (n,s) f))) ⇒ wff (Σf,Σp) (FALL (sinst σ s) (finst σ (abstract (n,s) f))))’
  by (qabbrev_tac ‘σ1 = DRESTRICT σ (ffv (mk_FALL n s f))’ >>
     qexists ‘σ1’ >>
     ‘cstt σ1’
       by (drule DRESTRICT_cstt >>
          rw[Abbr‘σ1’] >> first_x_assum irule >> simp[] >>
          rw[ffv_is_cont]) >> simp[] >>
     ‘wfcod Σf σ1’ by metis_tac[DRESTRICT_wfcod] >>
     simp[] >>
     ‘ffv (mk_FALL n s f) = FDOM σ1’
       by (rw[Abbr‘σ1’,DRESTRICT_DEF]  >>
          gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
     simp[] >>
     ‘(sinst σ1 s) = (sinst σ s)’
       by (irule $ cj 2 fmap_fv_inst_eq_alt >>
          gs[mk_FALL_def,ffv_def] >>
          ‘sfv s ⊆ FDOM σ1 ∧ sfv s ⊆ FDOM σ’
          by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
          simp[] >> rw[] >>
          ‘x ∈ FDOM σ1 ∧ x ∈ FDOM σ’
           by metis_tac[SUBSET_DEF] >>
          gs[Abbr‘σ1’,DRESTRICT_DEF]) >>
     ‘finst σ1 (abstract (n,s) f) =
      finst σ (abstract (n,s) f)’
      by (irule $ fmap_ffv_finst_eq >>
      gs[mk_FALL_def,ffv_def] >>
      ‘ffv (abstract (n,s) f) ⊆ FDOM σ1 ∧ ffv (abstract (n,s) f) ⊆ FDOM σ’
          by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
      simp[] >> rw[] >>
     ‘x ∈ FDOM σ1 ∧ x ∈ FDOM σ’
           by metis_tac[SUBSET_DEF] >>
      gs[Abbr‘σ1’,DRESTRICT_DEF]) >> simp[]) >>
  first_x_assum irule>>
  qpat_x_assum ‘ffv (mk_FALL n s f) ⊆ FDOM σ’ (K all_tac) >>
  qpat_x_assum ‘ cstt σ’ (K all_tac) >>
  qpat_x_assum ‘wfcod Σf σ’ (K all_tac) >>
  rename [‘ cstt σ’]>>
  rw[abstract_def] >>(*need lemma ffv_mk_FALL*)
  drule ffv_mk_FALL >> rw[] >> gs[] >>
  ‘sfv s ⊆ FDOM σ’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[tm_tree_WF]) >>
  ‘(n,s) ∉ FDOM σ’ by gs[EXTENSION] >>
  ‘ffv f DELETE (n,s) ⊆ FDOM σ’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[tm_tree_WF]) >>
  (*‘∃nn.
   (∀x s1. x ∈ FDOM σ ⇒ (nn,s1) ∉ tfv (σ ' x))’
   by cheat >>*)
  ‘∃nn.
   (∀x s1. x ∈ ffv f ∪ sfv s ∧ x ≠ (n,s) ⇒ (nn,s1) ∉ tfv (σ ' x))’
   by
   (qabbrev_tac
   ‘names = BIGUNION {tfv (σ ' x) | x | x ∈ FDOM σ}’ >>
   qexists ‘variant (fromSet (IMAGE FST names)) "a"’ >>
   rw[] >>
   ‘x ∈ FDOM σ’ by simp[] >>
   ‘FINITE names’
    by (qpat_x_assum ‘FDOM _ = _’ (assume_tac o GSYM) >>
       rw[Abbr‘names’] (* 2 *)
       >- (‘{tfv (σ ' x) | x | x ∈ FDOM σ} =
           IMAGE (tfv o (λx. σ ' x)) (FDOM σ)’
           by rw[Once EXTENSION] >> simp[])
       >- simp[]) >>
   drule_then assume_tac variant_var_NOTIN >>
   gs[Abbr‘names’] >>
   metis_tac[]) >>
  drule_at_then Any assume_tac finst_abstract >>
  ‘finst σ (abs (n,s) 0 f) =
   abs (nn,sinst σ s) 0 (finst (σ |+ ((n,s),Var nn (sinst σ s))) f)’
    by (rw[Once EQ_SYM_EQ] >> irule finst_abstract >>
       simp[] >> metis_tac[]) >>
  simp[] >> rw[GSYM mk_FALL_def,GSYM abstract_def] >>
  irule $ cj 5 wff_rules >>
  ‘wfs Σf (sinst σ s)’
    by (irule $ cj 2 wft_tinst >> simp[]) >> simp[] >>
  ‘wff (Σf,Σp) (finst (σ |+ ((n,s),Var nn (sinst σ s))) f)’
    by
     (first_x_assum irule >>
     simp[FDOM_FUPDATE,SUBSET_INSERT_DELETE ] >> gs[] >>
     ‘wfcod Σf (σ |+ ((n,s),Var nn (sinst σ s)))’
      by (irule FUPDATE_wfcod >> simp[wft_def]) >> simp[]>>
     irule FUPDATE_cstt >>
     simp[complete_FDOM_is_cont,sort_of_def] >>
     ‘is_cont (ffv f ∪ sfv s DELETE (n,s))’
       by metis_tac[ffv_is_cont] >> simp[] >>       
     metis_tac[tm_tree_WF,vsort_tfv_closed]) >> simp[] >>
  rw[] >>
  ‘cstt (σ |+ ((n,s),Var nn (sinst σ s)))’
   by ( irule FUPDATE_cstt >>
     simp[complete_FDOM_is_cont,sort_of_def] >>
     ‘is_cont (ffv f ∪ sfv s DELETE (n,s))’
       by metis_tac[ffv_is_cont] >> simp[] >>       
     metis_tac[tm_tree_WF,vsort_tfv_closed]) >>
  drule ffv_finst >> rw[FDOM_FUPDATE,SUBSET_INSERT_DELETE]>>
  first_x_assum $ qspecl_then [‘f’,‘n1’,‘s1’] assume_tac >>
  gs[] >>
  ‘wfcod Σf (σ |+ ((n,s),Var nn (sinst σ s)))’
      by (irule FUPDATE_wfcod >> simp[wft_def]) >> simp[]>>
  drule wfcod_no_bound >> rw[] >> gs[] >>
  Cases_on ‘(n,s) = (n0,st0)’ (* 2 *)
  >- (gs[FAPPLY_FUPDATE_THM] (* 2 *)
     >- metis_tac[tm_tree_WF] >>
     rev_drule $ cj 2 tfv_sinst >> rw[] >>
     first_x_assum (qspecl_then [‘s’,‘n1’,‘s1’] assume_tac)>>
     gs[] >>
     rev_drule wfcod_no_bound >> rw[] >> gs[] >>
     ‘(n0,st0) ≠ (n,s)’ by metis_tac[tm_tree_WF] >>
     first_x_assum (qspecl_then [‘(n0,st0)’,‘sinst σ s’] assume_tac) >> gs[] >> metis_tac[vsort_tfv_closed]) >>
  gs[FAPPLY_FUPDATE_THM] >>
  first_x_assum (qspecl_then [‘(n0,st0)’,‘sinst σ s’] assume_tac) >> gs[] >> metis_tac[vsort_tfv_closed]
QED          


Theorem wff_FALL:
 ∀s b. wff (Σf,Σp) (FALL s b) ⇔
 (∃f n. wff (Σf,Σp) f ∧
          wfs Σf s ∧
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
          FALL s b = mk_FALL n s f)
Proof
 rw[Once wff_cases,EQ_IMP_THM] (* 2 *)
 >- (gs[mk_FALL_def] >> metis_tac[]) >>
 simp[] >> irule $ cj 5 wff_rules >> simp[] >> metis_tac[]
QED 


(*
Definition fpreplace_def:
  fpreplace bmap False = False ∧
  fpreplace bmap (IMP f1 f2) =
   IMP (fpreplace bmap f1) (fpreplace bmap f2) ∧
  fpreplace bmap (Pred p tl) =
  Pred p (MAP (tpreplace bmap) tl) ∧
  fpreplace bmap (fVar p sl tl) =
   fVar p (MAP (spreplace bmap) sl)
        (MAP (tpreplace bmap) tl) ∧
  fpreplace bmap (FALL s b) =
  FALL (spreplace bmap s) (fpreplace (shift_bmap bmap) b)
End
*)

Definition fprpl_def:
  fprpl bmap False = False ∧
  fprpl bmap (IMP f1 f2) =
   IMP (fprpl bmap f1) (fprpl bmap f2) ∧
  fprpl bmap (Pred p tl) =
  Pred p (MAP (tprpl bmap) tl) ∧
  fprpl bmap (fVar p sl tl) =
   fVar p (slprpl bmap sl)
        (MAP (tprpl bmap) tl) ∧
  fprpl bmap (FALL s b) =
  FALL (sprpl bmap s) (fprpl (shift_bmap 1 bmap) b)
End

        
        
Definition fVar_subst_def:
 fVar_subst (P:string,sl:sort list,ϕ:form) False = False ∧
 fVar_subst (P,sl,ϕ) (Pred p tl) = Pred p tl ∧
 (fVar_subst (P,sl,ϕ) (IMP f1 f2) =
 IMP (fVar_subst (P,sl,ϕ) f1)
     (fVar_subst (P,sl,ϕ) f2))   ∧
 (fVar_subst (P,sl,ϕ) (FALL s f) =
  FALL s (fVar_subst (P,sl,ϕ) f)) ∧
 fVar_subst (P,sl,ϕ) (fVar p sl1 tl1) =
 if (P = p ∧ sl = sl1 ∧ ok_abs sl1) then fprpl (mk_bmap (REVERSE tl1)) ϕ
 else (fVar p sl1 tl1)
End

Definition FALLL_def:
FALLL [] ϕ = ϕ ∧
FALLL (h :: t) ϕ = FALL h (FALLL t ϕ)
End
        


Theorem mk_bmap_NIL[simp]:
mk_bmap [] = FEMPTY
Proof
rw[mk_bmap_def]
QED



Theorem subst_FALLL:
∀sl ϕ t i.
 (subst t i (FALLL sl ϕ)) = 
 FALLL (specsl i t sl) (subst t (LENGTH sl + i) ϕ)
Proof
Induct_on ‘sl’ >>
rw[subst_bound_def,FALLL_def,specsl_def] >>
gs[subst_def,arithmeticTheory.ADD1]
QED
        
Theorem subst_bound_FALLL:
∀sl ϕ t.
 (subst_bound t (FALLL sl ϕ)) = 
 FALLL (specsl 0 t sl) (subst t (LENGTH sl) ϕ)
Proof
rw[] >>
qspecl_then [‘sl’,‘ϕ’,‘t’,‘0’] assume_tac subst_FALLL >>
gs[subst_bound_def]
QED        


        
        
Theorem fprpl_FEMPTY:
∀ϕ. (fprpl FEMPTY ϕ) = ϕ
Proof
Induct_on ‘ϕ’ >> rw[fprpl_def,tprpl_def,tprpl_FEMPTY,MAP_fix] >> gs[mk_bmap_NIL,shift_bmap_FEMPTY,slprpl_FEMPTY]
QED           

Theorem subst_abs:
∀f i n s.
  i ∉ fbounds f ⇒
  subst new i (abs (n,s) i f) =
  finst (TO_FMAP [((n,s),new)]) f
Proof
 reverse (Induct_on ‘f’) >>
 gs[subst_def,abs_def,abstract_def,finst_def,MAP_MAP_o,MAP_EQ_f,treplace_tsstt,tsubst_tsstt,PULL_EXISTS,fbounds_def,
   MEM_MAP] (* 3 *)
 >- (rw[]
    >- (rename [‘((n,st),new)’] >>
        rw[GSYM tsubst_eq_tinst1]  >>
        irule slreplace_slabs >> fs[slbounds_sbounds]) >>
    Cases_on ‘(n,s) ∈ tfv e’ 
    >- (gs[GSYM Var_tsubtm_tfv] >>
       ‘Bound i ∉ tsubtm e’
         by (gs[Bound_tsubtm] >> metis_tac[]) >>
       drule_then assume_tac $ cj 1 tsstt_tsstt1 >>
       simp[] >>
       simp[tsubst_eq_tinst,GSYM tsubst_tsstt]) >>
    ‘Bound i ∉ tsubtm e’
   by (gs[Bound_tsubtm] >> metis_tac[]) >>
   drule_then assume_tac $ cj 1 tsstt_tsstt1 >> simp[] >>
   rw[tsubst_eq_tinst,GSYM tsubst_tsstt])
 >- (rw[] (* 2 *)   
    >- (rw[GSYM tsubst_eq_tinst1,tsubst_tsstt] >>
        rename [‘Var n st’] >>
        irule $ cj 2 tsstt_tsstt1 >> gs[Bound_tsubtm]) >>
    first_x_assum irule >>
    first_x_assum (qspecl_then [‘SUC i’] assume_tac) >>
    gs[arithmeticTheory.ADD1]) >>
 rw[] >> rw[GSYM tsubst_eq_tinst1,tsubst_tsstt] >>
 irule $ cj 1 tsstt_tsstt1 >> gs[Bound_tsubtm] >>
 metis_tac[]
QED




Theorem abs_fbounds_in:
  ∀f n s i.
    (n,s) ∈ ffv f ⇒
    i ∈ fbounds (abs (n,s) i f)
Proof     
Induct_on ‘f’ >>
simp[fbounds_thm,abs_def,tfv_thm,MEM_MAP,PULL_EXISTS] >>
rw[] (* 7 *)
>- metis_tac[tsubst_tbounds_in]
>- metis_tac[]
>- metis_tac[]
>- metis_tac[tsubst_tbounds_in]
>- (disj2_tac >> qexists ‘SUC i’ >>
   simp[arithmeticTheory.ADD1])
>- (disj1_tac >> simp[IN_slbounds] >>
   gs[MEM_EL] >> qexists ‘n'’ >> gs[LENGTH_slabs] >>
   drule_then assume_tac slabs_EL >>
   simp[] >> metis_tac[tsubst_tbounds_in])
>- metis_tac[tsubst_tbounds_in]
QED        

Theorem fbounds_abs_SUBSET:
  ∀f n s i.
    (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = {}) ⇒ 
    fbounds f ⊆ fbounds (abs (n,s) i f)
Proof
Induct_on ‘f’ >>
simp[fbounds_thm,ffv_thm,PULL_EXISTS,abs_def,MEM_MAP] (* 4 *)
>- (rw[SUBSET_DEF,PULL_EXISTS] >>
   ‘tbounds t ⊆ tbounds (tsubst (n,s') (Bound i) t)’
     suffices_by metis_tac[SUBSET_DEF] >>
   irule $ cj 1 tbounds_tsubst_SUBSET >>
   metis_tac[])
>- (gs[SUBSET_DEF]>> metis_tac[])
>- (rw[] (* 2 *)
   >- (‘sbounds s ⊆
        sbounds (ssubst (n,s') (Bound i) s)’
        suffices_by gs[SUBSET_DEF,UNION_DEF] >>
       irule $ cj 2 tbounds_tsubst_SUBSET >>
       metis_tac[]) >>
   ‘IMAGE PRE (fbounds f DELETE 0) ⊆
    IMAGE PRE (fbounds (abs (n,s') (i + 1) f) DELETE 0)’
       suffices_by gs[SUBSET_DEF,UNION_DEF] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
rw[] (* 2 *)
>- (‘slbounds l ⊆
    slbounds (slabs (n,s') i l)’
  suffices_by gs[SUBSET_DEF,UNION_DEF] >>
  rw[SUBSET_DEF,IN_slbounds,LENGTH_slabs] >>
  qexists ‘m’ >> drule_then assume_tac slabs_EL >>
  simp[] >>
  ‘sbounds (EL m l) ⊆
   sbounds (ssubst (n,s') (Bound (i + m)) (EL m l))’
   suffices_by gs[SUBSET_DEF] >>
  irule $ cj 2 tbounds_tsubst_SUBSET >> metis_tac[MEM_EL]) >>
‘BIGUNION {tbounds t | MEM t l0} ⊆
 BIGUNION {tbounds t | (∃y. t = tsubst (n,s') (Bound i) y ∧ MEM y l0)}’
  suffices_by (gs[SUBSET_DEF,UNION_DEF] >> metis_tac[]) >>
rw[SUBSET_DEF,PULL_EXISTS] >>
‘tbounds t ⊆ tbounds (tsubst (n,s') (Bound i) t)’
suffices_by metis_tac[SUBSET_DEF] >>
irule $ cj 1 tbounds_tsubst_SUBSET >> metis_tac[MEM_EL]
QED           

Theorem fbounds_abs:
∀f i n s.
  (n,s) ∈ ffv f ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = {}) ⇒
  fbounds (abs (n,s) i f) = {i} ∪ fbounds f 
Proof
Induct_on ‘f’ >> simp[abs_def,fbounds_thm] (* 4 *)
>- (simp[MEM_MAP,PULL_EXISTS] >>
   rw[] >>
   rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
   >- (Cases_on ‘(n,s') ∈ tfv y’ (* 2 *)
      >- (‘tbounds (tsubst (n,s') (Bound i) y) =
          {i} ∪ tbounds y’
           by (irule $ cj 1 tbounds_tsubst >>
              gs[EXTENSION] >> metis_tac[])  >>
         gs[] >> metis_tac[]) >>
      metis_tac[tsubst_id])
   >- metis_tac[tsubst_tbounds_in]
   >- metis_tac[tbounds_tsubst_SUBSET,SUBSET_DEF])
>- (rw[] (* 2 *) >> 
   gs[EXTENSION] >> metis_tac[abs_id])
>- (rw[] (* 2 *)
   >- (‘sbounds (ssubst (n,s') (Bound i) s) =
      {i} ∪ sbounds s’ by metis_tac[tbounds_tsubst] >>
      simp[] >>
      Cases_on ‘(n,s') ∈ ffv f’ (* 2 *)
      >- (‘fbounds (abs (n,s') (i + 1) f) =
          {i + 1} ∪ fbounds f’ by metis_tac[] >>
         simp[] >>
         ‘IMAGE PRE ({i + 1} ∪ fbounds f DELETE 0) =
          {i} ∪ IMAGE PRE (fbounds f DELETE 0)’
          by (rw[EXTENSION,EQ_IMP_THM,GSYM arithmeticTheory.ADD1] >> simp[] (* 3 *)
          >- metis_tac[] >- (qexists ‘SUC i’ >> simp[]) >>
          metis_tac[]) >>
      gs[EXTENSION] >> metis_tac[]) >>
       ‘(abs (n,s') (i + 1) f) = f’ by metis_tac[abs_id] >>
       simp[UNION_ASSOC]) >>
   ‘fbounds (abs (n,s') (i + 1) f) =
    {i + 1} ∪ fbounds f’ by metis_tac[] >> simp[] >>
   ‘IMAGE PRE ({i + 1} ∪ fbounds f DELETE 0) =
          {i} ∪ IMAGE PRE (fbounds f DELETE 0)’
          by (rw[EXTENSION,EQ_IMP_THM,GSYM arithmeticTheory.ADD1] >> simp[] (* 3 *)
          >- metis_tac[] >- (qexists ‘SUC i’ >> simp[]) >>
          metis_tac[]) >> simp[] >>
   Cases_on ‘(n,s') ∈ sfv s’ (* 2 *)
   >- (‘sbounds (ssubst (n,s') (Bound i) s) =
      {i} ∪ sbounds s’ by metis_tac[tbounds_tsubst] >>
      gs[EXTENSION] >> metis_tac[]) >>
   ‘(ssubst (n,s') (Bound i) s) = s’
    by metis_tac[tsubst_id] >>
   gs[EXTENSION] >> metis_tac[]) >>
simp[PULL_EXISTS,MEM_MAP] >> rw[] (* 2 *)
>- (drule_then assume_tac $ iffLR MEM_EL >> gs[] >>
   drule_then assume_tac slbounds_slabs >>
   first_x_assum $ drule_then assume_tac >>
   ‘slbounds (slabs (n,s') i l) = {i} ∪ slbounds l’
    by (first_x_assum irule >> rw[] >> metis_tac[]) >>
   simp[] >>
   Cases_on ‘∃y. MEM y l0 ∧ (n,s') ∈ tfv y’ (* 2 *)
   >- (gs[] >>
      ‘BIGUNION {tbounds t | (∃y. t = tsubst (n,s') (Bound i) y ∧ MEM y l0)} = {i} ∪ BIGUNION {tbounds t | MEM t l0}’
       by (irule BIGUNION_tbounds >> gs[] >> metis_tac[]) >>
      gs[EXTENSION] >> metis_tac[]) >>
   ‘{tbounds t | (∃y. t = tsubst (n,s') (Bound i) y ∧ MEM y l0)} = {tbounds t | MEM t l0}’
    by (rw[Once EXTENSION] >> metis_tac[tsubst_id]) >>
   gs[EXTENSION] >> metis_tac[]) >>
‘BIGUNION {tbounds t | (∃y. t = tsubst (n,s') (Bound i) y ∧ MEM y l0)} = {i} ∪ BIGUNION {tbounds t | MEM t l0}’
  by (irule BIGUNION_tbounds >> gs[] >> metis_tac[]) >>
Cases_on ‘∃s. MEM s l ∧ (n,s') ∈ sfv s’ (* 2 *)
>- (gs[] >> drule_then assume_tac $ iffLR MEM_EL >>
   gs[] >>
   ‘slbounds (slabs (n,s') i l) = {i} ∪ slbounds l’
    by (irule slbounds_slabs >> gs[] >>
       metis_tac[]) >> simp[] >>
   gs[EXTENSION] >> metis_tac[]) >>
‘(slabs (n,s') i l) = l’
 by metis_tac[NOTIN_slbounds_slabs] >>
gs[EXTENSION] >> metis_tac[]
QED    
                                

Theorem wff_wfs:
(∀f. wff (Σf,Σp) f ⇒ ∀n s. (n,s) ∈ ffv f ⇒ wfs Σf s)
Proof
Induct_on ‘wff’ >> simp[ffv_thm,PULL_EXISTS] >> rw[] (* 6 *)
>- metis_tac[wft_wfs]
>- metis_tac[wft_wfs]
>- metis_tac[wft_wfs]
>- metis_tac[wfabsap_wfs]
>- (drule_then assume_tac wfabsap_wft >>
    metis_tac[wft_wfs])>>
gs[mk_FALL_def] (* 2 *)
>- metis_tac[wft_wfs] >>
Cases_on ‘(n,s) ∈ ffv f’ (* 2 *)
>- (drule_all_then assume_tac ffv_abs >>
   first_x_assum (qspecl_then [‘0’] assume_tac) >>
   gs[abstract_def] >> gs[EXTENSION] >>
   metis_tac[wft_wfs]) >>
metis_tac[abstract_def,abs_id]
QED

Theorem wff_fbounds:
∀f. wff Σf f ⇒ fbounds f = {}
Proof
Induct_on ‘wff’ >> rw[fbounds_thm] (* 4 *)
>- (Cases_on ‘tl’ >> simp[] >>
   disj2_tac >> rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
   >> (gs[] >> metis_tac[wft_no_bound]))
>- metis_tac[wfabsap_slbounds]
>- (Cases_on ‘tl’ >> simp[] >>
   disj2_tac >> drule_then assume_tac wfabsap_wft >>
   rw[Once EXTENSION] >> gs[] >>
   metis_tac[wft_no_bound]) >>
rw[mk_FALL_def,fbounds_thm] (* 2 *)
>- metis_tac[wft_no_bound] >>
rw[abstract_def] >>
Cases_on ‘(n,s) ∈ ffv f’ (* 2 *)
>- (‘fbounds (abs (n,s) 0 f) = {0} ∪ fbounds f’
    by (irule fbounds_abs >>
        metis_tac[wff_wfs,wft_no_bound]) >>
   simp[EXTENSION]) >>
‘(abs (n,s) 0 f)= f’ by metis_tac[abs_id] >>
simp[]
QED
Theorem finst_eq_cvmap:
  ∀f. (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,sort_of t) ∉ sfv s1) ⇒
      finst (TO_FMAP [((n,sort_of t),t)]) f =
      finst (cvmap (ffv f) |+ ((n,sort_of t),t)) f
Proof
  Induct_on ‘f’ >> simp[finst_def,MAP_EQ_f,FDOM_TO_FMAP,FDOM_cvmap] (* 4 *)
  >- (rw[] >>
      ‘tinst (TO_FMAP [((n,sort_of t),t)]) e =
       tinst (cvmap (tfv e) |+ ((n,sort_of t),t)) e’
        by (irule $ cj 1 tinst_eq_cvmap >> metis_tac[]) >>
      simp[] >>
      irule $ cj 1 fmap_fv_inst_eq_alt >>
      simp[FDOM_cvmap,FDOM_FUPDATE] >>
      ‘FINITE (BIGUNION {tfv t | MEM t l})’
        by (simp[] >> rw[PULL_EXISTS] >>
            ‘{tfv t | MEM t l} = IMAGE tfv {t | MEM t l}’
              by rw[EXTENSION] >> simp[]) >>
      simp[FDOM_cvmap,FDOM_FUPDATE] >>
      rw[SUBSET_DEF] (* 2 *)
      >- (simp[FAPPLY_cvmap,FAPPLY_FUPDATE_THM] >>
          Cases_on ‘x = (n,sort_of t)’ >-
           (Cases_on ‘x’ >> simp[FAPPLY_cvmap] >> gs[]) >>
          Cases_on ‘x’ >> simp[Once EQ_SYM_EQ,FAPPLY_cvmap] >>
          irule $ FAPPLY_cvmap >> simp[] >> metis_tac[]) >>
      metis_tac[])
  >- (rw[] (* 2 *)
      >- (‘finst (TO_FMAP [((n,sort_of t),t)]) f =
           finst (cvmap (ffv f) |+ ((n,sort_of t),t)) f’
            by metis_tac[] >> simp[] >>
          irule fmap_ffv_finst_eq >>
          simp[FDOM_cvmap,FDOM_FUPDATE,FAPPLY_FUPDATE_THM] >>
          rw[SUBSET_DEF] >> Cases_on ‘x’ >>
          simp[FAPPLY_cvmap]) >>
      ‘finst (TO_FMAP [((n,sort_of t),t)]) f' =
       finst (cvmap (ffv f') |+ ((n,sort_of t),t)) f'’
        by metis_tac[] >> simp[] >>
      irule fmap_ffv_finst_eq >>
      simp[FDOM_cvmap,FDOM_FUPDATE,FAPPLY_FUPDATE_THM] >>
      rw[SUBSET_DEF] >> Cases_on ‘x’ >>
      simp[FAPPLY_cvmap])
  >- (rw[] (* 2 *)
      >- (‘sinst (TO_FMAP [((n,sort_of t),t)]) s =
           sinst (cvmap (sfv s) |+ ((n,sort_of t),t)) s’
            by (irule $ cj 2 tinst_eq_cvmap >>
                simp[] >> metis_tac[]) >>
          simp[] >>
          irule $ cj 2 fmap_fv_inst_eq_alt >>
          simp[FDOM_cvmap,FDOM_FUPDATE] >>
          rw[SUBSET_DEF] >>
          Cases_on ‘x’ >>
          rw[FDOM_cvmap,FDOM_FUPDATE,FAPPLY_cvmap,
             FAPPLY_FUPDATE_THM]) >>
      ‘finst (TO_FMAP [((n,sort_of t),t)]) f =
       finst (cvmap (ffv f) |+ ((n,sort_of t),t)) f’
        by metis_tac[] >> simp[] >>
      irule fmap_ffv_finst_eq >>
      simp[FDOM_cvmap,FDOM_FUPDATE,FAPPLY_FUPDATE_THM] >>
      rw[SUBSET_DEF] >> Cases_on ‘x’ >>
      simp[FAPPLY_cvmap]) >>
  rw[] (* 2 *)
  >- (‘sinst (TO_FMAP [((n,sort_of t),t)]) e =
       sinst (cvmap (sfv e) |+ ((n,sort_of t),t)) e’
        by (irule $ cj 2 tinst_eq_cvmap >>
            simp[] >> metis_tac[]) >>
      simp[] >>
      irule $ cj 2 fmap_fv_inst_eq_alt >>
      ‘FINITE (BIGUNION {sfv s | MEM s l} ∪ BIGUNION {tfv t | MEM t l0})’
        by (simp[] >> rw[PULL_EXISTS] (* 2 *)
            >- (‘{sfv s | MEM s l} = IMAGE sfv {s | MEM s l}’
                  by rw[EXTENSION] >> simp[]) >>
            ‘{tfv t | MEM t l0} = IMAGE tfv {t | MEM t l0}’
              by rw[EXTENSION] >> simp[]) >>
      simp[FDOM_cvmap,FDOM_FUPDATE,FAPPLY_FUPDATE_THM] >>
      rw[SUBSET_DEF] (*2 *)
      >- (rw[] >>  Cases_on ‘x’ >>
          simp[Once EQ_SYM_EQ,FAPPLY_cvmap] >>
          irule $ FAPPLY_cvmap >> simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  ‘tinst (TO_FMAP [((n,sort_of t),t)]) e =
   tinst (cvmap (tfv e) |+ ((n,sort_of t),t)) e’    
    by (irule $ cj 1 tinst_eq_cvmap >>
        simp[] >> metis_tac[]) >> simp[] >>
  irule $ cj 1 fmap_fv_inst_eq_alt >>          
  ‘FINITE (BIGUNION {sfv s | MEM s l} ∪ BIGUNION {tfv t | MEM t l0})’
    by (simp[] >> rw[PULL_EXISTS] (* 2 *)
        >- (‘{sfv s | MEM s l} = IMAGE sfv {s | MEM s l}’
              by rw[EXTENSION] >> simp[]) >>
        ‘{tfv t | MEM t l0} = IMAGE tfv {t | MEM t l0}’
          by rw[EXTENSION] >> simp[]) >>
  simp[FDOM_cvmap,FDOM_FUPDATE,FAPPLY_FUPDATE_THM] >>
  rw[SUBSET_DEF] (*2 *)
  >- (rw[] >>  Cases_on ‘x’ >>
      simp[Once EQ_SYM_EQ,FAPPLY_cvmap] >>
      irule $ FAPPLY_cvmap >> simp[] >> metis_tac[]) >>
  metis_tac[]       
QED


val subst_bound_abstract =
subst_abs |> Q.SPECL [‘f’,‘0’] |> SRULE [GSYM subst_bound_def,GSYM abstract_def]
        
        

Theorem wff_spec:
 (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧
 wff (Σf,Σp) (FALL s ϕ) ⇒
 ∀t. wft Σf t ∧ sort_of t = s ⇒
     wff (Σf,Σp) (subst_bound t ϕ)
Proof
 rw[] >> gs[wff_FALL] >> gs[mk_FALL_def] >>
 ‘0 ∉ fbounds f’
  by (drule_then assume_tac wff_fbounds >>
     metis_tac[MEMBER_NOT_EMPTY]) >>
 drule_then assume_tac subst_bound_abstract >>
 simp[] >>
 ‘(finst (TO_FMAP [((n,sort_of t),t)]) f) =
  finst (cvmap (ffv f) |+ ((n,sort_of t),t)) f’
   by (irule finst_eq_cvmap >> metis_tac[]) >>
 simp[] >> irule wff_finst >> simp[] >>
 rw[] (* 3 *)
 >- (irule cstt_FUPDATE >> rw[] (*2  *)
    >- metis_tac[] >>
    CCONTR_TAC >> gs[is_bound_alt,wft_def])
 >- rw[FDOM_cvmap,SUBSET_DEF] >>
 rw[wfcod_def,FAPPLY_FUPDATE_THM] >>
 Cases_on ‘n' = n ∧ s = sort_of t’ >> simp[] >>
 gs[FDOM_cvmap,FAPPLY_cvmap] >>
 rw[wft_def] >> metis_tac[wff_wfs]
QED 
        


Definition fabs_def:
  fabs _ _ False = False ∧
  fabs v i (Pred p tl) =
  Pred p (MAP (tabs v i) tl) ∧
  fabs v i (fVar p vl tl) =
  fVar p (abssl v i vl)
         (MAP (tabs v i) tl) ∧
  fabs v i (IMP f1 f2) =
  IMP (fabs v i f1) (fabs v i f2) ∧
  fabs v i (FALL s b) =
  FALL (sabs v i s) (fabs v (i + 1) b)
End     



Theorem fprpl_mk_bmap_abs:
∀ϕ i bmap. (n,s) ∉ ffv ϕ
       ⇒ fprpl (FMAP_MAP (tabs (n,s) i) bmap) ϕ =
fabs (n,s) i (fprpl bmap ϕ)
Proof
Induct_on ‘ϕ’ >>
gs[fprpl_def,fabs_def,MAP_EQ_f,MAP_MAP_o] >>
rw[] (* 5 *)
>- metis_tac[tprpl_FMAP_MAP_tabs]
>- metis_tac[tprpl_FMAP_MAP_tabs]
>- (first_x_assum $ drule_then assume_tac >>
   ‘(shift_bmap 1 (FMAP_MAP (tabs (n,s) i) bmap)) =
    FMAP_MAP (tabs (n,s) (i+1)) (shift_bmap 1 bmap)’
     by simp[shift_bmap_FMAP_MAP_tabs] >> 
   simp[])
>- (irule LIST_EQ >>
   simp[LENGTH_abssl,LENGTH_slprpl,EL_MAP] >>
   rw[] >> simp[slabs_EL,EL_MAP] >>
   ‘x < LENGTH (slprpl bmap l)’
  by simp[LENGTH_slprpl] >>
   drule_then assume_tac abssl_EL >> simp[] >>
   rev_drule_then assume_tac slprpl_EL >> simp[] >>
   ‘(shift_bmap x (FMAP_MAP (tabs (n,s) i) bmap)) =
    FMAP_MAP (tabs (n,s) (i+x)) (shift_bmap x bmap) ⇒
    sprpl (shift_bmap x (FMAP_MAP (tabs (n,s) i) bmap)) (EL x l) =
    sprpl (FMAP_MAP (tabs (n,s) (i+x)) (shift_bmap x bmap)) (EL x l)’ by rw[] >> 
   ‘shift_bmap x (FMAP_MAP (tabs (n,s) i) bmap) =
    FMAP_MAP (tabs (n,s) (i+x)) (shift_bmap x bmap)’
     by simp[shift_bmap_FMAP_MAP_tabs] >>
   first_x_assum drule >> strip_tac >> simp[] >>
   metis_tac[tprpl_FMAP_MAP_tabs,MEM_EL]) >>
metis_tac[tprpl_FMAP_MAP_tabs]   
QED



Definition freefVars_def:
  freefVars False = {} ∧
  freefVars (IMP f1 f2) = freefVars f1 ∪ freefVars f2 ∧
  freefVars (Pred _ _) = {} ∧
  (freefVars (fVar P sl tl) =
  if ok_abs sl then {(P,sl)} else {}) ∧
  freefVars (FALL s b) = freefVars b
End


Theorem fVar_subst_id:
∀f P sl ϕ. (P,sl) ∉ freefVars f ⇒
 fVar_subst (P,sl,ϕ) f = f
Proof
Induct_on ‘f’ >> rw[fVar_subst_def,freefVars_def]
QED        




Theorem freefVars_abs:
∀f i. freefVars (abs (n,s) i f) =
    freefVars f DIFF {(P,sl) | (P,sl) ∈ freefVars f ∧
    ∃st. MEM st sl ∧ (n,s) ∈ sfv st}
Proof
Induct_on ‘f’ (* 5 *)
>- rw[Once EXTENSION,freefVars_def,abs_def]
>- rw[Once EXTENSION,freefVars_def,abs_def]
>- (gs[EXTENSION,freefVars_def,abs_def] >> metis_tac[])
>- rw[Once EXTENSION,freefVars_def,abs_def] >>
rw[Once EXTENSION,freefVars_def,abs_def] (* 3 *)
>- (Cases_on ‘x’ >> gs[] >> rw[EQ_IMP_THM] (* 3 *)
   >>  metis_tac[slabs_id,NOT_ok_abs])
>- metis_tac[slabs_id,NOT_ok_abs] >>
metis_tac[slabs_id,NOT_ok_abs]
QED


Theorem freefVars_abs_SUBSET:
  freefVars (abs (n,s) i f) ⊆ freefVars f
Proof
  simp[freefVars_abs] >> rw[SUBSET_DEF]
QED


Theorem freefVars_fabs_SUBSET:
  freefVars (fabs (n,s) i f) ⊆ freefVars f
Proof
  cheat
QED
        


Theorem fVar_subst_abs:
  ∀f i.
       (P,sl) ∈ freefVars f ∧
       (∀st. MEM st sl ⇒ (n,s) ∉ sfv st) ∧
       (n,s) ∉ ffv ϕ ⇒
      (fVar_subst (P,sl,ϕ) (fabs (n,s) i f)) =
     fabs (n,s) i (fVar_subst (P,sl,ϕ) f)
Proof
Induct_on ‘f’ >> rw[] (* 5 *)
>- rw[fabs_def,fVar_subst_def]
>- gs[fabs_def,fVar_subst_def,freefVars_def] 
>- (gs[fabs_def,fVar_subst_def,freefVars_def] (* 2 *)
   >- (Cases_on ‘(P,sl) ∈ freefVars f'’ (* 2 *)
      >- (first_x_assum $ drule_then assume_tac >> simp[])>>
      drule_then assume_tac fVar_subst_id >> simp[] >>
      ‘(P,sl) ∉ freefVars (fabs (n,s) i f')’
       suffices_by metis_tac[fVar_subst_id] >>
      metis_tac[freefVars_fabs_SUBSET,SUBSET_DEF]) >>
   Cases_on ‘(P,sl) ∈ freefVars f’ (* 2 *)
      >- (first_x_assum $ drule_then assume_tac >> simp[])>>
      drule_then assume_tac fVar_subst_id >> simp[] >>
      ‘(P,sl) ∉ freefVars (fabs (n,s) i f)’
       suffices_by metis_tac[fVar_subst_id] >>
      metis_tac[freefVars_fabs_SUBSET,SUBSET_DEF]) 
>- gs[fabs_def,fVar_subst_def,freefVars_def] >>
gs[fabs_def,fVar_subst_def,freefVars_def] >> rw[] (* 4 *)>>
gvs[freefVars_def]
>- (rw[mk_bmap_MAP,GSYM rich_listTheory.MAP_REVERSE] >>
    metis_tac[fprpl_mk_bmap_abs])
>- (drule_then assume_tac ok_abs_abssl >> gs[])
>- (drule_then assume_tac abssl_id >> gs[]) >>
Cases_on ‘ok_abs l’ >> gs[]
QED



Theorem fVar_subst_abs1:
  ∀f i.
       (P,sl) ∈ freefVars f ∧
       (∀st. MEM st sl ⇒ (n,s) ∉ sfv st) ∧
       (n,s) ∉ ffv ϕ ⇒
      (fVar_subst (P,sl,ϕ) (abs (n,s) i f)) =
     abs (n,s) i (fVar_subst (P,sl,ϕ) f)
Proof
cheat
QED
        

Theorem ffv_fprpl:
 ∀ϕ bmap.
  (∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅) ⇒
 ffv (fprpl bmap ϕ) = ffv ϕ ∪ BIGUNION {tfv (bmap ' i) | i|  i ∈ FDOM bmap ∩ fbounds ϕ}
Proof
Induct_on ‘ϕ’ >>
simp[fprpl_def,ffv_thm,fbounds_thm,MEM_MAP,PULL_EXISTS]
(* 4 *)
>- (rw[] >>
    ‘BIGUNION {tfv t | (∃a. t = tprpl bmap a ∧ MEM a l)} =
    BIGUNION {tfv (tprpl bmap a) | MEM a l}’
    by (rw[EXTENSION] >> metis_tac[]) >>
   simp[] >>
simp[PULL_EXISTS] >> simp[] >> 
‘ BIGUNION {tfv t | MEM t l} ∪
        BIGUNION
          {tfv (bmap ' i) | i| (∃t. i ∈ FDOM bmap ∧ i ∈ tbounds t ∧ MEM t l)} =
 BIGUNION {tfv tm ∪ BIGUNION {tfv (bmap ' i) | i|i ∈ FDOM bmap ∩ tbounds tm} | MEM tm l}’
 by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] 
    >>  metis_tac[]) >> simp[] >>
AP_TERM_TAC >>
rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 2 *)
>- (qexists ‘y’ >> simp[] >> simp[Once $ GSYM IN_INTER] >>
   qspecl_then [‘y’,‘bmap’] assume_tac $ cj 1 tfv_tprpl >>
   gs[IN_INTER] >> 
   first_x_assum irule >> metis_tac[]) >>
qexists ‘tm’ >> simp[] >>
qspecl_then [‘tm’,‘bmap’] assume_tac $ cj 1 tfv_tprpl >>
gs[IN_INTER] >> metis_tac[])
>- (rw[] >>
   gs[EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
   rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>  metis_tac[])
>- (rw[] >>
   ‘sfv (sprpl bmap s) =
    sfv s ∪ BIGUNION {tfv (bmap ' i) | i|i ∈ FDOM bmap ∩ sbounds s}’ by metis_tac[tfv_tprpl] >> simp[] >>
   ‘(∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅)’ by metis_tac[] >>
   first_x_assum $ drule_then assume_tac >>
   simp[FDOM_shift_bmap] >>
   ‘∀i.tfv (shift_bmap 1 bmap ' i)= tfv (bmap ' (i- 1)) ’
    by cheat >> simp[] >>
   ‘BIGUNION
          {tfv (bmap ' i) |
           i |
           i ∈ FDOM bmap ∧
           (i ∈ sbounds s ∨ ∃x. i = PRE x ∧ x ∈ fbounds ϕ ∧ x ≠ 0)} =
    BIGUNION
          {tfv (bmap ' i) |
           i |
           i ∈ FDOM bmap ∧ i ∈ sbounds s} ∪
    BIGUNION
          {tfv (bmap ' i) |
           i |
           i ∈ FDOM bmap ∧
           ∃x. i = PRE x ∧ x ∈ fbounds ϕ ∧ x ≠ 0} ’
     by
     (gs[EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
      rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
      metis_tac[]) >>
    simp[] >>
    ‘{tfv (bmap ' (i − 1)) |
            i |
            (∃x. i = x + 1 ∧ x ∈ FDOM bmap) ∧ i ∈ fbounds ϕ}=
    {tfv (bmap ' i) |
            i |
            i ∈ FDOM bmap ∧ ∃x. i = PRE x ∧ x ∈ fbounds ϕ ∧ x ≠ 0}’
      by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 2 *)
      >- (qexists ‘x' + 1’ >>
         simp[GSYM arithmeticTheory.ADD1]) >>
      Cases_on ‘x'’ >>
      gs[arithmeticTheory.num_CASES,
         GSYM arithmeticTheory.ADD1] >>
      metis_tac[])>> simp[] >> 
      rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
      metis_tac[]) >>
rw[] >>
‘BIGUNION {tfv t | (∃a. t = tprpl bmap a ∧ MEM a l0)} =
    BIGUNION {tfv (tprpl bmap a) | MEM a l0}’
    by (rw[EXTENSION] >> metis_tac[]) >> simp[] >>
‘BIGUNION
          {tfv (bmap ' i) |
           i |
           i ∈ FDOM bmap ∧ (i ∈ slbounds l ∨ ∃t. i ∈ tbounds t ∧ MEM t l0)} =
BIGUNION
          {tfv (bmap ' i) |
           i |
           i ∈ FDOM bmap ∧ i ∈ slbounds l} ∪
BIGUNION  {tfv (bmap ' i) |
           i |
           i ∈ FDOM bmap ∧ ∃t. i ∈ tbounds t ∧ MEM t l0}’
by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
      metis_tac[]) >>
simp[] >>
‘{tfv (tprpl bmap a) | MEM a l0} =
    {tfv tm ∪
            BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∧ i ∈ tbounds tm} | MEM tm l0}’
    by (rw[Once EXTENSION] >> rw[EQ_IMP_THM] (* 2 *)
       >- (qexists ‘a’ >> simp[] >>
            ‘(∀n s. (n,s) ∈ tfv a ⇒ sbounds s = ∅)’
           by metis_tac[] >>
          drule_then assume_tac $ cj 1 tfv_tprpl >>
          simp[]) >>
       qexists ‘tm’ >>
        ‘(∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅)’
           by metis_tac[] >>
        drule_then assume_tac $ cj 1 tfv_tprpl >>
       simp[]) >>
simp[] >>  
‘BIGUNION
          {tfv tm ∪
           BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∧ i ∈ tbounds tm} |
           MEM tm l0} =
BIGUNION
          {tfv tm | MEM tm l0}  ∪
BIGUNION {tfv (bmap ' i) | i | ∃tm.i ∈ FDOM bmap ∧ i ∈ tbounds tm ∧  MEM tm l0}’
by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 4 *)
    >>  metis_tac[]) >> simp[] >>
‘BIGUNION {sfv s | MEM s (slprpl bmap l)} =
 BIGUNION {sfv s | MEM s l} ∪
 BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∧ i ∈ slbounds l}’    
 suffices_by (rw[] >> rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 8 *)
    >>  metis_tac[]) >>
 rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
 >- (drule_then assume_tac $ iffLR MEM_EL >>
    gs[LENGTH_slprpl] >>
    drule_then assume_tac slprpl_EL >> gs[] >>
    ‘(∀n1 s. (n1,s) ∈ sfv (EL n l) ⇒ sbounds s = {})’
     by metis_tac[MEM_EL] >>
    drule_then assume_tac $ cj 2 tfv_tprpl >>
    gs[] (* 2 *)
    >-  metis_tac[MEM_EL] >>
    gs[FDOM_shift_bmap] >> rw[IN_slbounds,PULL_EXISTS] >>
    drule_then assume_tac FAPPLY_shift_bmap >>
    gs[] >> gs[tfv_tshift] >> disj2_tac >>
    qexistsl [‘x'’,‘n’] >> simp[])
 >- (drule_then assume_tac $ iffLR MEM_EL >> gs[] >>
    simp[MEM_EL] >>
    qexists ‘EL n (slprpl bmap l)’ >>   gs[LENGTH_slprpl] >>
    drule_then assume_tac slprpl_EL >> simp[] >>
    ‘(∀n1 s. (n1,s) ∈ sfv (EL n l) ⇒ sbounds s = {})’
     by metis_tac[MEM_EL] >>
    drule_then assume_tac $ cj 2 tfv_tprpl >>
    gs[] >> qexists ‘n’ >> simp[]) >>
 gs[IN_slbounds] >>
 drule_then assume_tac slprpl_EL >>
 qexists ‘EL m (slprpl bmap l)’ >> simp[MEM_EL] >>
 ‘(∀n1 s. (n1,s) ∈ sfv (EL m l) ⇒ sbounds s = {})’
     by metis_tac[MEM_EL] >>
    drule_then assume_tac $ cj 2 tfv_tprpl >>
    gs[PULL_EXISTS] >>
 qexists ‘m’ >> simp[LENGTH_slprpl] >>
 disj2_tac >> simp[FDOM_shift_bmap,PULL_EXISTS] >>
 qexists ‘i’ >> simp[FAPPLY_shift_bmap,tfv_tshift]
QED


Theorem ffv_fVar_subst:
∀f P sl ϕ.
(∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅) ∧
(P,sl) ∈ freefVars f ⇒
ffv (fVar_subst (P,sl,ϕ) f) ⊆
ffv f ∪ ffv ϕ
Proof
Induct_on ‘f’ >>
gs[freefVars_def,fVar_subst_def,ffv_thm] (* 3 *) >> rw[](*7*)
>- (first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (Cases_on ‘(P,sl) ∈ freefVars f'’ (* 2 *)
   >- (first_x_assum $ drule_then assume_tac >>
      gs[SUBSET_DEF] >> metis_tac[]) >>
   drule_then assume_tac fVar_subst_id >> simp[] >>
   rw[SUBSET_DEF])
>- (Cases_on ‘(P,sl) ∈ freefVars f’ (* 2 *)
   >- (first_x_assum $ drule_then assume_tac >>
      gs[SUBSET_DEF] >> metis_tac[]) >>
   drule_then assume_tac fVar_subst_id >> simp[] >>
   rw[SUBSET_DEF])
>- (first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (gs[SUBSET_DEF] >> metis_tac[])
>- (first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
drule_then assume_tac ffv_fprpl >> simp[FDOM_mk_bmap] >>
‘{tfv t | MEM t l0} = {tfv t | MEM t (REVERSE l0)}’
 by rw[EXTENSION,MEM_REVERSE] >>
pop_assum SUBST_ALL_TAC >>  
‘BIGUNION {tfv (mk_bmap (REVERSE l0) ' i) | i | i < LENGTH l0 ∧ i ∈ fbounds ϕ} ⊆ BIGUNION {tfv t | MEM t (REVERSE l0)} ’
 suffices_by (rw[SUBSET_DEF] >> metis_tac[]) >>
irule SUBSET_BIGUNION >>
rw[SUBSET_DEF,FAPPLY_mk_bmap] >>
irule_at Any EQ_REFL >>
‘i < LENGTH (REVERSE l0)’ by simp[] >>
drule_then assume_tac FAPPLY_mk_bmap >> 
metis_tac[MEM_EL,MEM_REVERSE]
QED


Theorem wff_no_vbound:
(∀f. wff Σf f ⇒ ∀n s. (n,s) ∈ ffv f ⇒ sbounds s = {})
Proof           
Induct_on ‘wff’ >> rw[wff_fbounds,tbounds_thm](* 6 *)
>- (first_x_assum drule >>
   rw[] >> drule $ cj 1 wft_tbounds >>
   rw[] >> CCONTR_TAC>> gs[GSYM MEMBER_NOT_EMPTY] >>
   drule_then assume_tac $ cj 1 sbounds_tbounds>>
   gs[SUBSET_DEF])
>- metis_tac[]
>- metis_tac[]
>- metis_tac[wfabsap_sfv_sbounds]
>- (drule_then assume_tac wfabsap_wft >>
   first_x_assum $ drule_then assume_tac >>
   drule_then assume_tac $ cj 1 wft_tbounds >>
   CCONTR_TAC>> gs[GSYM MEMBER_NOT_EMPTY] >>
   drule_then assume_tac $ cj 1 sbounds_tbounds>>
   gs[SUBSET_DEF]) >>
drule_then assume_tac ffv_mk_FALL >> gs[](* 2 *)
>- metis_tac[] >>
drule_then assume_tac $ cj 2 wft_tbounds >>
   CCONTR_TAC>> gs[GSYM MEMBER_NOT_EMPTY] >>
   drule_then assume_tac $ cj 2 sbounds_tbounds>>
   gs[SUBSET_DEF]
QED   


Theorem sfv_ffv:
∀f. (n,s) ∈ ffv f ⇒ sfv s ⊆ ffv f
Proof
rw[] >>
qspecl_then [‘f’] assume_tac ffv_is_cont >>
gs[is_cont_def] >> first_x_assum drule >> rw[]
QED


Definition frpl_def:
  frpl _ _ False = False ∧
  frpl i t (Pred p tl) =
  Pred p (MAP (trpl i t) tl) ∧
  frpl i t (fVar p sl tl) =
  fVar p (specsl i t sl) (MAP (trpl i t) tl) ∧
  frpl i t (IMP f1 f2) =
  IMP (frpl i t f1) (frpl i t f2) ∧
  frpl i t (FALL s b) =
  FALL (srpl i t s) (frpl (i + 1) t b)
End        




Theorem tprpl_mk_bmap_CONS:
(∀t tm tl n. tbounds tm = {} ⇒
 tprpl (shift_bmap n (mk_bmap (REVERSE tl ⧺ [tm]))) t =
 tprpl (shift_bmap n (mk_bmap (REVERSE tl))) (trpl (LENGTH tl + n) tm t)) ∧
(∀s tm tl n. tbounds tm = {} ⇒
 sprpl (shift_bmap n (mk_bmap (REVERSE tl ⧺ [tm]))) s =
 sprpl (shift_bmap n (mk_bmap (REVERSE tl))) (srpl (LENGTH tl + n) tm s)) 
Proof
ho_match_mp_tac better_tm_induction >>
rw[trpl_def,tprpl_def,MAP_EQ_f,FDOM_mk_bmap,MAP_MAP_o,
   FAPPLY_mk_bmap,FDOM_shift_bmap,FAPPLY_shift_bmap,FDOM_shift_bmap] >> gs[]
 (* 4 *)
>- (‘LENGTH tl ∈ FDOM (mk_bmap (REVERSE tl ⧺ [tm]))’
    by simp[FDOM_mk_bmap] >>
   drule_then assume_tac FAPPLY_shift_bmap >> simp[] >>
   gs[FDOM_mk_bmap,FAPPLY_mk_bmap,EL_REVERSE2] >>
   ‘tbounds tm ∩ FDOM (shift_bmap n' (mk_bmap (REVERSE tl))) = {}’
    by (gs[EXTENSION] >> metis_tac[]) >>
   metis_tac[tprpl_id,tshift_id])
>- (‘x ∈ FDOM (mk_bmap (REVERSE tl ⧺ [tm]))’
    by simp[FDOM_mk_bmap] >>
   drule_then assume_tac FAPPLY_shift_bmap >> simp[] >>
   ‘x ∈ FDOM (mk_bmap (REVERSE tl))’
    by simp[FDOM_mk_bmap] >>
   drule_then assume_tac FAPPLY_shift_bmap >> simp[] >>
   gs[FDOM_mk_bmap,FAPPLY_mk_bmap,EL_REVERSE2] >>
   ‘x < LENGTH tl’ by simp[] >> AP_TERM_TAC>>
   irule EL_REVERSE1 >> simp[]) >>
Cases_on ‘∃x. n = n' + x ∧ x < LENGTH tl’ >> simp[] >>
gs[]  
QED   
           
Theorem slprpl_mk_bmap_CONS:
∀l tl tm n. tbounds tm = {} ⇒
slprpl (shift_bmap n (mk_bmap (REVERSE tl ⧺ [tm]))) l =
        slprpl (shift_bmap n (mk_bmap (REVERSE tl)))
          (specsl (n + LENGTH tl) tm l)
Proof
Induct_on ‘l’ >> gs[slprpl_def,specsl_def] >> rw[] (* 2 *)
>- (‘sprpl (shift_bmap n (mk_bmap (REVERSE tl ⧺ [tm]))) h =
        sprpl (shift_bmap n (mk_bmap (REVERSE tl)))
          (srpl (n + LENGTH tl) tm h)’ suffices_by cheat >>
    drule_then assume_tac $ cj 2 tprpl_mk_bmap_CONS >>
   metis_tac[arithmeticTheory.ADD_COMM]) >>
first_x_assum $ drule_then assume_tac >>
simp[shift_bmap_SUM]
QED


                    
Theorem fprpl_mk_bmap_CONS:
∀ϕ tl tm n.tbounds tm = {} ⇒
fprpl (shift_bmap n (mk_bmap (REVERSE tl ⧺ [tm]))) ϕ =
fprpl (shift_bmap n (mk_bmap (REVERSE tl))) (frpl (LENGTH tl + n) tm ϕ)
Proof
Induct_on ‘ϕ’ >> gs[fprpl_def,frpl_def,MAP_MAP_o,MAP_EQ_f]
>- (rw[] >> drule_then assume_tac $ cj 1 tprpl_mk_bmap_CONS >>
   metis_tac[arithmeticTheory.ADD_COMM])
>- (rw[] (* 2 *)
   >- (drule_then assume_tac $ cj 2 tprpl_mk_bmap_CONS >>
       metis_tac[arithmeticTheory.ADD_COMM]) >>
   rw[shift_bmap_SUM]) >> rw[] (* 2 *)
>- metis_tac[slprpl_mk_bmap_CONS] >>
drule_then assume_tac $ cj 1 tprpl_mk_bmap_CONS >>
metis_tac[arithmeticTheory.ADD_COMM]   
QED


Theorem shift_bmap_0_I:
 shift_bmap 0 = I
Proof
rw[FUN_EQ_THM,shift_bmap_0]
QED

Theorem fprpl_mk_bmap_CONS:
tbounds tm = {} ⇒
fprpl (mk_bmap (REVERSE tl ⧺ [tm])) ϕ =
fprpl (mk_bmap (REVERSE tl)) (frpl (LENGTH tl) tm ϕ)
Proof
rw[] >> drule_then assume_tac fprpl_mk_bmap_CONS >>
first_x_assum (qspecl_then [‘ϕ’,‘tl’,‘0’] assume_tac) >>
gs[shift_bmap_0_I]
QED


Theorem subst_bound_FALLL:
∀sl tm ϕ i. subst tm i (FALLL sl ϕ) =
(FALLL (specsl i tm sl) (subst tm (i + LENGTH sl) ϕ))
Proof
Induct_on ‘sl’ >>
gs[subst_def,specsl_def,subst_bound_def,FALLL_def,
arithmeticTheory.ADD1]
QED
          


Theorem wff_fVar_subst_lemma:
 (∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
 ∀tl sl ϕ.
 wfabsap Σf sl tl ∧ wff (Σf,Σp) (FALLL sl ϕ) ⇒
 wff (Σf,Σp) (fprpl (mk_bmap (REVERSE tl)) ϕ)
Proof
strip_tac >> 
Induct_on ‘tl’ (* 2 *)
>- (Cases_on ‘sl’ >>
    simp[wfabsap_def,fprpl_FEMPTY,FALLL_def]) >>
Cases_on ‘sl’ >>
simp[wfabsap_def,fprpl_FEMPTY,FALLL_def] >>
rw[] >>
drule $ iffLR wff_FALL >> rw[] >>
drule_then assume_tac wff_spec >>
gs[mk_FALL_def] >> pop_assum (assume_tac o GSYM) >> gs[] >>
last_x_assum $ drule_then assume_tac >>
rename [‘wft Σf tm’] >>
qabbrev_tac ‘s = sort_of tm’ >>
first_x_assum (qspecl_then [‘(abstract (n,s) f)’,‘Σp’,‘tm’] assume_tac) >> gs[] >>
rename [‘wfabsap Σf (specsl 0 tm sl) tl’] >> 
‘subst_bound (Var n s) (FALLL sl ϕ) = subst_bound (Var n s) (abstract (n,s) f)’
  by simp[] >>
‘subst_bound (Var n s) (abstract (n,s) f) = f’ by cheat >>
pop_assum SUBST_ALL_TAC >>
pop_assum (assume_tac o GSYM) >>
pop_assum SUBST_ALL_TAC >>
‘abstract (n,s) (subst_bound (Var n s) (FALLL sl ϕ)) =
(FALLL sl ϕ)’ by cheat >> gs[] >> 
first_x_assum (qspecl_then [‘subst tm (LENGTH sl) ϕ’] assume_tac) >>
‘(fprpl (mk_bmap (REVERSE tl)) (subst tm (LENGTH sl) ϕ)) =  (fprpl (mk_bmap (REVERSE tl ⧺ [tm])) ϕ)’ by cheat >>
gs[] >> first_x_assum irule >>
‘wff (Σf,Σp) (subst_bound tm (FALLL sl ϕ))’
 by cheat (*wff spec*) >>
‘subst_bound tm (FALLL sl ϕ) =
(FALLL (specsl 0 tm sl) (subst tm (LENGTH sl) ϕ))’
 suffices_by metis_tac[] >>
 cheat
QED  



Theorem wff_fVar_subst:
(∀fsym.
        isfsym (Σf:string |-> sort # (string # sort) list)
         fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
∀f. wff (Σf,Σp) f ⇒
    ∀P sl ϕ. wff (Σf,Σp) (FALLL sl ϕ) ⇒
    wff (Σf,Σp) (fVar_subst (P,sl,ϕ) f)
Proof
Induct_on ‘wff’ >> rw[fVar_subst_def,wff_rules] (* 2 *)
>- (Cases_on ‘P' = P ∧ sl' = sl’ >> simp[] (* 2 *)
   >- (drule_then assume_tac wfabsap_ok_abs >> simp[] >>
      gvs[] >>
      assume_tac (GEN_ALL $ SRULE [] wff_fVar_subst_lemma) >>
      first_x_assum $ drule_then assume_tac >>
      metis_tac[]) >>
   ‘¬(P' = P ∧ sl' = sl ∧ ok_abs sl)’ by metis_tac[] >>
   simp[wff_rules]) >>
first_x_assum $ drule_then assume_tac >>
first_x_assum (qspecl_then [‘P’] assume_tac) >>
rw[mk_FALL_def,fVar_subst_def] >>
reverse (Cases_on ‘(P,sl) ∈ freefVars f’  (* 2 *))
>- (‘(P,sl) ∉ freefVars (abstract (n,s) f)’
       by metis_tac[freefVars_abs_SUBSET,
                    abstract_def,SUBSET_DEF] >>
    drule_then assume_tac fVar_subst_id >> simp[] >>
    rw[GSYM mk_FALL_def] >> irule $ cj 5 wff_rules >>
       simp[] >> metis_tac[]) 
>- (Cases_on ‘∃st. MEM st sl ∧ (n,s) ∈ sfv st’ (* 2 *)
   >- (‘(P,sl) ∉ freefVars (abstract (n,s) f)’
        by cheat >>
       drule_then assume_tac fVar_subst_id >> simp[] >>
       rw[GSYM mk_FALL_def] >> irule $ cj 5 wff_rules >>
       simp[] >> metis_tac[]) >>
   ‘(P,sl) ∈ freefVars (abstract (n,s) f)’ by cheat >>
   ‘(n,s) ∉ ffv ϕ’ by cheat >>
   ‘∀st. MEM st sl ⇒ (n,s) ∉ sfv st’ by metis_tac[] >>
   rev_drule_all_then assume_tac fVar_subst_abs1 >>
   rw[abstract_def] >> simp[] >>
   rw[GSYM mk_FALL_def,GSYM abstract_def] >>
   irule $ cj 5 wff_rules >>
   simp[] >>
   rev_drule_at_then Any assume_tac ffv_fVar_subst >>
   ‘(∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅)’ by cheat >>
   first_x_assum $ drule_then assume_tac >> rw[] >>
   gs[SUBSET_DEF] >>
   first_x_assum $ drule_then strip_assume_tac (* 2 *)
   >- metis_tac[] >>
   drule_then assume_tac sfv_ffv >> gs[SUBSET_DEF] >>
   metis_tac[])
QED   





Theorem subst_abs:
∀f i n s.
  (n,s) ∉ ffv f ⇒
  fabs (n,s) i (frpl i (Var n s) f) = f
Proof
 Induct_on ‘f’ >>
 gs[fabs_def,frpl_def,ffv_def,
    MAP_MAP_o,MEM_MAP,MAP_fix] >> rw[] (* 4 *)
 >- metis_tac[tabs_trpl]
 >- metis_tac[tabs_trpl]
 >- metis_tac[tabs_trpl,abssl_specsl]
 >- metis_tac[tabs_trpl]
QED        
                   
val _ = export_theory();

