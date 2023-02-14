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
  




Definition fabs_def:
  fabs _ _ False = False ∧
  fabs v i (Pred p tl) =
  Pred p (MAP (tabs v i) tl) ∧
  fabs v i (fVar p vl tl) =
  fVar p vl
         (MAP (tabs v i) tl) ∧
  fabs v i (IMP f1 f2) =
  IMP (fabs v i f1) (fabs v i f2) ∧
  fabs v i (FALL s b) =
  FALL (sabs v i s) (fabs v (i + 1) b)
End             


Definition abst_def:
  abst v = fabs v 0
End
        
Definition mk_FALL_def:
mk_FALL n s b = FALL s (abst (n,s) b)
End        

Definition fbounds_def:
fbounds False = {} ∧
fbounds (fVar P sl tl) = 
BIGUNION (set (MAP tbounds tl)) ∧
fbounds (Pred p tl) = BIGUNION (set (MAP tbounds tl)) ∧
fbounds (IMP f1 f2) = fbounds f1 ∪ fbounds f2 ∧
fbounds (FALL s b) =
sbounds s ∪ IMAGE PRE (fbounds b DELETE 0) 
End



Theorem fbounds_thm:
fbounds False = {} ∧
fbounds (fVar P sl tl) = 
BIGUNION {tbounds t | MEM t tl} ∧
fbounds (Pred p tl) = BIGUNION {tbounds t | MEM t tl} ∧
fbounds (IMP f1 f2) = fbounds f1 ∪ fbounds f2 ∧
fbounds (FALL s b) =
sbounds s ∪ IMAGE PRE (fbounds b DELETE 0) 
Proof
simp[fbounds_def,PULL_EXISTS] >> simp[Once EXTENSION,PULL_EXISTS,MEM_MAP,LIST_TO_SET_MAP,IMAGE_DEF,EXTENSION]
QED 
        





Definition fVars_def:
  fVars (Pred _ _) = {} ∧
  fVars (IMP f1 f2) = fVars f1 ∪ fVars f2 ∧
  fVars (FALL s b) = fVars b ∧
  fVars False = {} ∧
  fVars (fVar P sl tl) = {(P,sl)}
End


Definition Uof_def:
  Uof f s = BIGUNION {f e | e ∈ s}
End  


Definition ofFMAP_def:
ofFMAP f fmap s = BIGUNION {f (fmap ' a) | a | a ∈ FDOM fmap ∩ s}
End
             
    
Definition slfv_def:
  slfv sl = Uof sfv (set sl)
End

Theorem IN_slfv:
v ∈ slfv sl ⇔ ∃s. MEM s sl ∧ v ∈ sfv s
Proof
rw[slfv_def,Uof_def,PULL_EXISTS] >> metis_tac[]
QED          

Definition fVslfv_def:
  fVslfv f = Uof (slfv o SND) (fVars f)          
End         

Theorem IN_fVslfv:
  v ∈ fVslfv f ⇔
    ∃P sl s. (P,sl) ∈ fVars f ∧ MEM s sl ∧ v ∈ sfv s
Proof
 rw[fVslfv_def,Uof_def,PULL_EXISTS,IN_slfv,EQ_IMP_THM] (*2*)
 >- (Cases_on ‘e’ >> gs[] >> metis_tac[]) >>
 rpt $ first_x_assum $ irule_at Any >> gs[]
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
  (n,s) ∉ fVslfv f ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
  wff (Σf,Σp) (mk_FALL n s f))
End
 


Definition fprpl_def:
  fprpl bmap False = False ∧
  fprpl bmap (IMP f1 f2) =
   IMP (fprpl bmap f1) (fprpl bmap f2) ∧
  fprpl bmap (Pred p tl) =
  Pred p (MAP (tprpl bmap) tl) ∧
  fprpl bmap (fVar p sl tl) =
   fVar p sl
        (MAP (tprpl bmap) tl) ∧
  fprpl bmap (FALL s b) =
  FALL (sprpl bmap s) (fprpl (shift_bmap 1 bmap) b)
End

Definition fVinst_def:
fVinst fσ False = False ∧
fVinst fσ (Pred p tl) = Pred p tl ∧
fVinst fσ (IMP f1 f2) = IMP (fVinst fσ f1)
                              (fVinst fσ f2) ∧
fVinst fσ (FALL s ϕ) = FALL s (fVinst fσ ϕ) ∧
fVinst fσ (fVar P sl tl) =
if (P,sl) ∈ FDOM fσ then
  fprpl (mk_bmap (REVERSE tl)) (fσ ' (P,sl))
else fVar P sl tl
End


Definition FALLL_def:
FALLL [] ϕ = ϕ ∧
FALLL (h :: t) ϕ = FALL h (FALLL t ϕ)
End

Definition wffVmap_def:
  wffVmap Σ ε ⇔
  ∀P:string sl.
    (P,sl) ∈ FDOM ε ⇒ wff Σ (FALLL sl (ε ' (P,sl)))
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



Theorem fabs_id:
∀f n s i. (n,s) ∉ ffv f ⇒ fabs (n,s) i f = f
Proof
Induct_on ‘f’ (* 5 *)
>- rw[fabs_def]
>- (rw[fabs_def,MAP_fix] >>
   metis_tac[tabs_id])
>- rw[fabs_def]
>- (rw[fabs_def] >> metis_tac[tabs_id]) >>
rw[fabs_def,MAP_fix] >> 
metis_tac[tabs_id]
QED        


           

Theorem ffv_fabs:
∀fm i n s.
 (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ∧
 (∀P sl s0. (P,sl) ∈ fVars fm ∧ MEM s0 sl ⇒
            (n,s) ∉ sfv s0) ∧
 (n,s) ∈ ffv fm ⇒
 sfv s ∪ ffv (fabs (n,s) i fm) =
 ffv fm DELETE (n,s)
Proof
Induct_on ‘fm’ (* 5 *) >> gs[fVars_def]
>- (rw[ffv_thm,fabs_def] >>
    gs[MEM_MAP,PULL_EXISTS] >>
   rename [‘(n,s) ∈ tfv t’] >>
    ‘BIGUNION {tfv t' | (∃y. t' = tabs (n,s) i y ∧ MEM y l)} =
    (BIGUNION {tfv t1 | (∃y. t1 = tabs (n,s) i y ∧ MEM y l ∧ (n,s) ∈ tfv y)}) ∪
    (BIGUNION {tfv t1 | (∃y. t1 = tabs (n,s) i y ∧ MEM y l ∧ (n,s) ∉ tfv y)})’
    by (rw[EXTENSION] >> metis_tac[]) >>
    qabbrev_tac ‘BU =  BIGUNION {tfv t' | (∃y. t' = tabs (n,s) i y ∧ MEM y l)}’ >>
    qabbrev_tac ‘BU1 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tabs (n,s) i y ∧ MEM y l ∧ (n,s) ∈ tfv y)}’ >>
    qabbrev_tac ‘BU2 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tabs (n,s) i y ∧ MEM y l ∧ (n,s) ∉ tfv y)}’ >>
    simp[] >>
    ‘BU2 = BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y}’
     by
      (rw[Abbr‘BU2’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
      (* 2 *)
      >> (‘tabs (n,s) i y = y’
          suffices_by metis_tac[] >>
         irule $ cj 1 tabs_id >> simp[])) >>
    simp[UNION_ASSOC] >>
   ‘sfv s ∪ BU1 =
     BIGUNION {sfv s0 ∪ tfv t1 |
     (∃y. t1 = tabs (n,s0) i y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧ s0 = s}’
     by (rw[Abbr‘BU1’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv t1 |
           (∃y. t1 = tabs (n,s0) i y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧
           s0 = s} =
      BIGUNION
          {sfv s0 ∪ tfv (tabs (n0,s0) i y) |
            MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >> simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv (tabs (n0,s0) i y) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} =
      BIGUNION
          {tfv y DELETE (n0,s0) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by
        (‘∀y n0 s0. MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n ⇒
          sfv s0 ∪ tfv (tabs (n0,s0) i y) =
          tfv y DELETE (n0,s0)’
         suffices_by
          (strip_tac >> AP_TERM_TAC >> 
          rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
          metis_tac[]) >>
         rw[] >>
         irule $ cj 1 tfv_tabs >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {tfv y DELETE (n0,s0) | MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} ∪
        BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} =
     BIGUNION {tfv y | MEM y l} DELETE (n,s)’
      by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
         >>  metis_tac[]) >>
     simp[])
>- (rw[ffv_thm,fabs_def] (* 2 *)   
   >- (Cases_on ‘(n,s) ∈ ffv fm'’ (* 2 *)
      >- (‘sfv s ∪ (ffv (fabs (n,s) i fm) ∪ ffv (fabs (n,s) i fm')) = (sfv s ∪ ffv (fabs (n,s) i fm)) ∪ (sfv s ∪ ffv (fabs (n,s) i fm'))’ by (rw[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘sfv s ∪ ffv (fabs (n,s) i fm) = ffv fm DELETE (n,s) ∧
       sfv s ∪ ffv (fabs (n,s) i fm') = ffv fm' DELETE (n,s)’
       by metis_tac[] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
      rw[UNION_ASSOC] >>
      ‘sfv s ∪ ffv (fabs (n,s) i fm) = ffv fm DELETE (n,s)’
       by metis_tac[] >>
      ‘(fabs (n,s) i fm') = fm'’
       by metis_tac[fabs_id] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
  Cases_on ‘(n,s) ∈ ffv fm’ (* 2 *)
  >- (‘sfv s ∪ (ffv (fabs (n,s) i fm) ∪ ffv (fabs (n,s) i fm')) = (sfv s ∪ ffv (fabs (n,s) i fm)) ∪ (sfv s ∪ ffv (fabs (n,s) i fm'))’ by (rw[EXTENSION] >> metis_tac[]) >>
    simp[] >>
    ‘sfv s ∪ ffv (fabs (n,s) i fm) = ffv fm DELETE (n,s) ∧
     sfv s ∪ ffv (fabs (n,s) i fm') = ffv fm' DELETE (n,s)’
      by metis_tac[] >>
    simp[] >> rw[EXTENSION] >> metis_tac[]) >>
  rw[UNION_ASSOC] >>
  ‘sfv s ∪ ffv (fabs (n,s) i fm') = ffv fm' DELETE (n,s)’
    by metis_tac[] >>
  ‘(fabs (n,s) i fm) = fm’
   by metis_tac[fabs_id] >>
  simp[] >>
   ‘sfv s ∪ ffv fm ∪ ffv (fabs (n,s) i fm') =
   sfv s ∪ ffv (fabs (n,s) i fm') ∪ ffv fm’
    by (rw[EXTENSION] >> metis_tac[]) >> simp[] >>
   rw[EXTENSION] >> metis_tac[])
>- (rw[ffv_thm,fabs_def] (* 2 *)
   >- (Cases_on ‘(n,s') ∈ ffv fm’ (* 2 *) >-
      (‘sfv s' ∪ (sfv (sabs (n,s') i s) ∪ ffv (fabs (n,s') (i+1) fm)) =
      (sfv s' ∪ (sfv (sabs (n,s') i s)) ∪ (sfv s' ∪ ffv (fabs (n,s') (i+1) fm)))’
       by (rw[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘sfv s' ∪
        (sfv (sabs (n,s') i s)) =
       sfv s DELETE (n,s')’ by metis_tac[tfv_tabs] >>
      simp[] >>
      ‘(sfv s' ∪ ffv (fabs (n,s') (i+1) fm)) =
      ffv fm DELETE (n,s')’ by metis_tac[] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
      ‘fabs (n,s') (i + 1) fm = fm’ by metis_tac[fabs_id] >>
      simp[] >> rw[UNION_ASSOC]>>
      ‘sfv s' ∪ sfv (sabs (n,s') i s) =
      sfv s DELETE (n,s')’  by metis_tac[tfv_tabs] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
   (Cases_on ‘(n,s') ∈ sfv s’ (* 2 *) >-
      (‘sfv s' ∪ (sfv (sabs (n,s') i s) ∪ ffv (fabs (n,s') (i+1) fm)) =
      (sfv s' ∪ (sfv (sabs (n,s') i s)) ∪ (sfv s' ∪ ffv (fabs (n,s') (i+1) fm)))’
       by (rw[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘sfv s' ∪
        (sfv (sabs (n,s') i s)) =
       sfv s DELETE (n,s')’ by metis_tac[tfv_tabs] >>
      simp[] >>
      ‘(sfv s' ∪ ffv (fabs (n,s') (i+1) fm)) =
      ffv fm DELETE (n,s')’ by metis_tac[] >>
      simp[] >> rw[EXTENSION] >> metis_tac[]) >>
      ‘sabs (n,s') i s = s’
       by metis_tac[tabs_id] >>
      simp[] >> rw[UNION_ASSOC]>>
      ‘sfv s' ∪ sfv s ∪ ffv (fabs (n,s') (i + 1) fm) =
        sfv s ∪ (sfv s' ∪ ffv (fabs (n,s') (i + 1) fm)) ’
        by (rw[EXTENSION] >> metis_tac[]) >> simp[] >>
      ‘sfv s' ∪ ffv (fabs (n,s') (i + 1) fm) =
      ffv fm DELETE (n,s')’  by metis_tac[] >>
      simp[] >> rw[EXTENSION] >> metis_tac[])) >>
(*fVar case*)      
rw[ffv_thm,fabs_def] >> gs[MEM_MAP,PULL_EXISTS] >>
(*last subgoal*)
rename [‘(n,s) ∈ tfv t’,‘ ∀s0. MEM s0 sl ⇒ (n,s) ∉ sfv s0’] >>
‘sfv s ∪
 BIGUNION {tfv t' | (∃y. t' = tabs (n,s) i y ∧ MEM y l0)} = BIGUNION {tfv t | MEM t l0}  DELETE (n,s)’
  by
  (rw[Once EXTENSION,PULL_EXISTS] >>
   rw[EQ_IMP_THM] (* 3 *)
   >- (qexists ‘t’ >> simp[] >>
       metis_tac[vsort_tfv_closed] )
   >- (Cases_on ‘(n,s) ∈ tfv y’ (* 2 *)
       >- (‘sfv s ∪ tfv (tabs (n,s) i y) =
            tfv y DELETE (n,s)’
             by (irule $ cj 1 tfv_tabs >> metis_tac[]) >>
           ‘x ∈ sfv s ∪ tfv (tabs (n,s) i y) ’
             by rw[UNION_DEF] >>
           gs[EXTENSION] >> metis_tac[]) >>
       ‘tabs (n,s) i y = y’
         by (irule $ cj 1 tabs_id >> simp[]) >>
       metis_tac[]) >>
   rename [‘x ∈ tfv y’] >>
   Cases_on ‘(n,s) ∈ tfv y’ (* 2 *)
   >- (‘sfv s ∪ tfv (tabs (n,s) i y) =
        tfv y DELETE (n,s)’
         by (irule $ cj 1 tfv_tabs >> metis_tac[]) >>
       ‘x ∈ tfv y DELETE (n,s)’ by simp[] >>
       qpat_x_assum ‘sfv s ∪ tfv (tabs (n,s) i y) = tfv y DELETE (n,s)’ (assume_tac o GSYM) >>
       pop_assum SUBST_ALL_TAC >>
       gs[UNION_DEF] >> metis_tac[]) >>
   ‘tabs (n,s) i y = y’
     by (irule $ cj 1 tabs_id >> simp[]) >>
   metis_tac[]) >>
simp[] >> gs[EXTENSION] >> metis_tac[]
QED                                     

Theorem ffv_mk_FALL:
∀f n s.
(∀n0 s0. (n0,s0) ∈ ffv f ⇒ (n,s) ∉ sfv s0) ∧
(∀P sl s0. (P,sl) ∈ fVars f ∧ MEM s0 sl ⇒
            (n,s) ∉ sfv s0) ⇒
ffv (mk_FALL n s f) = (ffv f ∪ sfv s) DELETE (n,s)
Proof
rw[ffv_thm,mk_FALL_def,abst_def] >>
Cases_on ‘(n,s) ∈ ffv f’ (*2 *)
>- (drule_all_then assume_tac ffv_fabs >> simp[] >>
   ‘sfv s ⊆ ffv f DELETE (n,s)’
     suffices_by (gs[EXTENSION] >> gs[SUBSET_DEF] >>
                 metis_tac[]) >>
   gs[SUBSET_DEF,EXTENSION] >>  metis_tac[]) >>
‘(fabs (n,s) 0 f) = f’ by metis_tac[fabs_id] >>
simp[] >>
rw[EXTENSION] >> metis_tac[tm_tree_WF]
QED

              
Theorem finst_fabs:
∀f an ast σ nn i.
  ffv f ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧
  (an,ast) ∉ FDOM σ ∧
  (∀x s. x ∈ ffv f ∪ sfv ast ∧ x ≠ (an,ast) ⇒
   (nn,s) ∉ tfv (σ ' x)) ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (an,ast) ∉ sfv s1) ∧
  (∀P sl s0. (P,sl) ∈ fVars f ∧ MEM s0 sl ⇒
            (an,ast) ∉ sfv s0) ⇒ 
  fabs (nn,sinst σ ast) i
          (finst (σ |+ ((an,ast),Var nn (sinst σ ast))) f) =
  finst σ (fabs (an,ast) i f)
Proof
 Induct_on ‘f’ >> gs[fVars_def]
 >- rw[finst_def,fabs_def]
 >- (rw[finst_def,fabs_def,
        MAP_MAP_o,MAP_EQ_f] >>
    irule tabs_tinst >> simp[] >>
    gs[SUBSET_DEF] >> metis_tac[])
 >- (rw[fabs_def] (* 2 *) >>
    first_x_assum irule >>
    gs[SUBSET_DEF] >> metis_tac[])
 >- (rw[fabs_def] (* 2 *)
    >- (irule sabs_sinst >>
       gs[SUBSET_DEF] >> metis_tac[]) >>
    first_x_assum irule >>
    gs[SUBSET_DEF] >> metis_tac[]) >>
 rw[finst_def,fabs_def,
    MAP_MAP_o,MAP_EQ_f] (* 2 *)
 >- (‘(an,ast) ∉ sfv e’ by metis_tac[] >>
    irule $ cj 2 fmap_fv_inst_eq_alt >>
    rw[FDOM_FUPDATE,FAPPLY_FUPDATE_THM] (* 2 *)
    >> (gs[SUBSET_DEF] >> metis_tac[])) >>
 irule tabs_tinst >> simp[] >>
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

Theorem NOTIN_fVslfv:
  v ∉ fVslfv f ⇔
    ∀P sl s. (P,sl) ∈ fVars f ∧ MEM s sl ⇒ v ∉ sfv s
Proof
metis_tac[IN_fVslfv]
QED



Definition vinst_fVar_def:
vinst_fVar vσ (P,sl) = (P,MAP (sinst vσ) sl)
End


Theorem Uof_UNION:
  Uof f (A ∪ B) = Uof f A ∪ Uof f B
Proof
  rw[Uof_def,Once EXTENSION] >> metis_tac[]
QED   
 
Theorem Uof_Sing:
 Uof f {x} = f x
Proof
rw[Uof_def,Once EXTENSION]
QED



Theorem Uof_INSERT:
Uof f (a INSERT s)= f a ∪ Uof f s
Proof
metis_tac[Uof_Sing,Uof_UNION,INSERT_SING_UNION]
QED
              
Theorem Uof_SUBSET_MONO:
  s1 ⊆ s2 ⇒ Uof f s1 ⊆ Uof f s2
Proof
  rw[Uof_def,SUBSET_DEF] >> metis_tac[]
QED  

Theorem Uof_EMPTY:
Uof f {} = {}
Proof
rw[Uof_def,Once EXTENSION]
QED

Theorem Uof_SUBSET:
Uof f A ⊆ B ⇔ (∀a. a ∈ A ⇒ f a ⊆ B)
Proof
rw[Uof_def,SUBSET_DEF] >>  metis_tac[]
QED
        

Theorem fVars_finst:
∀f. fVars (finst vσ f) = IMAGE (vinst_fVar vσ) (fVars f)
Proof
Induct_on ‘f’ >> gs[vinst_fVar_def,finst_def,fVars_def]
QED


Theorem fVslfv_alt:
fVslfv False = {} ∧
fVslfv (IMP f1 f2) = fVslfv f1 ∪ fVslfv f2 ∧
fVslfv (FALL s b) = fVslfv b ∧
fVslfv (Pred p tl) = {} ∧
fVslfv (fVar P sl tl) = slfv sl
Proof
rw[fVslfv_def,fVars_def,Uof_UNION,Uof_Sing,Uof_EMPTY]
QED


Theorem fVslfv_SUBSET_ffv:
∀f. fVslfv f ⊆ ffv f
Proof
Induct_on ‘f’ >> gs[fVslfv_alt,ffv_thm] (* 2 *)
>- (gs[SUBSET_DEF] >> metis_tac[]) 
>- (gs[SUBSET_DEF] >> metis_tac[]) >>
gs[slfv_def,Uof_SUBSET] >>
gs[SUBSET_DEF] >>metis_tac[]
QED


Theorem MEM_fVsl_SUBSET_fVslfv:
∀P sl s. (P,sl) ∈ fVars f ∧ MEM s sl ⇒ sfv s ⊆ fVslfv f
Proof
simp[SUBSET_DEF,IN_fVslfv] >> metis_tac[]
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
  (wff (Σf,Σp) (FALL (sinst σ1 s) (finst σ1 (abst (n,s) f))) ⇒ wff (Σf,Σp) (FALL (sinst σ s) (finst σ (abst (n,s) f))))’
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
     ‘finst σ1 (abst (n,s) f) =
      finst σ (abst (n,s) f)’
      by (irule $ fmap_ffv_finst_eq >>
      gs[mk_FALL_def,ffv_def] >>
      ‘ffv (abst (n,s) f) ⊆ FDOM σ1 ∧ ffv (abst (n,s) f) ⊆ FDOM σ’
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
  rw[abst_def] >>(*need lemma ffv_mk_FALL*)
  drule ffv_mk_FALL >>
  ‘(∀P sl s0. (P,sl) ∈ fVars f ∧ MEM s0 sl ⇒ (n,s) ∉ sfv s0)’ by (gs[IN_fVslfv] >> metis_tac[]) >>
  rw[] >> 
  first_x_assum $ drule_then assume_tac >> 
  rw[] >> gs[] >>
  ‘sfv s ⊆ FDOM σ’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[tm_tree_WF]) >>
  ‘(n,s) ∉ FDOM σ’ by gs[EXTENSION] >>
  ‘ffv f DELETE (n,s) ⊆ FDOM σ’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[tm_tree_WF]) >>
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
  drule_at_then Any assume_tac finst_fabs >>
  ‘finst σ (fabs (n,s) 0 f) =
   fabs (nn,sinst σ s) 0 (finst (σ |+ ((n,s),Var nn (sinst σ s))) f)’
    by (rw[Once EQ_SYM_EQ] >> irule finst_fabs >>
       simp[] >> metis_tac[]) >>
  simp[] >> rw[GSYM mk_FALL_def,GSYM abst_def] >>
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
  drule wfcod_no_bound >> rw[] >> gs[] (* 2 *)
  >- (Cases_on ‘(n,s) = (n0,st0)’ (* 2 *)
      >- (gs[FAPPLY_FUPDATE_THM] (* 2 *)
          >- metis_tac[tm_tree_WF] >>
          rev_drule $ cj 2 tfv_sinst >> rw[] >>
          first_x_assum (qspecl_then [‘s’,‘n1’,‘s1’] assume_tac)>>
          gs[] >>
          rev_drule wfcod_no_bound >> rw[] >> gs[] >>
          ‘(n0,st0) ≠ (n,s)’ by metis_tac[tm_tree_WF] >>
          first_x_assum (qspecl_then [‘(n0,st0)’,‘sinst σ s’] assume_tac) >> gs[] >> metis_tac[vsort_tfv_closed]) >>
      gs[FAPPLY_FUPDATE_THM] >>
      first_x_assum (qspecl_then [‘(n0,st0)’,‘sinst σ s’] assume_tac) >> gs[] >> metis_tac[vsort_tfv_closed]) >>
  simp[NOTIN_fVslfv,fVars_finst,PULL_EXISTS,
       vinst_fVar_def] >>
  Cases_on ‘x’ >> simp[vinst_fVar_def,MEM_MAP,PULL_EXISTS]>>
  drule_then assume_tac $ cj 2 tfv_sinst >> gs[]>>
  rw[] >> 
  first_x_assum (qspecl_then [‘y’] assume_tac) >> gs[] >>
  ‘sfv y ⊆ fVslfv f’
    by metis_tac[MEM_fVsl_SUBSET_fVslfv] >>
  ‘fVslfv f ⊆ ffv f’
      by metis_tac[fVslfv_SUBSET_ffv] >>
  ‘sfv y ⊆ ffv f’ by metis_tac[SUBSET_TRANS] >> 
  ‘sfv y ⊆ (n,s) INSERT ffv f ∪ sfv s DELETE (n,s)’
   by (gs[SUBSET_DEF] >> metis_tac[]) >> gs[] >>
  rw[] >> Cases_on ‘(n0,st0) ∉ sfv y ’ >> gs[] >>
  ‘(n0,st0) ∈ ffv f’
    by (gs[SUBSET_DEF] >> metis_tac[]) >>
  ‘(n0,st0) ≠ (n,s)’ suffices_by
   (simp[FAPPLY_FUPDATE_THM] >> rw[] >>
   first_x_assum irule >> simp[]) >>
  ‘(n0,st0) ∈ fVslfv f’ suffices_by metis_tac[] >>
  simp[IN_fVslfv] >> metis_tac[]
QED          


Theorem wff_FALL:
 ∀s b. wff (Σf,Σp) (FALL s b) ⇔
 (∃f n. wff (Σf,Σp) f ∧
          wfs Σf s ∧
          (n,s) ∉ fVslfv f ∧
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
          FALL s b = mk_FALL n s f)
Proof
 rw[Once wff_cases,EQ_IMP_THM] (* 2 *)
 >- (gs[mk_FALL_def] >> metis_tac[]) >>
 simp[] >> irule $ cj 5 wff_rules >> simp[] >> metis_tac[]
QED 



Theorem mk_bmap_NIL[simp]:
mk_bmap [] = FEMPTY
Proof
rw[mk_bmap_def]
QED




        
Definition frpl_def:
  frpl _ _ False = False ∧
  frpl i t (Pred p tl) =
  Pred p (MAP (trpl i t) tl) ∧
  frpl i t (fVar p sl tl) =
  fVar p sl (MAP (trpl i t) tl) ∧
  frpl i t (IMP f1 f2) =
  IMP (frpl i t f1) (frpl i t f2) ∧
  frpl i t (FALL s b) =
  FALL (srpl i t s) (frpl (i + 1) t b)
End        

Theorem frpl_FALLL:
∀sl ϕ t i.
 (frpl i t (FALLL sl ϕ)) = 
 FALLL (specsl i t sl) (frpl (LENGTH sl + i) t ϕ)
Proof
Induct_on ‘sl’ >>
rw[frpl_def,FALLL_def,specsl_def] >>
gs[trpl_def,arithmeticTheory.ADD1]
QED
                


        
        
Theorem fprpl_FEMPTY:
∀ϕ. (fprpl FEMPTY ϕ) = ϕ
Proof
Induct_on ‘ϕ’ >> rw[fprpl_def,tprpl_def,tprpl_FEMPTY,MAP_fix] >> gs[mk_bmap_NIL,shift_bmap_FEMPTY,slprpl_FEMPTY]
QED           



Theorem frpl_fabs:
∀f i n s.
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = {}) ∧
  i ∉ fbounds f ∧
  (n,s) ∉ fVslfv f ⇒
  frpl i new (fabs (n,s) i f) =
  finst (TO_FMAP [((n,s),new)]) f
Proof
 reverse (Induct_on ‘f’) >>
 gs[frpl_def,fabs_def,finst_def,MAP_MAP_o,MAP_EQ_f,PULL_EXISTS,fbounds_def,tfv_thm,ffv_thm,
   MEM_MAP] (* 4 *)
 >- (rw[GSYM tsubst_eq_tinst1] (* 2 *)
    >- (rw[Once EQ_SYM_EQ] >> rw[MAP_fix] >>
       irule $ cj 2 tsubst_id >>
       gs[IN_fVslfv,fVars_def] >>
       metis_tac[]) >>
    metis_tac[trpl_tabs])
 >- (rw[GSYM tsubst_eq_tinst1] (* 2 *)
    >- metis_tac[trpl_tabs] >>
    first_x_assum irule >> rw[] (* 3 *)
    >- metis_tac[] >- metis_tac[] >>
    first_x_assum (qspecl_then [‘i + 1’] assume_tac) >>
    gs[arithmeticTheory.ADD1] >> gs[fVslfv_alt])
 >- (gs[fVslfv_alt] >> rw[] >> metis_tac[]) >>
 gs[fVslfv_alt] >>
 rw[GSYM tsubst_eq_tinst1] >> metis_tac[trpl_tabs]
QED



Theorem fabs_fbounds_in:
  ∀f n s i.
    (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
    (n,s) ∉ fVslfv f ∧
    (n,s) ∈ ffv f ⇒
    i ∈ fbounds (fabs (n,s) i f)
Proof     
Induct_on ‘f’ >>
simp[fbounds_thm,fabs_def,ffv_thm,
     tfv_thm,MEM_MAP,PULL_EXISTS,fVslfv_alt] >>
rw[] (* 7 *)
>- metis_tac[tabs_tbounds_in]
>- metis_tac[]
>- metis_tac[]
>- metis_tac[tabs_tbounds_in]
>- (disj2_tac >> qexists ‘SUC i’ >>
   simp[arithmeticTheory.ADD1] >>
   metis_tac[tabs_tbounds_in])
>- (gs[slfv_def,Uof_def] >>
   metis_tac[])
>- metis_tac[tabs_tbounds_in]
QED        

Theorem fbounds_fabs_SUBSET:
  ∀f n s i.
    (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = {}) ⇒ 
    fbounds f ⊆ fbounds (fabs (n,s) i f)
Proof
Induct_on ‘f’ >>
simp[fbounds_thm,ffv_thm,PULL_EXISTS,fabs_def,MEM_MAP] (* 4 *)
>- (rw[SUBSET_DEF,PULL_EXISTS] >>
   ‘tbounds t ⊆ tbounds (tabs (n,s') i t)’
     suffices_by metis_tac[SUBSET_DEF] >>
   irule $ cj 1 tbounds_tabs_SUBSET >>
   metis_tac[])
>- (gs[SUBSET_DEF]>> metis_tac[])
>- (rw[] (* 2 *)
   >- (‘sbounds s ⊆
        sbounds (sabs (n,s') i s)’
        suffices_by gs[SUBSET_DEF,UNION_DEF] >>
       irule $ cj 2 tbounds_tabs_SUBSET >>
       metis_tac[]) >>
   ‘IMAGE PRE (fbounds f DELETE 0) ⊆
    IMAGE PRE (fbounds (fabs (n,s') (i + 1) f) DELETE 0)’
       suffices_by gs[SUBSET_DEF,UNION_DEF] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
rw[] >>
‘BIGUNION {tbounds t | MEM t l0} ⊆
 BIGUNION {tbounds t | (∃y. t = tabs (n,s') i y ∧ MEM y l0)}’
  suffices_by (gs[SUBSET_DEF,UNION_DEF] >> metis_tac[]) >>
rw[SUBSET_DEF,PULL_EXISTS] >>
‘tbounds t ⊆ tbounds (tabs (n,s') i t)’
suffices_by metis_tac[SUBSET_DEF] >>
irule $ cj 1 tbounds_tabs_SUBSET >> metis_tac[MEM_EL]
QED           


Theorem IN_slfv:
(n,s) ∈ slfv sl ⇔ ∃s0. MEM s0 sl ∧ (n,s) ∈ sfv s0
Proof
rw[slfv_def,Uof_def] >> metis_tac[]
QED
         
Theorem fbounds_fabs:
∀f i n s.
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
  (n,s) ∈ ffv f ∧
  (n,s) ∉ fVslfv f ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = {}) ⇒
  fbounds (fabs (n,s) i f) = {i} ∪ fbounds f 
Proof
Induct_on ‘f’ >> simp[fabs_def,fbounds_thm,fVslfv_alt] (* 4 *)
>- (simp[MEM_MAP,PULL_EXISTS] >>
   rw[] >>
   rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
   >- (Cases_on ‘(n,s') ∈ tfv y’ (* 2 *)
      >- (‘tbounds (tabs (n,s') i y) =
          {i} ∪ tbounds y’
           by (irule $ cj 1 tbounds_tabs >>
              gs[EXTENSION] >> metis_tac[])  >>
         gs[] >> metis_tac[]) >>
      metis_tac[tabs_id])
   >- metis_tac[tabs_tbounds_in]
   >- metis_tac[tbounds_tabs_SUBSET,SUBSET_DEF])
>- (rw[] (* 2 *) >> 
   gs[EXTENSION] >> metis_tac[fabs_id])
>- (rw[] (* 2 *)
   >- (‘sbounds (sabs (n,s') i s) =
      {i} ∪ sbounds s’ by metis_tac[tbounds_tabs] >>
      simp[] >>
      Cases_on ‘(n,s') ∈ ffv f’ (* 2 *)
      >- (‘fbounds (fabs (n,s') (i + 1) f) =
          {i + 1} ∪ fbounds f’ by metis_tac[] >>
         simp[] >>
         ‘IMAGE PRE ({i + 1} ∪ fbounds f DELETE 0) =
          {i} ∪ IMAGE PRE (fbounds f DELETE 0)’
          by (rw[EXTENSION,EQ_IMP_THM,GSYM arithmeticTheory.ADD1] >> simp[] (* 3 *)
          >- metis_tac[] >- (qexists ‘SUC i’ >> simp[]) >>
          metis_tac[]) >>
      gs[EXTENSION] >> metis_tac[]) >>
       ‘(fabs (n,s') (i + 1) f) = f’ by metis_tac[fabs_id] >>
       simp[UNION_ASSOC]) >>
   ‘fbounds (fabs (n,s') (i + 1) f) =
    {i + 1} ∪ fbounds f’ by metis_tac[] >> simp[] >>
   ‘IMAGE PRE ({i + 1} ∪ fbounds f DELETE 0) =
          {i} ∪ IMAGE PRE (fbounds f DELETE 0)’
          by (rw[EXTENSION,EQ_IMP_THM,GSYM arithmeticTheory.ADD1] >> simp[] (* 3 *)
          >- metis_tac[] >- (qexists ‘SUC i’ >> simp[]) >>
          metis_tac[]) >> simp[] >>
   Cases_on ‘(n,s') ∈ sfv s’ (* 2 *)
   >- (‘sbounds (sabs (n,s') i s) =
      {i} ∪ sbounds s’ by metis_tac[tbounds_tabs] >>
      gs[EXTENSION] >> metis_tac[]) >>
   ‘(sabs (n,s') i s) = s’
    by metis_tac[tabs_id] >>
   gs[EXTENSION] >> metis_tac[]) >>
simp[PULL_EXISTS,MEM_MAP] >> rw[] (* 2 *)
>- (gs[IN_slfv] >> metis_tac[]) >>
irule BIGUNION_tbounds' >> gs[] >> metis_tac[]
QED

    
Theorem ffv_fabs_fVslfv:
∀fm i n s.
       (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ∧
       (n,s) ∉ fVslfv fm ∧
       (n,s) ∈ ffv fm ⇒
       sfv s ∪ ffv (fabs (n,s) i fm) = ffv fm DELETE (n,s)
Proof
metis_tac[IN_fVslfv,ffv_fabs]
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
>- (drule_all_then assume_tac ffv_fabs_fVslfv >>
   first_x_assum (qspecl_then [‘0’] assume_tac) >>
   gs[abst_def] >> gs[EXTENSION] >>
   metis_tac[wft_wfs]) >>
metis_tac[abst_def,fabs_id]
QED


Theorem fbounds_fabs_fVslfv:
∀f i n s.
       (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ (n,s) ∈ ffv f ∧
       (n,s) ∉ fVslfv f ∧ (∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = ∅) ⇒
       fbounds (fabs (n,s) i f) = {i} ∪ fbounds f
Proof
metis_tac[fbounds_fabs,IN_fVslfv]
QED     


                
Theorem wff_fbounds:
∀f. wff Σf f ⇒ fbounds f = {}
Proof
Induct_on ‘wff’ >> rw[fbounds_thm] (* 4 *)
>- (Cases_on ‘tl’ >> simp[] >>
   disj2_tac >> rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
   >> (gs[] >> metis_tac[wft_no_bound]))
>- (Cases_on ‘tl’ >> simp[] >>
   disj2_tac >> drule_then assume_tac wfabsap_wft >>
   rw[Once EXTENSION] >> gs[] >>
   metis_tac[wft_no_bound]) >>
rw[mk_FALL_def,fbounds_thm] (* 2 *)
>- metis_tac[wft_no_bound] >>
rw[abst_def] >>
Cases_on ‘(n,s) ∈ ffv f’ (* 2 *)
>- (‘fbounds (fabs (n,s) 0 f) = {0} ∪ fbounds f’
    by (irule fbounds_fabs >>
        metis_tac[wff_wfs,wft_no_bound]) >>
   simp[EXTENSION]) >>
‘(fabs (n,s) 0 f)= f’ by metis_tac[fabs_id] >>
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


Definition substb_def:
  substb t f = frpl 0 t f
End

val substb_abst =
frpl_fabs |> Q.SPECL [‘f’,‘0’] |> SRULE [GSYM substb_def,GSYM abst_def]        

                                        
Theorem ffv_mk_FALL_fVslfv:
∀f n s.
       (∀n0 s0. (n0,s0) ∈ ffv f ⇒ (n,s) ∉ sfv s0) ∧
       (n,s) ∉ fVslfv f ⇒
       ffv (mk_FALL n s f) = ffv f ∪ sfv s DELETE (n,s)
Proof
metis_tac[ffv_mk_FALL,IN_fVslfv]
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
drule_then assume_tac ffv_mk_FALL_fVslfv >> gs[](* 2 *)
>- metis_tac[] >>
drule_then assume_tac $ cj 2 wft_tbounds >>
   CCONTR_TAC>> gs[GSYM MEMBER_NOT_EMPTY] >>
   drule_then assume_tac $ cj 2 sbounds_tbounds>>
   gs[SUBSET_DEF]
QED   

                
Theorem wff_spec:
 (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧
 wff (Σf,Σp) (FALL s ϕ) ⇒
 ∀t. wft Σf t ∧ sort_of t = s ⇒
     wff (Σf,Σp) (substb t ϕ)
Proof
 rw[] >> gs[wff_FALL] >> gs[mk_FALL_def] >>
 ‘0 ∉ fbounds f’
  by (drule_then assume_tac wff_fbounds >>
     metis_tac[MEMBER_NOT_EMPTY]) >>
 drule_then assume_tac substb_abst >>
 ‘(∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = ∅)’
  by metis_tac[wff_no_vbound] >> gs[] >>
 first_x_assum $ drule_then assume_tac >> 
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
   simp[]) >>
metis_tac[tprpl_FMAP_MAP_tabs]   
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
   ‘{tfv (shift_bmap 1 bmap ' i) |
            i |
            (∃x. i = x + 1 ∧ x ∈ FDOM bmap) ∧ i ∈ fbounds ϕ} = {tfv (bmap ' (i − 1)) |
            i |
            (∃x. i = x + 1 ∧ x ∈ FDOM bmap) ∧ i ∈ fbounds ϕ}’
     by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
        >- (qexists ‘x'’ >> simp[] >>
           drule_then assume_tac FAPPLY_shift_bmap >>
           ‘(x' + 1) = 1 + x'’ by simp[] >>
           pop_assum SUBST_ALL_TAC >> simp[tfv_tshift]) >>
        qexists ‘x'’ >> simp[] >>
         drule_then assume_tac FAPPLY_shift_bmap >>
           ‘(x' + 1) = 1 + x'’ by simp[] >>
           pop_assum SUBST_ALL_TAC >> simp[tfv_tshift]) >>
      simp[] >>
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



Theorem sfv_ffv:
∀f. (n,s) ∈ ffv f ⇒ sfv s ⊆ ffv f
Proof
rw[] >>
qspecl_then [‘f’] assume_tac ffv_is_cont >>
gs[is_cont_def] >> first_x_assum drule >> rw[]
QED





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
>- (drule_then assume_tac $ cj 2 tprpl_mk_bmap_CONS >>
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
   rw[shift_bmap_SUM]) >> rw[] >>
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


Theorem frpl_FALLL:
∀sl tm ϕ i. frpl i tm (FALLL sl ϕ) =
(FALLL (specsl i tm sl) (frpl (i + LENGTH sl) tm ϕ))
Proof
Induct_on ‘sl’ >>
gs[frpl_def,specsl_def,FALLL_def,
arithmeticTheory.ADD1]
QED        
          

Theorem finst_vmap_id:
∀f.(∀n s. (n,s) ∈ FDOM σ ∩ ffv f ⇒ σ ' (n,s) = Var n s) ⇒
finst σ f = f
Proof
Induct_on ‘f’ >> gs[ffv_thm,finst_def,MAP_fix] (* 3 *)
>- (rw[] >> irule $ cj 1 tinst_vmap_id >>
   gs[] >> metis_tac[])
>- (rw[] >> irule $ cj 2 tinst_vmap_id >>
   gs[] >> metis_tac[])  >>
rw[] (* 2 *)
>- (rw[] >> irule $ cj 2 tinst_vmap_id >>
    gs[] >> metis_tac[]) >>
rw[] >> irule $ cj 1 tinst_vmap_id >>
gs[] >> metis_tac[]
QED


Theorem finst_TO_FMAP_id:
finst (TO_FMAP [((n,s),(Var n s))]) f = f
Proof        
irule finst_vmap_id >>
rw[FDOM_TO_FMAP,TO_FMAP_MEM]
QED



Theorem fabs_frpl:
∀f i n s.
  (n,s) ∉ ffv f ⇒
  fabs (n,s) i (frpl i (Var n s) f) = f
Proof
 Induct_on ‘f’ >>
 gs[fabs_def,frpl_def,ffv_def,
    MAP_MAP_o,MEM_MAP,MAP_fix] >> rw[] (* 3 *)
 >> metis_tac[tabs_trpl]
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
first_x_assum (qspecl_then [‘(abst (n,s) f)’,‘Σp’,‘tm’] assume_tac) >> gs[] >>
rename [‘wfabsap Σf (specsl 0 tm sl) tl’] >> 
‘substb (Var n s) (FALLL sl ϕ) = substb (Var n s) (abst (n,s) f)’
  by simp[] >>
‘substb (Var n s) (abst (n,s) f) = f’
 by (drule_then assume_tac substb_abst >>
    ‘substb (Var n s) (abst (n,s) f) = finst (TO_FMAP [((n,s),(Var n s))]) f’
     by (first_x_assum irule >> rw[] (* 2 *)
        >- metis_tac[wff_no_vbound] >>
        metis_tac[wff_fbounds,MEMBER_NOT_EMPTY]) >>
    simp[] >> metis_tac[finst_TO_FMAP_id]) >>
pop_assum SUBST_ALL_TAC >>
pop_assum (assume_tac o GSYM) >>
pop_assum SUBST_ALL_TAC >>
‘abst (n,s) (substb (Var n s) (FALLL sl ϕ)) =
(FALLL sl ϕ)’
 by rw[abst_def,substb_def]  >> gs[] >> 
first_x_assum (qspecl_then [‘frpl (LENGTH sl) tm ϕ’] assume_tac) >>
‘(fprpl (mk_bmap (REVERSE tl)) (frpl (LENGTH sl) tm ϕ)) =  (fprpl (mk_bmap (REVERSE tl ⧺ [tm])) ϕ)’
by metis_tac[wft_no_bound,fprpl_mk_bmap_CONS,
   wfabsap_LENGTH,LENGTH_specsl] >>
gs[] >> first_x_assum irule >>
‘wff (Σf,Σp) (substb tm (FALLL sl ϕ))’
 by (irule wff_spec >> simp[]) >>
‘substb tm (FALLL sl ϕ) =
(FALLL (specsl 0 tm sl) (frpl (LENGTH sl) tm ϕ))’
 suffices_by metis_tac[] >>
 rw[substb_def] >>
metis_tac[frpl_FALLL,arithmeticTheory.ADD]
QED  




Theorem wff_FALLL_ffv_SUBSET:
∀sl. ffv ϕ ⊆ ffv (FALLL sl ϕ)
Proof
Induct_on ‘sl’ >> gs[FALLL_def,SUBSET_DEF,ffv_thm]
QED

Theorem wff_FALLL_no_vbound:
∀sl. wff (Σf,Σp) (FALLL sl ϕ)⇒
    (∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅)
Proof
rw[] >>
‘ffv ϕ ⊆ ffv (FALLL sl ϕ)’
 by metis_tac[wff_FALLL_ffv_SUBSET] >>
drule_then assume_tac wff_no_vbound >>
gs[SUBSET_DEF] >> metis_tac[]
QED

        
        
Definition frename_def:
frename (n,s) nn f = finst (TO_FMAP [((n,s),Var nn s)]) f
End


Theorem wff_wfcod_cvmap_ffv:
wff (Σf,Σp) f ⇒  wfcod Σf (cvmap (ffv f))
Proof
rw[wfcod_def,FAPPLY_cvmap,FDOM_cvmap,wft_def] >>
metis_tac[wff_wfs]
QED


Theorem tinst_cvmap_UPDATE:
 (∀tm vs n s.
 (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,sort_of t) ∉ sfv s1) ∧
 FINITE vs ∧tfv tm ⊆ vs ⇒
tinst (cvmap vs |+ ((n,sort_of t),t)) tm =
tinst (TO_FMAP [((n,sort_of t),t)]) tm) ∧
 (∀st vs n s.
 (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,sort_of t) ∉ sfv s1) ∧
 FINITE vs ∧ sfv st ⊆ vs ⇒
sinst (cvmap vs |+ ((n,sort_of t),t)) st =
sinst (TO_FMAP [((n,sort_of t),t)]) st)
Proof
rw[] (* 2 *)
>- (drule_then assume_tac $ cj 1 tinst_eq_cvmap >>
   simp[] >>
   irule $ cj 1 fmap_fv_inst_eq_alt >>
   rw[FDOM_cvmap,FDOM_FUPDATE,SUBSET_DEF,
   FAPPLY_FUPDATE_THM] (* 2 *)
   >- (Cases_on ‘x’ >> gs[SUBSET_DEF,FAPPLY_cvmap]) >>
   gs[SUBSET_DEF]) >>
(drule_then assume_tac $ cj 2 tinst_eq_cvmap >>
   simp[] >>
   irule $ cj 2 fmap_fv_inst_eq_alt >>
   rw[FDOM_cvmap,FDOM_FUPDATE,SUBSET_DEF,
   FAPPLY_FUPDATE_THM] (* 2 *)
   >- (Cases_on ‘x’ >> gs[SUBSET_DEF,FAPPLY_cvmap]) >>
   gs[SUBSET_DEF])
QED   

   
Theorem finst_eq_cvmap:
∀f vs.
     (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,sort_of t) ∉ sfv s1) ∧
     FINITE vs ∧ ffv f ⊆ vs⇒
     finst (TO_FMAP [((n,sort_of t),t)]) f =
     finst (cvmap vs |+ ((n,sort_of t),t)) f
Proof
Induct_on ‘f’ >>
simp[ffv_thm,finst_def,tfv_thm,
     MAP_MAP_o,MAP_EQ_f,PULL_EXISTS] (* 4 *)
>- (rw[] >> rw[Once EQ_SYM_EQ] >>
   irule $ cj 1 tinst_cvmap_UPDATE >>
   rw[tfv_FINITE,SUBSET_DEF] (* 4 *)
   >- metis_tac[] >> 
   gs[SUBSET_DEF] >> metis_tac[])
>- (rw[] (* 2 *)
   >>first_x_assum irule >> simp[] >>
      metis_tac[])
>- (rw[] (* 2 *)
   >- (rw[Once EQ_SYM_EQ] >>
      irule $ cj 2 tinst_cvmap_UPDATE >>
      simp[] >> metis_tac[]) >>
   metis_tac[]) >>
rw[] (* 2 *)
>- (rw[Once EQ_SYM_EQ] >>
      irule $ cj 2 tinst_cvmap_UPDATE >>
      simp[] >> gs[SUBSET_DEF] >>  metis_tac[]) >>
(rw[Once EQ_SYM_EQ] >>
      irule $ cj 1 tinst_cvmap_UPDATE >>
      simp[] >> gs[SUBSET_DEF] >>  metis_tac[])
QED


val frename_alt =         
finst_eq_cvmap|> GEN_ALL
|> Q.SPECL [‘Var nn s’,‘n’,‘f’,‘ffv f’]
|> SRULE [sort_of_def,GSYM frename_def]
        

Theorem wff_frename:
∀f. wff (Σf,Σp) f ∧
         (∀fsym.
            isfsym Σf fsym ⇒
            sfv (fsymout Σf fsym) ⊆
            BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧ wfs Σf s ∧
    (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒ 
    wff (Σf,Σp) (frename (n,s) nn f)
Proof
 rw[] >> drule_then assume_tac wff_finst >> gs[] >>
 first_x_assum (qspecl_then [‘(cvmap (ffv f) |+ ((n,s),Var nn s))’] assume_tac) >>
 ‘wff (Σf,Σp) (finst (cvmap (ffv f) |+ ((n,s),Var nn s)) f)’
  by
   (first_x_assum irule >>
   simp[FDOM_FUPDATE,FDOM_cvmap,SUBSET_DEF] >>
   rw[] (* 2 *)
   >- (irule cstt_FUPDATE >> rw[is_bound_def,sort_of_def] >>
      metis_tac[]) >>
   irule FUPDATE_wfcod >> simp[wft_def] >>
   metis_tac[wff_wfcod_cvmap_ffv]) >>
 rw[frename_def] >>
 ‘ffv f ⊆ ffv f’ by simp[] >>
 drule_at_then Any assume_tac finst_eq_cvmap >>
 first_x_assum (qspecl_then [‘Var nn s’,‘n’] assume_tac) >>
 gs[sort_of_def,ffv_FINITE] >>
 first_x_assum $ drule_then assume_tac >> gs[]
QED

Definition trename_def:
trename (n,s) nn = tinst (TO_FMAP [((n,s),Var nn s)])
End



Definition srename_def:
srename (n,s) nn = sinst (TO_FMAP [((n,s),Var nn s)])
End
        
Theorem tabs_trename:
(∀tm.
   (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
   (nn,s) ∉ tfv tm ⇒
   tabs (n,s) i tm =
   tabs (nn,s) i (trename (n,s) nn tm)) ∧
(∀st.
   (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
   (nn,s) ∉ sfv st ⇒
   sabs (n,s) i st =
   sabs (nn,s) i (srename (n,s) nn st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tabs_def,tfv_thm,trename_def,srename_def,
tinst_def,MAP_MAP_o,MAP_EQ_f,PULL_EXISTS,FDOM_TO_FMAP] >>
rw[] (* 4 *)
>- (Cases_on ‘n = s0 ∧ s = st’ >> simp[] (* 2 *)
   >- (‘(TO_FMAP [((s0,st),Var nn st)] ' (s0,st)) =
       Var nn st’ by (irule TO_FMAP_MEM >> simp[]) >>
      simp[tabs_def]) >>
   ‘ s0 = n ⇒ st ≠ s’ by metis_tac[] >> simp[] >>
   ‘(sinst (TO_FMAP [((n,s),Var nn s)]) st) = st’
    by (irule $ cj 2 tinst_vmap_id >> rw[FDOM_TO_FMAP] >>
    irule TO_FMAP_MEM >> simp[] >> metis_tac[]) >>
   simp[] >> rw[tabs_def])
>> (first_x_assum irule >> metis_tac[])
QED

val tabs_trename' = tabs_trename |> SRULE [trename_def,srename_def]        

Theorem abssl_MAP_srename:
∀l i.
     (∀n1 s1 st. MEM st l ∧ (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧ (∀st. MEM st l ⇒ (nn,s) ∉ sfv st) ⇒
      abssl (n,s) i l =
      abssl (nn,s) i
            (MAP (srename (n,s) nn) l)
Proof
Induct_on ‘l’ >> simp[abssl_def,tfv_thm,srename_def] >> rw[]
(* 2 *)
>- (irule $ cj 2 tabs_trename' >>
   simp[] >> metis_tac[]) >>
gs[srename_def] >>   
first_x_assum irule >> metis_tac[]
QED   
        

Theorem trename_fix:
(∀tm n s nn. (n,s) ∉ tfv tm ⇒ trename (n,s) nn tm = tm) ∧
(∀st n s nn. (n,s) ∉ sfv st ⇒ srename (n,s) nn st = st)
Proof
rw[trename_def,srename_def] (* 2 *)
>- (irule $ cj 1 tinst_vmap_id  >>
   rw[FDOM_TO_FMAP] >> metis_tac[]) >>
(irule $ cj 2 tinst_vmap_id  >>
   rw[FDOM_TO_FMAP] >> metis_tac[])
QED








   
Theorem TO_FMAP_SING:
(TO_FMAP [(a,b)]) ' a = b
Proof
irule TO_FMAP_MEM >> simp[]
QED



Theorem tbounds_trename:
(∀tm n s nn.
tbounds (trename (n,s) nn tm) = tbounds tm) ∧
(∀st n s nn.
sbounds (srename (n,s) nn st) = sbounds st)
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 4 *)
>- (rw[trename_def,tinst_def] >> rw[tbounds_thm] >>
   gs[srename_def] >> gs[FDOM_TO_FMAP] >>
   rw[TO_FMAP_SING,tbounds_thm])
>- (rw[trename_def,tinst_def,SF ETA_ss] >>
   rw[tbounds_thm,MEM_MAP] >>
   gs[srename_def]>>
   ‘{tbounds t |
           (∃y. t = tinst (TO_FMAP [((n,s),Var nn s)]) y ∧ MEM y l)} = {tbounds t | MEM t l}’
     by (rw[Once EXTENSION]  >> rw[GSYM trename_def] >>
        metis_tac[]) >> simp[])
>- rw[trename_def,tinst_def] >>
rw[srename_def,tinst_def,SF ETA_ss,tbounds_thm,MEM_MAP] >>
AP_TERM_TAC >>
rw[Once EXTENSION]  >> rw[GSYM trename_def] >>
metis_tac[]
QED    
   
Theorem ok_abs_rename:
ok_abs (MAP (srename (n,s) nn) l) ⇔ ok_abs l
Proof
rw[ok_abs_def,EL_MAP,tbounds_trename]
QED

Theorem tfv_trename:
(∀tm n s nn.
  (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
  (n,s) ∈ tfv tm ⇒
  tfv (trename (n,s) nn tm) =
  tfv tm DELETE (n,s) ∪ {(nn,s)}) ∧
(∀st n s nn.
  (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
  (n,s) ∈ sfv st ⇒
  sfv (srename (n,s) nn st) =
  sfv st DELETE (n,s) ∪ {(nn,s)})
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 5 *)
>- (rw[trename_def,tinst_def,FDOM_TO_FMAP,TO_FMAP_SING] >>
   rw[EXTENSION] >> metis_tac[])
>- metis_tac[] (*(n,s) ∈ sfv st contradicts assum*)
>- (rw[trename_def,tinst_def,FDOM_TO_FMAP,TO_FMAP_SING,
      MEM_MAP] >>
   ‘BIGUNION {tfv t' | (∃a. t' = tinst (TO_FMAP [((n,s),Var nn s)]) a ∧ MEM a l)} = BIGUNION {tfv t | MEM t l} DELETE (n,s) ∪ {(nn,s)}’
    by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 2 *)
       >- (fs[GSYM trename_def] >>
          Cases_on ‘(n,s) ∈ tfv a’ (* 2 *)
          >- (‘tfv (trename (n,s) nn a) =
              tfv a DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[])
       >- (fs[GSYM trename_def] >>
          Cases_on ‘(n,s) ∈ tfv t'’ (* 2 *)
          >- (‘tfv (trename (n,s) nn t') =
              tfv t' DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[EXTENSION] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[]) >>
       fs[GSYM trename_def] >>
       Cases_on ‘(n,s) ∈ tfv t’ (* 2 *)
          >- (‘tfv (trename (n,s) nn t) =
              tfv t DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[EXTENSION] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[]) >>
   simp[] >> rw[GSYM srename_def] >>
   Cases_on ‘(n,s) ∈ sfv st’ (* 2 *)
   >- (‘sfv (srename (n,s) nn st) = sfv st DELETE (n,s) ∪ {(nn,s)}’ by metis_tac[] >> gs[EXTENSION] >> metis_tac[]) >>
   drule_then assume_tac $ cj 2 trename_fix >>
   simp[] >>  gs[EXTENSION] >> metis_tac[])
>- (rw[trename_def,tinst_def,FDOM_TO_FMAP,TO_FMAP_SING,
      MEM_MAP] >> rw[GSYM srename_def] >>
   ‘sfv (srename (n,s) nn st) = sfv st DELETE (n,s) ∪ {(nn,s)}’ by metis_tac[] >> simp[] >>
   Cases_on ‘∃t. (n,s) ∈ tfv t ∧ MEM t l’ >> gs[]
   >- (‘BIGUNION {tfv t' | (∃a. t' = tinst (TO_FMAP [((n,s),Var nn s)]) a ∧ MEM a l)} = BIGUNION {tfv t | MEM t l} DELETE (n,s) ∪ {(nn,s)}’
    by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
       >- (fs[GSYM trename_def] >>
          Cases_on ‘(n,s) ∈ tfv a’ (* 2 *)
          >- (‘tfv (trename (n,s) nn a) =
              tfv a DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[])
       >- (fs[GSYM trename_def] >>
          Cases_on ‘(n,s) ∈ tfv t'’ (* 2 *)
          >- (‘tfv (trename (n,s) nn t') =
              tfv t' DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[EXTENSION] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[]) >>
       fs[GSYM trename_def] >>
       Cases_on ‘(n,s) ∈ tfv t’ (* 2 *)
          >- (‘tfv (trename (n,s) nn t) =
              tfv t DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[EXTENSION] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[]) >>
   simp[] >> gs[EXTENSION] >> metis_tac[]) >>
   ‘{tfv t | (∃a. t = tinst (TO_FMAP [((n,s),Var nn s)]) a ∧ MEM a l)} = {tfv t | MEM t l}’
    by (rw[Once EXTENSION,GSYM trename_def] >>
       metis_tac[trename_fix]) >>
    gs[EXTENSION] >> metis_tac[]) >>
rw[srename_def,tfv_thm,MEM_MAP] >>      
(rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
       >- (fs[GSYM trename_def] >>
          Cases_on ‘(n,s) ∈ tfv a’ (* 2 *)
          >- (‘tfv (trename (n,s) nn a) =
              tfv a DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[])
       >- (fs[GSYM trename_def] >>
          Cases_on ‘(n,s) ∈ tfv t'’ (* 2 *)
          >- (‘tfv (trename (n,s) nn t') =
              tfv t' DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[EXTENSION] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[]) >>
       fs[GSYM trename_def] >>
       Cases_on ‘(n,s) ∈ tfv t’ (* 2 *)
          >- (‘tfv (trename (n,s) nn t) =
              tfv t DELETE (n,s) ∪ {(nn,s)}’
             by metis_tac[] >> gs[EXTENSION] >> metis_tac[]) >>
          drule_then assume_tac $ cj 1 trename_fix >>
          metis_tac[])
QED

Theorem trename_alt:
(trename (n,s) nn (Var n0 s0) =
if n0 = n ∧ s0 = s then Var nn s else
Var n0 (srename (n,s) nn s0)) ∧
trename (n,s) nn (Fn f st tl) =
Fn f (srename (n,s) nn st)
(MAP (trename (n,s) nn) tl) ∧
trename (n,s) nn (Bound i) = Bound i ∧
srename (n,s) nn (St sn tl) =
St sn (MAP (trename (n,s) nn) tl)
Proof
rw[trename_def,srename_def,tinst_def,FDOM_TO_FMAP,
   SF ETA_ss,TO_FMAP_SING] >> metis_tac[]
QED


Definition rnmap_def:
rnmap (n,s) nn vs =
FUN_FMAP (λ(n1,s1). trename (n,s) nn (Var n1 s1)) vs
End

Theorem FDOM_rnmap:
∀vs. FINITE vs ⇒ FDOM (rnmap (n,s) nn vs) = vs
Proof
rw[rnmap_def,FUN_FMAP_DEF]
QED


Theorem FAPPLY_rnmap:
∀vs n1 s1. FINITE vs ∧ (n1,s1) ∈ vs ⇒ (rnmap (n,s) nn vs) ' (n1,s1) =
trename (n,s) nn (Var n1 s1)
Proof
rw[rnmap_def,FUN_FMAP_DEF]
QED

                
Theorem trename_tinst:
(∀tm n s nn vs.
FINITE vs ∧ tfv tm ⊆ vs ⇒
trename (n,s) nn tm = tinst (rnmap (n,s) nn vs) tm) ∧
(∀st n s nn vs.
FINITE vs ∧ sfv st ⊆ vs ⇒
srename (n,s) nn st = sinst (rnmap (n,s) nn vs) st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,tinst_def,trename_alt,FDOM_rnmap,FAPPLY_rnmap,
   SF ETA_ss,MAP_EQ_f] >>
rw[] (* 2 *)
>> first_x_assum irule >> gs[SUBSET_DEF] >>
   metis_tac[]
QED
        
    
Theorem fabs_frename:
 ∀f i.
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
  (nn,s) ∉ ffv f ∧
  (n,s) ∉ fVslfv f ⇒
  fabs (n,s) i f = fabs (nn,s) i (frename (n,s) nn f)
Proof
 Induct_on ‘f’ >> gs[frename_def,fabs_def,
  MAP_MAP_o,MAP_EQ_f,PULL_EXISTS,fVslfv_alt] (* 4 *)
 >- (rw[] >> irule $ cj 1 tabs_trename' >>
    metis_tac[])
 >- metis_tac[]
 >- (rw[] (* 2 *)
    >- (irule $ cj 2 tabs_trename' >>
       metis_tac[]) >> metis_tac[]) >>
 rw[] (* 2 *)
 >- (rw[Once EQ_SYM_EQ] >>
    rw[MAP_fix]>>
    rw[GSYM tsubst_eq_tinst] >>
    irule $ cj 2 tsubst_id >>
    gs[IN_slfv] >> metis_tac[])>>
 irule $ cj 1 tabs_trename' >>
 metis_tac[]
QED         

 


Theorem ffv_frename:
∀f. (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = {}) ∧
(∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
(nn,s) ∉ ffv f ∧ (n,s) ∈ ffv f ⇒
ffv (frename (n,s) nn f) = ffv f DELETE (n,s) ∪ {(nn,s)}
Proof
rw[] >>
drule_then assume_tac frename_alt >> simp[] >>
‘cstt (cvmap (ffv f) |+ ((n,s),Var nn s)) ∧
 ffv f ⊆ FDOM (cvmap (ffv f) |+ ((n,s),Var nn s)) ∧
 no_bound (cvmap (ffv f) |+ ((n,s),Var nn s))’
 by (rw[] (* 3 *)
    >- (irule cstt_FUPDATE >> rw[] (* 3 *)
       >- metis_tac[] >- gs[is_bound_alt,wft_def] >>
       rw[sort_of_def])
    >- (‘FINITE (ffv f)’ by simp[] >>
        drule_then assume_tac FDOM_cvmap >>
        simp[SUBSET_DEF]) >>
    irule no_bound_FUPDATE >> gs[no_bound_def,tbounds_thm]>>
    rw[] (* 2 *)>-
    (‘FINITE (ffv f)’ by simp[] >> 
    drule_then assume_tac FDOM_cvmap >> Cases_on ‘x’ >>
    drule_then assume_tac FAPPLY_cvmap >>
    first_x_assum (qspecl_then [‘r’,‘q’] assume_tac) >>
    gs[tbounds_thm] >> metis_tac[]) >>
    metis_tac[]) >>
drule_all_then assume_tac ffv_finst >>
rw[Once EXTENSION] >> Cases_on ‘x’ >> simp[] >>
rw[EQ_IMP_THM] (* 3 *)
>- (Cases_on ‘(n0,st0) = (n,s)’ (* 2 *)
   >- (gs[] >> disj1_tac >> rw[] (*2 *) 
      >- (qspecl_then [‘f’] assume_tac ffv_is_cont >>
      gs[is_cont_def] >>
      first_x_assum (qspecl_then [‘n’,‘s’] assume_tac) >>
      gs[SUBSET_DEF]) >>
      metis_tac[tm_tree_WF]) >>
   gs[FAPPLY_FUPDATE_THM] >>
   ‘(cvmap (ffv f) ' (n0,st0)) = Var n0 st0’
    by metis_tac[ffv_FINITE,FAPPLY_cvmap] >> gs[] >>
   disj1_tac >> rw[] (* 2 *) 
   >- (qspecl_then [‘f’] assume_tac ffv_is_cont >>
      gs[is_cont_def] >>
      first_x_assum (qspecl_then [‘n0’,‘st0’] assume_tac) >>
      gs[SUBSET_DEF]) >>
   metis_tac[]) 
>- (qexistsl [‘q’,‘r’] >> simp[FAPPLY_FUPDATE_THM] >> simp[] >>
‘¬(q = n ∧ r = s)’ by metis_tac[] >> simp[] >>
drule_at_then Any assume_tac FAPPLY_cvmap >> gs[]) >>
qexistsl [‘n’,‘r’] >> simp[FAPPLY_FUPDATE_THM]
QED
   

Theorem trename_tprpl:
(∀tm l0 n s nn bmap.
 trename (n,s) nn (tprpl bmap tm) =
 tprpl (FMAP_MAP (trename (n,s) nn) bmap)
       (trename (n,s) nn tm)) ∧
(∀st l0 n s nn bmap.
 srename (n,s) nn (sprpl bmap st) =
 sprpl (FMAP_MAP (trename (n,s) nn) bmap)
       (srename (n,s) nn st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[trename_def,srename_def,tinst_def,tprpl_def,
   MAP_MAP_o,MAP_EQ_f,FDOM_TO_FMAP,FDOM_FMAP_MAP] >>
rw[] (* 2 *)
>- (Cases_on ‘s0 = n ⇒ st ≠ s’ >> simp[] (* 2 *)
   >- rw[tprpl_def] >>
   ‘(s0,s) = (n,st)’ by (simp[] >> metis_tac[]) >>
   ‘(TO_FMAP [((n,s),Var nn s)] ' (n,s)) =
    Var nn s’ by (irule TO_FMAP_MEM >> simp[]) >>
   gs[tprpl_def]) >>
rw[FMAP_MAP_DEF,FUN_FMAP_DEF]
QED   



Theorem trename_tshift:
(∀tm i n s nn.
trename (n,s) nn (tshift i tm) =
        tshift i (trename (n,s) nn tm)) ∧
(∀st i n s nn.
srename (n,s) nn (sshift i st) =
        sshift i (srename (n,s) nn st)) 
Proof
ho_match_mp_tac better_tm_induction >>
gs[trename_def,tinst_def,tshift_def,MAP_MAP_o,MAP_EQ_f,
   SF ETA_ss,FDOM_TO_FMAP] >> gs[GSYM trename_def,GSYM srename_def] >> rw[] (* 2 *)
>- (Cases_on ‘s0 = n ⇒ st ≠ s ’ >> simp[] (* 2 *)   
   >- rw[tshift_def] >>
   ‘TO_FMAP [((n,s),Var nn s)] ' (n,s) = Var nn s’
    by (irule TO_FMAP_MEM >> simp[]) >>
   simp[tshift_def]) >>
rw[srename_def] >> rw[SF ETA_ss] >> rw[GSYM trename_def] >>
rw[tshift_def,MAP_MAP_o,SF ETA_ss,MAP_EQ_f]   
QED


                      
Theorem trename_shift_bmap:
  FMAP_MAP (trename (n,s) nn) (shift_bmap i bmap) =
  shift_bmap i (FMAP_MAP (trename (n,s) nn) bmap)
Proof
rw[fmap_EXT,FDOM_FMAP_MAP,FDOM_shift_bmap] >>
‘i + x' ∈ FDOM (shift_bmap i bmap)’ by gs[FDOM_shift_bmap] >>
gs[FAPPLY_FMAP_MAP] >>
rev_drule_then assume_tac FAPPLY_shift_bmap >> simp[] >>
‘x' ∈ FDOM (FMAP_MAP (trename (n,s) nn) bmap)’
 by simp[FDOM_FMAP_MAP] >>
drule_then assume_tac FAPPLY_shift_bmap >> simp[] >>
gs[FAPPLY_FMAP_MAP] >>
metis_tac[trename_tshift]
QED

        
Theorem slprpl_trename:
∀l n s nn bmap.
MAP (srename (n,s) nn) (slprpl bmap l) =
   slprpl (FMAP_MAP (trename (n,s) nn) bmap) (MAP (srename (n,s) nn) l)
Proof
Induct_on ‘l’ >> simp[slprpl_def] >> rw[] (* 2 *)
>- metis_tac[trename_tprpl] >>
‘(FMAP_MAP (trename (n,s) nn) (shift_bmap 1 bmap)) =
(shift_bmap 1 (FMAP_MAP (trename (n,s) nn) bmap))’
suffices_by metis_tac[] >> metis_tac[trename_shift_bmap]
QED


(*here*)        
        
Theorem frename_fprpl:
∀ϕ l0 n s nn bmap. frename (n,s) nn (fprpl bmap ϕ) =
        fprpl
          (FMAP_MAP (trename (n,s) nn) bmap)
          (frename (n,s) nn ϕ)
Proof
Induct_on ‘ϕ’ >>
gs[frename_def,fprpl_def,finst_def,MAP_MAP_o,MAP_EQ_f] (* 5 *) >> rw[] >> gs[GSYM trename_def,GSYM srename_def,GSYM frename_def]
>- metis_tac[trename_tprpl]
>- metis_tac[trename_tprpl]
>- (‘(shift_bmap 1 (FMAP_MAP (trename (n,s') nn) bmap)) =
     (FMAP_MAP (trename (n,s') nn) (shift_bmap 1 bmap))’
   suffices_by metis_tac[] >> metis_tac[trename_shift_bmap]) >> 
metis_tac[trename_tprpl]
QED



Theorem no_subrename:
∀n0 s0. (n0,s0) ∈ sfv s ⇒ trename (n,s) nn (Var n0 s0) = Var n0 s0
Proof
rw[] >> irule $ cj 1 trename_fix >> rw[tfv_thm] (* 2 *)
>- metis_tac[tm_tree_WF] >>
CCONTR_TAC >> metis_tac[vsort_tfv_closed,tm_tree_WF]
QED

Theorem cstt_rnmap:
∀vs. FINITE vs ∧ is_cont vs ⇒ cstt (rnmap (n,s) nn vs)
Proof
  rw[cstt_def,FDOM_rnmap,FAPPLY_rnmap,trename_alt] >>
  Cases_on ‘n' = n ∧ s' = s’ >> simp[sort_of_def] (* 2 *)
  >- (rw[Once EQ_SYM_EQ] >>
      irule $ cj 2 tinst_vmap_id >>
      rw[FDOM_rnmap,FAPPLY_rnmap,no_subrename]) >>
  irule $ cj 2 trename_tinst >> gs[is_cont_def] >>
  metis_tac[]
QED  



Theorem BIGUNION_is_cont:
(∀s. s ∈ ss ⇒ is_cont s) ⇒ is_cont (BIGUNION ss)
Proof
rw[is_cont_def]>> rw[SUBSET_DEF] >>
metis_tac[SUBSET_DEF]
QED

Theorem trename_tinst_tfv:
(∀tm.trename (n,s) nn tm = tinst (rnmap (n,s) nn (tfv tm)) tm) ∧
(∀st.srename (n,s) nn st = sinst (rnmap (n,s) nn (sfv st)) st)
Proof
rw[] (* 2 *)
>- (irule $ cj 1 trename_tinst >> simp[]) >>
irule $ cj 2 trename_tinst >> simp[]
QED


Theorem FAPPLY_rnmap_SUBSET:
FINITE vs ∧ ss ⊆ vs ⇒
∀n1 s1. (n1,s1) ∈ ss ⇒
rnmap (n,s) nn ss ' (n1,s1) = rnmap (n,s) nn vs ' (n1,s1)
Proof
rw[] >> ‘FINITE ss’ by (irule SUBSET_FINITE >> metis_tac[])>>
rw[FDOM_rnmap,FAPPLY_rnmap] >>
gs[SUBSET_DEF] >> first_x_assum $ drule_then assume_tac >>
rw[FDOM_rnmap,FAPPLY_rnmap]
QED


Theorem wfcod_rnmap_SUBSET:
FINITE vs ∧ wfcod Σf (rnmap (n,s) nn vs) ⇒
∀ss. ss ⊆ vs ⇒ wfcod Σf (rnmap (n,s) nn ss)
Proof
rw[wfcod_def] >> gs[FDOM_rnmap] >>
‘FINITE ss’ by (irule SUBSET_FINITE >> metis_tac[]) >>
gs[FDOM_rnmap] >>
‘(n',s') ∈ vs’ by metis_tac[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >>
‘(rnmap (n,s) nn vs ' (n',s')) = rnmap (n,s) nn ss ' (n',s')’
suffices_by metis_tac[] >>
rw[Once EQ_SYM_EQ] >>
irule $ FAPPLY_rnmap_SUBSET >> simp[]
QED


Theorem wfcod_rnmap_BIGUNION:
(∀vs. vs ∈ ss ⇒ wfcod Σf (rnmap (n,s) nn vs)) ∧
FINITE (BIGUNION ss) ⇒
wfcod Σf (rnmap (n,s) nn (BIGUNION ss))
Proof
rw[wfcod_def] >>
gs[FDOM_rnmap] >>
‘(rnmap (n,s) nn (BIGUNION ss) ' (n',s')) =
 (rnmap (n,s) nn  s'' ' (n',s'))’
 by (rw[Once EQ_SYM_EQ] >>
    irule FAPPLY_rnmap_SUBSET >>
    simp[SUBSET_DEF] >> metis_tac[]) >>
simp[]
QED


Theorem FINITE_lemma:
FINITE {f t | MEM t l}
Proof
‘{f t | MEM t l} = IMAGE f {t | MEM t l}’ suffices_by simp[] >> simp[EXTENSION]
QED

Theorem wft_trename0:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
(∀tm. wft Σf tm ⇒
      ∀n s ss. wft Σf (trename (n,s) nn tm) ∧
               wfcod Σf (rnmap (n,s) nn (tfv tm))) ∧
∀st. wfs Σf st ⇒
     ∀n s ss. wfs Σf (srename (n,s) nn st) ∧
              wfcod Σf (rnmap (n,s) nn (sfv st))
Proof
strip_tac >> 
ho_match_mp_tac better_tm_induction >> rw[] (* 8 *)
>- (gs[wft_def,trename_alt] >>
   Cases_on ‘s0 = n ∧ st = s’ >> simp[] (* 2 *)
   >> gs[wft_def])
>- (rw[wfcod_def] >>
   gs[FDOM_rnmap,FAPPLY_rnmap,wft_def,trename_alt] (* 2 *)
   >- (Cases_on ‘s0 = n ∧ st = s’ >> simp[] (* 2 *)
      >> gs[wft_def]) >>
   Cases_on ‘n' = n ∧ s' = s’ >> simp[]  (* 2 *)
   >- (gs[wft_def] >> metis_tac[wft_wfs]) >>
   ‘srename (n,s) nn s' =
    sinst (rnmap (n,s) nn (sfv st)) s'’
    by (irule $ cj 2 trename_tinst >>
       simp[] >> metis_tac[tfv_is_cont,is_cont_def]) >>
   simp[] >> rw[wft_def] >>
   irule $ cj 2 wft_tinst  >> simp[] >>
   rw[] (* 3 *)
   >- (irule cstt_rnmap >> simp[tfv_is_cont])
   >- (rw[FDOM_rnmap] >> metis_tac[tfv_is_cont,is_cont_def])
   >> metis_tac[wft_wfs])
>- (‘trename (n,s) nn (Fn s0 st l) =
    tinst (rnmap (n,s) nn (tfv (Fn s0 st l))) (Fn s0 st l)’
    by (irule $ cj 1 trename_tinst >> simp[]) >>
   pop_assum SUBST_ALL_TAC >>
   irule $ cj 1 wft_tinst >> simp[FDOM_rnmap] >>
   rw[] (* 2 *)
   >- (irule cstt_rnmap >> rw[] (* 3 *)
      >- (‘{tfv t | MEM t l} = IMAGE tfv {t | MEM t l}’
         suffices_by simp[] >> simp[EXTENSION])
      >- simp[] >>
      irule UNION_is_cont >> simp[tfv_is_cont] >>
      irule BIGUNION_is_cont >> gs[tfv_is_cont] >>
      metis_tac[tfv_is_cont]) >>
   ‘FINITE (BIGUNION {tfv t | MEM t l} ∪ sfv st)’
    by (simp[] >> rw[] (* 2 *)
       >- simp[FINITE_lemma] >> simp[tfv_FINITE]) >>
   ‘(BIGUNION {tfv t | MEM t l} ∪ sfv st) =
    BIGUNION {vs | (∃t. MEM t l ∧ vs = tfv t) ∨ vs = sfv st}’
    by (simp[Once EXTENSION] >> metis_tac[]) >>
   simp[] >> irule wfcod_rnmap_BIGUNION >>
   rw[tfv_FINITE] (* 5 *)
   >- gs[wft_def]
   >- gs[wft_def]
   >- (‘{vs | (∃t. MEM t l ∧ vs = tfv t) ∨ vs = sfv st} =
       {tfv t | MEM t l} ∪ {sfv st}’
       by (rw[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘{tfv t | MEM t l} = IMAGE tfv {t | MEM t l}’
       suffices_by simp[] >>
      rw[Once EXTENSION])
   >- rw[tfv_FINITE]
   >- rw[tfv_FINITE])
>- (‘FINITE (BIGUNION {tfv t | MEM t l} ∪ sfv st)’
    by (simp[] >> rw[] (* 2 *)
       >- simp[FINITE_lemma] >> simp[tfv_FINITE]) >>
   ‘(BIGUNION {tfv t | MEM t l} ∪ sfv st) =
    BIGUNION {vs | (∃t. MEM t l ∧ vs = tfv t) ∨ vs = sfv st}’
    by (simp[Once EXTENSION] >> metis_tac[]) >>
   simp[] >> irule wfcod_rnmap_BIGUNION >>
   rw[tfv_FINITE] (* 5 *)
   >- gs[wft_def]
   >- gs[wft_def]
   >- (‘{vs | (∃t. MEM t l ∧ vs = tfv t) ∨ vs = sfv st} =
       {tfv t | MEM t l} ∪ {sfv st}’
       by (rw[EXTENSION] >> metis_tac[]) >>
      simp[] >>
      ‘{tfv t | MEM t l} = IMAGE tfv {t | MEM t l}’
       suffices_by simp[] >>
      rw[Once EXTENSION])
   >- rw[tfv_FINITE] >>
   rw[tfv_FINITE])
>- rw[trename_alt]
>- rw[wfcod_def,FDOM_rnmap]
>- (gs[wft_def,EVERY_MEM] >> simp[trename_alt] >>
   rw[wft_def,MEM_MAP,EVERY_MEM]   >>
   metis_tac[]) >>
irule wfcod_rnmap_BIGUNION >>
simp[FINITE_lemma] >> rw[] (* 2 *)
>- gs[wft_def,EVERY_MEM] >>
rw[tfv_FINITE]
QED
       
Theorem frename_alt:
frename (n,s) nn False = False ∧
frename (n,s) nn (IMP f1 f2) =
IMP (frename (n,s) nn f1) (frename (n,s) nn f2) ∧
frename (n,s) nn (fVar p sl tl) =
fVar p (MAP (srename (n,s) nn) sl)
     (MAP (trename (n,s) nn) tl) ∧
frename (n,s) nn (Pred p tl) =
Pred p (MAP (trename (n,s) nn) tl) ∧
frename (n,s) nn (FALL st f) =
FALL (srename (n,s) nn st) (frename (n,s) nn f)
Proof
  rw[frename_def,srename_def,trename_def,finst_def,tinst_def]
QED

Theorem frename_finst:
∀f n s nn vs.
  FINITE vs ∧ ffv f ⊆ vs ⇒
  frename (n,s) nn f = finst (rnmap (n,s) nn vs) f       
Proof
Induct_on ‘f’ (* 5 *)
>- simp[frename_alt,finst_def]
>- (simp[ffv_thm,frename_alt,finst_def,MAP_EQ_f] >>
   rw[] >> irule $ cj 1 trename_tinst >>
   gs[SUBSET_DEF] >> metis_tac[])
>- rw[ffv_thm,frename_alt,finst_def]
>- (rw[ffv_thm,frename_alt,finst_def] >>
   irule $ cj 2 trename_tinst >> simp[]) >>
simp[ffv_thm,frename_alt,finst_def,MAP_EQ_f] >>
rw[] (* 2 *)
>- (irule $ cj 2 trename_tinst >> gs[SUBSET_DEF] >>
    metis_tac[]) >>
irule $ cj 1 trename_tinst >> gs[SUBSET_DEF] >>
metis_tac[]
QED 

Theorem frename_finst_ffv:
frename (n,s) nn f = finst (rnmap (n,s) nn (ffv f)) f
Proof
irule frename_finst >> simp[]
QED

Definition gcont_def:
gcont vs = vs ∪ BIGUNION {sfv s | ∃n.(n,s) ∈ vs}
End

Theorem gcont_is_cont:
∀vs. is_cont (gcont vs)
Proof
rw[is_cont_def,gcont_def] >>
rw[SUBSET_DEF] >> metis_tac[vsort_tfv_closed]
QED


Theorem gcont_of_cont:
∀ct. is_cont ct ⇒ gcont ct = ct
Proof
rw[gcont_def,is_cont_def] >>
rw[Once EXTENSION,PULL_EXISTS] >>
gs[SUBSET_DEF] >> metis_tac[vsort_tfv_closed]
QED
        

Theorem gcont_FINITE:
∀vs. FINITE vs ⇒ FINITE (gcont vs)
Proof
Induct_on ‘FINITE’ >>
rw[gcont_def] (* 3 *) >> simp[tfv_FINITE] >>
‘{sfv s | (∃n. (n,s) = e ∨ (n,s) ∈ vs)} =
 IMAGE (sfv o SND) (e INSERT vs)’ suffices_by simp[] >>
rw[Once EXTENSION] >> rw[EQ_IMP_THM] (* 4 *)
>- (qexists_tac ‘(n,s)’ >> simp[])
>- (qexists_tac ‘(n,s)’ >> simp[])
>- (qexists_tac ‘SND e’ >> simp[] >>
   qexists_tac ‘FST e’ >> simp[]) >>
rw[PULL_EXISTS] >> qexistsl [‘SND x'’,‘FST x'’] >>
simp[]
QED   

Theorem gcont_EMPTY:
gcont {} = {}
Proof
rw[gcont_def,EXTENSION]
QED

Theorem gcont_UNION:
gcont (A ∪ B) = gcont A ∪ gcont B
Proof
rw[gcont_def,Once EXTENSION] >> metis_tac[]
QED


Theorem gcont_SING:
gcont {(n,s)} = tfv (Var n s)
Proof
rw[tfv_thm,gcont_def] >> rw[EXTENSION] >>
metis_tac[]
QED 
        

Theorem wfcod_rnmap_tfv:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
     (∀tm.
        wft Σf tm ⇒
        ∀n s ss. wfcod Σf (rnmap (n,s) nn (tfv tm))) ∧
     ∀st.
       wfs Σf st ⇒
       ∀n s ss. wfcod Σf (rnmap (n,s) nn (sfv st))
Proof
metis_tac[wft_trename0]
QED



Theorem wft_trename:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
     (∀tm.
        wft Σf tm ⇒
        ∀n s ss.
          wft Σf (trename (n,s) nn tm)) ∧
     ∀st.
       wfs Σf st ⇒
       ∀n s ss.
         wfs Σf (srename (n,s) nn st)
Proof
metis_tac[wft_trename0]
QED
                
Theorem wfcod_rnmap_gcont:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
∀vs. FINITE vs ⇒ 
     (∀n1 s1. (n1,s1) ∈ vs ⇒ wfs Σf s1) ⇒
     wfcod Σf (rnmap (n,s) nn (gcont vs))
Proof
strip_tac >>
Induct_on ‘FINITE’ >> rw[is_cont_def] (* 2 *)
>- rw[FDOM_rnmap,wfcod_def,gcont_EMPTY] >>
‘wfcod Σf (rnmap (n,s) nn (gcont vs))’
 by metis_tac[] >>
simp[Once INSERT_SING_UNION] >>
simp[gcont_UNION] >>
‘(gcont {e} ∪ gcont vs) = BIGUNION {gcont {e} ; gcont vs}’
 by simp[] >>
pop_assum SUBST_ALL_TAC >>  
irule wfcod_rnmap_BIGUNION >> simp[] >>
rw[] >> simp[gcont_FINITE] >>
Cases_on ‘e’ >> rw[gcont_SING] >>
‘({(q,r)} ∪ sfv r) = tfv (Var q r)’ by simp[tfv_thm] >>
pop_assum SUBST_ALL_TAC >>
irule $ cj 1 wfcod_rnmap_tfv >>
simp[] >> rw[wft_def]
QED


      
Theorem wfcod_rnmap_cont:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒ 
∀vs. FINITE vs ⇒ is_cont vs ⇒
     (∀n1 s1. (n1,s1) ∈ vs ⇒ wfs Σf s1) ⇒
     wfcod Σf (rnmap (n,s) nn vs)
Proof
rw[] >> drule_at_then Any assume_tac wfcod_rnmap_gcont >>
gs[] >>
metis_tac[gcont_of_cont]
QED

Theorem wfcod_rnmap_ffv:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
     (∀f. wff (Σf,Σp) f ⇒ ∀n s ss. wfcod Σf (rnmap (n,s) nn (ffv f)))
Proof
rw[] >> irule wfcod_rnmap_cont >>
simp[ffv_is_cont] >> metis_tac[wff_wfs]
QED


Theorem FINITE_BIGUNION_tfv:
FINITE (BIGUNION {tfv t | MEM t tl})
Proof
simp[FINITE_lemma] >> metis_tac[tfv_FINITE]
QED
         
Theorem wff_frename:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
∀f. wff (Σf,Σp) f ⇒
    ∀n s nn. wff (Σf,Σp) (frename (n,s) nn f)
Proof
strip_tac >> Induct_on ‘wff’ >>
rw[] (* 5 *)
>- rw[frename_alt,wff_rules]
>- (‘(frename (n,s) nn (Pred p tl)) =
    finst (rnmap (n,s) nn (ffv (Pred p tl))) (Pred p tl)’
    by metis_tac[frename_finst_ffv] >>
   pop_assum SUBST_ALL_TAC >>
   irule wff_finst >>
   simp[] >> simp[FINITE_BIGUNION_tfv,FDOM_rnmap] >>
   rw[] (* 3 *)
   >- (irule cstt_rnmap >> rw[FINITE_BIGUNION_tfv] >>
      irule BIGUNION_is_cont >> gs[tfv_is_cont] >>
      metis_tac[tfv_is_cont])
   >- (irule wfcod_rnmap_BIGUNION >>
      rw[FINITE_BIGUNION_tfv] >>
      metis_tac[wfcod_rnmap_tfv]) >>
   irule wff_Pred >> simp[])
>- (rw[frename_alt] >> irule wff_IMP >>
   metis_tac[])
>- (‘(frename (n,s) nn (fVar P sl tl)) =
    finst (rnmap (n,s) nn (ffv (fVar P sl tl)))
          (fVar P sl tl)’ by simp[frename_finst_ffv] >>
   pop_assum SUBST_ALL_TAC >>
   irule wff_finst >> simp[] >>
   ‘FINITE (BIGUNION {sfv s | MEM s sl} ∪ BIGUNION {tfv t | MEM t tl})’
   by (simp[] >> rw[] >> simp[FINITE_lemma,tfv_FINITE]) >>
   simp[FDOM_rnmap] >> rw[] (* 3 *)
   >- (rw[GSYM BIGUNION_UNION,Excl "BIGUNION_UNION"] >>
      irule cstt_rnmap >> strip_tac (* 2 *)
      >- (gs[BIGUNION_UNION] >> metis_tac[]) >>
      irule BIGUNION_is_cont >> gs[tfv_is_cont] >>
      metis_tac[tfv_is_cont])
   >- (rw[GSYM BIGUNION_UNION,Excl "BIGUNION_UNION"] >>
      irule wfcod_rnmap_BIGUNION >>
      rw[] >> simp[tfv_FINITE,FINITE_lemma] (* 2 *)
      >- (irule wfcod_rnmap_cont >>
         simp[tfv_FINITE] >>
         metis_tac[wfabsap_wfs,tfv_is_cont]) >>
      metis_tac[wfcod_rnmap_tfv,wfabsap_wft]) >>
   irule wff_fVar >> simp[]) >>
rw[frename_finst_ffv] >>
irule wff_finst >> simp[FDOM_rnmap] >>
rw[] (* 3 *)
>- (irule cstt_rnmap >> simp[ffv_FINITE,ffv_is_cont])
>- (irule wfcod_rnmap_cont >>
   simp[ffv_FINITE,ffv_is_cont] >> rw[] >>
   irule wff_wfs >>
   first_x_assum $ irule_at Any >>
   qexists ‘Σp’ >>
   irule $ cj 5 wff_rules >>
   simp[] >> metis_tac[]) >>
irule $ cj 5 wff_rules >>
simp[] >> metis_tac[]   
QED


Theorem mk_FALL_rename_eq:
∀f.
(∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
(n,s) ∉ fVslfv f ∧
(nn,s) ∉ ffv f ⇒
mk_FALL n s f = mk_FALL nn s (frename (n,s) nn f)
Proof
rw[mk_FALL_def,abst_def] >> 
irule fabs_frename >> metis_tac[]
QED





Theorem frename_fix:
∀f n s. (n,s) ∉ ffv f ⇒ frename (n,s) nn f = f
Proof
rw[frename_finst_ffv] >> irule finst_vmap_id >>
simp[FDOM_rnmap,FAPPLY_rnmap,ffv_FINITE] >>
rw[] >>
rw[trename_tinst_tfv,FDOM_rnmap,tfv_FINITE] >>
rw[FAPPLY_rnmap] >>
irule $ cj 1 trename_fix >> CCONTR_TAC >> gs[] >>
metis_tac[ffv_is_cont,is_cont_def,SUBSET_DEF]
QED
        
Theorem ffv_fabs_SUBSET:
∀fm i n s.
    (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ∧
    (n,s) ∉ fVslfv fm ⇒ 
    ffv (fabs (n,s) i fm) ⊆ ffv fm DELETE (n,s)
Proof
rw[] >> Cases_on ‘(n,s) ∈ ffv fm’
>- (drule_all_then assume_tac ffv_fabs_fVslfv >>
   gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
drule_all_then assume_tac fabs_id  >>
gs[SUBSET_DEF] 
QED





Theorem IN_tfv_trename:
(∀tm n s nn. (n,s) ∈ tfv tm ⇒
            (nn,s) ∈ tfv (trename (n,s) nn tm)) ∧
(∀st n s nn. (n,s) ∈ sfv st ⇒
            (nn,s) ∈ sfv (srename (n,s) nn st))
Proof            
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,trename_alt,PULL_EXISTS,MEM_MAP] >>
rw[] (* 4 *)
>- (Cases_on ‘s0 = n ∧ st = s’ >> simp[])
>> metis_tac[]
QED



Theorem trename_back:
(∀tm n s nn. (nn,s) ∉ tfv tm ⇒
 trename (nn,s) n (trename (n,s) nn tm) = tm) ∧
(∀st n s nn. (nn,s) ∉ sfv st ⇒
 srename (nn,s) n (srename (n,s) nn st) = st)
Proof
  ho_match_mp_tac better_tm_induction >>
  gs[tfv_thm,trename_alt,MAP_MAP_o,MAP_EQ_f,MAP_fix] >>
  rw[] (* 3 *)
  >- (Cases_on ‘s0 = n ∧ st = s’ >> simp[] (* 2 *)
     >- rw[trename_alt] >>
     rw[trename_alt] >> Cases_on ‘(n,s) ∈ sfv st’ (* 2 *)
     >- (drule_then assume_tac $ cj 2 IN_tfv_trename >>
         metis_tac[sfv_tfv,tm_tree_WF]) >>
     metis_tac[trename_fix])
  >> metis_tac[]
QED  
         
Theorem tprpl_FMAP_MAP_tabs_IN:
(∀tm i n s nn bmap.
(nn,s) ∉ tfv tm ∧
(∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
(∀b n1 s1. b ∈ FDOM bmap ∧
           (n1,s1) ∈ tfv (bmap ' b) ⇒
           (n,s) ∉ sfv s1)  ∧
n ≠ nn ⇒
tprpl (FMAP_MAP (tabs (n,s) i) bmap) tm =
        trename (nn,s) n (tabs (n,s) i (tprpl bmap (trename (n,s) nn tm)))) ∧
(∀st i n s nn bmap.
(nn,s) ∉ sfv st ∧
(∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
(∀b n1 s1. b ∈ FDOM bmap ∧
           (n1,s1) ∈ tfv (bmap ' b) ⇒
           (n,s) ∉ sfv s1) ∧
n ≠ nn ⇒
sprpl (FMAP_MAP (tabs (n,s) i) bmap) st =
        srename (nn,s) n (sabs (n,s) i (sprpl bmap (srename (n,s) nn st))))         
Proof
ho_match_mp_tac better_tm_induction>>
gs[trename_alt,tprpl_def,tabs_def,SF ETA_ss,
   FDOM_FMAP_MAP,MAP_MAP_o,MAP_EQ_f,PULL_EXISTS] >>
rw[] (* 6 *)
>- (Cases_on ‘s0 = n ∧ st = s’ >> gs[] (* 2 *)
   >- gs[trename_alt,tprpl_def,tabs_def,SF ETA_ss,
   FDOM_FMAP_MAP,MAP_MAP_o,MAP_EQ_f,PULL_EXISTS] >>
   ‘¬(s0 = n ∧ st = s)’ by metis_tac[] >> simp[] >>
    gs[trename_alt,tprpl_def,tabs_def,SF ETA_ss,
   FDOM_FMAP_MAP,MAP_MAP_o,MAP_EQ_f,PULL_EXISTS] >>
   Cases_on ‘n = s0 ∧ s = srename (n,s) nn st’ >> simp[]
   (* 2 *)
   >- (gs[] >>
      Cases_on ‘(s0,s) ∈ sfv st’ (* 2 *)
      >- (drule_then assume_tac $ cj 2 IN_tfv_trename >>
         metis_tac[sfv_tfv,tm_tree_WF]) >> 
   ‘srename (n,s) nn st = st’
    by metis_tac[trename_fix] >> gs[]) >>
   simp[trename_alt] >> rw[] (* 2 *)
   >- (gs[] >> Cases_on ‘(n,s) ∈ sfv st’ (* 2 *)
      >- (drule_then assume_tac $ cj 2 IN_tfv_trename >>
         metis_tac[sfv_tfv,tm_tree_WF]) >>
      metis_tac[trename_fix]) >>
   metis_tac[trename_back])
>- (first_x_assum irule >> simp[] >>
   metis_tac[])
>- (first_x_assum irule >> metis_tac[])
>- (rw[FAPPLY_FMAP_MAP] >>
   rw[Once EQ_SYM_EQ] >>
   irule $ cj 1 trename_fix >>
   ‘tfv (tabs (n',s) i (bmap ' n)) ⊆
    tfv (bmap ' n) DELETE (n',s)’
    by metis_tac[tfv_tabs_SUBSET] >>
   CCONTR_TAC >> gs[SUBSET_DEF] >> metis_tac[])
>-  gs[trename_alt,tprpl_def,tabs_def,SF ETA_ss,
   FDOM_FMAP_MAP,MAP_MAP_o,MAP_EQ_f,PULL_EXISTS] >>
first_x_assum irule >> metis_tac[]
QED





Theorem slprpl_FMAP_MAP_abssl_IN:
∀sl i n s nn bmap.
(∀st. MEM st sl ⇒ (nn,s) ∉ sfv st) ∧
(∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
(∀b n1 s1. b ∈ FDOM bmap ∧
           (n1,s1) ∈ tfv (bmap ' b) ⇒
           (n,s) ∉ sfv s1) ∧
n ≠ nn ⇒
slprpl (FMAP_MAP (tabs (n,s) i) bmap) sl =
 MAP (srename (nn,s) n)
          (abssl (n,s) i (slprpl bmap (MAP (srename (n,s) nn) sl)))
Proof
rw[] >> irule LIST_EQ >>
gs[LENGTH_slprpl,EL_MAP,LENGTH_abssl] >> rw[] >>
drule_then assume_tac slprpl_EL >> simp[] >>
‘x < LENGTH (slprpl bmap (MAP (srename (n,s) nn) sl))’
 by gs[LENGTH_slprpl] >>
drule_then assume_tac abssl_EL >> simp[] >>
‘x < LENGTH (MAP (srename (n,s) nn) sl)’
 by gs[] >>
drule_then assume_tac slprpl_EL >> simp[] >>
gs[EL_MAP] >>
rw[shift_bmap_FMAP_MAP_tabs] >> 
irule $ cj 2 tprpl_FMAP_MAP_tabs_IN >>
simp[FDOM_shift_bmap,PULL_EXISTS] >>
ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM] >>
rw[] (* 3 *)
>- (drule_then assume_tac FAPPLY_shift_bmap >>
   gs[] >> gs[tfv_tshift] >> metis_tac[])
>- (drule_then assume_tac FAPPLY_shift_bmap >>
   gs[] >> gs[tfv_tshift] >> metis_tac[]) >>
metis_tac[MEM_EL]
QED



Theorem fprpl_FMAP_MAP_fabs_IN:
∀ϕ i n s bmap.
(nn,s) ∉ ffv ϕ ∧
(∀b. b ∈ FDOM bmap ⇒ (nn,s) ∉ tfv (bmap ' b)) ∧
(∀b n1 s1. b ∈ FDOM bmap ∧
           (n1,s1) ∈ tfv (bmap ' b) ⇒
           (n,s) ∉ sfv s1)  ∧
n ≠ nn ⇒
fprpl (FMAP_MAP (tabs (n,s) i) bmap) ϕ =
        frename (nn,s) n
          (fabs (n,s) i (fprpl bmap (frename (n,s) nn ϕ)))
Proof
Induct_on ‘ϕ’ >>
gs[fprpl_def,frename_alt,fabs_def,MAP_MAP_o,MAP_EQ_f] (* 4 *)
>- (rw[] >> metis_tac[tprpl_FMAP_MAP_tabs_IN])
>- (rw[] >> metis_tac[])
>- (rw[] >- metis_tac[tprpl_FMAP_MAP_tabs_IN] >>
   rw[shift_bmap_FMAP_MAP_tabs] >>
   first_x_assum irule >> simp[] >> rw[] (* 3 *)
   >- (gs[FDOM_shift_bmap,FAPPLY_shift_bmap] >>
      drule_then assume_tac FAPPLY_shift_bmap >>
      gs[] >>
      ‘x + 1 = 1 + x’ by simp[] >>
      pop_assum SUBST_ALL_TAC >> gs[] >>
      gs[tfv_tshift] >> metis_tac[]) >>
      gs[FDOM_shift_bmap,FAPPLY_shift_bmap] >>
    drule_then assume_tac FAPPLY_shift_bmap >>
    gs[] >>
    ‘x + 1 = 1 + x’ by simp[] >>
    pop_assum SUBST_ALL_TAC >> gs[] >>
    gs[tfv_tshift] >> metis_tac[]) >>
rw[]
>- (rw[Once EQ_SYM_EQ,MAP_fix] >>
   rw[Once EQ_SYM_EQ] >>
   irule $ cj 2 trename_back >>
   metis_tac[]) >>
metis_tac[tprpl_FMAP_MAP_tabs_IN]
QED



          
                  

Theorem NOTIN_trename:
  (∀tm. nn ≠ n ⇒ (n,s) ∉ tfv (trename (n,s) nn tm)) ∧
  (∀st. nn ≠ n ⇒ (n,s) ∉ sfv (srename (n,s) nn st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,trename_alt,MEM_MAP] >>
rw[] (* 3 *)
>- (Cases_on ‘s0 = n ∧ st = s’ >> simp[tfv_thm] (* 2 *)
   >- metis_tac[tm_tree_WF] >>
   rw[] >> Cases_on ‘(n,s) ∈ sfv st’ (* 2 *)
   >- (drule_then assume_tac $ cj 2 IN_tfv_trename >>
      metis_tac[tm_tree_WF]) >>
   metis_tac[trename_fix])
>> metis_tac[]
QED


Theorem NOTIN_frename:
  ∀f. nn ≠ n ⇒ (n,s) ∉ ffv (frename (n,s) nn f)
Proof
Induct_on ‘f’ >> 
gs[ffv_thm,frename_alt,MEM_MAP] >>
rw[] (* 4 *)
>> metis_tac[NOTIN_trename]
QED
                
        
       
Theorem frename_FALLL:
∀sl ϕ. frename (n,s) nn (FALLL sl ϕ) =
FALLL (MAP (srename (n,s) nn) sl) (frename (n,s) nn ϕ)
Proof
Induct_on ‘sl’ >> gs[frename_alt,FALLL_def]
QED

(*this one*)

Theorem ffv_FALLL:
∀sl f.
ffv (FALLL sl f) = BIGUNION {sfv s | MEM s sl} ∪ ffv f
Proof
Induct_on ‘sl’ >> simp[ffv_thm,FALLL_def] >>
rw[EXTENSION] >> metis_tac[]
QED

Theorem BIGUNION_IMAGE_sbounds_tfv:
(∀tm.   
BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn tm))) = BIGUNION (IMAGE (sbounds ∘ SND) (tfv tm))) ∧
∀st.   
BIGUNION (IMAGE (sbounds ∘ SND) (sfv (srename (n,s) nn st))) = BIGUNION (IMAGE (sbounds ∘ SND) (sfv st))
Proof
ho_match_mp_tac better_tm_induction >> rpt strip_tac
>- (rw[] >> rw[tfv_thm,trename_alt,tbounds_trename])
>- (rw[trename_alt,tfv_thm,MEM_MAP] >>
   ‘BIGUNION
          (IMAGE (sbounds ∘ SND)
             (BIGUNION {tfv t | (∃y. t = trename (n,s) nn y ∧ MEM y l)})) =
     BIGUNION (IMAGE (sbounds ∘ SND) (BIGUNION {tfv t | MEM t l}))’ suffices_by metis_tac[] >>
   rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
   >- (first_x_assum $ drule_then assume_tac >>
      Cases_on ‘x'’ >> gs[] >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn y)))’ by (simp[PULL_EXISTS] >>
              qexists ‘(q,r)’ >> simp[]) >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv y))’
      by metis_tac[] >> gs[] >>
      metis_tac[]) >>
   first_x_assum $ drule_then assume_tac >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv t))’
     by (simp[PULL_EXISTS] >> metis_tac[]) >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn t)))’ by metis_tac[] >>
   gs[] >> metis_tac[])
>- rw[trename_alt] >>
simp[tfv_thm,trename_alt,MEM_MAP] >>     
‘BIGUNION
          (IMAGE (sbounds ∘ SND)
             (BIGUNION {tfv t | (∃y. t = trename (n,s) nn y ∧ MEM y l)})) =
     BIGUNION (IMAGE (sbounds ∘ SND) (BIGUNION {tfv t | MEM t l}))’ suffices_by metis_tac[] >>
   rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
   >- (first_x_assum $ drule_then assume_tac >>
      Cases_on ‘x'’ >> gs[] >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn y)))’ by (simp[PULL_EXISTS] >>
              qexists ‘(q,r)’ >> simp[]) >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv y))’
      by metis_tac[] >> gs[] >>
      metis_tac[]) >>
   first_x_assum $ drule_then assume_tac >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv t))’
     by (simp[PULL_EXISTS] >> metis_tac[]) >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn t)))’ by metis_tac[] >>
   gs[] >> metis_tac[]
QED




Theorem BIGUNION_IMAGE_sbounds_ffv:
∀f.   
BIGUNION (IMAGE (sbounds ∘ SND) (ffv (frename (n,s) nn f))) = BIGUNION (IMAGE (sbounds ∘ SND) (ffv f))
Proof
Induct_on ‘f’ (* 5 *)
>- rw[frename_alt]
>- (rw[frename_alt,MEM_MAP] >>
   ‘∀tm.
          MEM tm l ⇒
          BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn tm))) =
          BIGUNION (IMAGE (sbounds ∘ SND) (tfv tm))’
    by metis_tac[BIGUNION_IMAGE_sbounds_tfv] >>
    rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
   >- (first_x_assum $ drule_then assume_tac >>
      Cases_on ‘x'’ >> gs[] >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn y)))’ by (simp[PULL_EXISTS] >>
              qexists ‘(q,r)’ >> simp[]) >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv y))’
      by metis_tac[] >> gs[] >>
      metis_tac[]) >>
   first_x_assum $ drule_then assume_tac >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv t))’
     by (simp[PULL_EXISTS] >> metis_tac[]) >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn t)))’ by metis_tac[] >>
   gs[] >> metis_tac[])
>- simp[frename_alt,ffv_thm]
>- (simp[frename_alt,ffv_thm] >>
   metis_tac[BIGUNION_IMAGE_sbounds_tfv]) >>
simp[frename_alt,ffv_thm,MEM_MAP] >> rw[] >>
‘BIGUNION
     (IMAGE (sbounds ∘ SND)
        (BIGUNION {sfv s' | (∃y. s' = srename (n,s) nn y ∧ MEM y l)})) =
 BIGUNION (IMAGE (sbounds ∘ SND) (BIGUNION {sfv s | MEM s l}))  ∧
 BIGUNION
     (IMAGE (sbounds ∘ SND)
        (BIGUNION {tfv t | (∃y. t = trename (n,s) nn y ∧ MEM y l0)})) =
 BIGUNION (IMAGE (sbounds ∘ SND) (BIGUNION {tfv t | MEM t l0}))’  suffices_by metis_tac[] >> rw[] (* 2 *)
>- (‘∀st.
          MEM st l ⇒
          BIGUNION (IMAGE (sbounds ∘ SND) (sfv (srename (n,s) nn st))) =
          BIGUNION (IMAGE (sbounds ∘ SND) (sfv st))’
    by metis_tac[BIGUNION_IMAGE_sbounds_tfv] >>
    rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
   >- (first_x_assum $ drule_then assume_tac >>
      Cases_on ‘x'’ >> gs[] >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (sfv (srename (n,s) nn y)))’ by (simp[PULL_EXISTS] >>
              qexists ‘(q,r)’ >> simp[]) >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (sfv y))’
      by metis_tac[] >> gs[] >>
      metis_tac[]) >>
   first_x_assum $ drule_then assume_tac >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (sfv s'))’
     by (simp[PULL_EXISTS] >> metis_tac[]) >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (sfv (srename (n,s) nn s'))) ’ by metis_tac[] >>
   gs[] >> metis_tac[]) >>
rename [‘BIGUNION
     (IMAGE (sbounds ∘ SND)
        (BIGUNION {tfv t | (∃y. t = trename (n,s) nn y ∧ MEM y l)}))’] >>
‘∀tm.
          MEM tm l ⇒
          BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn tm))) =
          BIGUNION (IMAGE (sbounds ∘ SND) (tfv tm))’
    by metis_tac[BIGUNION_IMAGE_sbounds_tfv] >>
    rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
   >- (first_x_assum $ drule_then assume_tac >>
      Cases_on ‘x'’ >> gs[] >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn y)))’ by (simp[PULL_EXISTS] >>
              qexists ‘(q,r)’ >> simp[]) >>
      ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv y))’
      by metis_tac[] >> gs[] >>
      metis_tac[]) >>
   first_x_assum $ drule_then assume_tac >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv t))’
     by (simp[PULL_EXISTS] >> metis_tac[]) >>
   ‘x ∈ BIGUNION (IMAGE (sbounds ∘ SND) (tfv (trename (n,s) nn t)))’ by metis_tac[] >>
   gs[] >> metis_tac[]
QED
        
Theorem fresh_name_ex:
∀vs:string # sort -> bool. FINITE vs ⇒ ∃nn. ∀s. (nn,s) ∉ vs
Proof
rw[] >> qexists ‘variant (fromSet (IMAGE FST vs)) ("")’ >>
metis_tac[variant_var_NOTIN]
QED



Definition inst_eff_def:
  inst_eff σ (n,s) = if (n,s) ∈ FDOM σ then σ ' (n,s)
  else Var n (sinst σ s)
End


        
Theorem inst_eff_tinst:
(∀tm σ1 σ2.
  (∀n s. (n,s) ∈ tfv tm ⇒
         inst_eff σ1 (n,s) = inst_eff σ2 (n,s)) ⇒
  tinst σ1 tm = tinst σ2 tm) ∧
(∀st σ1 σ2.
  (∀n s. (n,s) ∈ sfv st ⇒
         inst_eff σ1 (n,s) = inst_eff σ2 (n,s)) ⇒
  sinst σ1 st = sinst σ2 st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,tinst_def,PULL_EXISTS,MAP_EQ_f] >> rw[] (* 3 *)
>- (Cases_on ‘(s0,st) ∉ FDOM σ1’ >>
   Cases_on ‘(s0,st) ∉ FDOM σ2’ >> gs[] (* 3 *)
   >> (first_x_assum $ qspecl_then [‘s0’,‘st’] assume_tac>>
   gs[inst_eff_def]))
>> metis_tac[]
QED



Theorem cstt_EXT:
cstt σ ⇒
∀vs. FINITE vs ∧ FDOM σ ⊆ vs ⇒
     ∃σ1. FDOM σ1 = (gcont vs) ∧ complete σ1 ∧ cstt σ1 ∧
          ∀v. v ∈ vs ⇒
              inst_eff σ1 v = inst_eff σ v
Proof
rw[] >>
qexists ‘FUN_FMAP (λ(n,s). if (n,s) ∈ FDOM σ then σ ' (n,s) else Var n (sinst σ s)) (gcont vs)’ >>
rw[FUN_FMAP_DEF] (* 3 *)
>- (drule_then assume_tac gcont_FINITE >>
   rw[FUN_FMAP_DEF])
>- (rw[complete_FDOM_is_cont]  >>
   drule_then assume_tac gcont_FINITE >>
   rw[FUN_FMAP_DEF] >>
   metis_tac[gcont_is_cont])
>- (rw[cstt_def] >>
   drule_then assume_tac gcont_FINITE >>
   gs[FUN_FMAP_DEF] >>
   Cases_on ‘(n,s) ∈ FDOM σ’ >> gs[] (* 2 *)
   >- (gs[cstt_def] >> 
      irule $ cj 2 inst_eff_tinst >>
      rw[inst_eff_def] >> rw[] (* 4 *)
      >- rw[FUN_FMAP_DEF]
      >- metis_tac[gcont_is_cont,is_cont_def,SUBSET_DEF]
      >- rw[FUN_FMAP_DEF] >>
      metis_tac[gcont_is_cont,is_cont_def,SUBSET_DEF]) >>
   rw[sort_of_def] >>
   irule $ cj 2 inst_eff_tinst >>
      rw[inst_eff_def] >> rw[] (* 4 *)
      >- rw[FUN_FMAP_DEF]
      >- metis_tac[gcont_is_cont,is_cont_def,SUBSET_DEF]
      >- rw[FUN_FMAP_DEF] >>
      metis_tac[gcont_is_cont,is_cont_def,SUBSET_DEF]) >>
Cases_on ‘v’ >> rename [‘(n,s)’] >>
drule_then assume_tac gcont_FINITE >>
rw[inst_eff_def] (* 4 *)
>- gs[FUN_FMAP_DEF]
>- gs[FUN_FMAP_DEF]
>- gs[gcont_def,EXTENSION] >>
gs[gcont_def]
QED        




Theorem ill_formed_fabs_still_in:
(∀f n s n0 s0 i. (n0,s0) ∈ ffv f ∧ (n,s) ∈ sfv s0 ⇒
   (n,s) ∈ ffv (fabs (n,s) i f))
Proof
Induct_on ‘f’ >> gs[ffv_thm,fabs_def,PULL_EXISTS,MEM_MAP] (* 4 *)
>- (rw[] >> metis_tac[ill_formed_tabs_still_in])
>- metis_tac[]
>- (rw[] (* 2 *)
   >>metis_tac[ill_formed_tabs_still_in]) >>
rw[] (* 2 *)
>- metis_tac[vsort_tfv_closed] >>
metis_tac[ill_formed_tabs_still_in]
QED    


           
                   
val _ = export_theory();

