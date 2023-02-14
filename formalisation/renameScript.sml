open HolKernel Parse boolLib bossLib;

val _ = new_theory "rename";

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
(nn,s) ∉ ffv f ⇒
mk_FALL n s f = mk_FALL nn s (frename (n,s) nn f)
Proof
rw[mk_FALL_def,abst_def] >> 
irule fabs_frename >> metis_tac[]
QED



(*
Theorem mk_FALL_IN_rename_eq:
∀f.
(∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
(nn,s) ∉ ffv f ⇒
FALL n s f =
frename (nn,s) mk_FALL nn s (frename (n,s) nn f)
Proof
rw[mk_FALL_def,abst_def] >> 
irule fabs_frename >> metis_tac[]
QED
*)

        

        (*

∀f i.
 (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
 (P,sl) ∈ freefVars f ∧
 (∀st. MEM st sl ⇒ (n,s) ∉ sfv st) ∧
 (nn,s) ∉ ffv ϕ ∧
 (∀st. MEM st sl ⇒ (nn,s) ∉ sfv st) ∧
 (nn,s) ∉ ffv f ⇒
(fVar_subst (P,sl,ϕ) (fabs (n,s) i f)) =
       frename (nn,s) n
       (fabs (n,s) (fVar_subst (P,sl,frename (n,s) nn ϕ)
                   f))


among above,                    

(∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) must have for IMP
 (nn,s) ∉ ffv f must have for IMP
 (nn,s) ∉ ffv ϕ ,mustt have for fv ind hyp??
*)


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
    (∀n0 s0. (n0,s0) ∈ ffv fm ⇒ (n,s) ∉ sfv s0) ⇒ 
    ffv (fabs (n,s) i fm) ⊆ ffv fm DELETE (n,s)
Proof
Induct_on ‘fm’ >> gs[fabs_def,ffv_thm,MEM_MAP,PULL_EXISTS]
>- (rw[SUBSET_DEF,PULL_EXISTS] >>
   ‘tfv (tabs (n,s') i y) ⊆ tfv y DELETE (n,s')’
    by (irule $ cj 1 tfv_tabs_SUBSET >>
       metis_tac[]) >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (gs[SUBSET_DEF] >> metis_tac[])
>- (rw[] (* 2 *)
   >- (‘sfv (sabs (n,s') i s) ⊆ sfv s DELETE (n,s')’
        suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
      irule $ cj 2 tfv_tabs_SUBSET >> metis_tac[])>>
   ‘ffv (fabs (n,s') (i + 1) fm) ⊆ ffv fm DELETE (n,s')’
     suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
   metis_tac[]) >>
rw[] (* 2 *)
>- (‘BIGUNION {sfv s | MEM s (abssl (n,s') i l)} ⊆
    BIGUNION {sfv s | MEM s l} DELETE (n,s')’
    suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
   simp[SUBSET_DEF,MEM_EL,PULL_EXISTS,LENGTH_abssl] >>
   rw[] >> gs[] >> (*AQ: weird*)
   ‘∃n' s0. n' < LENGTH l ∧ s0 = EL n' (abssl (n,s') i l) ∧
    s = sfv s0’ by (gs[IN_DEF] >> metis_tac[])>>
    qpat_x_assum ‘s ∈ _’ (K all_tac) >>
   qexists ‘n'’>> simp[] >>
   drule_then assume_tac abssl_EL >> gs[] >>
   ‘sfv (sabs (n,s') (i + n') (EL n' l)) ⊆
    sfv (EL n' l) DELETE (n,s')’
    suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
   irule $ cj 2 tfv_tabs_SUBSET >>
   metis_tac[MEM_EL]) >>
‘BIGUNION {tfv t | (∃y. t = tabs (n,s') i y ∧ MEM y l0)} ⊆
 BIGUNION {tfv t | MEM t l0} DELETE (n,s')’
 suffices_by (rw[SUBSET_DEF] >> metis_tac[]) >>
simp[SUBSET_DEF,PULL_EXISTS] >>
rw[] >>
‘tfv (tabs (n,s') i y) ⊆ tfv y DELETE (n,s')’
 suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
 irule $ cj 1 tfv_tabs_SUBSET >>
 metis_tac[]
QED


(*
∀i n s l0.
          (∀t. MEM t l0 ⇒ (nn,s) ∉ tfv t) ⇒
          fprpl (mk_bmap (REVERSE (MAP (tabs (n,s) i) l0))) ϕ =
          frename (nn,s) n
            (fabs (n,s) i (fprpl (mk_bmap (REVERSE l0)) (frename (n,s) nn ϕ)))

val it =
   Initial goal:
   
   ∀ϕ i n s l0.
     (∀t. MEM t l0 ⇒ (nn,s) ∉ tfv t) ⇒
     fprpl (mk_bmap (REVERSE (MAP (tabs (n,s) i) l0))) ϕ =
     frename (nn,s) n
       (fabs (n,s) i (fprpl (mk_bmap (REVERSE l0)) (frename (n,s) nn ϕ))):
   proof            

            
*)

(*
tprpl (FMAP_MAP (tabs (n,s') i) bmap) e =
        trename (nn,s') n (tabs (n,s') i (tprpl bmap (trename (n,s') nn e)))
*)



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
rw[] >- (irule slprpl_FMAP_MAP_abssl_IN >>
        metis_tac[]) >>
metis_tac[tprpl_FMAP_MAP_tabs_IN]
QED



   
(*
fprpl (mk_bmap (REVERSE (MAP (tabs (n,s) i) l0))) ϕ  =
specl  (mk_bmap (REVERSE (MAP (tabs (n,s) i) l0)))
(FALL l ϕ)

*)          
          
                  

Theorem fVar_subst_fabs:
∀f i.
 (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
 (P,sl) ∈ freefVars f ∧
 (∀st. MEM st sl ⇒ (n,s) ∉ sfv st) ∧
 (nn,s) ∉ ffv ϕ ∧
 (∀st. MEM st sl ⇒ (nn,s) ∉ sfv st) ∧
 (nn,s) ∉ ffv f ∧
 nn ≠ n ⇒
(fVar_subst (P,sl,ϕ) (fabs (n,s) i f)) =
       frename (nn,s) n
       (fabs (n,s) i (fVar_subst (P,sl,frename (n,s) nn ϕ)
                   f))
Proof
Induct_on ‘f’ >>
simp[fVar_subst_def,fabs_def,frename_alt,PULL_EXISTS](* 4 *)
>- (rw[MAP_EQ_f,MAP_MAP_o] >>
    rw[Once EQ_SYM_EQ] >>
    irule $ cj 1 trename_fix >>
    ‘tfv (tabs (n,s) i e) ⊆ tfv e DELETE (n,s)’
     by (irule $ cj 1 tfv_tabs_SUBSET >> metis_tac[]) >>
    CCONTR_TAC >> gs[] >>
    ‘(nn,s) ∈ tfv e DELETE (n,s)’ by metis_tac[SUBSET_DEF]>>
    gs[] >> metis_tac[])
>- (rw[] (* 2 *)
   >- (Cases_on ‘(P,sl) ∈ freefVars f’
      >- (first_x_assum irule >> metis_tac[]) >>
      ‘(P,sl) ∉ freefVars (fabs (n,s) i f)’
       by (CCONTR_TAC >> gs[] >>
          ‘freefVars (fabs (n,s) i f) ⊆ freefVars f’
           suffices_by metis_tac[SUBSET_DEF] >>
          irule freefVars_fabs_SUBSET >>
          metis_tac[]) >>
      ‘(fVar_subst (P,sl,frename (n,s) nn ϕ) f) = f’
        by metis_tac[fVar_subst_id] >>
      simp[] >>
      qspecl_then [‘(fabs (n,s) i f)’,‘P’,‘sl’,‘ϕ’]
      assume_tac fVar_subst_id >>
      simp[] >> rw[Once EQ_SYM_EQ] >>
      irule frename_fix >>
      ‘(nn,s) ∉ ffv f DELETE (n,s)’
       suffices_by metis_tac[SUBSET_DEF,ffv_fabs_SUBSET] >>
      gs[]) >>
   (Cases_on ‘(P,sl) ∈ freefVars f'’
      >- (first_x_assum irule >> metis_tac[]) >>
      ‘(P,sl) ∉ freefVars (fabs (n,s) i f')’
       by (CCONTR_TAC >> gs[] >>
          ‘freefVars (fabs (n,s) i f') ⊆ freefVars f'’
           suffices_by metis_tac[SUBSET_DEF] >>
          irule freefVars_fabs_SUBSET >>
          metis_tac[]) >>
      ‘(fVar_subst (P,sl,frename (n,s) nn ϕ) f') = f'’
        by metis_tac[fVar_subst_id] >>
      simp[] >>
      qspecl_then [‘(fabs (n,s) i f')’,‘P’,‘sl’,‘ϕ’]
      assume_tac fVar_subst_id >>
      simp[] >> rw[Once EQ_SYM_EQ] >>
      irule frename_fix >>
      ‘(nn,s) ∉ ffv f' DELETE (n,s)’
       suffices_by metis_tac[SUBSET_DEF,ffv_fabs_SUBSET] >>
      gs[]) (*same*))
>- (rw[] (* 2 *)
   >- (rw[Once EQ_SYM_EQ] >>
      irule $ cj 2 trename_fix >>
      ‘(nn,s) ∉ sfv s' DELETE (n,s)’
        suffices_by metis_tac[tfv_tabs_SUBSET,SUBSET_DEF] >>
      gs[]) >>
   ‘fVar_subst (P,sl,ϕ) (fabs (n,s) (i +1) f) =
            frename (nn,s) n
              (fabs (n,s) (i+1) (fVar_subst (P,sl,frename (n,s) nn ϕ) f))’
    by (first_x_assum irule >> gs[freefVars_def] >>
       metis_tac[]) (*>>
   pop_assum SUBST_ALL_TAC >>
   simp[frename_alt] >> *)
   (* by assumption (nn,s) ∉ sfv s' and hence not in sabs s',
    hence fixed*)) >>
rw[] >> gs[] (* 4 *)
(*should use nn notin any of the l0, bur n may,
  aim only rename the ones in ϕ, not in l0*)
>- (rw[GSYM rich_listTheory.MAP_REVERSE,mk_bmap_MAP] >>
   irule fprpl_FMAP_MAP_fabs_IN >> simp[FDOM_mk_bmap] >>
   rw[] (* 2 *)
   >- (‘b < LENGTH (REVERSE l0)’ by simp[] >>
      drule_then assume_tac FAPPLY_mk_bmap >>
      gs[] >> ‘MEM (EL b (REVERSE l0)) l0’
      suffices_by metis_tac[] >>
      drule_then assume_tac EL_REVERSE >> simp[] >>
      simp[MEM_EL] >>
      irule_at Any EQ_REFL >> simp[]) >>
   ‘b < LENGTH (REVERSE l0)’ by simp[] >>
drule_then assume_tac FAPPLY_mk_bmap >>
      gs[] >> ‘MEM (EL b (REVERSE l0)) l0’
      suffices_by metis_tac[] >>
      drule_then assume_tac EL_REVERSE >> simp[] >>
      simp[MEM_EL] >>
      irule_at Any EQ_REFL >> simp[])
>- (‘abssl (n,s) i l = l’ suffices_by metis_tac[] >>
    gs[freefVars_def] >>
    ‘ok_abs l’ by metis_tac[ok_abs_abssl] >> gs[])
>- (‘l = abssl (n,s) i l’ suffices_by metis_tac[] >>
   metis_tac[abssl_id]) >>
gs[freefVars_def] >>
Cases_on ‘ok_abs l’ >> gs[]
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
                
        

val _ = export_theory();

