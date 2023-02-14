val idem_def = qdefine_psym("idem",[‘F:B->B’])
‘F o F = F’

val rtn_def = qdefine_psym("rtn",[‘r:B->A’])
‘?i:A->B. r o i = Id(A)’


val rtn_idem = prove_store("rtn_idem",
e0
(rw[idem_def] >> rpt strip_tac >> rw[o_assoc] >>
 qsuff_tac ‘i o (r o i) o r = i o r’ >-- rw[o_assoc] >>
 arw[IdL,IdR])
(form_goal “!r:B->A i:A->B. r o i = Id(A) ==> idem(i o r)”));


val isEq_Mono = prove_store("isEq_Mono",
e0
(rpt strip_tac >> rw[Mono_def] >> rpt strip_tac >>
 drule $ iffLR isEq_def >> pop_assum strip_assume_tac >>
 first_x_assum (qsspecl_then [‘e o h’] assume_tac) >>
 rfs[GSYM o_assoc] >>
 pop_assum (strip_assume_tac o uex_expand) >>
 qsuff_tac
 ‘h = a0 & g' = a0’
 >-- (strip_tac >> once_arw[] >> rw[]) >> 
 strip_tac (* 2 *) >> first_x_assum irule >> arw[])
(form_goal “!A B f:A->B g:A->B E0 e:E0->A. isEq(f,g,e) ==> Mono(e)”));

val new_Thm1 = prove_store("new_Thm1",
e0
(rpt strip_tac >> 
 drule $ iffLR isEq_def >>
 fs[IdL] >> 
 first_x_assum (qsspecl_then [‘F’] assume_tac) >> rfs[idem_def] >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choose_then "r" assume_tac) >>
 qexists_tac ‘r’ >> 
 drule isEq_Mono >> 
 fs[Mono_def] >> first_x_assum irule >>
 fs[IdR,o_assoc])
(form_goal 
 “!B F:B->B. idem(F) ==>
  !A i:A->B. isEq(F,Id(B),i) ==> 
  ?r:B->A.r o i = Id(A) & i o r = F ”));

val new_Thm17 = prove_store("new_Thm17",
e0
(x_choosel_then ["cA","A","A'"] strip_assume_tac Thm14 >>
 drule $ iffLR iso_def >>
 pop_assum (x_choose_then "finv" strip_assume_tac) >>
 qby_tac 
 ‘?F:cA->cA.
   F o A = A & 
   (!A''. ~(A'' = A) ==> F o A'' = A') & 
   !g:2->cA. 
    (dom(g) = A & cod(g) = A ==> F o g = id(A)) & 
    (dom(g) = A & ~(cod(g) = A) ==> F o g = f) & 
    (~(dom(g) = A) & cod(g) = A ==> F o g = finv) & 
    (~(dom(g) = A) & ~(cod(g) = A) ==> F o g = id(A'))’
 >-- (qsuff_tac ‘?(cf : fun(cA, cA)).
        !(a : fun(2, cA))  (b : fun(2, cA)).
          dom(a) = A & cod(a) = A & b = id(A) |
          (dom(a) = A & ~(cod(a) = A) & b = f) |
          (~(dom(a) = A) & cod(a) = A & b = finv) |
          ~(dom(a) = A) & ~(cod(a) = A) & b = id(A') <=> cf o a = b’ >-- 
     (strip_tac >> qexists_tac ‘cf’ >> 
     qby_tac ‘cf o A = A’ 
     >-- (irule $ iffLR id_eq_eq >> rw[id_o] >>
         first_x_assum (irule o iffLR) >> rw[id_dom,id_cod]) >> arw[] >>
     qby_tac ‘!A''. ~(A'' = A) ==> cf o A'' = A'’ 
     >-- (rpt strip_tac >> 
         irule $ iffLR id_eq_eq >> rw[id_o] >>
         first_x_assum (irule o iffLR) >> rw[id_dom,id_cod] >> arw[]) >>
     arw[] >> rpt strip_tac (* 4 *)
     >> (first_x_assum (irule o iffLR) >> arw[])) >>
     match_mp_tac
(CC5 |> qspecl [‘cA’,‘cA’] 
 |> fVar_sInst_th “R(g1:2->cA,g2:2->cA)”
    “(dom(g1:2->cA) = A & cod(g1) = A & g2:2->cA = id(A)) | 
     (dom(g1) = A & ~(cod(g1) = A) & g2 = f) |
     (~(dom(g1) = A) & cod(g1) = A & g2 = finv) |
     (~(dom(g1) = A) & ~(cod(g1) = A) & g2 = id(A'))’”) >>
strip_tac (* 2 *)
>-- (strip_tac >> uex_tac >>
    qcases ‘dom(f') = A’ >> qcases ‘cod(f') = A’ (* 4 *)
    >-- (arw[] >> qexists_tac ‘id(A)’ >> rw[])
    >-- (arw[] >> qexists_tac ‘f’ >> rw[]) 
    >-- (arw[] >> qexists_tac ‘finv’ >> rw[]) >>
    arw[] >> qexists_tac ‘id(A')’ >> rw[]) >>
strip_tac (* 2 *)
>-- (rw[id_dom,id_cod] >> rpt strip_tac (* 8 *)
    >> arw[id_dom,id_cod] (* 2 *)
    >> qpick_x_assum ‘dom(f) = cod(finv)’ (assume_tac o GSYM) >> arw[]) >>
rpt gen_tac >> strip_tac >>
drule oa_dom_cod >> arw[] >> rpt strip_tac >> arw[] >> rw[oa_id] (* 14 *)
>> fs[cpsb_def] (* 10 *) >> rfs[] (* 6 *) >> fs[GSYM id_def] (* 4 *)
 (*before rfs, first goal has assumption A = cod(f') and ~cod(f') = A *)
>-- (flip_tac >> irule cpsb_idR >> arw[cpsb_def,id_cod])
>-- (flip_tac >> irule cpsb_idL >> arw[cpsb_def,id_dom]) 
>-- (flip_tac >> irule cpsb_idL >> arw[cpsb_def,id_dom]) 
>-- (flip_tac >> irule cpsb_idR >> arw[cpsb_def,id_cod])) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘F o A' = A'’ >-- (first_x_assum irule >> flip_tac >> arw[]) >>
 qby_tac ‘F o f = f’ 
 >-- (first_x_assum (qspecl_then [‘f’] strip_assume_tac) >>
      first_x_assum irule >> arw[] >> flip_tac >> arw[] >>
      qpick_x_assum ‘dom(f) = cod(finv)’ (assume_tac o GSYM) >> arw[]) >>
 qby_tac ‘F o finv = finv’ 
 >-- (first_x_assum (qspecl_then [‘finv’] strip_assume_tac) >>
      first_x_assum irule >> arw[] >> flip_tac >> arw[] >>
      qpick_x_assum ‘dom(f) = cod(finv)’ (assume_tac o GSYM) >> arw[]) >>
 qby_tac ‘idem(F)’ 
 >-- (rw[idem_def] >> 
     irule $ iffLR fun_ext >> rw[o_assoc] >> strip_tac >>
     qcases ‘dom(a) = A’ >> qcases ‘cod(a) = A’ (* 4 *)
     >-- (first_assum (qsspecl_then [‘a’] strip_assume_tac) >>
         rfs[] >> 
         qpick_x_assum ‘A = cod(finv)’ (assume_tac o GSYM) >> 
         fs[] >>
         first_assum (qsspecl_then [‘id(A)’] strip_assume_tac) >>
         first_assum irule >> rw[id_dom,id_cod]) 
     >-- (first_assum (qsspecl_then [‘a’] strip_assume_tac) >>
         rfs[] >> 
         qpick_x_assum ‘A = cod(finv)’ (assume_tac o GSYM) >> 
         fs[] >>
         first_assum (qsspecl_then [‘id(A)’] strip_assume_tac) >>
         first_assum irule >> rw[id_dom,id_cod]) 
     >-- (first_assum (qsspecl_then [‘a’] strip_assume_tac) >>
         rfs[] >> 
         qpick_x_assum ‘A = cod(finv)’ (assume_tac o GSYM) >> 
         fs[] >>
         first_assum (qsspecl_then [‘id(A)’] strip_assume_tac) >>
         first_assum irule >> rw[id_dom,id_cod]) >>
     first_assum (qsspecl_then [‘a’] strip_assume_tac) >>
     rfs[] >> arw[GSYM id_o]) >>
 drule new_Thm1 >>
 qsspecl_then [‘F’,‘Id(cA)’] assume_tac isEq_ex >>
 pop_assum (x_choosel_then ["Cl","i"] assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 drule isEq_Mono >>
 (*qby_tac ‘F o A' = A'’ >-- (first_x_assum irule >> flip_tac >> arw[]) >>*)
 qby_tac ‘?A0:1->Cl. i o A0 = A’ 
 >-- (drule $ iffLR isEq_def >>
     pop_assum strip_assume_tac >>
     first_x_assum (qsspecl_then [‘A’] assume_tac) >> fs[IdL] >>
     first_x_assum drule >>
     pop_assum (assume_tac o uex2ex_rule) >> flip_tac >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘?A0':1->Cl. i o A0' = A'’ 
 >-- (drule $ iffLR isEq_def >>
     pop_assum strip_assume_tac >>
     first_x_assum (qsspecl_then [‘A'’] assume_tac) >> fs[IdL] >>
     first_x_assum drule >>
     pop_assum (assume_tac o uex2ex_rule) >> flip_tac >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘~(A0 = A0')’ 
 >-- (fs[Mono_def] >> ccontra_tac >>
     first_x_assum (qsspecl_then [‘A0’,‘A0'’] assume_tac) >> fs[]) >>
 qby_tac 
 ‘!a:1->Cl. a = A0 | a = A0'’ 
 >-- (strip_tac >>
     qcases ‘i o a = A’ 
     >-- (fs[Mono_def] >>
         disj1_tac >> first_x_assum irule >> arw[]) >>
     disj2_tac >>
     drule $ iffLR isEq_def >> pop_assum strip_assume_tac >>
     first_x_assum (qspecl_then [‘i o a’] assume_tac) >>
     first_x_assum drule >>
     rfs[GSYM o_assoc] >> fs[IdL] >>
     fs[Mono_def] >> first_x_assum irule >> arw[]) >>
 qexistsl_tac [‘Cl’,‘A0’] >>
 (*qby_tac ‘F o f = f’ 
 >-- (first_x_assum (qspecl_then [‘f’] strip_assume_tac) >>
      first_x_assum irule >> arw[] >> flip_tac >> arw[] >>
      qpick_x_assum ‘dom(f) = cod(finv)’ (assume_tac o GSYM) >> arw[]) >> *)
 qby_tac ‘?f0:2->Cl. i o f0 = f’ 
 >-- (drule $ iffLR isEq_def >>
     pop_assum strip_assume_tac >>
     first_x_assum (qsspecl_then [‘f’] assume_tac) >> fs[IdL] >>
     first_x_assum drule >>
     pop_assum (assume_tac o uex2ex_rule) >> flip_tac >> arw[]) >>
 pop_assum strip_assume_tac >>
 (*qby_tac ‘F o finv = finv’ 
 >-- (first_x_assum (qspecl_then [‘finv’] strip_assume_tac) >>
      first_x_assum irule >> arw[] >> flip_tac >> arw[] >>
      qpick_x_assum ‘dom(f) = cod(finv)’ (assume_tac o GSYM) >> arw[]) >>*)
 qby_tac ‘?finv0:2->Cl. i o finv0 = finv’ 
 >-- (drule $ iffLR isEq_def >>
     pop_assum strip_assume_tac >>
     first_x_assum (qsspecl_then [‘finv’] assume_tac) >> fs[IdL] >>
     first_x_assum drule >>
     pop_assum (assume_tac o uex2ex_rule) >> flip_tac >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘i o id(A0) = id(A)’ >-- arw[id_def,GSYM o_assoc] >> 
 qby_tac ‘i o id(A0') = id(A')’ >-- arw[id_def,GSYM o_assoc] >> 
 qby_tac 
 ‘!h:2->Cl. h = f0 | h = finv0 | h = id(A0) | h = id(A0')’ 
 >-- (strip_tac >> 
     qcases ‘dom(h) = A0’ >> qcases ‘cod(h) = A0’ (* 4 *)
     >-- (qsuff_tac ‘h = id(A0)’ >-- (strip_tac >> arw[]) >>
         first_x_assum (qspecl_then [‘i o h’] strip_assume_tac) >>
         fs[Mono_def]>> first_x_assum irule >> arw[] >>
         drule $ iffLR isEq_def >> fs[GSYM o_assoc] >> fs[IdL] >>
         first_x_assum irule >> arw[dom_o,cod_o]) 
     >-- (qsuff_tac ‘h = f0’ >-- (strip_tac >> arw[]) >>
         first_x_assum (qspecl_then [‘i o h’] strip_assume_tac) >>
         fs[Mono_def]>> first_x_assum irule >> arw[] >>
         drule $ iffLR isEq_def >> fs[GSYM o_assoc] >> fs[IdL] >>
         first_x_assum irule >> arw[dom_o,cod_o] >>
         qby_tac ‘cod(h) = A0'’ 
         >-- (first_x_assum (qsspecl_then [‘cod(h)’] assume_tac) >> fs[]) >> 
         arw[] >> flip_tac >> arw[]) 
     >-- (qsuff_tac ‘h = finv0’ >-- (strip_tac >> arw[]) >>
         first_x_assum (qspecl_then [‘i o h’] strip_assume_tac) >>
         fs[Mono_def]>> first_x_assum irule >> arw[] >>
         drule $ iffLR isEq_def >> fs[GSYM o_assoc] >> fs[IdL] >>
         first_x_assum irule >> arw[dom_o,cod_o] >>
         qby_tac ‘dom(h) = A0'’ 
         >-- (first_x_assum (qsspecl_then [‘dom(h)’] assume_tac) >> fs[]) >> 
         arw[] >> flip_tac >> arw[]) >>
      qby_tac ‘dom(h) = A0'’ 
      >-- (first_x_assum (qsspecl_then [‘dom(h)’] assume_tac) >> fs[]) >> 
      qby_tac ‘cod(h) = A0'’ 
      >-- (first_x_assum (qsspecl_then [‘cod(h)’] assume_tac) >> fs[]) >>     
      qsuff_tac ‘h = id(A0')’ >-- (strip_tac >> arw[]) >>
      first_x_assum (qspecl_then [‘i o h’] strip_assume_tac) >>
      fs[Mono_def]>> first_x_assum irule >> arw[] >>
      drule $ iffLR isEq_def >> fs[GSYM o_assoc] >> fs[IdL] >>
      first_x_assum irule >> arw[dom_o,cod_o] >>
      flip_tac >> arw[]) >>
 qsspecl_then [‘A0’,‘A0'’,‘f0’,‘finv0’] assume_tac indisc_2_FSCC >>
 first_x_assum irule >> arw[] >>
 qby_tac
 ‘!a:2->Cl.  a = id(A0) | a = id(A0') | a = f0 | a = finv0’ 
 >-- (strip_tac >>
     first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >> fs[]) >>
 arw[] >>
 qby_tac ‘dom(f0) = A0’ 
 >-- (fs[Mono_def] >> first_x_assum irule >> rw[GSYM dom_o] >> arw[]) >>
 qby_tac ‘cod(f0) = A0'’ 
 >-- (fs[Mono_def] >> first_x_assum irule >> rw[GSYM cod_o] >> arw[]) >>
 qby_tac ‘dom(finv0) = A0'’ 
 >-- (fs[Mono_def] >> first_x_assum irule >> rw[GSYM dom_o] >> arw[]) >>
 qby_tac ‘cod(finv0) = A0’ 
 >-- (fs[Mono_def] >> first_x_assum irule >> rw[GSYM cod_o] >> arw[]) >>
 arw[] >>
 strip_tac (* 2 *)
 >-- (fs[Mono_def] >> first_x_assum irule >> arw[] >>
     qby_tac ‘cpsb(finv0,f0)’ >-- arw[cpsb_def] >>
     drule fun_pres_oa >> arw[] >> rw[id_def]) >>
 fs[Mono_def] >> first_x_assum irule >> arw[] >>
 qby_tac ‘cpsb(f0,finv0)’ >-- arw[cpsb_def] >>
 drule fun_pres_oa >> arw[] >> rw[id_def])
(form_goal
 “?Cl t:1->Cl. FSCC(t)”));


val no_ar_10 = prove_store("no_ar_10",
e0
(strip_tac >> ccontra_tac >>
 qsspecl_then [‘f’] assume_tac CC2_1 >>
 pop_assum strip_assume_tac (* 3 *)
 >-- fs[dom_cod_zot,zf_ne_of] 
 >-- fs[dom_cod_zot,GSYM zf_ne_of] >>
 fs[dom_cod_zot,GSYM zf_ne_of])
(form_goal “!f:2->2.~(dom(f) = 1f & cod(f) = 0f)”));

val no_arrow_E10 = prove_store("no_arrow_E10",
e0
(strip_tac >> ccontra_tac >> pop_assum strip_assume_tac >>
 qsuff_tac ‘?F:E->2. F o dom(ε1) = 0f & F o cod(ε1) = 1f’
 >-- (strip_tac >>
     qby_tac ‘dom(F o f) = 1f’ 
     >-- arw[dom_o] >> 
     qby_tac ‘cod(F o f) = 0f’ 
     >-- arw[cod_o] >> 
     qsspecl_then [‘F o f’] assume_tac no_ar_10 >> rfs[]) >>
 assume_tac E_def >>
 drule $ iffLR isPo_def >>
 pop_assum strip_assume_tac >>
 first_x_assum (qsspecl_then [‘𝟚’,‘𝟚’] assume_tac) >> fs[]>>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘a’ >> arw[dom_def,cod_def,GSYM o_assoc] >>
 rw[GSYM dom_def,GSYM cod_def,dom_cod_zot])
(form_goal “!f:2->E. ~(dom(f) = cod(ε1) & cod(f) = dom(ε1))”));

val E_jointEpi2 = prove_store("E_jointEpi2",
e0
(rw[jointEpi2_def] >> rpt strip_tac >>
 assume_tac E_def >>
 fs[isPo_def] >>
 first_assum 
 (qsspecl_then [‘y1 o ε1’,‘y1 o ε2’] assume_tac) >>
 qby_tac 
 ‘(y1 o ε1) o coPa(0f, 1f) = (y1 o ε2) o coPa(0f, 1f)’
 >-- arw[o_assoc] >>
 first_x_assum drule >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘y1 = a & y2 = a’ 
 >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule (* 2 *)
 >-- rw[] >> arw[])
(form_goal “jointEpi2(ε1,ε2)”));


val E_ob = prove_store("E_ob",
e0
(rpt strip_tac >>
 assume_tac E_jointEpi2 >>
 drule jointEpi2_onto >>
 first_x_assum (qsspecl_then [‘Eob’] strip_assume_tac)
 (* 2 *)
 >-- (qsspecl_then [‘a1’] strip_assume_tac ob_of_2 (* 2 *)
     >-- fs[GSYM dom_def,GSYM cod_def] >>
     fs[GSYM dom_def]) >>
 qsspecl_then [‘a2’] strip_assume_tac ob_of_2 (* 2 *)
 >-- fs[e1_e2_same_cod,GSYM cod_def] >>
 fs[e1_e2_same_dom,GSYM dom_def])
(form_goal
 “∀Eob:1->E. Eob = dom(ε1) | Eob = cod(ε1)”));


val dom_e1_ne_cod_e1 = prove_store("dom_e1_ne_cod_e1",
e0
(ccontra_tac >>
 qsuff_tac ‘?F:E->2. F o dom(ε1) = 0f & F o cod(ε1) = 1f’
 >-- (strip_tac >> rfs[zf_ne_of]) >>
 assume_tac E_def >>
 drule $ iffLR isPo_def >>
 pop_assum strip_assume_tac >>
 first_x_assum (qsspecl_then [‘𝟚’,‘𝟚’] assume_tac) >> 
 last_x_assum (K all_tac) >> fs[] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘a’ >> 
 arw[dom_def,cod_def,GSYM o_assoc] >>
 rw[GSYM dom_def,GSYM cod_def,dom_cod_zot])
(form_goal “~(dom(ε1) = cod(ε1))”));

val Po12_eq_eq = proved_th $
e0
(rpt strip_tac >> fs[isPo_def] >>
 first_x_assum
 (qsspecl_then [‘t2 o p’,‘t2 o q’] assume_tac) >>
 rfs[o_assoc] >>
 pop_assum (assume_tac o uex_expand) >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘t1 = a & t2 = a’ >-- (strip_tac >> arw[]) >>
 strip_tac >> first_x_assum irule >> arw[])
(form_goal
 “!X Y f:X->Y Z g:X->Z
   P p:Y->P q:Z ->P.
  isPo(f,g,p,q) ==>
  !T t1:P->T t2. t1 o p = t2 o p & t1 o q = t2 o q ==>
  t1 = t2”)


val isPo_unique = proved_th $
e0
(rpt strip_tac >>
 drule $ iffLR isPo_def >>
 pop_assum strip_assume_tac >>
 rev_drule $ iffLR isPo_def >>  
 pop_assum strip_assume_tac >>
 first_x_assum rev_drule >>
 first_x_assum drule >>
 pop_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choosel_then ["i"] assume_tac) >>
 first_x_assum (assume_tac o uex2ex_rule) >>
 pop_assum (x_choosel_then ["j"] assume_tac) >>
 qexistsl_tac [‘j’,‘i’] >>
 arw[] >> strip_tac (*2 *)
 >-- (drule Po12_eq_eq >> first_x_assum irule >>
     arw[o_assoc] >> rw[IdL]) >>
 rev_drule Po12_eq_eq >> first_x_assum irule >>
 arw[o_assoc] >> rw[IdL])
(form_goal
 “!X Y f:X->Y Z g:X->Z
   P p:Y->P q:Z ->P
   P' p':Y->P' q':Z ->P'.
  isPo(f,g,p,q) &
  isPo(f,g,p',q') ==>
  ?i: P-> P' j:P'->P.
  i o j = Id(P') & j o i = Id(P) &
  j o p' = p & j o q' = q &
  i o p = p' & i o q = q'
  ”);


val E_ar_cases0 = proved_th $
e0
(assume_tac no_arrow_E10 >>
 assume_tac E_ob >>
 strip_tac >>
 first_x_assum (qsspecl_then [‘f’] assume_tac) >>
 first_assum (qsspecl_then [‘dom(f)’] assume_tac) >>
 first_x_assum (qsspecl_then [‘cod(f)’] assume_tac) >>
 fs[] >> fs[])
(form_goal 
“!f:2->E. (dom(f) = dom(ε1) & cod(f) = dom(ε1)) | 
 (dom(f) = cod(ε1) & cod(f) = cod(ε1)) | 
 (dom(f) = dom(ε1) & cod(f) = cod(ε1))” )


val dom_cod_ne_ne_id = prove_store("dom_cod_ne_ne_id",
e0
(rpt strip_tac >> ccontra_tac >> fs[id_dom,id_cod])
(form_goal “!A f:2->A. ~(dom(f) = cod(f)) ==> 
  !a:1->A. ~(f = id(a))”));


val E_ar_ne = prove_store("E_ar_ne",
e0
(assume_tac e1_ne_e2 >> arw[] >> 
 assume_tac dom_e1_ne_cod_e1 >> 
 assume_tac e1_e2_same_dom  >> assume_tac e1_e2_same_cod >>
 rw[id_eq_eq] >> arw[] >>
 rpt strip_tac (* 4 *)
 >-- (irule dom_cod_ne_ne_id >> arw[])
 >-- (irule dom_cod_ne_ne_id >> arw[])
 >-- (irule dom_cod_ne_ne_id >> arw[] >> fs[]) >>
 irule dom_cod_ne_ne_id >> arw[] >> fs[])
(form_goal
 “~(ε1 = ε2) & ~(ε1 = id(dom(ε1))) & ~(ε1 = id(cod(ε1))) &
  ~(ε2 = id(dom(ε1))) & ~(ε2 = id(cod(ε1))) &
  ~(id(dom(ε1)) = id(cod(ε1)))”));


(*
val E_ar = prove_store("E_ar",
e0
(assume_tac E_ob >>
 qabbrev_tac ‘dom(ε1) = E0’ >>
 qabbrev_tac ‘cod(ε1) = E1’ >>
 fs[] >>
 assume_tac no_arrow_E10 >> rfs[] >>
 assume_tac E_ob >> rfs[] >> 
 assume_tac dom_e1_ne_cod_e1 >> rfs[] >>
 qby_tac ‘~(E1 = E0)’ 
 >-- (flip_tac >> arw[]) >> 
 qby_tac
 ‘!f:2->E. ~(dom(f) = cod(f)) ==> 
  dom(f) = E0 & cod(f) = E1’ 
 >-- (rpt strip_tac >> 
     first_assum
     (qsspecl_then [‘dom(f)’] strip_assume_tac)>>
     first_x_assum
     (qsspecl_then [‘cod(f)’] strip_assume_tac) (* 3 *)
     >-- (first_x_assum (qsspecl_then [‘f’] assume_tac) >>
         rfs[]) 
     >-- fs[] >-- fs[] >>
     first_x_assum (qsspecl_then [‘f’] assume_tac) >> 
     rfs[]) >> 
 assume_tac (GSYM e1_e2_same_dom) >> rfs[] >> 
 assume_tac (GSYM e1_e2_same_cod) >> rfs[] >> 
 qby_tac ‘?F:E->E.
 F o E0 = E0 & F o E1 = E1 & 
 F o ε1 = ε1 & 
 (!f. dom(f) = E0 & cod(f) = E1 & ~(f = ε1) ==> 
      F o f = ε2) &
 (!f. dom(f) = E0 & cod(f) = E0 ==> F o f = id(E0)) &
 (!f. dom(f) = E1 & cod(f) = E1 ==> F o f = id(E1))’
 >--
 qsuff_tac
 ‘?(cf : fun(E, E)).
        !(a : fun(2, E))  (b : fun(2, E)).
          a = ε1 & b = ε1 |
          dom(a) = E0 & cod(a) = E0 & b = id(E0) |
          dom(a) = E1 & cod(a) = E1 & b = id(E1) |
          ~(a = ε1) & dom(a) = E0 & cod(a) = E1 & b = ε2 <=> cf o a = b’ 
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qby_tac ‘cf o E0 = E0’ 
     >-- (irule $ iffLR id_eq_eq >>
         rw[id_o] >> arw[] >>
         rw[id_dom,id_cod]) >>
     qby_tac ‘cf o E1 = E1’ 
     >-- (irule $ iffLR id_eq_eq >>
         rw[id_o] >> arw[] >>
         rw[id_dom,id_cod]) >> arw[] >>
     rw[id_eq_eq] >> arw[] >> 
     assume_tac E_ar_ne >> rfs[] >>
     flip_tac >> arw[] >> flip_tac >>
     rpt strip_tac  >> arw[]) >>
 match_mp_tac
 (CC5 |> qspecl [‘E’,‘E’] 
 |> fVar_sInst_th “R(f:2->E,g:2->E)”
    “(f = ε1 & g = ε1) | 
     (dom(f) = E0 & cod(f) = E0 & g = id(E0)) |
     (dom(f) = E1 & cod(f) = E1 & g = id(E1)) |
     (~(f = ε1) & dom(f) = E0 & cod(f) = E1 & g = ε2)”) >>
 qby_tac ‘!f:2->E. dom(f) = E0 & cod(f) = E0 | 
 dom(f) = E1 & cod(f) = E1 |
 dom(f) = E0 & cod(f) = E1’
 >-- (strip_tac >>   
     qcases ‘dom(f) = cod(f)’ (* 2 *)
     >-- (first_x_assum 
         (qsspecl_then [‘dom(f)’] assume_tac) >>
         fs[] >> rfs[]) >>
     first_x_assum drule >> arw[]) >>
 strip_tac (* 2 *)
 >-- (strip_tac >> 
     first_x_assum (qsspecl_then [‘f’] strip_assume_tac) 
     (* 3 *)
     >-- (arw[] >> 
         qby_tac ‘~(f = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         uex_tac >> qexists_tac ‘id(E0)’ >> rw[]) 
     >-- (arw[] >> 
         qby_tac ‘~(f = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         uex_tac >> qexists_tac ‘id(E1)’ >> rw[]) >>
     arw[] >> qcases ‘f = ε1’ >> arw[] (* 2 *)
     >-- (uex_tac >> qexists_tac ‘ε1’ >> rw[]) >>
     uex_tac >> qexists_tac ‘ε2’ >> rw[]) >>
 qby_tac
 ‘!Eo:1->E. ~(ε1 = id(Eo))’ 
 >-- cheat >>
 qby_tac
 ‘!Eo:1->E. ~(ε2 = id(Eo))’ 
 >-- cheat >>
 strip_tac (* 2 *)
 >-- (rw[id_dom,id_cod,id_eq_eq] >>  
     flip_tac >> arw[] >> flip_tac >>
     rpt gen_tac >>
     first_x_assum (qsspecl_then [‘f’] assume_tac) >>
     pop_assum strip_assume_tac (* 3 *)
     >-- (arw[] >> 
         qby_tac ‘~(f = ε1)’ >-- (ccontra_tac >> fs[]) >>
         arw[] >> strip_tac >> arw[id_dom,id_cod]) 
     >-- (arw[] >>
         qby_tac ‘~(f = ε1)’ >-- (ccontra_tac >> fs[]) >>
         arw[] >> strip_tac >> arw[id_dom,id_cod]) >>
     arw[] >> qcases ‘f = ε1’ >> arw[] (* 2 *)
     >> strip_tac >> arw[]) >>
 qby_tac 
 ‘!f:2->E. dom(f) = E1 ==> cod(f) = E1’ 
 >-- (rpt strip_tac >>
     first_x_assum (qsspecl_then [‘f’] assume_tac) >>
     fs[] >> rfs[]) >>
 rpt gen_tac >>
 qpick_x_assum ‘!(f : fun(2, E)).
               dom(f) = E0 & cod(f) = E0 |
               dom(f) = E1 & cod(f) = E1 | dom(f) = E0 & cod(f) = E1’ assume_tac >>
 first_assum (qsspecl_then [‘f’] assume_tac) >>
 pop_assum strip_assume_tac (* 3 *)
 >-- arw[] >> strip_tac >>
     drule $ iffLR cpsb_def >>
     rfs[] >> 
     last_x_assum (qsspecl_then [‘cod(g)’] assume_tac) >>
     pop_assum strip_assume_tac (* 2 *)
     >-- (arw[] >>  
         drule oa_dom_cod >> arw[] >>
         rfs[] >> 
         qby_tac ‘~(g @ f = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         qby_tac ‘~(f = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         qby_tac ‘~(g = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         rpt strip_tac >> flip_tac >>arw[] >>
         irule cpsb_idL >> rw[cpsb_def,id_dom,id_cod]) >>
     arw[] >> drule oa_dom_cod >> rfs[] >>
     qby_tac ‘~(f = ε1)’ >-- (ccontra_tac >> fs[]) >>
     arw[] >>
     strip_tac
     

 (*qby_tac ‘!f:2->E. F o f = ε1 <=> f = ε1’
 >-- cheat >> *)
 pop_assum strip_assume_tac >>
 qby_tac ‘idem(F)’ 
 >-- (rw[idem_def] >> irule $ iffLR fun_ext >>
     strip_tac >> rw[o_assoc] >>
     qsspecl_then [‘a’] assume_tac E_ar_cases0 >>
     pop_assum strip_assume_tac (* 3 *)
     >-- (rfs[] >>
         qby_tac ‘F o a = id(E0)’ 
         >-- (first_x_assum irule >> arw[]) >>
         arw[] >> first_x_assum irule >>
         rw[id_dom,id_cod] ) 
     >-- (rfs[] >>
         qby_tac ‘F o a = id(E1)’ 
         >-- (first_x_assum irule >> arw[]) >>
         arw[] >> first_x_assum irule >>
         rw[id_dom,id_cod]) 
     >-- (rfs[] >>
         qcases ‘a = ε1’ >> arw[] >>
         qby_tac ‘F o a = ε2’ 
         >-- (first_x_assum irule >> arw[]) >>
         arw[] >>
         first_x_assum irule >> arw[] >>
         rw[GSYM e1_ne_e2])) >>
 drule new_Thm1 >> 
 qsspecl_then [‘F’,‘Id(E)’] assume_tac isEq_ex >>
 pop_assum (x_choosel_then ["sE","i"] assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qabbrev_tac ‘r o ε1 = ε10’ >>
 qby_tac ‘i o ε10 = ε1’ 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     arw[GSYM o_assoc]) >>
 qabbrev_tac ‘r o ε2 = ε20’ >>
 qby_tac ‘i o ε20 = ε2’ 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     arw[GSYM o_assoc] >> first_x_assum irule >>
     rw[GSYM e1_ne_e2,e1_e2_same_dom,e1_e2_same_cod] >>
     arw[GSYM e1_e2_same_cod,GSYM e1_e2_same_dom]) >> 
 qby_tac ‘dom(ε10) = r o E0’ 
 >-- (qpick_x_assum ‘r o ε1 = ε10’ (assume_tac o GSYM) >>
     arw[dom_o]) >>
 qby_tac ‘cod(ε10) = r o E1’ 
 >-- (qpick_x_assum ‘r o ε1 = ε10’ (assume_tac o GSYM) >>
     arw[cod_o]) >>
 qby_tac ‘dom(ε20) = r o E0’ 
 >-- (qpick_x_assum ‘r o ε2 = ε20’ (assume_tac o GSYM) >>
     arw[dom_o]) >>
 qby_tac ‘cod(ε20) = r o E1’ 
 >-- (qpick_x_assum ‘r o ε2 = ε20’ (assume_tac o GSYM) >>
     arw[cod_o]) >> 
 drule isEq_Mono >>
 qby_tac 
 ‘!f:2->E. F o f = ε1 | F o f = ε2 | 
           F o f = id(E0) | F o f = id(E1)’ 
 >-- (strip_tac >>
     qsspecl_then [‘f’] assume_tac E_ar_cases0 >>
     pop_assum strip_assume_tac (* 3 *)
     >-- (rfs[] >>
         disj2_tac >> disj2_tac >> disj1_tac >>
         first_x_assum irule >> arw[])
     >-- (rfs[] >>
         rpt disj2_tac >> first_x_assum irule >> arw[]) >>
     rfs[] >> qcases ‘f = ε1’ >> arw[] >>
     disj2_tac >> disj1_tac >> first_x_assum irule >>
     arw[]) >> 
 qby_tac ‘!f:2->sE. i o f = ε1 | i o f = ε2 | i o f = id(E0) | i o f = id(E1)’ 
 >-- (strip_tac >>
     first_x_assum (qsspecl_then [‘F o i o f’] assume_tac)>>
     drule $ iffLR idem_def >> 
     drule $ iffLR isEq_def >> fs[GSYM o_assoc,IdL]) >>
 qby_tac ‘!f:2->sE. f = ε10 | f = ε20 | f = id(r o E0) |
           f = id(r o E1)’
 >-- (strip_tac >>
     first_x_assum (qsspecl_then [‘f’] strip_assume_tac) 
     (* 4 *)
     >-- (fs[Mono_def] >> disj1_tac >> 
         first_x_assum irule >> arw[]) 
     >-- (disj2_tac >> disj1_tac >>
         fs[Mono_def] >> first_x_assum irule >> arw[]) 
     >-- (disj2_tac >> disj2_tac >> disj1_tac >>
         fs[Mono_def] >> first_x_assum irule >>
         arw[] >> rw[GSYM id_o,id_eq_eq] >>
         arw[GSYM o_assoc]) >>
     rpt disj2_tac >> fs[Mono_def] >>
     first_x_assum irule >> arw[GSYM id_o,id_eq_eq] >>
     arw[GSYM o_assoc]) >>
 qby_tac ‘isPo(coPa(0f,1f),coPa(0f,1f),ε10,ε20)’  
 >-- (rw[isPo_def] >>
     qby_tac ‘ε10 o coPa(0f, 1f) = ε20 o coPa(0f, 1f)’ 
     >-- (fs[Mono_def] >> first_x_assum irule >>
         arw[GSYM o_assoc] >>
         assume_tac E_def >> fs[isPo_def]) >> arw[] >>
     rpt strip_tac >>
     qsuff_tac ‘?(a : fun(sE, A)). a o ε10 = u & 
                 a o ε20 = v’
     >-- (strip_tac >> uex_tac >> qexists_tac ‘a’ >> 
         arw[] >>
         rpt strip_tac >> irule $ iffLR fun_ext >>
         strip_tac >>
         first_x_assum (qsspecl_then [‘a''’] assume_tac) >>
         pop_assum strip_assume_tac >> arw[] (* 2 *)
         >-- (rw[GSYM id_o,id_eq_eq] >>
             qby_tac ‘a o ε10 = a' o ε10’ >-- arw[] >>
             qby_tac ‘a o ε10 o 0f = a' o ε10 o 0f’ 
             >-- arw[GSYM o_assoc] >>
             pop_assum mp_tac >> rw[GSYM dom_def] >>
             arw[] >> strip_tac >> arw[]) >>
         rw[GSYM id_o,id_eq_eq] >>
         qby_tac ‘a o ε10 = a' o ε10’ >-- arw[] >>
         qby_tac ‘a o ε10 o 1f = a' o ε10 o 1f’ 
         >-- arw[GSYM o_assoc] >>
         pop_assum mp_tac >> rw[GSYM cod_def] >>
         arw[] >> strip_tac >> arw[]) >>
     qsuff_tac 
     ‘?(cf : fun(sE, A)).
        !(a : fun(2, sE))  (b : fun(2, A)).
          a = ε10 & b = u |
          a = ε20 & b = v |
          a = id(r o E0) & b = id(dom(u)) |
          a = id(r o E1) & b = id(cod(u)) <=> cf o a = b’
     >-- (strip_tac >> qexists_tac ‘cf’ >>
         pop_assum (assume_tac o GSYM) >> arw[]) >>
     match_mp_tac
     (CC5 |> qspecl [‘sE’,‘A’] 
     |> fVar_sInst_th “R(f:2->sE, g:2->A)”
        “(f = ε10:2->sE & g:2->A = u) |
         (f = ε20 & g = v) |
         (f = id(r o E0) & g = id(dom(u))) |
         (f = id(r o E1) & g = id(cod(u)))”) >>
     qby_tac ‘~(ε10 = ε20)’ 
     >-- (ccontra_tac >>
         qsuff_tac ‘ε1 = ε2’ >-- rw[e1_ne_e2] >>
         qpick_x_assum ‘i o ε10 = ε1’
         (assume_tac o GSYM) >> 
         qpick_x_assum ‘i o ε20 = ε2’
         (assume_tac o GSYM) >> arw[]) >>
     qby_tac ‘~(r o E0 = r o E1)’ 
     >-- (ccontra_tac >>
         qsuff_tac ‘E0 = E1’ >-- arw[] >>
         qpick_x_assum ‘~(E0 = E1)’ (K all_tac) >>
         qby_tac ‘i o r o E0 = i o r o E1’  
         >-- arw[] >>
         pop_assum mp_tac >> arw[GSYM o_assoc]) >>
     qby_tac ‘~(ε10 = id(r o E0))’ 
     >-- (ccontra_tac >>
         qby_tac ‘i o ε10 = i o id(r o E0)’ 
         >-- (qpick_x_assum ‘i o ε10 = ε1’ (K all_tac) >>
             arw[]) >>
         pop_assum mp_tac >>
         rw[GSYM id_o] >> arw[GSYM o_assoc] >>  
         assume_tac E_ar_ne >> rfs[]) >>
     qby_tac ‘~(ε10 = id(r o E1))’ 
     >-- (ccontra_tac >>
         qby_tac ‘i o ε10 = i o id(r o E1)’ 
         >-- (qpick_x_assum ‘i o ε10 = ε1’ (K all_tac) >>
             arw[]) >>
         pop_assum mp_tac >>
         rw[GSYM id_o] >> arw[GSYM o_assoc] >>  
         assume_tac E_ar_ne >> rfs[]) >>
     qby_tac ‘~(ε20 = id(r o E0))’ 
     >-- (ccontra_tac >>
         qby_tac ‘i o ε20 = i o id(r o E0)’ 
         >-- (qpick_x_assum ‘i o ε20 = ε2’ (K all_tac) >>
             arw[]) >>
         pop_assum mp_tac >>
         rw[GSYM id_o] >> arw[GSYM o_assoc] >>  
         assume_tac E_ar_ne >> rfs[]) >>
     qby_tac ‘~(ε20 = id(r o E1))’ 
     >-- (ccontra_tac >>
         qby_tac ‘i o ε20 = i o id(r o E1)’ 
         >-- (qpick_x_assum ‘i o ε20 = ε2’ (K all_tac) >>
             arw[]) >>
         pop_assum mp_tac >>
         rw[GSYM id_o] >> arw[GSYM o_assoc] >>  
         assume_tac E_ar_ne >> rfs[]) >>
     strip_tac (* 2 *)
     >-- (strip_tac >>
         first_x_assum (qsspecl_then [‘f’] assume_tac) >>
         pop_assum strip_assume_tac >> arw[] (* 4 *)
         >-- (uex_tac  >> qexists_tac ‘u’ >> rw[]) 
         >-- (qpick_x_assum ‘~(ε10 = ε20)’ 
              (assume_tac o GSYM) >> arw[] >>
              uex_tac  >> qexists_tac ‘v’ >> rw[]) 
         >-- (flip_tac >> arw[] >> flip_tac >>
             rw[id_eq_eq] >> arw[] >>
             uex_tac >> qexists_tac ‘id(dom(u))’ >> rw[])>>
         flip_tac >> arw[] >> rw[id_eq_eq] >>
         arw[] >> uex_tac >> qexists_tac ‘id(cod(u))’ >>
         rw[] >> rpt strip_tac >> arw[]) >>
     qby_tac ‘dom(u) = dom(v) & cod(u) = cod(v)’
     >-- (qby_tac 
         ‘u o coPa(0f, 1f) o i1(1,1) = 
          v o coPa(0f, 1f) o i1(1,1) & 
          u o coPa(0f, 1f) o i2(1,1) =
          v o coPa(0f, 1f) o i2(1,1)’ 
          >-- arw[GSYM o_assoc] >>
          pop_assum mp_tac >> rw[i12_of_coPa] >>
          rw[GSYM dom_def,GSYM cod_def]) >>
     pop_assum strip_assume_tac >>
     strip_tac (* 2 *)
     >-- (rpt gen_tac >> rw[id_eq_eq] >> strip_tac >>
         arw[id_dom,id_cod] >> rpt strip_tac >> arw[]) >>
     qby_tac ‘!g.dom(g) = r o E1 ==> g = id(r o E1)’ 
     >-- (rpt strip_tac >> 
         first_x_assum (qsspecl_then [‘g’] assume_tac) >>
         pop_assum strip_assume_tac (* 4 *) >> arw[] (* 3 *)
         >-- (fs[] >> qpick_x_assum ‘r o E1 = r o E0’
             (assume_tac o GSYM) >> fs[]) 
         >-- (fs[] >> qpick_x_assum ‘r o E1 = r o E0’
             (assume_tac o GSYM) >> fs[]) >>
         fs[id_dom,id_cod]) >> 
     qpick_x_assum ‘!(f : fun(2, sE)).
               f = ε10 | f = ε20 | f = id(r o E0) | f = id(r o E1)’ assume_tac >> 
     rpt gen_tac >> strip_tac >>
     first_assum (qsspecl_then [‘f’] strip_assume_tac) 
     (* 4 *)
     >-- (arw[] >>
         qby_tac ‘g = id(r o E1)’ 
         >-- (first_x_assum irule >> fs[cpsb_def]) >>
         arw[] >> flip_tac >> arw[] >> flip_tac >>
         qby_tac ‘id((r o E1)) @ ε10 = ε10’ 
         >-- (irule cpsb_idL >> arw[cpsb_def,id_dom]) >>
         arw[] >> arw[id_eq_eq] >> flip_tac >> arw[] >>
         flip_tac >> rpt strip_tac >> arw[] >>
         flip_tac >> irule cpsb_idL >>
         arw[cpsb_def,id_cod,id_dom]) 
     >-- (arw[] >>
         qby_tac ‘g = id(r o E1)’ 
         >-- (first_x_assum irule >> fs[cpsb_def]) >>
         arw[] >> flip_tac >> arw[] >> flip_tac >>
         qby_tac ‘id((r o E1)) @ ε20 = ε20’ 
         >-- (irule cpsb_idL >> arw[cpsb_def,id_dom]) >>
         arw[] >> arw[id_eq_eq] >> flip_tac >> arw[] >>
         flip_tac >> rpt strip_tac >> arw[] >>
         flip_tac >> irule cpsb_idL >>
         arw[cpsb_def,id_cod,id_dom]) 
     >-- (arw[] >> flip_tac >> arw[] >> flip_tac >>
         qby_tac ‘g = id(r o E0) | g = ε10 | g = ε20’ 
         >-- (first_x_assum 
             (qsspecl_then [‘g’] strip_assume_tac) >>
             arw[] >> 
             fs[cpsb_def,id_dom,id_cod]) >> 
         pop_assum strip_assume_tac >> arw[] (* 3 *)
         >-- (qby_tac
             ‘id(r o E0) @ id(r o E0) = id(r o E0)’
             >-- (irule cpsb_idL >> 
                 rw[cpsb_def,id_dom,id_cod]) >>
             arw[] >> flip_tac >> arw[] >> 
             rw[id_eq_eq] >> flip_tac >> arw[] >>
             rpt strip_tac >> arw[] >>
             flip_tac >> irule cpsb_idL >> 
             rw[cpsb_def,id_dom,id_cod]) 
         >-- (qby_tac ‘ε10 @ id(r o E0) = ε10’ 
             >-- (irule cpsb_idR >>
                 arw[cpsb_def,id_dom,id_cod]) >>
             arw[id_eq_eq] >> rpt strip_tac >> arw[] >>
             flip_tac >> irule cpsb_idR >>
             arw[cpsb_def,id_dom,id_cod]) >>
         arw[id_eq_eq] >> 
         qby_tac ‘ε20 @ id(r o E0) = ε20’
         >-- (irule cpsb_idR >> 
             rw[cpsb_def,id_dom,id_cod] >>
             arw[]) >>
         arw[] >> flip_tac >> arw[] >> flip_tac >>
         rpt strip_tac >> arw[] >> flip_tac >>
         irule cpsb_idR >> rw[id_cod,id_dom,cpsb_def]) >>
     arw[] >>
     qby_tac ‘g = id(r o E1)’ 
     >-- (first_x_assum irule >> fs[cpsb_def,id_cod]) >>
     arw[] >> flip_tac >> arw[] >> flip_tac >>
     qby_tac ‘id((r o E1)) @ id(r o E1) = id(r o E1)’ 
     >-- (irule cpsb_idL >> arw[cpsb_def,id_dom,id_cod]) >>
     arw[] >> arw[id_eq_eq] >> flip_tac >> arw[] >>
     flip_tac >> rpt strip_tac >> arw[] >>
     flip_tac >> irule cpsb_idL >>
     arw[cpsb_def,id_cod,id_dom]) >> 
 assume_tac E_def >>
 qsspecl_then [‘coPa(0f, 1f)’,‘coPa(0f, 1f)’,‘ε1’,‘ε2’,
               ‘ε10’,‘ε20’] assume_tac isPo_unique >>
 rfs[] >> 
 strip_tac >>
 first_x_assum (qsspecl_then [‘i' o f’] strip_assume_tac) 
 >-- (disj1_tac >>
     qby_tac ‘j o i' o f = j o ε10’
     >-- arw[] >>
     pop_assum mp_tac >> arw[GSYM o_assoc,IdL]) 
 >-- (disj2_tac >> disj1_tac >>
     qby_tac ‘j o i' o f = j o ε20’
     >-- arw[] >>
     pop_assum mp_tac >> arw[GSYM o_assoc,IdL]) 
 >-- (disj2_tac >> disj2_tac >> disj1_tac >>
     qby_tac ‘j o i' o f = j o id(r o E0)’
     >-- arw[] >>
     pop_assum mp_tac >> arw[GSYM o_assoc,IdL] >>
     rw[GSYM id_o] >> strip_tac >> arw[] >>
     rw[id_eq_eq] >> 
     qby_tac ‘j o ε10 o 0f = ε1 o 0f’
     >-- arw[GSYM o_assoc] >>
     pop_assum mp_tac >> arw[GSYM dom_def]) >>
 rpt disj2_tac >>
 qby_tac ‘j o i' o f = j o id(r o E1)’ 
 >-- arw[] >>
 pop_assum mp_tac >> arw[GSYM o_assoc,IdL] >>
 rw[GSYM id_o] >> strip_tac >> arw[] >>
 rw[id_eq_eq] >> 
 qby_tac ‘j o ε10 o 1f = ε1 o 1f’
 >-- arw[GSYM o_assoc] >>
 pop_assum mp_tac >> arw[GSYM cod_def])
(form_goal 
“(!f:2->E. dom(f) = dom(ε1) & dom(f) = dom(ε1) ==>
           ε1 @ f = ε1) & 
 (!f:2->E. dom(f) = dom(ε1) & dom(f) = dom(ε1) ==>
           f @ ε1 = ε1) &
 (!f:2->E. dom(f) = dom(ε1) & dom(f) = dom(ε1) ==>
           (!g. f @ g = ε1 <=> g = ε1) & 
 !f:2->E. 
  f = ε1 | f = ε2 | f = id(dom(ε1)) | f = id(cod(ε1))”));
*)



val E_ar = prove_store("E_ar",
e0
(strip_tac >> assume_tac E_ob >>
 qabbrev_tac ‘dom(ε1) = E0’ >>
 qabbrev_tac ‘cod(ε1) = E1’ >>
 fs[] >>
 assume_tac no_arrow_E10 >> rfs[] >>
 assume_tac E_ob >> rfs[] >> 
 assume_tac dom_e1_ne_cod_e1 >> rfs[] >>
 qby_tac ‘~(E1 = E0)’ 
 >-- (flip_tac >> arw[]) >> 
 qby_tac
 ‘!f:2->E. ~(dom(f) = cod(f)) ==> 
  dom(f) = E0 & cod(f) = E1’ 
 >-- (rpt strip_tac >> 
     first_assum
     (qsspecl_then [‘dom(f)’] strip_assume_tac)>>
     first_x_assum
     (qsspecl_then [‘cod(f)’] strip_assume_tac) (* 3 *)
     >-- (first_x_assum (qsspecl_then [‘f’] assume_tac) >>
         rfs[]) 
     >-- fs[] >-- fs[] >>
     first_x_assum (qsspecl_then [‘f’] assume_tac) >> 
     rfs[]) >> 
 assume_tac (GSYM e1_e2_same_dom) >> rfs[] >> 
 assume_tac (GSYM e1_e2_same_cod) >> rfs[] >> 
 qby_tac ‘?F:E->E.
 F o E0 = E0 & F o E1 = E1 & 
 F o ε1 = ε1 & 
 (!f. dom(f) = E0 & cod(f) = E1 & ~(f = ε1) ==> 
      F o f = ε2) &
 (!f. dom(f) = E0 & cod(f) = E0 ==> F o f = id(E0)) &
 (!f. dom(f) = E1 & cod(f) = E1 ==> F o f = id(E1))’
 >--

 (qsuff_tac
 ‘?(cf : fun(E, E)).
        !(a : fun(2, E))  (b : fun(2, E)).
          a = ε1 & b = ε1 |
          dom(a) = E0 & cod(a) = E0 & b = id(E0) |
          dom(a) = E1 & cod(a) = E1 & b = id(E1) |
          ~(a = ε1) & dom(a) = E0 & cod(a) = E1 & b = ε2 <=> cf o a = b’ 
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qby_tac ‘cf o E0 = E0’ 
     >-- (irule $ iffLR id_eq_eq >>
         rw[id_o] >> arw[] >>
         rw[id_dom,id_cod]) >>
     qby_tac ‘cf o E1 = E1’ 
     >-- (irule $ iffLR id_eq_eq >>
         rw[id_o] >> arw[] >>
         rw[id_dom,id_cod]) >> arw[] >>
     rw[id_eq_eq] >> arw[] >> 
     assume_tac E_ar_ne >> rfs[] >>
     flip_tac >> arw[] >> flip_tac >>
     rpt strip_tac  >> arw[]) >>
 match_mp_tac
 (CC5 |> qspecl [‘E’,‘E’] 
 |> fVar_sInst_th “R(f:2->E,g:2->E)”
    “(f = ε1 & g = ε1) | 
     (dom(f) = E0 & cod(f) = E0 & g = id(E0)) |
     (dom(f) = E1 & cod(f) = E1 & g = id(E1)) |
     (~(f = ε1) & dom(f) = E0 & cod(f) = E1 & g = ε2)”) >>
 qby_tac ‘!f:2->E. dom(f) = E0 & cod(f) = E0 | 
 dom(f) = E1 & cod(f) = E1 |
 dom(f) = E0 & cod(f) = E1’
 >-- (strip_tac >>   
     qcases ‘dom(f) = cod(f)’ (* 2 *)
     >-- (first_x_assum 
         (qsspecl_then [‘dom(f)’] assume_tac) >>
         fs[] >> rfs[]) >>
     first_x_assum drule >> arw[]) >>
 strip_tac (* 2 *)
 >-- (strip_tac >> 
     first_x_assum (qsspecl_then [‘f’] strip_assume_tac) 
     (* 3 *)
     >-- (arw[] >> 
         qby_tac ‘~(f = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         uex_tac >> qexists_tac ‘id(E0)’ >> rw[]) 
     >-- (arw[] >> 
         qby_tac ‘~(f = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         uex_tac >> qexists_tac ‘id(E1)’ >> rw[]) >>
     arw[] >> qcases ‘f = ε1’ >> arw[] (* 2 *)
     >-- (uex_tac >> qexists_tac ‘ε1’ >> rw[]) >>
     uex_tac >> qexists_tac ‘ε2’ >> rw[]) >>
 qby_tac
 ‘!Eo:1->E. ~(ε1 = id(Eo))’ 
 >-- (strip_tac >> irule dom_cod_ne_ne_id >> arw[]) >>
 qby_tac
 ‘!Eo:1->E. ~(ε2 = id(Eo))’ 
 >-- (strip_tac >> irule dom_cod_ne_ne_id >> arw[]) >>
 strip_tac (* 2 *)
 >-- (rw[id_dom,id_cod,id_eq_eq] >>  
     flip_tac >> arw[] >> flip_tac >>
     rpt gen_tac >>
     first_x_assum (qsspecl_then [‘f’] assume_tac) >>
     pop_assum strip_assume_tac (* 3 *)
     >-- (arw[] >> 
         qby_tac ‘~(f = ε1)’ >-- (ccontra_tac >> fs[]) >>
         arw[] >> strip_tac >> arw[id_dom,id_cod]) 
     >-- (arw[] >>
         qby_tac ‘~(f = ε1)’ >-- (ccontra_tac >> fs[]) >>
         arw[] >> strip_tac >> arw[id_dom,id_cod]) >>
     arw[] >> qcases ‘f = ε1’ >> arw[] (* 2 *)
     >> strip_tac >> arw[]) >>
 qby_tac 
 ‘!f:2->E. dom(f) = E1 ==> cod(f) = E1’ 
 >-- (rpt strip_tac >>
     first_x_assum (qsspecl_then [‘f’] assume_tac) >>
     fs[] >> rfs[]) >>
 rpt gen_tac >>
 qpick_x_assum ‘!(f : fun(2, E)).
               dom(f) = E0 & cod(f) = E0 |
               dom(f) = E1 & cod(f) = E1 | dom(f) = E0 & cod(f) = E1’ assume_tac >>
 first_assum (qsspecl_then [‘f’] assume_tac) >>
 pop_assum strip_assume_tac (* 3 *)
 >-- (arw[] >> strip_tac >>
     drule $ iffLR cpsb_def >>
     rfs[] >> 
     last_x_assum (qsspecl_then [‘cod(g)’] assume_tac) >>
     pop_assum strip_assume_tac (* 2 *)
     >-- (arw[] >>  
         drule oa_dom_cod >> arw[] >>
         rfs[] >> 
         qby_tac ‘~(g @ f = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         qby_tac ‘~(f = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         qby_tac ‘~(g = ε1)’ 
         >-- (ccontra_tac >> fs[]) >> arw[] >>
         rpt strip_tac >> flip_tac >>arw[] >>
         irule cpsb_idL >> rw[cpsb_def,id_dom,id_cod]) >>
     arw[] >> drule oa_dom_cod >> rfs[] >>
     qby_tac ‘~(f = ε1)’ >-- (ccontra_tac >> fs[]) >>
     arw[] >>
     last_x_assum (qsspecl_then [‘f’] assume_tac) >> 
     rfs[] >> qcases ‘g = ε1’ >> arw[] (* 2 *)
     >-- (strip_tac >> arw[] >> 
         rpt strip_tac >> arw[] >> flip_tac >>
         irule cpsb_idR >> arw[cpsb_def,id_cod]) >>
     rpt strip_tac >> arw[] >> flip_tac >>
     irule cpsb_idR >> arw[cpsb_def,id_cod])
 >-- (arw[] >> strip_tac >>
     drule $ iffLR cpsb_def >> rfs[] >>
     qby_tac ‘cod(g) = E1’ >--
     (last_x_assum (qsspecl_then [‘cod(g)’] assume_tac) >>
     qpick_x_assum ‘!f.~(dom(f) = E1 & cod(f) = E0)’
     assume_tac >>
     first_x_assum (qsspecl_then [‘g’] assume_tac) >>
     rfs[]) >>
     arw[] >> drule oa_dom_cod >> arw[] >>
     qby_tac ‘~(g @ f = ε1)’ 
     >-- (ccontra_tac >> fs[]) >> arw[] >>
     qby_tac ‘~(f = ε1)’ >-- (ccontra_tac >> fs[]) >>
     qby_tac ‘~(g = ε1)’ >-- (ccontra_tac >> fs[]) >> 
     arw[] >> rpt strip_tac >> arw[] >>
     flip_tac >> irule cpsb_idL >>
     arw[cpsb_def,id_cod,id_dom]) >>
 arw[] >> strip_tac >>
 drule $ iffLR cpsb_def >> rfs[] >>
 qby_tac ‘cod(g) = E1’ >--
     (last_x_assum (qsspecl_then [‘cod(g)’] assume_tac) >>
     qpick_x_assum ‘!f.~(dom(f) = E1 & cod(f) = E0)’
     assume_tac >>
     first_x_assum (qsspecl_then [‘g’] assume_tac) >>
     rfs[]) >>
 arw[] >> drule oa_dom_cod >>
 arw[] >> qby_tac ‘~(g = ε1)’ >-- (ccontra_tac >> fs[]) >> 
 arw[] >>
 qpick_x_assum ‘!f:2->E. dom(f) = E1 & cod(f) = E1 ==>
           (!g. f @ g = ε1 <=> g = ε1)’ assume_tac >> 
 first_x_assum (qsspecl_then [‘g’] assume_tac) >>
 rfs[] >>
 qcases ‘f = ε1’ >> arw[] (* 2 *)
 >-- (rpt strip_tac >> arw[] >>
     flip_tac >> irule cpsb_idL >>
     arw[cpsb_def,id_dom,id_cod]) >>
 rpt strip_tac >> arw[] >> flip_tac >>
 irule cpsb_idL >> arw[cpsb_def,id_dom,id_cod]) >> 
 pop_assum strip_assume_tac >>
 qby_tac ‘idem(F)’ 
 >-- (rw[idem_def] >> irule $ iffLR fun_ext >>
     strip_tac >> rw[o_assoc] >>
     qsspecl_then [‘a’] assume_tac E_ar_cases0 >>
     pop_assum strip_assume_tac (* 3 *)
     >-- (rfs[] >>
         qby_tac ‘F o a = id(E0)’ 
         >-- (first_x_assum irule >> arw[]) >>
         arw[] >> first_x_assum irule >>
         rw[id_dom,id_cod] ) 
     >-- (rfs[] >>
         qby_tac ‘F o a = id(E1)’ 
         >-- (first_x_assum irule >> arw[]) >>
         arw[] >> first_x_assum irule >>
         rw[id_dom,id_cod]) 
     >-- (rfs[] >>
         qcases ‘a = ε1’ >> arw[] >>
         qby_tac ‘F o a = ε2’ 
         >-- (first_x_assum irule >> arw[]) >>
         arw[] >>
         first_x_assum irule >> arw[] >>
         rw[GSYM e1_ne_e2])) >>
 drule new_Thm1 >> 
 qsspecl_then [‘F’,‘Id(E)’] assume_tac isEq_ex >>
 pop_assum (x_choosel_then ["sE","i"] assume_tac) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qabbrev_tac ‘r o ε1 = ε10’ >>
 qby_tac ‘i o ε10 = ε1’ 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     arw[GSYM o_assoc]) >>
 qabbrev_tac ‘r o ε2 = ε20’ >>
 qby_tac ‘i o ε20 = ε2’ 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >>
     arw[GSYM o_assoc] >> first_x_assum irule >>
     rw[GSYM e1_ne_e2,e1_e2_same_dom,e1_e2_same_cod] >>
     arw[GSYM e1_e2_same_cod,GSYM e1_e2_same_dom]) >> 
 qby_tac ‘dom(ε10) = r o E0’ 
 >-- (qpick_x_assum ‘r o ε1 = ε10’ (assume_tac o GSYM) >>
     arw[dom_o]) >>
 qby_tac ‘cod(ε10) = r o E1’ 
 >-- (qpick_x_assum ‘r o ε1 = ε10’ (assume_tac o GSYM) >>
     arw[cod_o]) >>
 qby_tac ‘dom(ε20) = r o E0’ 
 >-- (qpick_x_assum ‘r o ε2 = ε20’ (assume_tac o GSYM) >>
     arw[dom_o]) >>
 qby_tac ‘cod(ε20) = r o E1’ 
 >-- (qpick_x_assum ‘r o ε2 = ε20’ (assume_tac o GSYM) >>
     arw[cod_o]) >> 
 drule isEq_Mono >>
 qby_tac 
 ‘!f:2->E. F o f = ε1 | F o f = ε2 | 
           F o f = id(E0) | F o f = id(E1)’ 
 >-- (strip_tac >>
     qsspecl_then [‘f’] assume_tac E_ar_cases0 >>
     pop_assum strip_assume_tac (* 3 *)
     >-- (rfs[] >>
         disj2_tac >> disj2_tac >> disj1_tac >>
         first_x_assum irule >> arw[])
     >-- (rfs[] >>
         rpt disj2_tac >> first_x_assum irule >> arw[]) >>
     rfs[] >> qcases ‘f = ε1’ >> arw[] >>
     disj2_tac >> disj1_tac >> first_x_assum irule >>
     arw[]) >> 
 qby_tac ‘!f:2->sE. i o f = ε1 | i o f = ε2 | i o f = id(E0) | i o f = id(E1)’ 
 >-- (strip_tac >>
     first_x_assum (qsspecl_then [‘F o i o f’] assume_tac)>>
     drule $ iffLR idem_def >> 
     drule $ iffLR isEq_def >> fs[GSYM o_assoc,IdL]) >>
 qby_tac ‘!f:2->sE. f = ε10 | f = ε20 | f = id(r o E0) |
           f = id(r o E1)’
 >-- (strip_tac >>
     first_x_assum (qsspecl_then [‘f’] strip_assume_tac) 
     (* 4 *)
     >-- (fs[Mono_def] >> disj1_tac >> 
         first_x_assum irule >> arw[]) 
     >-- (disj2_tac >> disj1_tac >>
         fs[Mono_def] >> first_x_assum irule >> arw[]) 
     >-- (disj2_tac >> disj2_tac >> disj1_tac >>
         fs[Mono_def] >> first_x_assum irule >>
         arw[] >> rw[GSYM id_o,id_eq_eq] >>
         arw[GSYM o_assoc]) >>
     rpt disj2_tac >> fs[Mono_def] >>
     first_x_assum irule >> arw[GSYM id_o,id_eq_eq] >>
     arw[GSYM o_assoc]) >>
 qby_tac ‘isPo(coPa(0f,1f),coPa(0f,1f),ε10,ε20)’  
 >-- (rw[isPo_def] >>
     qby_tac ‘ε10 o coPa(0f, 1f) = ε20 o coPa(0f, 1f)’ 
     >-- (fs[Mono_def] >> first_x_assum irule >>
         arw[GSYM o_assoc] >>
         assume_tac E_def >> fs[isPo_def]) >> arw[] >>
     rpt strip_tac >>
     qsuff_tac ‘?(a : fun(sE, A)). a o ε10 = u & 
                 a o ε20 = v’
     >-- (strip_tac >> uex_tac >> qexists_tac ‘a’ >> 
         arw[] >>
         rpt strip_tac >> irule $ iffLR fun_ext >>
         strip_tac >>
         first_x_assum (qsspecl_then [‘a''’] assume_tac) >>
         pop_assum strip_assume_tac >> arw[] (* 2 *)
         >-- (rw[GSYM id_o,id_eq_eq] >>
             qby_tac ‘a o ε10 = a' o ε10’ >-- arw[] >>
             qby_tac ‘a o ε10 o 0f = a' o ε10 o 0f’ 
             >-- arw[GSYM o_assoc] >>
             pop_assum mp_tac >> rw[GSYM dom_def] >>
             arw[] >> strip_tac >> arw[]) >>
         rw[GSYM id_o,id_eq_eq] >>
         qby_tac ‘a o ε10 = a' o ε10’ >-- arw[] >>
         qby_tac ‘a o ε10 o 1f = a' o ε10 o 1f’ 
         >-- arw[GSYM o_assoc] >>
         pop_assum mp_tac >> rw[GSYM cod_def] >>
         arw[] >> strip_tac >> arw[]) >>
     qsuff_tac 
     ‘?(cf : fun(sE, A)).
        !(a : fun(2, sE))  (b : fun(2, A)).
          a = ε10 & b = u |
          a = ε20 & b = v |
          a = id(r o E0) & b = id(dom(u)) |
          a = id(r o E1) & b = id(cod(u)) <=> cf o a = b’
     >-- (strip_tac >> qexists_tac ‘cf’ >>
         pop_assum (assume_tac o GSYM) >> arw[]) >>
     match_mp_tac
     (CC5 |> qspecl [‘sE’,‘A’] 
     |> fVar_sInst_th “R(f:2->sE, g:2->A)”
        “(f = ε10:2->sE & g:2->A = u) |
         (f = ε20 & g = v) |
         (f = id(r o E0) & g = id(dom(u))) |
         (f = id(r o E1) & g = id(cod(u)))”) >>
     qby_tac ‘~(ε10 = ε20)’ 
     >-- (ccontra_tac >>
         qsuff_tac ‘ε1 = ε2’ >-- rw[e1_ne_e2] >>
         qpick_x_assum ‘i o ε10 = ε1’
         (assume_tac o GSYM) >> 
         qpick_x_assum ‘i o ε20 = ε2’
         (assume_tac o GSYM) >> arw[]) >>
     qby_tac ‘~(r o E0 = r o E1)’ 
     >-- (ccontra_tac >>
         qsuff_tac ‘E0 = E1’ >-- arw[] >>
         qpick_x_assum ‘~(E0 = E1)’ (K all_tac) >>
         qby_tac ‘i o r o E0 = i o r o E1’  
         >-- arw[] >>
         pop_assum mp_tac >> arw[GSYM o_assoc]) >>
     qby_tac ‘~(ε10 = id(r o E0))’ 
     >-- (ccontra_tac >>
         qby_tac ‘i o ε10 = i o id(r o E0)’ 
         >-- (qpick_x_assum ‘i o ε10 = ε1’ (K all_tac) >>
             arw[]) >>
         pop_assum mp_tac >>
         rw[GSYM id_o] >> arw[GSYM o_assoc] >>  
         assume_tac E_ar_ne >> rfs[]) >>
     qby_tac ‘~(ε10 = id(r o E1))’ 
     >-- (ccontra_tac >>
         qby_tac ‘i o ε10 = i o id(r o E1)’ 
         >-- (qpick_x_assum ‘i o ε10 = ε1’ (K all_tac) >>
             arw[]) >>
         pop_assum mp_tac >>
         rw[GSYM id_o] >> arw[GSYM o_assoc] >>  
         assume_tac E_ar_ne >> rfs[]) >>
     qby_tac ‘~(ε20 = id(r o E0))’ 
     >-- (ccontra_tac >>
         qby_tac ‘i o ε20 = i o id(r o E0)’ 
         >-- (qpick_x_assum ‘i o ε20 = ε2’ (K all_tac) >>
             arw[]) >>
         pop_assum mp_tac >>
         rw[GSYM id_o] >> arw[GSYM o_assoc] >>  
         assume_tac E_ar_ne >> rfs[]) >>
     qby_tac ‘~(ε20 = id(r o E1))’ 
     >-- (ccontra_tac >>
         qby_tac ‘i o ε20 = i o id(r o E1)’ 
         >-- (qpick_x_assum ‘i o ε20 = ε2’ (K all_tac) >>
             arw[]) >>
         pop_assum mp_tac >>
         rw[GSYM id_o] >> arw[GSYM o_assoc] >>  
         assume_tac E_ar_ne >> rfs[]) >>
     strip_tac (* 2 *)
     >-- (strip_tac >>
         first_x_assum (qsspecl_then [‘f’] assume_tac) >>
         pop_assum strip_assume_tac >> arw[] (* 4 *)
         >-- (uex_tac  >> qexists_tac ‘u’ >> rw[]) 
         >-- (qpick_x_assum ‘~(ε10 = ε20)’ 
              (assume_tac o GSYM) >> arw[] >>
              uex_tac  >> qexists_tac ‘v’ >> rw[]) 
         >-- (flip_tac >> arw[] >> flip_tac >>
             rw[id_eq_eq] >> arw[] >>
             uex_tac >> qexists_tac ‘id(dom(u))’ >> rw[])>>
         flip_tac >> arw[] >> rw[id_eq_eq] >>
         arw[] >> uex_tac >> qexists_tac ‘id(cod(u))’ >>
         rw[] >> rpt strip_tac >> arw[]) >>
     qby_tac ‘dom(u) = dom(v) & cod(u) = cod(v)’
     >-- (qby_tac 
         ‘u o coPa(0f, 1f) o i1(1,1) = 
          v o coPa(0f, 1f) o i1(1,1) & 
          u o coPa(0f, 1f) o i2(1,1) =
          v o coPa(0f, 1f) o i2(1,1)’ 
          >-- arw[GSYM o_assoc] >>
          pop_assum mp_tac >> rw[i12_of_coPa] >>
          rw[GSYM dom_def,GSYM cod_def]) >>
     pop_assum strip_assume_tac >>
     strip_tac (* 2 *)
     >-- (rpt gen_tac >> rw[id_eq_eq] >> strip_tac >>
         arw[id_dom,id_cod] >> rpt strip_tac >> arw[]) >>
     qby_tac ‘!g.dom(g) = r o E1 ==> g = id(r o E1)’ 
     >-- (rpt strip_tac >> 
         first_x_assum (qsspecl_then [‘g’] assume_tac) >>
         pop_assum strip_assume_tac (* 4 *) >> arw[] (* 3 *)
         >-- (fs[] >> qpick_x_assum ‘r o E1 = r o E0’
             (assume_tac o GSYM) >> fs[]) 
         >-- (fs[] >> qpick_x_assum ‘r o E1 = r o E0’
             (assume_tac o GSYM) >> fs[]) >>
         fs[id_dom,id_cod]) >> 
     qpick_x_assum ‘!(f : fun(2, sE)).
               f = ε10 | f = ε20 | f = id(r o E0) | f = id(r o E1)’ assume_tac >> 
     rpt gen_tac >> strip_tac >>
     first_assum (qsspecl_then [‘f’] strip_assume_tac) 
     (* 4 *)
     >-- (arw[] >>
         qby_tac ‘g = id(r o E1)’ 
         >-- (first_x_assum irule >> fs[cpsb_def]) >>
         arw[] >> flip_tac >> arw[] >> flip_tac >>
         qby_tac ‘id((r o E1)) @ ε10 = ε10’ 
         >-- (irule cpsb_idL >> arw[cpsb_def,id_dom]) >>
         arw[] >> arw[id_eq_eq] >> flip_tac >> arw[] >>
         flip_tac >> rpt strip_tac >> arw[] >>
         flip_tac >> irule cpsb_idL >>
         arw[cpsb_def,id_cod,id_dom]) 
     >-- (arw[] >>
         qby_tac ‘g = id(r o E1)’ 
         >-- (first_x_assum irule >> fs[cpsb_def]) >>
         arw[] >> flip_tac >> arw[] >> flip_tac >>
         qby_tac ‘id((r o E1)) @ ε20 = ε20’ 
         >-- (irule cpsb_idL >> arw[cpsb_def,id_dom]) >>
         arw[] >> arw[id_eq_eq] >> flip_tac >> arw[] >>
         flip_tac >> rpt strip_tac >> arw[] >>
         flip_tac >> irule cpsb_idL >>
         arw[cpsb_def,id_cod,id_dom]) 
     >-- (arw[] >> flip_tac >> arw[] >> flip_tac >>
         qby_tac ‘g = id(r o E0) | g = ε10 | g = ε20’ 
         >-- (first_x_assum 
             (qsspecl_then [‘g’] strip_assume_tac) >>
             arw[] >> 
             fs[cpsb_def,id_dom,id_cod]) >> 
         pop_assum strip_assume_tac >> arw[] (* 3 *)
         >-- (qby_tac
             ‘id(r o E0) @ id(r o E0) = id(r o E0)’
             >-- (irule cpsb_idL >> 
                 rw[cpsb_def,id_dom,id_cod]) >>
             arw[] >> flip_tac >> arw[] >> 
             rw[id_eq_eq] >> flip_tac >> arw[] >>
             rpt strip_tac >> arw[] >>
             flip_tac >> irule cpsb_idL >> 
             rw[cpsb_def,id_dom,id_cod]) 
         >-- (qby_tac ‘ε10 @ id(r o E0) = ε10’ 
             >-- (irule cpsb_idR >>
                 arw[cpsb_def,id_dom,id_cod]) >>
             arw[id_eq_eq] >> rpt strip_tac >> arw[] >>
             flip_tac >> irule cpsb_idR >>
             arw[cpsb_def,id_dom,id_cod]) >>
         arw[id_eq_eq] >> 
         qby_tac ‘ε20 @ id(r o E0) = ε20’
         >-- (irule cpsb_idR >> 
             rw[cpsb_def,id_dom,id_cod] >>
             arw[]) >>
         arw[] >> flip_tac >> arw[] >> flip_tac >>
         rpt strip_tac >> arw[] >> flip_tac >>
         irule cpsb_idR >> rw[id_cod,id_dom,cpsb_def]) >>
     arw[] >>
     qby_tac ‘g = id(r o E1)’ 
     >-- (first_x_assum irule >> fs[cpsb_def,id_cod]) >>
     arw[] >> flip_tac >> arw[] >> flip_tac >>
     qby_tac ‘id((r o E1)) @ id(r o E1) = id(r o E1)’ 
     >-- (irule cpsb_idL >> arw[cpsb_def,id_dom,id_cod]) >>
     arw[] >> arw[id_eq_eq] >> flip_tac >> arw[] >>
     flip_tac >> rpt strip_tac >> arw[] >>
     flip_tac >> irule cpsb_idL >>
     arw[cpsb_def,id_cod,id_dom]) >> 
 assume_tac E_def >>
 qsspecl_then [‘coPa(0f, 1f)’,‘coPa(0f, 1f)’,‘ε1’,‘ε2’,
               ‘ε10’,‘ε20’] assume_tac isPo_unique >>
 rfs[] >> 
 strip_tac >>
 first_x_assum (qsspecl_then [‘i' o f’] strip_assume_tac) 
 >-- (disj1_tac >>
     qby_tac ‘j o i' o f = j o ε10’
     >-- arw[] >>
     pop_assum mp_tac >> arw[GSYM o_assoc,IdL]) 
 >-- (disj2_tac >> disj1_tac >>
     qby_tac ‘j o i' o f = j o ε20’
     >-- arw[] >>
     pop_assum mp_tac >> arw[GSYM o_assoc,IdL]) 
 >-- (disj2_tac >> disj2_tac >> disj1_tac >>
     qby_tac ‘j o i' o f = j o id(r o E0)’
     >-- arw[] >>
     pop_assum mp_tac >> arw[GSYM o_assoc,IdL] >>
     rw[GSYM id_o] >> strip_tac >> arw[] >>
     rw[id_eq_eq] >> 
     qby_tac ‘j o ε10 o 0f = ε1 o 0f’
     >-- arw[GSYM o_assoc] >>
     pop_assum mp_tac >> arw[GSYM dom_def]) >>
 rpt disj2_tac >>
 qby_tac ‘j o i' o f = j o id(r o E1)’ 
 >-- arw[] >>
 pop_assum mp_tac >> arw[GSYM o_assoc,IdL] >>
 rw[GSYM id_o] >> strip_tac >> arw[] >>
 rw[id_eq_eq] >> 
 qby_tac ‘j o ε10 o 1f = ε1 o 1f’
 >-- arw[GSYM o_assoc] >>
 pop_assum mp_tac >> arw[GSYM cod_def])
(form_goal 
“(!f:2->E. dom(f) = dom(ε1) & cod(f) = dom(ε1) ==>
           (!g. g @ f = ε1 <=> g = ε1)) & 
 (!f:2->E. dom(f) = cod(ε1) & cod(f) = cod(ε1) ==>
           (!g. f @ g = ε1 <=> g = ε1)) ==>
 !f:2->E. 
  f = ε1 | f = ε2 | f = id(dom(ε1)) | f = id(cod(ε1))”));


(*
val E_ar = prove_store ("E_ar",
e0
(rpt strip_tac >>
 qby_tac ‘?F:E->E. ’
 )
(form_goal “!f:2->E. f = id(dom(ε1)) | f = id(cod(ε1)) | f = ε1 | f = ε2 ”));
*)

val acyclic_def = qdefine_psym("acyclic",[‘d0:C1->C0’,‘d1:C1->C0’,‘i:C0->C1’,‘gamma:Pbo(d1:C1->C0,d0:C1->C0)->C1’])
‘!f g:1->C1. d0 o f = d1 o g & d1 o f = d0 o g ==> f = g’


val acyclic_def = proved_th $
e0
cheat
(form_goal “
!C0 C1 d0:C1->C0 d1 i gamma. acyclic(d0,d1,i,gamma) <=> Icat(d0, d1, i, gamma) & (!f g:1->C1. d0 o f = d1 o g & d1 o f = d0 o g ==> f = g)”)




val acyclic_alt1 = prove_store("acyclic_alt1",
e0
(rpt strip_tac >>
 drule $ iffLR acyclic_def >> pop_assum strip_assume_tac >>
 first_assum irule >> 
 drule $ iffLR Icat_def >> arw[GSYM o_assoc] >>
 rw[IdL] >>
 qby_tac ‘f = g’ >-- (first_assum irule >> arw[]) >> arw[] >> fs[])
(form_goal “!C0 C1 d0:C1->C0 d1 i gamma. acyclic(d0,d1,i,gamma) ==> 
 !f g:1->C1. d0 o f = d1 o g & d1 o f = d0 o g ==> f = i o d0 o f”));

val acyclic_alt2 = prove_store("acyclic_alt2",
e0
()
(form_goal
 “!C0 C1 d0:C1->C0 d1 i gamma. Icat(d0,d1,i,gamma) & 
  (!f g:1->C1. d0 o f = d1 o g & d1 o f = d0 o g ==> f = i o d0 o f) ==> 
  !h:1->C1. d0 o h = d1 o h ==> ?”));

val oneway_def = qdefine_psym("oneway",[‘A’])
‘!f:2->A. dom(f) = cod(f) ==> f = id(dom(f))’

val Eo0_def = qdefine_fsym("Eo0",[]) ‘dom(ε1)’;
val Eo1_def = qdefine_fsym("Eo1",[]) ‘cod(ε1)’;

val new_Coro1 = prove_store("new_Coro1",
e0
(rpt strip_tac >>
 qabbrev_tac ‘dom(f) = A1’ >>
 qabbrev_tac ‘cod(f) = A2’ >>
 qsuff_tac
 ‘?(cf : fun(A, E)).
        !(a : fun(2, A))  (b : fun(2, E)).
          (?(k : fun(2, A)). dom(k) = cod(a) & cod(k) = A1) & b = id(Eo0) |
          (!(k : fun(2, A)). ~(dom(k) = cod(a) & cod(k) = A1)) &
          (?(k : fun(2, A)). dom(k) = dom(a) & cod(k) = A1) &
          ~(a = f) & b = ε1 |
          a = f & b = ε2 |
          (!(k : fun(2, A)). ~(dom(k) = dom(a) & cod(k) = A1)) &
          b = id(Eo1) <=> cf o a = b’
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     strip_tac >> qcases ‘g = f’ >> arw[] >>
     ccontra_tac >> pop_assum strip_assume_tac (* 3 *)
     >-- fs[E_ar_ne]
     >-- fs[GSYM E_ar_ne] >> fs[E_ar_ne]) >>
 match_mp_tac
 (CC5 |> qspecl [‘A’,‘E’] 
 |> fVar_sInst_th “R(g:2->A,h:2->E)”
 “((?k. dom(k) = cod(g:2->A) & cod(k) = A1) & h = id(Eo0)) |
  ((!k. ~(dom(k) = cod(g) & cod(k) = A1)) & 
  (?k. dom(k) = dom(g) & cod(k) = A1) & ~(g = f) & h = ε1) | 
  (g = f & h = ε2) |
  ((!k. ~(dom(k) = dom(g) & cod(k) = A1)) & h = id(Eo1))”) >>
 qby_tac ‘!g:2-> A. (?(k : fun(2, A)). dom(k) = dom(g) & cod(k) = A1) <=>
                    ~(!(k : fun(2, A)). ~(dom(k) = cod(g) & cod(k) = A1))’
 >-- cheat >>
 qby_tac ‘!g. (!(k : fun(2, A)). (dom(k) = cod(g) & cod(k) = A1)) ==>
              ?k1. dom(k1) = dom(g) & cod(k1) = A1’
 >-- cheat >>
 qby_tac ‘!g. (!(k : fun(2, A)). ~(dom(k) = dom(g) & cod(k) = A1)) ==>
          (!(k : fun(2, A)). ~(dom(k) = cod(g) & cod(k) = A1))’
 >-- cheat >> 
 strip_tac (* 2 *)
 >-- strip_tac >> qcases ‘(?k. dom(k) = cod(f':2->A) & cod(k) = A1)’ (* 2 *)
     >-- arw[] >> uex_tac >>
         qby_tac
         ‘!g. ~((!(k : fun(2, A)). ~(dom(k) = cod(f') & cod(k) = A1)) &
               ~(!(k : fun(2, A)). ~(dom(k) = cod(f') & cod(k) = A1)) &
               ~(f' = f) & g = ε1 )’ 
         >-- (strip_tac >> ccontra_tac >> fs[]) >> arw[] >>
         qby_tac ‘~(!(k : fun(2, A)). ~(dom(k) = dom(f') & cod(k) = A1))’ 
         >-- (ccontra_tac >> first_x_assum drule >> fs[]) >> arw[] >>
         qby_tac ‘~(f' = f)’ 
         >-- 
             
         
         
         )
(form_goal
 “!A. oneway(A) ==> !f:2->A. ?δ:A->E. 
  !g:2->A. δ o g = ε2 <=> g = f”));


val neg_conj_distr = proved_th $
e0
cheat
(form_goal “~(A & B) <=> (~A | ~ B)”)

val new_Coro1 = prove_store("new_Coro1",
e0
(rpt strip_tac >>
 qabbrev_tac ‘dom(f) = A1’ >>
 qabbrev_tac ‘cod(f) = A2’ >>
 qsuff_tac
 ‘?(cf : fun(A, E)).
        !(a : fun(2, A))  (b : fun(2, E)).
          (?(k : fun(2, A)). dom(k) = cod(a) & cod(k) = A1) & b = id(Eo0) |
          (!(k : fun(2, A)). ~(dom(k) = cod(a) & cod(k) = A1)) &
          (?(k : fun(2, A)). dom(k) = dom(a) & cod(k) = A1) &
           ~(a = f) & b = ε1 |
          a = f & b = ε2 |
          (!(k : fun(2, A)). ~(dom(k) = dom(a) & cod(k) = A1)) &
          b = id(Eo1) <=> cf o a = b’
 >-- (strip_tac >> qexists_tac ‘cf’ >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     strip_tac >> qcases ‘g = f’ >> arw[] >>
     ccontra_tac >> pop_assum strip_assume_tac (* 3 *)
     >-- fs[E_ar_ne]
     >-- fs[GSYM E_ar_ne] >> fs[E_ar_ne]) >>
 match_mp_tac
 (CC5 |> qspecl [‘A’,‘E’] 
 |> fVar_sInst_th “R(g:2->A,h:2->E)”
 “((?k. dom(k) = cod(g:2->A) & cod(k) = A1) &  h = id(Eo0)) |
  ((!k. ~(dom(k) = cod(g) & cod(k) = A1)) & 
  (?k. dom(k) = dom(g) & cod(k) = A1) &  ~(g = f) & h = ε1) | 
  (g = f & h = ε2) |
  ((!k. ~(dom(k) = dom(g) & cod(k) = A1)) & h = id(Eo1))”) >>
 qby_tac ‘!g:2-> A. (?(k : fun(2, A)). dom(k) = dom(g) & cod(k) = A1) <=>
                    ~(!(k : fun(2, A)). ~(dom(k) = dom(g) & cod(k) = A1))’
 >-- (strip_tac >> 
     assume_tac(exists_forall_dual |> qspecl [‘2’,‘A’]
     |> fVar_sInst_th “P(k:2->A)”
        “dom(k) = dom(g) & cod(k) = A1:1->A”) >> arw[]) >>
 qby_tac ‘!g k : fun(2, A). (dom(k) = cod(g) & cod(k) = A1) ==>
              ?k1. dom(k1) = dom(g) & cod(k1) = A1’
 >-- (rpt strip_tac >>
     qexists_tac ‘k @ g’ >> fs[GSYM cpsb_def] >>
     drule oa_dom_cod >> arw[]) >>
 qby_tac ‘!g. (!(k : fun(2, A)). ~(dom(k) = dom(g) & cod(k) = A1)) ==>
          (!(k : fun(2, A)). ~(dom(k) = cod(g) & cod(k) = A1))’
 >-- (rpt strip_tac >> ccontra_tac >>
     first_x_assum drule >> fs[] >>
     first_x_assum (qsspecl_then [‘k1’] assume_tac) >> rfs[]) >>  
 qby_tac 
 ‘!k. ~(dom(k) = A2 & cod(k) = A1)’
 >-- strip_tac >> fs[oneway_def] 
 strip_tac (* 2 *)
 >-- strip_tac >> qcases ‘(f' = f)’
     >-- (arw[] >> 
         qby_tac ‘~(!(k : fun(2, A)). ~(dom(k) = A1 & cod(k) = A1))’ 
         >-- (ccontra_tac >> 
             first_x_assum (qsspecl_then [‘id(A1)’] assume_tac) >>
             fs[id_dom,id_cod]) >> arw[] >>
         qby_tac ‘~()’
         uex_tac >> qexists_tac ‘ε2’ >> rw[]) >>
     arw[] >>
     qcases ‘(?k. dom(k) = cod(f':2->A) & cod(k) = A1)’ (* 2 *)
     >-- (arw[] >> pop_assum strip_assume_tac >>
         first_x_assum (qsspecl_then [‘f'’,‘k’] assume_tac) >>
         rfs[] >>
         qby_tac ‘~(!(k : fun(2, A)). ~(dom(k) = cod(f') & cod(k) = A1))’ 
         >-- (ccontra_tac >> first_x_assum drule >> fs[]) >> arw[] >>
         uex_tac >> qexists_tac ‘id(Eo0)’ >> rw[]) >>
     arw[] >> 




     qcases ‘(?k. dom(k) = cod(f':2->A) & cod(k) = A1) & ~(f' = f)’ (* 2 *)
     >-- (arw[] >> uex_tac >>
         qby_tac
         ‘!g. ~((!(k : fun(2, A)). ~(dom(k) = cod(f') & cod(k) = A1)) &
               ~(!(k : fun(2, A)). ~(dom(k) = cod(f') & cod(k) = A1)) 
               & g = ε1 )’ 
         >-- (strip_tac >> ccontra_tac >> fs[]) >> arw[] >>
         qby_tac ‘~(!(k : fun(2, A)). ~(dom(k) = dom(f') & cod(k) = A1))’ 
         >-- (ccontra_tac >> first_x_assum drule >> fs[]) >> arw[] >>
         qexists_tac ‘id(Eo0)’ >> rw[]) >>
     fs[neg_conj_distr] (* 2 *)
     >-- rw[GSYM neg_conj_distr] >> 
         qcases ‘(?k. dom(k) = dom(f':2->A) & cod(k) = A1)’
        (*2*) >-- 
         qby_tac ‘~(f' = f)’ 
         >-- ccontra_tac >>
             qsuff_tac ‘?(k : fun(2, A)). dom(k) = cod(f') & cod(k) = A1’
             >-- arw[] >>
             qpick_x_assum 
             ‘~(?(k : fun(2, A)). dom(k) = cod(f') & cod(k) = A1)’
             (K all_tac) >>
             arw[] >> 
         qcases ‘(?k. dom(k) = dom(f':2->A) & cod(k) = A1)’
             
         
         
         )
(form_goal
 “!A. oneway(A) ==> !f:2->A. ~(f = id(dom(f))) ==> ?δ:A->E. 
  !g:2->A. δ o g = ε2 <=> g = f”));

