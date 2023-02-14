(*facts about ultrafilters*)



val filter_def = qdefine_psym("filter",[‘L:mem(Pow(Pow(J)))’])
‘~EMPTY(J) & IN(Whole(J),L) & 
  (!X Y. IN(X,L) & IN(Y,L) ==> IN(Inter(X,Y),L)) & 
  (!X. IN(X,L) ==> !Y. SS(X,Y) ==> IN(Y,L))’


val ufilter_def = qdefine_psym("ufilter",[‘L:mem(Pow(Pow(J)))’])
‘filter(L) & 
 (!X. ~(IN(Compl(X),L)) <=> IN(X,L))’

val Inter_IN_filter = filter_def |> iffLR |> undisch |> conjE2
                                 |> conjE2 |> conjE1
                                 |> disch_all
                                 |> gen_all

val ufilter_filter = ufilter_def |> iffLR |> undisch |> conjE1
                                 |> disch_all |> gen_all

val Inter_IN_ufilter = prove_store("Inter_IN_ufilter",
e0
(rpt strip_tac >> drule ufilter_filter >>
 drule Inter_IN_filter >> first_x_assum irule >> arw[])
(form_goal “!J L:mem(Pow(Pow(J))). ufilter(L) ==>
 !X Y. IN(X,L) & IN(Y,L) ==> IN(Inter(X,Y),L)”));

val SS_IN_filter = filter_def |> iffLR |> undisch |> conjE2
                              |> conjE2 |> conjE2
                              |> disch_all
                              |> gen_all

val SS_IN_ufilter = prove_store("SS_IN_ufilter",
e0
(rpt strip_tac >> drule ufilter_filter >>
 drule SS_IN_filter >> first_x_assum drule >>
 first_x_assum drule >> arw[])
(form_goal “!J L:mem(Pow(Pow(J))). ufilter(L) ==>
 !X. IN(X,L) ==> !Y. SS(X,Y) ==> IN(Y,L)”))

val Whole_IN_filter = filter_def |> iffLR |> undisch |> conjE2
                                 |> conjE1
                                 |> disch_all |> gen_all
                                 |> store_as "Whole_IN_filter"

val Whole_IN_ufilter = prove_store("Whole_IN_ufilter",
e0
(rpt strip_tac >> drule ufilter_filter >> drule Whole_IN_filter >> arw[])
(form_goal “!J L:mem(Pow(Pow(J))). ufilter(L) ==> IN(Whole(J),L)”));

val Empty_NOTIN_UF = prove_store("Empty_NOTIN_UF",
e0
(rw[ufilter_def] >> rpt strip_tac >>
 first_x_assum (qsspecl_then [‘Whole(J)’] assume_tac) >>
 fs[Compl_Whole] >> drule Whole_IN_filter >> arw[])
(form_goal “!J L.ufilter(L) ==> ~IN(Empty(J),L)”));


val IN_UF_NONEMPTY = prove_store("IN_UF_NONEMPTY",
e0
(rpt strip_tac >> drule Empty_NOTIN_UF >> ccontra_tac >> fs[])
(form_goal “!J L.ufilter(L) ==> !X.IN(X,L) ==> ~(X = Empty(J))”));

val UFs_def = Thm_2_4' |> qtinst_thm [(‘A’,‘Pow(Pow(J))’)]
                      |> qfVar_prpl_th1 ("P",[‘a:mem(Pow(Pow(J)))’],‘ufilter(a:mem(Pow(Pow(J))))’)    |> set_spec (rastt "Pow(Pow(J))") "UFs" "iUF" 
                      [("J",set_sort)]


val Repu_def = qdefine_fsym("Repu",[‘u:mem(UFs(J))’])
‘App(iUF(J),u)’

val from_UFs = UFs_def |> conjE2 |> rewr_rule[GSYM Repu_def]

val Repu_ufilter = prove_store("Repu_ufilter",
e0
(rw[UFs_def,Repu_def] >> rpt strip_tac >> qexists_tac ‘u’ >> rw[])
(form_goal “!A u:mem(UFs(A)). ufilter(Repu(u))”));
 


val Empty_NOTIN_UFs = prove_store("Empty_NOTIN_UFs",
e0
(rpt strip_tac >> qsspecl_then [‘u’] assume_tac Repu_ufilter >>
 drule Empty_NOTIN_UF >> arw[])
(form_goal “!J u.~IN(Empty(J),Repu(u))”));



val ufilter_alt = prove_store("ufilter_alt",
e0
(rw[ufilter_def] >> dimp_tac >> strip_tac  
 >-- (strip_tac >-- first_x_assum accept_tac >>
     strip_tac >> first_x_assum (qspecl_then [‘X’] (assume_tac o GSYM)) >>
     arw[]) >>
 strip_tac >-- first_x_assum accept_tac >>
 strip_tac >> first_x_assum (qspecl_then [‘X’] assume_tac) >> arw[])
(form_goal “ufilter(L) <=> filter(L) &
  !X. IN(Compl(X:mem(Pow(J))),L) <=> ~IN(X,L)”));

val Compl_Repu = prove_store("Compl_Repu",
e0
(qsspecl_then [‘u’] assume_tac Repu_ufilter >>
 drule $ iffLR ufilter_alt >>
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘X’] assume_tac) >> arw[])
(form_goal “IN(Compl(X:mem(Pow(J))), Repu(u)) <=> ~IN(X,Repu(u))”));

 
val Union_Repu = prove_store("Union_Repu",
e0
(dimp_tac >> strip_tac (* 3 *)
 >-- (ccontra_tac >> fs[neg_or_distr] >>
     fs[GSYM Compl_Repu] >> 
     qby_tac ‘IN(Inter(Compl(s1),Compl(s2)),Repu(u))’
     >-- (irule Inter_IN_ufilter >> arw[Repu_ufilter]) >>
     fs[Inter_Compl_Compl] >>
     fs[Compl_Repu]) 
 >-- (qsspecl_then [‘s1’,‘s2’] assume_tac SS_Union1 >>
     irule SS_IN_ufilter >> rw[Repu_ufilter] >>
     qexists_tac ‘s1’ >> arw[SS_Union]) >>
 qsspecl_then [‘s1’,‘s2’] assume_tac SS_Union2 >>
 irule SS_IN_ufilter >> rw[Repu_ufilter] >>
 qexists_tac ‘s2’ >> arw[SS_Union])
(form_goal “IN(Union(s1:mem(Pow(J)),s2), Repu(u)) <=> (IN(s1,Repu(u)) | IN(s2,Repu(u)))”));




val FIP_def = qdefine_psym("FIP",[‘ss:mem(Pow(Pow(A)))’])
‘!ss0. SS(ss0,ss) & Fin(ss0) & ~(ss0 = Empty(Pow(A))) ==> ~(BIGINTER(ss0) = Empty(A))’

(*closed under finite intersection*)
val CUI_def = qdefine_psym("CUI",[‘ss:mem(Pow(Pow(A)))’])
                      ‘!ss0.
        SS(ss0, ss) & Fin(ss0) & ~(ss0 = Empty(Pow(A))) ==>
        IN(BIGINTER(ss0),ss)’


val CUI_iff_binary = prove_store("CUI_iff_binary",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qsuff_tac ‘!s. Fin(s) ==> SS(s,A) & ~(s = Empty(Pow(W))) ==> 
     IN(BIGINTER(s),A)’
     >-- (rpt strip_tac >> first_x_assum irule >> arw[]) >>
     ind_with (Fin_induct |> qtinst_thm [(‘X’,‘Pow(W)’)]) >>
     rw[Ins_NONEMPTY] >> rpt strip_tac >>
     qcases ‘IN(BIGINTER(xs0), A)’ 
     >-- (rw[BIGINTER_Ins] >> 
         first_x_assum irule >> arw[] >>
         fs[SS_def,Ins_def] >> first_x_assum irule >> arw[]) >>
     qby_tac ‘~(SS(xs0, A) & ~(xs0 = Empty(Pow(W))))’
     >-- (ccontra_tac >>  first_x_assum drule >> fs[]) >>
     fs[neg_and_distr] (* 2 *)
     >-- (qby_tac ‘SS(xs0,Ins(x,xs0))’ 
         >-- rw[SS_Ins] >>
         drule SS_Trans >> first_x_assum drule >> fs[]) >>
     rw[BIGINTER_Ins,BIGINTER_Empty,Inter_Whole] >>
     fs[SS_def,Ins_def] >> first_x_assum irule >> arw[]) >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘Ins(a1,Ins(a2,Empty(Pow(W))))’] assume_tac) >>
 fs[GSYM Union_Sing,BIGINTER_Union,BIGINTER_Empty,Inter_Whole,BIGINTER_Sing] >>
 first_x_assum irule >> rw[Union_Sing,Ins_NONEMPTY] >> 
 rw[Fin_Ins_Ins] >> rw[SS_def,Ins_def,Empty_def] >> rpt strip_tac >> arw[])
(form_goal
 “!W A:mem(Pow(Pow(W))).
  (!a1. IN(a1,A) ==> !a2.IN(a2,A) ==> IN(Inter(a1,a2),A)) <=> 
  (!s. SS(s,A) & Fin(s) & ~(s = Empty(Pow(W))) ==> IN(BIGINTER(s),A))”));

val FIP_CUI_lemma = prove_store("FIP_CUI_lemma",
e0
(rpt strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[] >> fs[GSYM IN_NONEMPTY] >>
     first_x_assum (qspecl_then [‘Empty(W)’] assume_tac) >>
     first_x_assum drule >> first_x_assum drule >>
     fs[Empty_Inter,Empty_def]) >>
 ccontra_tac >> fs[] >> fs[GSYM IN_NONEMPTY] >>
 first_x_assum drule >>
 first_x_assum (qspecl_then [‘Empty(W)’] assume_tac) >>
 first_x_assum drule >>
 fs[Inter_Empty,Empty_def])
(form_goal “!W A B. 
 ~(A = Empty(Pow(W))) & ~(B = Empty(Pow(W))) &
 (!a. IN(a,A) ==> !b. IN(b,B) ==> ~(Inter(a,b) = Empty(W))) ==>
 ~IN(Empty(W),A) & ~IN(Empty(W),B)
 ”));

val FIP_closed_under_Inter = prove_store("FIP_closed_under_Inter",
e0
(rpt strip_tac >> fs[CUI_iff_binary] >>
 rw[FIP_def] >> strip_tac >> rw[SS_Union_split] >>
 rpt strip_tac >> arw[BIGINTER_Union] >> rfs[Union_EMPTY,Fin_Union] >>
 qby_tac ‘~IN(Empty(W),A) & ~IN(Empty(W),B)’ 
 >-- (irule FIP_CUI_lemma >> arw[]) >> fs[] >> 
 qcases ‘s1 = Empty(Pow(W))’
 >-- (fs[BIGINTER_Empty,Whole_Inter] >>
     qby_tac ‘IN(BIGINTER(s2),B)’ 
     >-- (first_x_assum irule >> arw[]) >>
     fs[GSYM IN_NONEMPTY] >> rw[IN_NONEMPTY] >>
     first_x_assum drule >>
     first_x_assum drule >> fs[IN_NONEMPTY] >>
     ccontra_tac >> fs[Inter_Empty]) >>
 qcases ‘s2 = Empty(Pow(W))’
 >-- (fs[BIGINTER_Empty,Inter_Whole] >>
     qby_tac ‘IN(BIGINTER(s1),A)’ 
     >-- (first_x_assum irule >> arw[]) >>
     fs[GSYM IN_NONEMPTY] >> rw[IN_NONEMPTY] >>
     first_x_assum drule >>
     first_x_assum drule >> fs[IN_NONEMPTY] >>
     ccontra_tac >> fs[Empty_Inter]) >>
 first_x_assum irule >> strip_tac (* 2 *) >>
 first_x_assum irule >> arw[])
(form_goal
 “!W A B. ~(A = Empty(Pow(W))) & ~(B = Empty(Pow(W))) &
  (!a1. IN(a1,A) ==> !a2.IN(a2,A) ==> IN(Inter(a1,a2),A)) &
  (!b1. IN(b1,B) ==> !b2.IN(b2,B) ==> IN(Inter(b1,b2),B)) & 
  (!a. IN(a,A) ==> !b. IN(b,B) ==> ~(Inter(a,b) = Empty(W))) ==>
  FIP(Union(A,B))
 ”));

val gfss_def = proved_th $
e0
(rpt strip_tac >>
 assume_tac
 (IN_def_P |> qtinst_thm [(‘A’,‘Pow(Pow(A))’)]
 |> qfVar_prpl_th1 ("P",[‘a:mem(Pow(Pow(A)))’],‘SS(s0,a:mem(Pow(Pow(A)))) & filter(a)’))
    >>
 arw[])
(form_goal “!A s0:mem(Pow(Pow(A))).
 ?!ss. !s. IN(s,ss) <=> SS(s0,s) & filter(s)”)
|> spec_all |> qsimple_uex_spec "gfss" [‘s0’]

val gfilter_def = qdefine_fsym("gfilter",[‘s:mem(Pow(Pow(A)))’])
‘BIGINTER(gfss(s:mem(Pow(Pow(A)))))’

val IN_gfilter = 
    gfilter_def |> rewr_rule[GSYM IN_EXT_iff,IN_BIGINTER,gfss_def] 

val gfilter_ind = IN_gfilter |> iffLR  
                             |> strip_all_and_imp
                             |> disch “IN(x:mem(Pow(A)), gfilter(s))”
                             |> qgen ‘x’
                             |> disch_all
                             |> gen_all

val gfilter_filter = prove_store("gfilter_filter",
e0
(rw[filter_def] >> rpt strip_tac >> arw[] (* 3 *)
 >-- (rw[IN_gfilter] >> rpt strip_tac >> irule Whole_IN_filter >> arw[]) 
 >-- (fs[IN_gfilter] >> rpt strip_tac >> irule Inter_IN_filter >>
     arw[] >> strip_tac >> first_x_assum irule >> arw[]) >>
 fs[IN_gfilter] >> rpt strip_tac >>
 irule SS_IN_filter >> arw[] >>
 qexists_tac ‘X’ >> arw[] >> first_x_assum irule >> arw[])
(form_goal “!A.~(EMPTY(A)) ==>  !s:mem(Pow(Pow(A))). filter(gfilter(s))”));

val pfilter_def = qdefine_psym("pfilter",[‘L:mem(Pow(Pow(J)))’])
‘filter(L) & ~(L = Whole(Pow(J)))’

val SS_gfilter = prove_store("SS_gfilter",
e0
(rw[SS_def,IN_gfilter] >>
 rpt strip_tac >>  first_x_assum irule >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))).SS(s,gfilter(s))”));

val gfilter1_def = proved_th $
e0
(strip_tac >>
 assume_tac
 (IN_def_P |> qtinst_thm [(‘A’,‘Pow(A)’)]
           |> qfVar_prpl_th1 ("P",[‘a:mem(Pow(A))’],‘a = Whole(A) |
               ?ss. SS(ss,s) & Fin(ss) & ~(ss = Empty(Pow(A))) & SS(BIGINTER(ss),a)’)) >> arw[])
(form_goal
 “!s. ?!gf. !x. IN(x,gf) <=>
 ( x = Whole(A) | ?ss. SS(ss,s) & Fin(ss) & ~(ss = Empty(Pow(A))) & SS(BIGINTER(ss),x))”)
|> spec_all |> qsimple_uex_spec "gfilter1" [‘s’]

val gfilter1_filter = prove_store("gfilter1_filter",
e0
(rw[filter_def] >> rpt strip_tac >> arw[] (* 3 *)
 >-- rw[gfilter1_def]
 >-- (rw[gfilter1_def] >>
     qcases ‘X = Whole(A)’ (* 2 *)
     >-- (qcases ‘Y = Whole(A)’ 
         >-- (disj1_tac >> arw[Inter_Whole]) >>
         fs[Whole_Inter] >> drule $ iffLR gfilter1_def >> rfs[] >>
         qexists_tac ‘ss’ >> arw[]) >>
     qcases ‘Y = Whole(A)’ (* 2 *)
     >-- (arw[Inter_Whole] >> rev_drule $ iffLR gfilter1_def >> rfs[] >>
         qexists_tac ‘ss’ >> arw[]) >> arw[Inter_Whole_Whole] >>
     fs[gfilter1_def] >>
     qexists_tac ‘Union(ss,ss')’ >>
     arw[Union_SS1,Fin_Union,Union_Empty,BIGINTER_Union,SS_Inter] >>
     strip_tac >> irule SS_Trans (* 2 *)
     >-- (qexists_tac ‘BIGINTER(ss)’ >> arw[Inter_SS]) >>
     qexists_tac ‘BIGINTER(ss')’ >> arw[Inter_SS]) >>
 fs[gfilter1_def] (* 2 *)
 >-- (disj1_tac >> irule Whole_SS >> rfs[]) >>
 disj2_tac >> qexists_tac ‘ss’ >> arw[] >>
 irule SS_Trans >> qexists_tac ‘X’ >> arw[])
(form_goal “!A.~(EMPTY(A)) ==>  !s:mem(Pow(Pow(A))). filter(gfilter1(s))”));

val SS_gfilter1 = prove_store("SS_gfilter1",
e0
(rw[SS_def,gfilter1_def] >> rpt strip_tac >>
 disj2_tac >>
 qexists_tac ‘Sing(a)’ >> rw[IN_Sing,Sing_NONEMPTY,BIGINTER_Sing,Fin_Sing] >>
 rpt strip_tac >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))). SS(s,gfilter1(s))”));

val CUI_filter = prove_store("CUI_filter",
e0
(rpt strip_tac >> fs[filter_def,CUI_def] >> rpt gen_tac >> strip_tac >>
 irule $ iffLR CUI_iff_binary >> arw[] >>
 rpt strip_tac >> last_x_assum irule >> arw[])
(form_goal “!A L:mem(Pow(Pow(A))).filter(L) ==> CUI(L)”));

val gfilter_gfilter1 = prove_store("gfilter_gfilter1",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff] >> rpt strip_tac >>
 drule gfilter_filter >> drule gfilter1_filter >>
 dimp_tac >--
 (match_mp_tac gfilter_ind >> arw[SS_gfilter1]) >>
 rw[IN_gfilter,gfilter1_def] >> rpt strip_tac >> arw[]
 >-- (irule Whole_IN_filter >> arw[]) >>
 drule CUI_filter >> fs[CUI_def] >>
 first_x_assum (qspecl_then [‘ss’] assume_tac) >>
 rfs[] >>
 qby_tac ‘SS(ss, ss')’ >-- (irule SS_Trans >> qexists_tac ‘s’ >> arw[]) >>
 fs[] >>
 irule SS_IN_filter >> arw[] >> qexists_tac ‘BIGINTER(ss)’ >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))).~(EMPTY(A)) ==> gfilter(s) = gfilter1(s)”));

val Empty_NOTIN_pfilter = prove_store("Empty_NOTIN_pfilter",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[pfilter_def] >> ccontra_tac >>
     qsuff_tac ‘s = Whole(Pow(A))’ 
     >-- arw[] >>
     rw[GSYM IN_EXT_iff,Whole_def] >> strip_tac >>
     irule SS_IN_filter >> arw[] >>
     qexists_tac ‘Empty(A)’ >> arw[Empty_SS]) >>
 fs[pfilter_def] >> ccontra_tac >> fs[Whole_def])
(form_goal “!A s.pfilter(s) <=> filter(s) & ~IN(Empty(A),s)”));

val FIP_Empty_NOTIN_gfilter = prove_store("FIP_Empty_NOTIN_gfilter",
e0
(rpt strip_tac >> ccontra_tac >>
 fs[FIP_def] >> drule gfilter_gfilter1 >> fs[] >>
 fs[gfilter1_def] 
 >-- fs[EMPTY_Empty_Whole] >>
 fs[SS_Empty] >>
 first_x_assum (qspecl_then [‘ss’] assume_tac) >> rfs[])
(form_goal “!A.~EMPTY(A) ==> !s:mem(Pow(Pow(A))).FIP(s) ==> 
 ~IN(Empty(A),gfilter(s)) ”));

val FIP_PSUBSET_proper_filter = prove_store("FIP_PSUBSET_proper_filter",
e0
(rpt strip_tac >> qexists_tac ‘gfilter(s)’ >> 
 rw[SS_gfilter] >> rw[Empty_NOTIN_pfilter] >>
 drule gfilter_filter >> arw[] >>
 irule FIP_Empty_NOTIN_gfilter >> arw[])
(form_goal “!A. ~EMPTY(A) ==>
 !s:mem(Pow(Pow(A))).FIP(s) ==> ?v.pfilter(v) & SS(s,v)”));

val filter_Whole = prove_store("filter_Whole",
e0
(rw[Whole_def,filter_def])
(form_goal “!J.~EMPTY(J) ==> filter(Whole(Pow(J)))”));

val filter_Empty_Whole = prove_store("filter_Empty_Whole",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (rw[GSYM IN_EXT_iff,Whole_def] >> 
     drule SS_IN_filter >> first_x_assum drule >>
     strip_tac >> first_x_assum (qspecl_then [‘x’] assume_tac) >>
     fs[Empty_SS]) >>
 drule filter_Whole >> arw[Whole_def])
(form_goal “!J. ~EMPTY(J) ==> !L. filter(L) & IN(Empty(J),L) <=> L = Whole(Pow(J))”));

val ufilter_maximal = prove_store("ufilter_maximal",
e0
(rpt strip_tac >> fs[] >> fs[PSS_alt] >>
 irule $ iffLR filter_Empty_Whole >> arw[] >>
 qby_tac ‘~EMPTY(J)’ >-- fs[filter_def] >> arw[] >>
 drule Inter_IN_filter >>
 fs[ufilter_def] >>
 last_x_assum (qspecl_then [‘a’] assume_tac) >>
 pop_assum (assume_tac o GSYM) >> rfs[] >>
 fs[SS_def] >> first_x_assum drule >>
 first_x_assum (qspecl_then [‘a’,‘Compl(a)’] assume_tac) >>
 rfs[Inter_Compl])
(form_goal
 “!J u:mem(Pow(Pow(J))). ufilter(u) ==>
  !s. filter(s) & PSS(u,s) ==> s = Whole(Pow(J))”));



val CUI_Empty_NOTIN_FIP = prove_store("CUI_Empty_NOTIN_FIP",
e0
(rw[FIP_def,CUI_def] >> rpt strip_tac >>
 ccontra_tac >> 
 qsuff_tac ‘IN(BIGINTER(ss0),s)’ 
 >-- arw[] >>
 first_x_assum irule >> arw[])
(form_goal “!W s:mem(Pow(Pow(W))). 
 CUI(s) & ~IN(Empty(W),s) ==> FIP(s)”));

val pfilter_FIP = prove_store("pfilter_FIP",
e0
(rpt strip_tac >> irule CUI_Empty_NOTIN_FIP >>
 fs[Empty_NOTIN_pfilter] >> drule CUI_filter >> arw[] )
(form_goal “!W s:mem(Pow(Pow(W))). pfilter(s) ==>
 FIP(s)”));

val pfilter_filter = prove_store("pfilter_filter",
e0
(rw[pfilter_def] >> rpt strip_tac)
(form_goal “!A s:mem(Pow(Pow(A))). pfilter(s) ==> filter(s)”));

val pfilter_INSERT_FIP =
    prove_store("proper_filter_INSERT_FIP",
e0
(rw[FIP_def] >> rpt strip_tac >>
 qby_tac ‘~(b = Empty(W))’ >-- 
 (ccontra_tac >> fs[Compl_Empty,pfilter_def,filter_def]) >>  
 drule pfilter_FIP >>
 fs[GSYM Union_Sing] >> fs[SS_Union_split] >>
 fs[SS_Sing] (* 2 *)
 >-- (qcases ‘s2 = Empty(Pow(W))’ (* 2 *)
     >-- arw[Union_Empty2,BIGINTER_Sing] >>
     rw[BIGINTER_Union,BIGINTER_Sing] >>
     drule pfilter_filter >>
     drule CUI_filter >> ccontra_tac >>
     qsuff_tac ‘SS(BIGINTER(s2), Compl(b))’ 
     >-- (strip_tac >> drule SS_IN_filter >>
         first_x_assum
         (qspecl_then [‘BIGINTER(s2)’] assume_tac) >>
         rfs[Fin_Union] >>
         qby_tac ‘IN(BIGINTER(s2), s)’ 
         >-- (fs[CUI_def] >> last_x_assum irule >>
             arw[]) >>
         first_x_assum drule >>
         first_x_assum drule >> fs[]) >>
     fs[Inter_eq_Empty]) >>
 fs[Empty_Union] >> 
 qcases ‘s2 = Empty(Pow(W))’ (* 2 *)
 >-- (arw[BIGINTER_Empty] >> flip_tac >> 
     rw[GSYM EMPTY_Empty_Whole] >>
     fs[pfilter_def,filter_def]) >>
 ccontra_tac >> 
 drule pfilter_filter >>
 drule CUI_filter >>
 qby_tac ‘IN(BIGINTER(s2), s)’ 
 >-- (drule $ iffLR CUI_def >> last_x_assum irule >>
      arw[] >> rfs[Fin_Union]) >>
 qby_tac ‘IN(b,s)’ 
 >-- (irule SS_IN_filter >> fs[pfilter_def] >>
     qexists_tac ‘Empty(W)’ >> rfs[Empty_SS]) >>
 fs[])
(form_goal “!W s:mem(Pow(Pow(W))). pfilter(s) ==>
 !b. ~IN(b,s) & ~IN(Compl(b),s) ==> FIP(Ins(b,s))”));


val maximal_ufilter = prove_store("maximal_ufilter",
e0
(rpt strip_tac >> arw[ufilter_def] >>
 qby_tac ‘filter(u)’ >-- fs[pfilter_def] >> arw[] >>
 strip_tac >> ccontra_tac >>
 fs[neg_iff] (* 2 *)
 >-- (qby_tac ‘FIP(Ins(X,u))’ >-- 
      (irule pfilter_INSERT_FIP >> arw[]) >>
     qby_tac ‘~EMPTY(J)’ >-- fs[filter_def,pfilter_def] >>
     drule FIP_PSUBSET_proper_filter >> first_x_assum drule >>
     pop_assum strip_assume_tac >> 
     first_x_assum (qspecl_then [‘v’] assume_tac) >>
     qby_tac ‘filter(v)’ >-- fs[pfilter_def] >> 
     qby_tac ‘PSS(u,v)’ 
     >-- (rw[PSS_alt] >> strip_tac (* 2 *)
         >-- (irule SS_Trans >> qexists_tac ‘Ins(X, u)’ >>
             arw[SS_Ins]) >>
         qexists_tac ‘X’ >> arw[] >>
         fs[SS_def] >> first_x_assum irule >> rw[Ins_def]) >>
     fs[pfilter_def]) >>
 drule Inter_IN_filter >>
 first_x_assum (qspecl_then [‘X’,‘Compl(X)’] assume_tac) >> rfs[] >>
 fs[Inter_Compl] >> 
 qby_tac ‘u = Whole(Pow(J))’ 
 >-- (irule $ iffLR filter_Empty_Whole >>
     fs[filter_def]) >>
 fs[pfilter_def])
(form_goal “!J u. pfilter(u) ==> 
 (!s. filter(s) & PSS(u,s) ==> s = Whole(Pow(J))) ==>
 ufilter(u) ”));



val chain_def = qdefine_psym("chain",[‘t:mem(Pow(A))’,‘R:A~>A’])
‘!a1 a2. IN(a1,t) & IN(a2,t) ==> Holds(R,a1,a2) | Holds(R,a2,a1)’

val ptorder_def = qdefine_psym("ptorder",[‘R:A~>A’])
‘Trans(R) & Refl(R) & Asym(R)’

val ubound_def = qdefine_psym("ubound",[‘s:mem(Pow(A))’,‘R:A~>A’,‘x:mem(A)’])
‘!y. IN(y,s) ==> Holds(R,y,x)’

val ismax_def = qdefine_psym("ismax",[‘R:A~>A’,‘m:mem(A)’]) 
‘!x. Holds(R,m,x) ==> x = m’;

use "zorns.sml";

val ufilter_iff_maximal = prove_store("ufilter_iff_maximal",
e0
(rpt strip_tac >> dimp_tac >> strip_tac 
 >-- (drule maximal_ufilter >> first_x_assum drule >> arw[]) >>
 drule ufilter_maximal >> arw[])
(form_goal “!J u. pfilter(u) ==>
 ((!s. filter(s) & PSS(u,s) ==> s= Whole(Pow(J))) <=> ufilter(u))”));



val UNION_chain_filter_filter = prove_store("UNION_chain_filter_filter",
e0
(rpt strip_tac >> arw[filter_def] >> rpt strip_tac (* 3 *)
 >-- (rw[IN_BIGUNION] >> fs[GSYM IN_NONEMPTY] >>
     qexists_tac ‘a’ >> arw[] >> first_x_assum drule >>
     fs[filter_def])
 >-- (fs[IN_BIGUNION] >>
     qby_tac ‘SS(ss',ss'') | SS(ss'',ss')’ 
     >-- (first_x_assum irule >> arw[]) >>
     pop_assum strip_assume_tac (* 2 *) >--
     (qexists_tac ‘ss''’ >> fs[SS_def] >>
     first_x_assum drule >>
     irule Inter_IN_filter >> arw[] >>
     first_x_assum irule >> arw[]) >>
     qexists_tac ‘ss'’ >> fs[SS_def] >>
     first_x_assum drule >>
     irule Inter_IN_filter >> arw[] >>
     first_x_assum irule >> arw[]) >>
 fs[IN_BIGUNION] >>
 qexists_tac ‘ss'’ >> arw[] >> irule SS_IN_filter >> 
 qby_tac ‘filter(ss')’ 
 >-- (first_x_assum irule >> arw[]) >> arw[] >>
 qexists_tac ‘X’ >> arw[])
(form_goal “!W. ~EMPTY(W) ==>
 !ss. ~(ss = Empty(Pow(Pow(W)))) & 
 (!s:mem(Pow(Pow(W))). IN(s,ss) ==> filter(s)) &
 (!a b. IN(a,ss) & IN(b,ss) ==> SS(a,b) | SS(b,a)) ==>
 filter(BIGUNION(ss))”));


val UNION_chain_pfilter_pfilter = prove_store("UNION_chain_pfilter_pfilter",
e0
(rpt strip_tac >> rw[Empty_NOTIN_pfilter] >> strip_tac (* 2 *)
 >-- (irule UNION_chain_filter_filter >> arw[] >>
     rpt strip_tac >> first_x_assum drule >> fs[pfilter_def]) >>
 qby_tac ‘!s.IN(s,ss) ==> ~(IN(Empty(W),s))’ 
 >-- (rpt strip_tac >> first_x_assum drule >>
     fs[Empty_NOTIN_pfilter]) >>
 rw[IN_BIGUNION] >> ccontra_tac >> pop_assum strip_assume_tac >>
 first_x_assum drule >> fs[])
(form_goal “!W. ~EMPTY(W) ==>
 !ss. ~(ss = Empty(Pow(Pow(W)))) & 
 (!s:mem(Pow(Pow(W))). IN(s,ss) ==> pfilter(s)) &
 (!a b. IN(a,ss) & IN(b,ss) ==> SS(a,b) | SS(b,a)) ==>
 pfilter(BIGUNION(ss))”));

val ufilter_thm = prove_store("ufilter_thm",
e0
(rpt strip_tac >>
 x_choosel_then ["pf","i"] strip_assume_tac
 (Thm_2_4 |> qtinst_thm [(‘A’,‘Pow(Pow(A))’)]
 |> qfVar_prpl_th1 ("P",[‘v:mem(Pow(Pow(A)))’],‘pfilter(v:mem(Pow(Pow(A)))) & SS(s,v)’)) >>
 qby_tac ‘?r.!s1 s2:mem(pf). Holds(r,s1,s2)<=> SS(App(i,s1),App(i,s2))’
 >-- accept_tac(AX1 |> qtinst_thm [(‘A’,‘pf’),(‘B’,‘pf’)]
                    |> qfVar_prpl_th1 ("P",[‘s1:mem(pf)’,‘s2:mem(pf)’],
‘SS(App(i:pf->Pow(Pow(A)),s1),App(i,s2))’)
|> uex2ex_rule) >>
 pop_assum strip_assume_tac >>
 qsuff_tac ‘?m. ismax(r,m)’ >--
 (strip_tac >> fs[ismax_def] >>
 qexists_tac ‘App(i,m)’ >>
 qby_tac ‘pfilter(App(i,m)) & SS(s,App(i,m))’
 >-- (arw[] >> qexists_tac ‘m’ >> rw[]) >>
 arw[] >>
 pop_assum strip_assume_tac >> drule $ GSYM ufilter_iff_maximal >>
 arw[] >> 
 pop_assum (K all_tac) >>
 rpt strip_tac >>
 ccontra_tac >>
 qsuff_tac ‘?x. Holds(r,m,x) & ~(x = m)’
 >-- (strip_tac >> first_x_assum drule >> fs[]) >>
 qby_tac ‘pfilter(s') & SS(s,s')’ 
 >-- (rw[pfilter_def] >> arw[] >> irule SS_Trans >>
     qexists_tac ‘App(i,m)’ >> arw[] >> irule PSS_SS >> arw[]) >>
 qby_tac ‘?s0. s' = App(i,s0)’ >-- (rfs[] >> qexists_tac ‘b’>> rw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘s0’ >> arw[] >> fs[] >>
 drule PSS_SS >> arw[] >>
 ccontra_tac >> fs[PSS_def]) >>
 irule zorns_lemma >>
 qby_tac ‘ptorder(r)’ 
 >-- (rw[ptorder_def,Trans_def,Refl_def,Asym_def] >> rpt strip_tac (* 3 *)
     >-- (rfs[] >> irule SS_Trans >> qexists_tac ‘App(i,a2)’>> arw[]) 
     >-- arw[SS_Refl] >>
     rfs[] >> fs[Inj_def] >> first_x_assum irule >>
     irule SS_SS_eq >> arw[]) >>
 arw[] >>
 qby_tac ‘~EMPTY(pf)’ 
 >-- (rw[NOT_EMPTY] >>
     first_x_assum 
     (qspecl_then [‘s’] assume_tac) >> 
    rfs[SS_Refl] >> qexists_tac ‘b’ >> arw[]) >>
 arw[] >>
 rpt strip_tac >>
 qby_tac ‘~EMPTY(A)’ >-- fs[pfilter_def,filter_def] >>
 qby_tac ‘pfilter(BIGUNION(IMAGE(i,c)))’
 >-- (irule UNION_chain_pfilter_pfilter >>
     arw[IMAGE_eq_Empty] >> rpt strip_tac (* 2 *)
     >-- (qsuff_tac ‘pfilter(s') & SS(s,s')’ 
         >-- (strip_tac >> arw[]) >>
         arw[] >> fs[IMAGE_def] >> 
         qexists_tac ‘a’ >> rw[]) >>
     fs[chain_def] >>
     rfs[] >> fs[IMAGE_def] >>
     first_x_assum irule >> arw[]) >>
 qby_tac ‘SS(s,BIGUNION(IMAGE(i,c)))’ 
 >-- (irule SS_BIGUNION >> fs[GSYM IN_NONEMPTY] >>
     qexists_tac ‘App(i,a)’ >> 
     qby_tac ‘?b. App(i,a) = App(i,b)’ >-- (qexists_tac ‘a’ >> rw[]) >>
     first_x_assum (drule o iffRL) >> arw[] >>
     rw[IMAGE_def] >> qexists_tac ‘a’ >> arw[])  >>
 qby_tac ‘?u0. BIGUNION(IMAGE(i, c)) = App(i,u0)’ 
 >-- (first_x_assum (irule o iffLR) >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘u0’ >> arw[ubound_def] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> rpt strip_tac >>
 irule SS_BIGUNION >> qexists_tac ‘App(i,y)’ >> rw[SS_Refl] >>
 rw[IMAGE_def] >> qexists_tac ‘y’ >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))). pfilter(s) ==>
 ?u. ufilter(u) & SS(s,u)”));

val ufilter_thm_coro = prove_store("ufilter_thm_coro",
e0
(rpt strip_tac >> drule FIP_PSUBSET_proper_filter >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >> drule ufilter_thm >>
 pop_assum strip_assume_tac >> qexists_tac ‘u’ >> arw[] >>
 irule SS_Trans >> qexists_tac ‘v’ >> arw[])
(form_goal “!A ss:mem(Pow(Pow(A))). FIP(ss) & ~(EMPTY(A)) ==>
 ?u. ufilter(u) & SS(ss,u)”));




val Prop_5_3 = prove_store("Prop_5_3",
e0
(rpt gen_tac >> disch_tac >> drule ufilter_thm_coro >>
 pop_assum strip_assume_tac >> 
 drule $ iffLR from_UFs >> 
 pop_assum strip_assume_tac >>
 qexists_tac ‘b’ >> fs[])
(form_goal “!A ss:mem(Pow(Pow(A))). FIP(ss) & ~(EMPTY(A)) ==>
 ?u:mem(UFs(A)). SS(ss,Repu(u))”));


val FIP_Sing = prove_store("FIP_Sing",
e0
(rw[FIP_def] >> rpt strip_tac >>
 fs[SS_Sing,BIGINTER_Sing])
(form_goal “!W a. ~(a = Empty(W)) ==> FIP(Sing(a)) ”));

