

val overfun_def = qdefine_psym("overfun",[],
‘’);

val isset_FIB = prove_store("isset_FIB",
e0
cheat
(form_goal 
 “!A B f:A->B A0 i:A0->A b. isset(i,FIB(f,b)) ==>
  f o i = constf(A0,b)”));

val col_of_set = prove_store("col_of_set",
e0
(rpt strip_tac >>
 qspecl_then [‘U’] assume_tac AX5 >>
 pop_assum strip_assume_tac >>
 qexistsl_tac [‘B’,‘p’] >>
 qby_tac ‘Surj(p)’ 
 >-- (rw[Surj_def] >> strip_tac >> 
     first_x_assum irule >> arw[]) >> arw[] >>
 x_choosel_then ["R","inc"] strip_assume_tac
 (Thm_2_4 |> qspecl [‘B * Y’] 
 |> fVar_sInst_th “P(pair:mem(B*Y))”
    “Holds(M:B~>Y,Fst(pair),Snd(pair))”) >>
 qexistsl_tac [‘R’,‘p1(B,Y) o inc’] >> 
 rpt strip_tac >> 
 first_x_assum irule >> 
 rw[isset_def] >> 
 qby_tac ‘Inj(p2(B, Y) o inc o i)’ 
 >-- (rw[Inj_def] >> rpt strip_tac >> fs[App_App_o] >>
     drule isset_FIB >> fs[o_assoc] >> 
     drule $ iffLR isset_def >>
     pop_assum strip_assume_tac >>
     drule Inj_eq_eq >>
     first_x_assum (irule o iffLR) >> 
     rev_drule Inj_eq_eq >>
     first_x_assum (irule o iffLR) >> 
     qsspecl_then [‘App(inc, App(i, x1))’] 
     strip_assume_tac Pair_has_comp >> 
     qsspecl_then [‘App(inc, App(i, x2))’] 
     strip_assume_tac Pair_has_comp >> fs[] >>
     rw[Pair_eq_eq] >> strip_tac (* 2 *) >--
     (qby_tac ‘Fst(App(inc, App(i, x1))) = Fst(Pair(a, b))’ 
     >-- arw[] >>
     pop_assum mp_tac >> rw[Pair_def'] >>
     flip_tac >> strip_tac >> once_arw[] >>
     qby_tac ‘Fst(App(inc, App(i, x2))) = Fst(Pair(a', b'))’ 
     >-- arw[] >>
     pop_assum mp_tac >> rw[Pair_def'] >>
     qpick_x_assum ‘p1(B, Y) o inc o i = constf(vA, v)’ 
     mp_tac >> pop_assum_list (map_every (K all_tac)) >>
     rpt strip_tac >> pop_assum (assume_tac o GSYM) >>
     arw[] >> arw[GSYM Fst_def,GSYM App_App_o,constf_def,o_assoc]) >>
     fs[p12_of_Pair]) >>
  qexistsl_tac [‘p2(B, Y) o inc o i’] >> arw[] >>
 rw[GSYM IN_EXT_iff,IMAGE_def,Whole_def,IN_rsi] >>
 strip_tac >> rw[rsi_def,Rsi_def,Ri_def,App_App_o,Sg_def] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘v’ >> rw[] >> arw[] >>
     first_x_assum (qspecl_then [‘Pair(v,  App(p2(B, Y), App(inc, App(i, a))))’] assume_tac) >>
     fs[Pair_def'] >> qexists_tac ‘App(i,a)’ >>
     qsspecl_then [‘App(inc,App(i,a))’] assume_tac
     Pair_has_comp >>
     pop_assum (x_choosel_then ["b","y"] assume_tac) >>
     arw[p12_of_Pair,Pair_eq_eq] >>  
     qby_tac
     ‘App(p1(B,Y),App(inc, App(i, a))) = 
      App(p1(B,Y),Pair(b, y))’ 
     >-- arw[] >> fs[p12_of_Pair] >>
     pop_assum (assume_tac o GSYM) >>
     once_arw[] >> drule isset_FIB >>
     pop_assum mp_tac >> 
     pop_assum_list (map_every (K all_tac)) >>
     strip_tac >> fs[o_assoc,GSYM App_App_o,constf_def]) >>
 rfs[] >>
 first_x_assum (qsspecl_then [‘Pair(v,x)’] mp_tac) >>
 (*why fs after assume tac kills M(v,x)?*)
 fs[Pair_def'] >> strip_tac >>
 drule $ iffLR isset_def >>
 pop_assum strip_assume_tac >>
 drule $ iffLR IMAGE_eq_FIB >>
 fs[Whole_def] >>
 first_x_assum (qspecl_then [‘b’] assume_tac) >>
 rfs[App_App_o]>>  
 qpick_x_assum ‘Pair(v, x) = App(inc, b)’
  (assume_tac o GSYM) >> fs[] >> fs[p12_of_Pair] >>
 qexists_tac ‘a'’ >> once_arw[] >> arw[p12_of_Pair])
(form_goal
 “(!u:mem(U). ?X. P(u,X)) ==>
  ?V p:V->U. Surj(p) & 
  ?A fa:A->V. 
   !v vA i:vA -> A. isset(i,FIB(fa,v)) ==>
   P(App(p,v),vA)”));


psyms := #1 (Binarymap.remove (!psyms,"isPb")  )

(*lookup_pred (!psyms) "isPb" *)

val isPb_def = qdefine_psym("isPb",[‘f:X->K’,‘g:Y->K’,‘p: P ->X’,‘q: P -> Y’])
‘ f o p = g o q &
 !A u : A -> X v : A -> Y. 
    f o u = g o v ==> 
    ?!a : A -> P. p o a = u & q o a = v’
|> qgenl [‘X’,‘K’,‘f:X->K’,‘Y’,‘g:Y->K’,‘P’,‘p:P ->X’,‘q: P ->Y’]
|> store_as "isPb_def";

(*helpful to prove there exists a inj to product*)
val Pb_epi_epi = prove_store("Pb_epi_epi",
e0
(rpt strip_tac >> cheat)
(form_goal
 “!X K f:X->K Y g:Y->K P p:P->X q:P->Y. 
  isPb(f,g,p,q) ==>
  Surj(f) ==> Surj(q)”));



val isPb_expand = isPb_def
                      |> conv_rule $ once_depth_fconv no_conv (rewr_fconv $ uex_def “?!a : A -> P. p:P->X o a = u & q:P->Y o a = v”) |> store_as "isPb_expand";


val isPb_ex = prove_store("isPb_ex",
e0
(cheat)
(form_goal
 “!X K f:X->K Y g:Y->K. ?P p:P->X q. isPb(f,g,p,q)”));


val isKer_def = 
 qdefine_psym("isKer",[‘r:XX->X’,‘s:XX->X’,‘p:X->Y’])
 ‘isPb(p,p,r,s)’



val isKer_ex = prove_store("isKer_ex",
e0
(cheat)
(form_goal
 “!X Y f:X->Y. ?XX r:XX->X s. isKer(r,s,f)”));

val all_FIB_eq = prove_store("all_FIB_eq",
e0
(rpt strip_tac >>
 irule $ iffLR FUN_EXT >> strip_tac >>
 first_x_assum (qsspecl_then [‘App(f,a)’] assume_tac) >>
 fs[GSYM IN_EXT_iff,IN_FIB] >>
 flip_tac >> first_x_assum (irule o iffLR) >> rw[])
(form_goal
 “!U A B f g:A->B.
  (!u. FIB(f,u) = FIB(g,u)) ==> f = g”));

val repl_of_equality = prove_store("repl_of_equality",
e0
(rpt strip_tac >>
 irule $ iffLR FUN_EXT >> strip_tac >>
 first_x_assum irule >> 
 qexists_tac ‘App(fa,a)’ >>
 rw[IN_FIB])
(form_goal
 “!U A fa:A->U B f g:A->B.
  (!u a. IN(a,FIB(fa,u)) ==> App(f,a) = App(g,a)) ==> 
  f = g”));





(*pack things up using product?*)
val Pbover_def = qdefine_psym("Pbover",[
‘p:V->U’,‘a:A->U’,‘pa1:Av->V’,‘pa2:Av->A’,
         ‘b:B->U’,‘pb1:Bv->V’,‘pb2:Bv->B’,
‘f:A->B’,‘fv:Av->Bv’])
‘isPb(p,a,pa1,pa2) & isPb(p,b,pb1,pb2) & 
 pb1 o fv = pa1 & pb2 o fv = f o pa2’




   
val col_of_fun = prove_store("col_of_fun",
e0
cheat
(form_goal
 “!A fa:A->U B fb:B->U.
    (!u uA ia:uA->A uB ib:uB->B.
      isset(ia,FIB(fa,u)) & isset(ib,FIB(fb,u)) ==>
     ?f:uA -> uB. P(u,f)) ==> 
    ?V e:V->U. 
     epi(e) & 
     !eA ea2:eA -> A ea1:eA -> V
      eB eb2:eB -> A eb1:eB -> V.
      isPb(e,fa,ea1,ea2) & isPb(e,fb,eb1,eb2) ==> 
     ?g:eA -> eB. 
     !v:mem(V) vA vea:vA -> eA vB veb:vB->eB vg:vA -> vB. 
     isset(vea,FIB(ea1,v)) & isset(veb,FIB(eb1,v)) & 
     g o vea = veb o vg 
      ==>
     P(App(e,v),g)
     ”));


val p41_def = qdefine_fsym("p41",[‘A’,‘B’,‘C’,‘D’]) ‘p1(A,B * C * D)’ 
                          |> gen_all 

val p42_def = qdefine_fsym("p42",[‘A’,‘B’,‘C’,‘D’])
                          ‘p1(B, C * D) o p2(A,B * C * D)’ 
                          |> gen_all 

val p43_def = qdefine_fsym("p43",[‘A’,‘B’,‘C’,‘D’]) 
                          ‘p1(C,D) o p2(B, C * D) o p2(A,B * C * D)’ 
                          |> gen_all 

val p44_def = qdefine_fsym("p44",[‘A’,‘B’,‘C’,‘D’]) 
                          ‘p2(C,D) o p2(B, C * D) o p2(A,B * C * D)’ 
                          |> gen_all 

val item41_def = qdefine_fsym("item41",[‘abcd:mem(A*B*C*D)’]) ‘App(p41(A,B,C,D),abcd)’ 
                          |> gen_all 


val item42_def = qdefine_fsym("item42",[‘abcd:mem(A*B*C*D)’]) ‘App(p42(A,B,C,D),abcd)’ 
                          |> gen_all 


val item43_def = qdefine_fsym("item43",[‘abcd:mem(A*B*C*D)’]) ‘App(p43(A,B,C,D),abcd)’ 
                          |> gen_all 


val item44_def = qdefine_fsym("item44",[‘abcd:mem(A*B*C*D)’]) ‘App(p44(A,B,C,D),abcd)’ 
                          |> gen_all 

val Pbsq_def = 
qdefine_psym("Pbsq",[‘fgpq:mem(Exp(X,K) * Exp(Y,K) * Exp(P,X) * Exp(P,Y))’])
‘isPb(tof(item41(fgpq)),tof(item42(fgpq)),
      tof(item43(fgpq)),tof(item44(fgpq)))’

val Pbsq1_def = qdefine_fsym("Pbsq1",[‘fgpq:mem(Exp(X,K) * Exp(Y,K) * Exp(P,X) * Exp(P,Y))’])
‘tof(item41(fgpq))’



val Pbsq2_def = qdefine_fsym("Pbsq2",[‘fgpq:mem(Exp(X,K) * Exp(Y,K) * Exp(P,X) * Exp(P,Y))’])
‘tof(item42(fgpq))’


val Pbsq3_def = qdefine_fsym("Pbsq3",[‘fgpq:mem(Exp(X,K) * Exp(Y,K) * Exp(P,X) * Exp(P,Y))’])
‘tof(item43(fgpq))’


val Pbsq4_def = qdefine_fsym("Pbsq4",[‘fgpq:mem(Exp(X,K) * Exp(Y,K) * Exp(P,X) * Exp(P,Y))’])
‘tof(item44(fgpq))’


(*
(*pack things up using product?*)
val Pbsqover_def = qdefine_psym("Pbsqover",[
‘p:V->U’,‘a:A->U’,‘pa1:Av->V’,‘pa2:Av->A’,
         ‘b:B->U’,‘pb1:Bv->V’,‘pb2:Bv->B’,
‘f:A->B’,‘fv:Av->Bv’])
‘Pbsq(pbsq1) & Pbsq(pbsq2) &
 pb1 o fv = pa1 & pb2 o fv = f o pa2’
*)

psyms := #1 (Binarymap.remove (!psyms,"Pbover")  )


(*pack things up using product?*)
val Pbover_def = qdefine_psym("Pbover",[
‘p:V->U’,‘a:A->U’,‘pa1:Av->V’,‘pa2:Av->A’,
         ‘b:B->U’,‘pb1:Bv->V’,‘pb2:Bv->B’,
‘f:A->B’,‘fv:Av->Bv’])
‘b o f = a & isPb(p,a,pa1,pa2) & isPb(p,b,pb1,pb2) & 
 pb1 o fv = pa1 & pb2 o fv = f o pa2’


val repl_of_fun = prove_store("repl_of_fun",
e0
()
(form_goal 
 “!A a:A->U B b:B->U. 
  (!u:mem(U). 
   !uA ia:uA->A uB ib:uB->B. 
       isset(ia,FIB(a,u)) & isset(ib,FIB(b,u)) ==>
   ?!f:uA -> uB. P(u,f)) ==>
  ?g:A->B. 
  !u uA ia:uA->A uB ib:uB->B u. 
       isset(ia,FIB(a,u)) & isset(ib,FIB(b,u)) ==>
   !f:uA -> uB. ib o f = g o ia ==> P(u,f)”));




val col_of_cont_Upows = prove_store("col_of_cont_Upows",
e0
cheat
(form_goal
 “!n. ?X p:X->N R:X~>X z:N->X. P(n,p,R,z) ==>
  ?V e:V->N. 
  epi(e) & 
  ?X' f:X'->N p':X'->N * N R': X' ~> X' z':N*N -> X'.
  !v:mem(V) Xev i:Xev->X' pev:Xev-> N Rev:Xev~>Xev zev. 
  isset(i,FIB(f,App(e,v))) & 
  p' o i = Pa(Id(N),Id(N)) o pev & 
  (!x1 x2. Holds(Rev,x1,x2) <=>
           Holds(R',App(i,x1),App(i,x2))) & 
  (i o zev = z' o Pa(Id(N),Id(N)))
  ==>
  P(App(e,v),pev,Rev,zev)”));

