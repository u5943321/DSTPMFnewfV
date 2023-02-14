val Inj_same_IMAGE = 
prove_store("Inj_same_IMAGE",
e0
(rpt strip_tac >>
 assume_tac 
 (Thm_2_4_unique |> qtinst_thm [(‘A’,‘X’)] 
                 |> qgen ‘B’
                 |> qsspecl [‘i1:A1->X’,‘i2:A2->X’] 
                 |> qfVar_prpl_th1 ("P",[‘x:mem(X)’],
‘IN(x,IMAGE(i1:A1->X,Whole(A1)))’)) >>
 first_x_assum irule >> 
 rw[Whole_def,IMAGE_def] >> arw[] >>
 fs[GSYM IN_EXT_iff,IMAGE_def,Whole_def])
(form_goal 
 “!X A1 i1:A1->X A2 i2:A2->X. 
  Inj(i1) & Inj(i2) & IMAGE(i1,Whole(A1)) = IMAGE(i2,Whole(A2)) ==>
  ?f:A1->A2 g:A2->A1. f o g = Id(A2) & g o f = Id(A1) & 
   i2 o f = i1 & i1 o g = i2”));



val Inj_same_IMAGE_unique = prove_store("Inj_same_IMAGE_unique",
e0
(rpt gen_tac >> disch_tac >> 
 drule Inj_same_IMAGE >>
 pop_assum strip_assume_tac >>
 uex_tac >> qexists_tac ‘f’ >> arw[] >>
 rpt strip_tac >> irule Inj_lcancel >>
 qexistsl_tac [‘X’,‘i2’]  >> arw[])
(form_goal
 “!X A1 i1:A1->X A2 i2:A2->X. 
  Inj(i1) & Inj(i2) & IMAGE(i1,Whole(A1)) = IMAGE(i2,Whole(A2)) ==>
  ?!f:A1->A2. 
   i2 o f = i1”));



val Bij_Inj = prove_store("Bij_Inj",
e0
(rw[Bij_def] >> rpt strip_tac >> arw[])
(form_goal “!A B f:A->B. Bij(f) ==> Inj(f)”));


val ex_mem_eq = prove_store("ex_mem_eq",
e0
(rpt strip_tac (* 4 *)
 >> qexists_tac ‘a’ >> rw[])
(form_goal “(!A a:mem(A). ?a0. a = a0) & 
            (!A a:mem(A). ?a0. a0 = a) & 
            (!A B f:A->B a. ?a0. App(f,a0) = App(f,a)) &
            (!A B f:A->B a. ?a0. App(f,a) = App(f,a0))”));

(*“R(x,s) <=> ?A ....” *)
val Inj_Pow_EXT = prove_store("Inj_Pow_EXT",
e0
(rpt strip_tac >> 
 qby_tac
 ‘sx1 = sx2 <=>  
  ?s:mem(Pow(A)). App(pi,s) = sx1 & App(pi,s) = sx2’ 
 >-- (fs[IMAGE_def,Whole_def] >> 
     drule Inj_eq_eq >> arw[] >>
     dimp_tac >> strip_tac (* 2 *)
     >-- (qexists_tac ‘a’ >> arw[]) >> 
     pop_assum (assume_tac o GSYM) >> fs[]) >>
 arw[] >>
 rw[IMAGE_def,Whole_def] >> 
 dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac >>
     first_assum (qsspecl_then [‘ax’,‘sx1’] assume_tac) >>
     qby_tac
     ‘Holds(R,ax, sx1) <=>
             ?(a : mem(A))  (s : mem(Pow(A))).
               IN(a, s) & App(i, a) = ax & App(pi, s) = sx1’
     >-- (pop_assum irule >>
         strip_tac (* 2 *)
         >-- (qexists_tac ‘a’ >> arw[]) >>
         qexists_tac ‘s’ >> arw[] >> qexists_tac ‘s’ >>
         arw[] >> qpick_x_assum ‘App(pi, s) = sx1’
         (assume_tac o GSYM) >> arw[]) >>
     qby_tac
     ‘Holds(R,ax, sx2) <=>
             ?(a : mem(A))  (s : mem(Pow(A))).
               IN(a, s) & App(i, a) = ax & App(pi, s) = sx2’
     >-- (first_x_assum irule >>
         strip_tac (* 2 *)
         >-- (qexists_tac ‘a’ >> arw[]) >>
         qexists_tac ‘s’ >> arw[] >> qexists_tac ‘s’ >>
         arw[] >> qpick_x_assum ‘App(pi, s) = sx2’
         (assume_tac o GSYM) >> arw[]) >>
     arw[] >>
     qpick_x_assum ‘App(pi, s) = sx1’ (assume_tac o GSYM)>>
     qpick_x_assum ‘App(pi, s) = sx2’ (assume_tac o GSYM)>>
     arw[]) >>
 fs[IMAGE_def,Whole_def] >>
 qsuff_tac ‘a = a'’ 
 >-- (strip_tac >> arw[] >> qexists_tac ‘a'’ >> rw[]) >>
 irule IN_EXT >> strip_tac >>
 first_x_assum (qsspecl_then [‘App(i,x)’] assume_tac)>>
 qby_tac ‘Holds(R, App(i, x), sx1) <=>
 Holds(R, App(i, x), sx2)’
 >-- (first_x_assum irule >>
     qexists_tac ‘x’>> rw[]) >>
 pop_assum mp_tac >> pop_assum (K all_tac) >>
 strip_tac >> 
 qsuff_tac ‘(Holds(R, App(i, x), sx1) <=> IN(x,a)) & 
 (Holds(R, App(i, x), sx2) <=> IN(x,a'))’
 >-- (strip_tac >> fs[]) >> strip_tac (* 2 *)
 >-- (first_x_assum
     (qsspecl_then [‘App(i,x)’,‘sx1’] assume_tac) >>
     drule Inj_eq_eq >>
     rev_drule Inj_eq_eq >> rfs[] >> fs[] >> 
     fs[ex_mem_eq] >> (*silly from here*)
     dimp_tac >> strip_tac (* 2 *)
     >-- fs[] >>
     qexistsl_tac [‘x’,‘a’] >> arw[]) >>
 first_x_assum
     (qsspecl_then [‘App(i,x)’,‘sx2’] assume_tac) >>
 drule Inj_eq_eq >>
 rev_drule Inj_eq_eq >> rfs[] >> fs[] >> 
 fs[ex_mem_eq] >> (*silly from here*)
 dimp_tac >> strip_tac (* 2 *)
 >-- fs[] >>
 qexistsl_tac [‘x’,‘a'’] >> arw[])
(form_goal
 “!X A i:A->X pi:Pow(A)->X R:X~>X. Inj(i) & Inj(pi) & 
  (!ax:mem(X) sx:mem(X). 
  (?a. ax = App(i,a)) & (?s. sx = App(pi,s)) ==> 
   (Holds(R,ax,sx) <=>
    ?a s. IN(a,s) & App(i,a) = ax & App(pi,s)= sx)) ==>
  !sx1 sx2:mem(X). 
  IN(sx1,IMAGE(pi,Whole(Pow(A)))) &
  IN(sx2,IMAGE(pi,Whole(Pow(A)))) ==>
  (sx1 = sx2 <=> 
   !ax. IN(ax,IMAGE(i,Whole(A))) ==>
   (Holds(R,ax,sx1) <=> Holds(R,ax,sx2)))”));





val Les_def = 
IN_def_P |> qtinst_thm [(‘A’,‘N’)] 
         |> qfVar_prpl_th1 ("P",[‘a:mem(N)’],‘Le(a,n)’)
            |> qsimple_uex_spec "Les" [‘n’]

val Les_def = Les_def |> gen_all



val Upows_def = qdefine_psym("Upows",[‘n:mem(N)’,‘p:X->N’,‘R:X~>X’,‘z:N->X’])
‘IMAGE(p:X->N,Whole(X)) = Les(n) &  
 Inj(z) &  
 IMAGE(z:N->X,Whole(N)) = FIB(p,O) & 
 (!n0. Lt(n0,n) ==>
 ?A i:A->X pi:Pow(A) ->X.
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,n0) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0))& 
   (!a:mem(A) s. 
   Holds(R,App(i,a),App(pi,s)) <=> IN(a,s))) & 
 (!x:mem(X) s:mem(X). 
  Holds(R,x,s) <=> 
  (Lt(App(p,x),n) & 
  Suc(App(p,x)) = App(p,s) &
  ?A i:A->X pi:Pow(A) ->X a:mem(A) sa:mem(Pow(A)). 
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,App(p,x)) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,App(p,s)) & 
   (!a:mem(A) s. 
                Holds(R,App(i,a),App(pi,s)) <=> IN(a,s)) & 
   IN(a,sa) & App(i,a) = x & App(pi,sa) = s))’


val Les_O_Sing = prove_store("Les_O_Sing",
e0
(irule IN_EXT >> rw[IN_Sing,Les_def] >>
 rw[Le_O_iff])
(form_goal “Les(O) = Sing(O)”));

val constf_iff_Sing = prove_store("constf_iff_Sing",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (irule $ iffLR FUN_EXT >>
     rw[constf_def] >> 
     fs[GSYM IN_EXT_iff,IMAGE_def,IN_Sing,Whole_def] >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     rw[ex_mem_eq]) >>
 arw[GSYM IN_EXT_iff,IMAGE_def,IN_Sing,Whole_def] >>
 rw[constf_def] >> strip_tac >>
 dimp_tac >> rpt strip_tac >> fs[] >>
 qexists_tac ‘a’ >> rw[]
)
(form_goal “!A.
(?a:mem(A).T) ==> ! B f:A->B b.(IMAGE(f,Whole(A)) = Sing(b) <=> 
 f = constf(A,b))”));

val IMAGE_constf = prove_store("IMAGE_constf",
e0
(rw[constf_def,IMAGE_def,
    GSYM IN_EXT_iff,IN_Sing,Empty_def]>> 
 rpt strip_tac >>
 assume_tac (exists_forall_dual 
|> qfVar_prpl_th1 ("P",[‘a:mem(A)’],‘IN(a:mem(A),s)’)
|> GSYM) >>
 fs[] >>
 dimp_tac >> strip_tac >> arw[] >>
 qexists_tac ‘a’ >> arw[]
 )
(form_goal “!A s. ~(s = Empty(A)) ==>
 !X x:mem(X).
 IMAGE(constf(A,x),s) = Sing(x)”));


val Upows_O = prove_store("Upows_O",
e0
(rw[Upows_def,NOT_Lt_O,Bij_def] >> 
 dimp_tac >> rpt strip_tac >> arw[] (* 3 *)
 >-- (fs[Les_O_Sing] >>
     qby_tac ‘?a:mem(X).T’ 
     >-- (qexists_tac ‘App(z,O)’ >> rw[]) >>
     drule constf_iff_Sing >> fs[])
 >-- (fs[Surj_def,Les_O_Sing,GSYM IN_EXT_iff,IMAGE_def,IN_Sing,FIB_def,PREIM_def,Whole_def] >>
     strip_tac >> flip_tac >>
     arw[]>> qexists_tac ‘O’ >> rw[] >>
     last_x_assum (assume_tac o GSYM) >> arw[] >>
     qexists_tac ‘b’ >> rw[]) >>
 rw[Les_O_Sing] >> irule IMAGE_constf >>
 rw[GSYM IN_EXT_iff,Whole_def,Empty_def] >>
 ccontra_tac >>
 first_x_assum (qsspecl_then [‘App(z,O)’] assume_tac) >>
 arw[])
(form_goal 
 “Upows(O, p:X->N, R:X~>X, z) <=> 
  IMAGE(z, Whole(N)) = FIB(p, O) & 
  p = constf(X,O) & 
  (!x1 x2.~Holds(R,x1,x2)) & 
  Bij(z) 
  ”));


val REmpty_def = 
AX1 |> qtinst_thm [(‘B’,‘A’)] 
    |> qfVar_prpl_th1 ("P",[‘a:mem(A)’,‘b:mem(A)’],‘F’)
    |> rewr_rule[] 
    |> qsimple_uex_spec "REmpty" [‘A’]
    |> gen_all

val IMAGE_Id = prove_store("IMAGE_Id",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IMAGE_def,Id_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> fs[] >>
 qexists_tac ‘x’ >> arw[])
(form_goal “!A s. IMAGE(Id(A),s) = s”));

val Id_Surj = prove_store("Id_Surj",
e0
(rw[Surj_def,Id_def] >> rpt strip_tac >> 
 qexists_tac ‘b’ >> rw[])
(form_goal “!A. Surj(Id(A))”));

val Bij_Id = prove_store("Bij_Id",
e0
(rw[Id_Inj,Id_Surj,Bij_def])
(form_goal “!A. Bij(Id(A))”));


val Upows_O_ex = prove_store("Upows_O_ex",
e0
(rw[Upows_O,FIB_constf,IMAGE_Id,REmpty_def,Bij_Id])
(form_goal “Upows(O,constf(N,O),REmpty(N),Id(N))”));


val Apr_def = AX1 |> qtinst_thm [(‘B’,‘A’)] 
                  |> qfVar_prpl_th1 
("P",[‘a1:mem(A)’,‘a2:mem(A)’],
‘?x1 x2. App(f:X->A,x1) = a1 & App(f,x2) =
 a2 & Holds(R0,x1,x2)’)
|> qsimple_uex_spec "Apr" [‘f’,‘R0’] |> gen_all


val Inj_Pow_choice_independence = 
prove_store("Inj_Pow_choice_independence",
e0
(rpt strip_tac >>
 qby_tac
 ‘?f:A->A1.
  !a a1. App(f,a) = a1 <=> App(i,a) = App(i1,a1)’ 
 >-- (match_mp_tac
     (P2fun|> qtinst_thm [(‘B’,‘A1’)] 
           |> qfVar_prpl_th1 ("P",[‘a:mem(A)’,‘a1:mem(A1)’],
‘App(i:A->X,a) = App(i1:A1->X,a1)’)) >>
     strip_tac >> uex_tac >>
     fs[GSYM IN_EXT_iff,IMAGE_def,Whole_def] >>
     last_x_assum (qsspecl_then [‘App(i,x)’] assume_tac) >>
     fs[ex_mem_eq] >> qexists_tac ‘a’ >>
     rw[] >> qpick_x_assum ‘Inj(i1)’ assume_tac >>
     drule Inj_eq_eq >> fs[] >>
     rpt strip_tac >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >>
 qby_tac ‘i1 o f = i’
 >-- (irule $ iffLR FUN_EXT >> 
     pop_assum (assume_tac o GSYM) >>
     flip_tac >> arw[App_App_o]) >> arw[] >>
 qby_tac ‘Bij(f)’ 
 >-- (rw[Bij_def,Inj_def,Surj_def] >>
     arw[GSYM App_App_o] >> rev_drule Inj_eq_eq >> arw[]>>
     fs[GSYM IN_EXT_iff,IMAGE_def,Whole_def] >>
     strip_tac >>
     last_x_assum (qsspecl_then [‘App(i1,b)’] assume_tac)>>
     fs[ex_mem_eq] >> arw[]) >>
 arw[] >> 
 irule $ iffLR FUN_EXT >>
 strip_tac >>
 qby_tac
 ‘!ax. IN(ax, IMAGE(i, Whole(A))) ==>
       (Holds(R, ax, App(pi1 o Image(f), a)) <=> 
        Holds(R, ax, App(pi,a)))’ 
 >-- (rpt strip_tac >>
     fs[IMAGE_def,Whole_def] >>
     qby_tac ‘Holds(R, App(i, a'), App(pi, a)) <=> 
              IN(a',a)’
     >-- (last_x_assum 
         (qsspecl_then 
              [‘App(i,a')’,‘App(pi,a)’] assume_tac) >>
         rev_drule Inj_eq_eq >>
         qpick_x_assum ‘Inj(pi)’ assume_tac >>
         drule Inj_eq_eq >> fs[] >>
         fs[ex_mem_eq] >> 
         dimp_tac >> strip_tac >> fs[] >>
         qexistsl_tac [‘a'’,‘a’] >> arw[]) >> arw[] >>
     qpick_x_assum ‘i1 o f = i’ (assume_tac o GSYM) >>
     arw[] >> rw[App_App_o] >>
     first_assum (*was first_x_assum*)
     (qsspecl_then [‘App(i1, App(f, a'))’,
                    ‘App(pi1, App(Image(f), a))’]
      assume_tac) >>
     drule Inj_eq_eq >>
     qpick_x_assum ‘Inj(i1)’ assume_tac >>
     drule Inj_eq_eq >> fs[ex_mem_eq] >>
     rw[App_App_o] >> once_arw[] >>
     drule Bij_Inj >> drule Inj_eq_eq >>
     once_arw[] >> 
     qby_tac ‘?s. App(pi1, App(Image(f), a)) = App(pi,s)’ 
     >-- (qpick_x_assum ‘IMAGE(pi, Whole(Pow(A))) = IMAGE(pi1, Whole(Pow(A1)))’ mp_tac >>
         rw[GSYM IN_EXT_iff,IMAGE_def,Whole_def] >> 
         strip_tac >>
         first_x_assum (qsspecl_then [‘App(pi1, App(Image(f), a))’] assume_tac) >> fs[ex_mem_eq]) >>
     pop_assum strip_assume_tac >>
     once_arw[] >> 
     qpick_x_assum ‘Inj(pi)’ assume_tac >>
     drule Inj_eq_eq >> once_arw[] >>
     qsuff_tac ‘IN(a',s) <=> IN(a',a)’
     >-- (strip_tac >> pop_assum (assume_tac o GSYM) >>
          arw[] >> qpick_x_assum ‘Inj(f)’ assume_tac >>
          drule IN_IMAGE_Inj >> arw[] >> rw[Image_IMAGE] >>
          dimp_tac >> strip_tac >> fs[] >>
          qexistsl_tac [‘App(f,a')’,‘IMAGE(f,a)’] >> 
          arw[]) >>
     qby_tac ‘IN(a', a) <=> IN(App(f,a'),IMAGE(f,a))’ 
     >-- (qpick_x_assum ‘Inj(f)’ assume_tac >>
          drule IN_IMAGE_Inj >> arw[]) >> 
     qby_tac ‘IN(App(f, a'), IMAGE(f, a)) <=> 
              Holds(R,App(i1,App(f, a')),
                    App(pi1,IMAGE(f,a)))’
     >-- (first_x_assum 
         (qsspecl_then [‘App(i1, App(f, a'))’,
                        ‘App(pi1, IMAGE(f, a))’]
          assume_tac) >>
         rfs[] >> fs[App_App_o] >>
         rfs[] >> fs[ex_mem_eq] >> 
         dimp_tac >> strip_tac >> fs[] >>
         qexistsl_tac [‘ App(f, a')’,‘IMAGE(f, a)’] >>
         arw[]) >>
     qby_tac
     ‘Holds(R, App(i1, App(f, a')), App(pi1, IMAGE(f, a))) 
      <=> Holds(R, App(i, a'), App(pi1, IMAGE(f, a)))’ 
     >-- (rw[GSYM App_App_o] >> arw[]) >>
     qby_tac
     ‘Holds(R, App(i, a'), App(pi1, IMAGE(f, a))) <=>
      Holds(R, App(i, a'), App(pi, s))’    
     >-- fs[Image_IMAGE] >>
     qby_tac
     ‘Holds(R, App(i, a'), App(pi, s)) <=> IN(a',s)’      
     >-- (last_x_assum 
         (qsspecl_then [‘App(i, a')’,‘App(pi,s)’]
          assume_tac) >>
         pop_assum mp_tac >> arw[] >> rw[ex_mem_eq] >>
         strip_tac >> arw[] >> rw[App_App_o] >> arw[] >>
         dimp_tac >> strip_tac >> arw[] >> fs[] >>
         qexistsl_tac [‘a'’,‘s’] >> arw[]) >>
     arw[]) >>
 qsspecl_then [‘i’,‘pi’,‘R’] assume_tac Inj_Pow_EXT >>
 rfs[] >>
 first_x_assum (irule o iffRL) >>
 arw[] >> strip_tac (* 2 *)
 >-- (qpick_x_assum ‘IMAGE(pi, Whole(Pow(A))) = IMAGE(pi1, Whole(Pow(A1)))’ (assume_tac o GSYM) >> arw[] >>
     rw[IMAGE_def,Whole_def] >> qexists_tac ‘a’ >> rw[]) >>
 rw[App_App_o,IMAGE_def,Whole_def] >> 
 qexists_tac ‘App(Image(f),a)’ >> rw[])
(form_goal
 “!X A i:A->X pi:Pow(A)->X R:X~>X. Inj(i) & Inj(pi) & 
  (!ax:mem(X) sx:mem(X). 
  (?a. ax = App(i,a)) & (?s. sx = App(pi,s)) ==> 
   (Holds(R,ax,sx) <=>
    ?a s. IN(a,s) & App(i,a) = ax & App(pi,s)= sx)) ==>
  !A1 i1:A1->X pi1:Pow(A1) -> X. 
  Inj(i1) & Inj(pi1) & 
  (!ax:mem(X) sx:mem(X). 
  (?a1. ax = App(i1,a1)) & (?s1. sx = App(pi1,s1)) ==> 
   (Holds(R,ax,sx) <=>
    ?a1 s1. IN(a1,s1) & App(i1,a1) = ax & App(pi1,s1)= sx)) &   IMAGE(i,Whole(A)) = IMAGE(i1, Whole(A1)) & 
  IMAGE(pi,Whole(Pow(A))) = IMAGE(pi1, Whole(Pow(A1))) ==>
  ?f:A->A1 . 
   Bij(f) &
   i1 o f = i & pi1 o Image(f) = pi”));

(*
val Inj_Pow_choice_independence = 
prove_store("Inj_Pow_choice_independence",
e0
(rpt strip_tac >>
 qby_tac
 ‘?f:A->A1.
  !a a1. App(f,a) = a1 <=> App(i,a) = App(i1,a1)’ 
 >-- (match_mp_tac
     (P2fun|> qspecl [‘A’,‘A1’] 
           |> fVar_sInst_th “P(a:mem(A),a1:mem(A1))”
              “App(i:A->X,a) = App(i1:A1->X,a1)”) >>
     strip_tac >> uex_tac >>
     fs[GSYM IN_EXT_iff,IMAGE_def,Whole_def] >>
     last_x_assum (qsspecl_then [‘App(i,x)’] assume_tac) >>
     fs[ex_mem_eq] >> qexists_tac ‘a’ >>
     rw[] >> qpick_x_assum ‘Inj(i1)’ assume_tac >>
     drule Inj_eq_eq >> fs[] >>
     rpt strip_tac >> arw[]) >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f’ >>
 qby_tac ‘i1 o f = i’
 >-- (irule $ iffLR FUN_EXT >> 
     pop_assum (assume_tac o GSYM) >>
     flip_tac >> arw[App_App_o]) >> arw[] >>
 qby_tac ‘Bij(f)’ 
 >-- (rw[Bij_def,Inj_def,Surj_def] >>
     arw[GSYM App_App_o] >> rev_drule Inj_eq_eq >> arw[]>>
     fs[GSYM IN_EXT_iff,IMAGE_def,Whole_def] >>
     strip_tac >>
     last_x_assum (qsspecl_then [‘App(i1,b)’] assume_tac)>>
     fs[ex_mem_eq] >> arw[]) >>
 arw[] >> 
 irule $ iffLR FUN_EXT >>
 strip_tac >>
 qby_tac
 ‘!ax. IN(ax, IMAGE(i, Whole(A))) ==>
       (Holds(R, ax, App(pi1 o Image(f), a)) <=> 
        Holds(R, ax, App(pi,a)))’ 
 >-- (rpt strip_tac >>
     fs[IMAGE_def,Whole_def] >>
     qby_tac ‘Holds(R, App(i, a'), App(pi, a)) <=> 
              IN(a',a)’
     >-- (last_x_assum 
         (qsspecl_then 
              [‘App(i,a')’,‘App(pi,a)’] assume_tac) >>
         rev_drule Inj_eq_eq >>
         qpick_x_assum ‘Inj(pi)’ assume_tac >>
         drule Inj_eq_eq >> fs[] >>
         fs[ex_mem_eq] >> 
         dimp_tac >> strip_tac >> fs[] >>
         qexistsl_tac [‘a'’,‘a’] >> arw[]) >> arw[] >>
     qpick_x_assum ‘i1 o f = i’ (assume_tac o GSYM) >>
     arw[] >> rw[App_App_o] >>
     first_assum (*was first_x_assum*)
     (qsspecl_then [‘App(i1, App(f, a'))’,
                    ‘App(pi1, App(Image(f), a))’]
      assume_tac) >>
     drule Inj_eq_eq >>
     qpick_x_assum ‘Inj(i1)’ assume_tac >>
     drule Inj_eq_eq >> fs[ex_mem_eq] >>
     rw[App_App_o] >> once_arw[] >>
     drule Bij_Inj >> drule Inj_eq_eq >>
     once_arw[] >> 
     qby_tac ‘?s. App(pi1, App(Image(f), a)) = App(pi,s)’ 
     >-- (qpick_x_assum ‘IMAGE(pi, Whole(Pow(A))) = IMAGE(pi1, Whole(Pow(A1)))’ mp_tac >>
         rw[GSYM IN_EXT_iff,IMAGE_def,Whole_def] >> 
         strip_tac >>
         first_x_assum (qsspecl_then [‘App(pi1, App(Image(f), a))’] assume_tac) >> fs[ex_mem_eq]) >>
     pop_assum strip_assume_tac >>
     once_arw[] >> 
     qpick_x_assum ‘Inj(pi)’ assume_tac >>
     drule Inj_eq_eq >> once_arw[] >>
     qsuff_tac ‘IN(a',s) <=> IN(a',a)’
     >-- (strip_tac >> pop_assum (assume_tac o GSYM) >>
          arw[] >> qpick_x_assum ‘Inj(f)’ assume_tac >>
          drule IN_IMAGE_Inj >> arw[] >> rw[Image_IMAGE] >>
          dimp_tac >> strip_tac >> fs[] >>
          qexistsl_tac [‘App(f,a')’,‘IMAGE(f,a)’] >> 
          arw[]) >>
     qby_tac ‘IN(a', a) <=> IN(App(f,a'),IMAGE(f,a))’ 
     >-- (qpick_x_assum ‘Inj(f)’ assume_tac >>
          drule IN_IMAGE_Inj >> arw[]) >> 
     qby_tac ‘IN(App(f, a'), IMAGE(f, a)) <=> 
              Holds(R,App(i1,App(f, a')),
                    App(pi1,IMAGE(f,a)))’
     >-- (first_x_assum 
         (qsspecl_then [‘App(i1, App(f, a'))’,
                        ‘App(pi1, IMAGE(f, a))’]
          assume_tac) >>
         rfs[] >> fs[App_App_o] >>
         rfs[] >> fs[ex_mem_eq] >> 
         dimp_tac >> strip_tac >> fs[] >>
         qexistsl_tac [‘ App(f, a')’,‘IMAGE(f, a)’] >>
         arw[]) >>
     qby_tac
     ‘Holds(R, App(i1, App(f, a')), App(pi1, IMAGE(f, a))) 
      <=> Holds(R, App(i, a'), App(pi1, IMAGE(f, a)))’ 
     >-- (rw[GSYM App_App_o] >> arw[]) >>
     qby_tac
     ‘Holds(R, App(i, a'), App(pi1, IMAGE(f, a))) <=>
      Holds(R, App(i, a'), App(pi, s))’    
     >-- fs[Image_IMAGE] >>
     qby_tac
     ‘Holds(R, App(i, a'), App(pi, s)) <=> IN(a',s)’      
     >-- (last_x_assum 
         (qsspecl_then [‘App(i, a')’,‘App(pi,s)’]
          assume_tac) >>
         pop_assum mp_tac >> arw[] >> rw[ex_mem_eq] >>
         strip_tac >> arw[] >> rw[App_App_o] >> arw[] >>
         dimp_tac >> strip_tac >> arw[] >> fs[] >>
         qexistsl_tac [‘a'’,‘s’] >> arw[]) >>
     arw[]) >>
 qsspecl_then [‘i’,‘pi’,‘R’] assume_tac Inj_Pow_EXT >>
 rfs[] >>
 first_x_assum (irule o iffRL) >>
 arw[] >> strip_tac (* 2 *)
 >-- (qpick_x_assum ‘IMAGE(pi, Whole(Pow(A))) = IMAGE(pi1, Whole(Pow(A1)))’ (assume_tac o GSYM) >> arw[] >>
     rw[IMAGE_def,Whole_def] >> qexists_tac ‘a’ >> rw[]) >>
 rw[App_App_o,IMAGE_def,Whole_def] >> 
 qexists_tac ‘App(Image(f),a)’ >> rw[])
(form_goal
 “!X A i:A->X pi:Pow(A)->X R:X~>X. Inj(i) & Inj(pi) & 
  (!ax:mem(X) sx:mem(X). 
  (?a. ax = App(i,a)) & (?s. sx = App(pi,s)) ==> 
   (Holds(R,ax,sx) <=>
    ?a s. IN(a,s) & App(i,a) = ax & App(pi,s)= sx)) ==>
  !A1 i1:A1->X pi1:Pow(A1) -> X. 
  Inj(i1) & Inj(pi1) & 
  (!ax:mem(X) sx:mem(X). 
  (?a1. ax = App(i1,a1)) & (?s1. sx = App(pi1,s1)) ==> 
   (?a1 s1. IN(a1,s1) & App(i1,a1) = ax & App(pi1,s1)= sx) <=>
    Holds(R,ax,sx)) &   IMAGE(i,Whole(A)) = IMAGE(i1, Whole(A1)) & 
  IMAGE(pi,Whole(Pow(A))) = IMAGE(pi1, Whole(Pow(A1))) ==>
  ?f:A->A1 . 
   Bij(f) &
   i1 o f = i & pi1 o Image(f) = pi”));
*)

val Upow_choice_independence = prove_store(
"Upow_choice_independence",
e0
(rpt strip_tac >>
 qby_tac
 ‘?A i:A->X pi:Pow(A) ->X.
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,n0) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0))& 
   !a:mem(A) s. 
                Holds(R,App(i,a),App(pi,s)) <=> IN(a,s)’ 
 >-- (drule $ iffLR Upows_def >> 
     pop_assum strip_assume_tac >>
     first_x_assum drule >> arw[]) >>
 pop_assum (x_choosel_then ["uA","ui","upi"] 
            strip_assume_tac) >>
 qexistsl_tac [‘uA’,‘ui’,‘upi’] >>
 once_arw[] >> rw[] >> 
 rpt strip_tac >>
 qsspecl_then [‘ui’,‘upi’,‘R’] assume_tac 
     Inj_Pow_choice_independence >>
     rfs[] >>
     first_x_assum irule >> arw[] >> 
     rpt strip_tac (* 2 *)
     >-- (arw[] >> drule Inj_eq_eq >> arw[] >>
         qpick_x_assum ‘Inj(i)’ assume_tac >>
         drule Inj_eq_eq >> arw[] (* need automate*) >>
         dimp_tac >> rpt strip_tac >> fs[] >>
         qexistsl_tac [‘a1’,‘s1’] >> arw[]) >>
     arw[] >> rev_drule Inj_eq_eq >> arw[] >>
     qpick_x_assum ‘Inj(upi)’ assume_tac >>
     drule Inj_eq_eq >> arw[] (* need automate*) >>
     dimp_tac >> rpt strip_tac >> fs[] >>
     qexistsl_tac [‘a’,‘s’] >> arw[])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !n0. Lt(n0,n) ==>
   ?uA ui:uA->X upi:Pow(uA) ->X.
   Inj(ui) & Inj(upi) & 
      IMAGE(ui,Whole(uA)) = FIB(p,n0) &  
      IMAGE(upi,Whole(Pow(uA))) = FIB(p,Suc(n0)) &
      (!a:mem(uA) s. 
                    Holds(R,App(ui,a),App(upi,s)) <=> IN(a,s)) &
   !A i:A->X pi:Pow(A) ->X.
      (Inj(i) & Inj(pi) & 
      IMAGE(i,Whole(A)) = FIB(p,n0) &  
      IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0)) &
      (!a:mem(A) s.
                  Holds(R,App(i,a),App(pi,s)) <=> IN(a,s)))==>
      ?f:uA->A. 
       Bij(f) & i o f = ui & pi o Image(f) = upi”));

val FIB_PREIM_FIB = prove_store("FIB_PREIM_FIB",
e0
(rpt strip_tac >> 
 rw[GSYM IN_EXT_iff,FIB_def,PREIM_def,IN_Sing] >>
 rpt strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘App(i,x')’ >> rw[] >>
     qexists_tac ‘x’ >> rw[] >> arw[GSYM App_App_o]) >>
 qexists_tac ‘x’ >> rw[] >>  
 last_x_assum (assume_tac o GSYM) >> arw[App_App_o])
(form_goal
 “!A1 A2 i:A1->A2.
   !X p1:A1->X p2:A2->X. p2 o i = p1 ==>
   !x.FIB(p1,x) = PREIM(i,FIB(p2,x))”));


(*
val Apr_def = AX1 |> qspecl [‘A’,‘A’] |> fVar_sInst_th
 “P(a1:mem(A),a2:mem(A))” “?x1 x2. App(f:X->A,x1) = a1 & App(f,x2) =
 a2 & Holds(R0,x1,x2)” |> qsimple_uex_spec "Apr" [‘f’,‘R0’] |> gen_all
*)
 
val Image_Id = prove_store("Image_Id",
e0
(rpt strip_tac >>
 irule $ iffLR FUN_EXT >> rw[Id_def,Image_IMAGE] >>
 rw[IMAGE_Id])
(form_goal “!A. Image(Id(A)) = Id(Pow(A))”));


val Upows_p1_O_iff_z1 = prove_store("Upows_p1_O_iff_z1",
e0
(rpt strip_tac >>
 drule $ iffLR Upows_def >>
 qby_tac ‘IMAGE(z, Whole(N)) = FIB(p, O)’ 
 >-- (once_arw[] >> rw[]) >>
 pop_assum mp_tac >>
 pop_assum_list $ map_every $ K all_tac >>
 rw[GSYM IN_EXT_iff,IMAGE_def,Whole_def,PREIM_def,FIB_def,IN_Sing] >> rpt strip_tac >> arw[] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- rfs[] >>
 qexists_tac ‘O’ >> arw[])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !x. (?n. x = App(z,n)) <=> App(p,x) = O”));



val Upows_Le_n = prove_store("Upows_Le_n",
e0
(rpt strip_tac >>
 fs[Upows_def] >> last_x_assum mp_tac >>
 pop_assum_list $ map_every (K all_tac) >>
 rw[GSYM IN_EXT_iff,IMAGE_def,Whole_def,PREIM_def,FIB_def,IN_Sing] >> rpt strip_tac >>
 fs[Les_def] >> pop_assum (assume_tac o GSYM) >> arw[] >>
 qexists_tac ‘x’ >> rw[])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !x. Le(App(p,x),n) ”));


val Upows_Lt_i_ex = prove_store("Upows_Lt_i_ex",
e0
(rpt strip_tac >>
 drule $ iffLR Upows_def >> 
 pop_assum strip_assume_tac >>
 first_x_assum irule >> arw[])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !n0. Lt(n0,n) ==>
 ?A i:A->X pi:Pow(A) ->X.
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,n0) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0))& 
   !a:mem(A) s. 
                Holds(R,App(i,a),App(pi,s)) <=> IN(a,s)”));


val IMAGE_eq_FIB = prove_store("IMAGE_eq_FIB",
e0
(rpt strip_tac >>
 rw[GSYM IN_EXT_iff,IMAGE_def,Whole_def,
    PREIM_def,FIB_def,IN_Sing] >>
 dimp_tac >> rpt strip_tac >> fs[] (* 2 *)
 >-- (dimp_tac >> strip_tac >> fs[] (* 2 *)
     >-- (first_x_assum 
         (qsspecl_then [‘App(f,a)’] assume_tac) >>
         qby_tac ‘?a'. IN(a',s) & App(f,a) = App(f,a')’ 
         >-- (qexists_tac ‘a’ >> arw[]) >>
     first_x_assum (drule o iffLR) >>
     pop_assum strip_assume_tac >> rfs[])  >>
     flip_tac >> arw[] >> qexists_tac ‘c’ >> rw[])  >>
 flip_tac >> arw[] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘c’ >> arw[]) >>
 arw[])
(form_goal
 “!A B f:A->B s C p:B->C c. IMAGE(f,s) = FIB(p,c) <=> 
  !b. (?a. IN(a,s) & App(f,a) = b) <=> App(p,b) = c”));

val Inj_Inj_o = prove_store("Inj_Inj_o",
e0
(rpt strip_tac >>
 rw[Inj_def] >> rw[App_App_o] >>
 fs[Inj_def] >> rpt strip_tac >>
 first_x_assum irule >>
 first_x_assum irule >> arw[])
(form_goal
 “!A B f:A->B.Inj(f) ==>
   !C g:B->C. Inj(g) ==> Inj(g o f)”));



val Inj_o_comm = prove_store("Inj_o_comm",
e0
(rpt strip_tac >>
 arw[IMAGE_o] >> rw[IMAGE_eq_FIB] >>
 rw[FIB_def,PREIM_def,IN_Sing] >>
 qpick_x_assum ‘p2 o f = p1’ (assume_tac o GSYM) >>
 arw[] >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rfs[App_App_o] >> fs[]) >>
 qby_tac ‘?b0. App(f,b0) = b'’ 
 >-- fs[Bij_def,Surj_def] >>
 pop_assum strip_assume_tac >> qexists_tac ‘b0’ >>
 arw[] >> qexists_tac ‘b’ >> arw[App_App_o])
(form_goal
 “!X1 X2 f:X1->X2. Bij(f) ==>
   !B p1:X1->B p2:X2->B. p2 o f = p1 ==>
   !A i b. IMAGE(i, Whole(A)) = FIB(p1, b) ==>  
   IMAGE(f o i:A->X1,Whole(A)) = FIB(p2:X2->B,b)”
   ));



val Inj_Apr = prove_store("Inj_Apr",
e0
(rw[Apr_def] >> rpt strip_tac >>
 drule Inj_eq_eq >> arw[] >> dimp_tac 
 >-- (strip_tac >> fs[]>> rfs[]) >>
 strip_tac >>
 qexistsl_tac [‘a1’,‘a2’] >> arw[])
(form_goal
 “!A B f:A->B. Inj(f) ==>
  !R:A~>A a1 a2. Holds(Apr(f,R),App(f,a1),App(f,a2)) <=> 
  Holds(R,a1,a2) ”));

val Bij_Apr = prove_store("Bij_Apr",
e0
(rpt strip_tac >> drule Bij_Inj >>
 drule Inj_Apr >> arw[])
(form_goal
 “!A B f:A->B. Bij(f) ==>
  !R:A~>A a1 a2. Holds(Apr(f,R),App(f,a1),App(f,a2)) <=> 
  Holds(R,a1,a2) ”));


val Upows_iso_unique = prove_store("Upows_iso_unique",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘!n x. App(p1,x) = n ==> App(f1,x) = App(f2,x)’ 
 >-- (rpt strip_tac >>
     irule $ iffLR FUN_EXT >> strip_tac >>
     first_x_assum irule >> qexists_tac ‘App(p1,a)’>> 
     rw[]) >> 
 ind_with N_induct >> strip_tac 
 >-- (rpt strip_tac >>
     qsuff_tac ‘?n. x = App(z1,n)’ 
     >-- (strip_tac >> arw[GSYM App_App_o]) >>
     rev_drule Upows_p1_O_iff_z1 >> arw[]) >>
 rpt strip_tac >>
 qby_tac ‘Lt(n',n)’ 
 >-- (irule $ iffRL Lt_Le_Suc >>
     rev_drule Upows_Le_n >>   
     first_x_assum (qsspecl_then [‘x’] assume_tac) >> 
     rfs[]) >>
 rev_drule Upows_Lt_i_ex >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qby_tac ‘f1 o i = f2 o i’ 
 >-- (irule $ iffLR FUN_EXT >>
     rw[App_App_o] >> strip_tac >>
     first_x_assum irule >> 
     rev_drule $ iffLR IMAGE_eq_FIB >>
     pop_assum (assume_tac o GSYM) >> arw[] >>
     qexists_tac ‘a’ >> rw[] >> rw[Whole_def]) >>
 drule $ iffLR IMAGE_eq_FIB >>
 pop_assum mp_tac >> rw[Whole_def] >> strip_tac >>
 qsuff_tac ‘f1 o pi = f2 o pi’  
 >-- (strip_tac >>
     first_x_assum (drule o iffRL) >>
     pop_assum (strip_assume_tac o GSYM) >>
     arw[GSYM App_App_o]) >> 
 qby_tac ‘Inj(f1 o pi) &  Inj(f1 o i) & 
          Inj(f2 o pi) &  Inj(f2 o i)’
 >-- (rev_drule Bij_Inj >> drule Bij_Inj >>
     rpt strip_tac >> irule Inj_Inj_o >> arw[])  >>
 qby_tac ‘IMAGE(f1 o i,Whole(A)) = FIB(p2,n')’ 
 >-- (irule Inj_o_comm >> arw[] >> qexists_tac ‘p1’>>rw[])>>
 qby_tac ‘IMAGE(f2 o i,Whole(A)) = FIB(p2,n')’ 
 >-- (irule Inj_o_comm >> arw[] >> qexists_tac ‘p1’>>rw[])>>
 qby_tac ‘IMAGE(f1 o pi, Whole(Pow(A))) =
          FIB(p2,Suc(n'))’
 >-- (irule Inj_o_comm >> arw[] >>
     qexists_tac ‘p1’ >> rw[]) >>
 qby_tac ‘IMAGE(f2 o pi, Whole(Pow(A))) =
          FIB(p2,Suc(n'))’
 >-- (irule Inj_o_comm >> arw[] >>
     qexists_tac ‘p1’ >> rw[]) >>
 qby_tac 
 ‘?iso:A -> A.
   Bij(iso) & (f2 o i) o iso = f1 o i &
   (f2 o pi) o Image(iso) = f1 o pi’ 
 >-- (irule Inj_Pow_choice_independence >>
     once_arw[] >> rw[] >> 
     qexists_tac ‘R2’ >> rpt strip_tac (* 2 *)
     >-- (qpick_x_assum ‘R2 = Apr(f2, R1)’ (K all_tac) >> arw[] >>
         qpick_x_assum ‘f1 o i = f2 o i’ (assume_tac o GSYM) >> arw[] >>
         rev_drule Bij_Inj >> drule Inj_eq_eq >>
         arw[Apr_def,App_App_o] >>   
         qpick_x_assum ‘Inj(i)’ assume_tac  >> drule Inj_eq_eq >>
         qpick_x_assum ‘Inj(pi)’ assume_tac >> drule Inj_eq_eq >> arw[] >>
         qpick_x_assum ‘!a s. Holds(R1,App(i,a),App(pi,s)) <=> IN(a,s)’
         (assume_tac o GSYM) >> arw[]  >> 
         dimp_tac >> rpt strip_tac >> fs[] (* 2 *)
         >-- (qexistsl_tac [‘a’,‘s’] >> rfs[]) >>
         qexistsl_tac [‘App(i,a)’,‘App(pi,s)’] >> arw[]) >>
     qpick_x_assum ‘R2 = Apr(f1, R1)’ (K all_tac) >> arw[] >>
     qpick_x_assum ‘Bij(f2)’ assume_tac>>
     drule Bij_Inj >> drule Inj_eq_eq >> 
     arw[Apr_def,App_App_o] >>   
     qpick_x_assum ‘Inj(i)’ assume_tac  >> drule Inj_eq_eq >>
     qpick_x_assum ‘Inj(pi)’ assume_tac >> drule Inj_eq_eq >> arw[] >>
     qpick_x_assum ‘!a s. Holds(R1,App(i,a),App(pi,s)) <=> IN(a,s)’
     (assume_tac o GSYM) >> arw[]  >> 
     dimp_tac >> rpt strip_tac >> fs[] (* 2 *)
     >-- (qexistsl_tac [‘a1’,‘s1’] >> rfs[]) >>
     qexistsl_tac [‘App(i,a1)’,‘App(pi,s1)’] >> arw[]) >>
 pop_assum strip_assume_tac >>
 qby_tac ‘iso = Id(A)’ 
 >-- (irule Inj_lcancel >>
     qexistsl_tac [‘X2’,‘f2 o i’] >> arw[] >>
     rw[IdR]) >> fs[] >>
 fs[Image_Id] >> fs[IdR])
(form_goal
 “!n X1 p1:X1->N R1:X1~>X1 z1:N->X1 
     X2 p2:X2->N R2:X2~>X2 z2:N->X2. 
  Upows(n,p1,R1,z1) & Upows(n,p2,R2,z2) ==>
  !f1:X1->X2 f2:X1->X2.
              Bij(f1) & Bij(f2) & 
              p2 o f1 = p1 & 
              R2 = Apr(f1,R1) & 
              f1 o z1 = z2 &
              p2 o f2 = p1 & 
              R2 = Apr(f2,R1) & 
              f2 o z1 = z2 ==> f1 = f2”));


val IMAGE_Union = prove_store("IMAGE_Union",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IMAGE_def,IN_Union] >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 4 *)
 >-- (disj1_tac >> qexists_tac ‘a’ >> arw[]) 
 >-- (disj2_tac >> qexists_tac ‘a’ >> arw[]) 
 >-- (qexists_tac ‘a’ >> arw[]) >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!A B f:A->B s1 s2. IMAGE(f,Union(s1,s2)) = Union(IMAGE(f,s1),IMAGE(f,s2))”));

(*
val SS_of_coPr = prove_store("SS_of_coPr",
e0
()
(form_goal “!A B s. Union(PREIM(i1(A,B),s),PREIM(i2(A,B),s)) = ”));
*)


val IMAGE_coPa = prove_store("IMAGE_coPa",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IMAGE_def,IN_Union,PREIM_def] >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 3 *)
 >-- (qsspecl_then [‘a’] strip_assume_tac i1_or_i2 (* 2 *)
     >-- (disj1_tac >> qexists_tac ‘a'’ >> fs[GSYM App_App_o,coPa_def] >>
         qexists_tac ‘App(i1(A,B),a')’ >> arw[]) >>
     disj2_tac >> qexists_tac ‘b’ >> fs[GSYM App_App_o,coPa_def] >>
     qexists_tac ‘App(i2(A,B),b)’ >> arw[]) 
 >-- (qexists_tac ‘b’ >> arw[] >> 
     qpick_x_assum ‘App(i1(A, B), a) = b’ (assume_tac o GSYM) >>
     arw[GSYM App_App_o,coPa_def]) >>
 qexists_tac ‘b’ >> arw[] >>
 qpick_x_assum ‘App(i2(A,B),a) = b’ (assume_tac o GSYM) >>
 arw[GSYM App_App_o,coPa_def])
(form_goal
 “!A X f:A->X B g:B->X s. IMAGE(coPa(f,g),s) = 
  Union(IMAGE(f,PREIM(i1(A,B),s)),
        IMAGE(g,PREIM(i2(A,B),s)))”));

val PREIM_i12_Whole = prove_store("PREIM_i12_Whole",
e0
(rpt gen_tac >> rw[GSYM IN_EXT_iff,PREIM_def,Whole_def] >>
 rpt strip_tac >> rw[ex_mem_eq])
(form_goal “!A B. PREIM(i1(A,B),Whole(A+B)) = Whole(A) &
                  PREIM(i2(A,B),Whole(A+B)) = Whole(B) ”));

val IMAGE_coPa_Whole = prove_store("IMAGE_coPa_Whole",
e0
(rpt strip_tac >> rw[IMAGE_coPa,PREIM_i12_Whole])
(form_goal
 “!A X f:A->X B g:B->X. IMAGE(coPa(f,g),Whole(A+B)) = 
  Union(IMAGE(f,Whole(A)),
        IMAGE(g,Whole(B)))”));


val Les_Suc = prove_store("Les_Suc",
e0
(rw[GSYM IN_EXT_iff,Les_def,Ins_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (drule Le_Suc >> pop_assum strip_assume_tac >> arw[]) 
 >-- arw[Le_refl]  >>
 irule Le_Lt_Le >> qexists_tac ‘n’ >> arw[Lt_Suc])
(form_goal “!n. Les(Suc(n)) = Ins(Suc(n),Les(n))”));

val Upows_z_Inj = prove_store("Upows_z_Inj",
e0
(rpt strip_tac >> fs[Upows_def])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==> Inj(z)”));


val Upows_IMAGE_p = prove_store("Upows_IMAGE_p",
e0
(rpt strip_tac >> fs[Upows_def])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>  IMAGE(p, Whole(X)) = Les(n)”));


val Pow_NOT_EMPTY = prove_store("Pow_NOT_EMPTY",
e0
(strip_tac >> qexists_tac ‘Whole(A)’ >> rw[])
(form_goal “!A. ?s:mem(Pow(A)). T”));


val Union_comm = prove_store("Union_comm",
e0
(rw[GSYM IN_EXT_iff,IN_Union] >> rpt strip_tac >>
 dimp_tac >> strip_tac >> arw[])
(form_goal “!A s1 s2:mem(Pow(A)). Union(s1,s2) = Union(s2,s1)”));

(*EXISTS_EQN_FCONV “?b':mem(B). b' = b & App(f:A->B,a) = b'”*)

fun EXISTS_EQN_FCONV f = 
    case view_form f of
        vQ("?",n,s,b) => 
        let val (eqn, pred) = dest_conj b
            val (x,y) = dest_eq eqn
            val eqnth = assume eqn
            val predth = assume pred
            val p2p' = basic_fconv 
                           (rewr_conv eqnth) no_fconv pred
            val th1 = dimpl2r p2p' |> undisch 
            val cjed_th1 = conj_assum eqn pred th1
            val l2r = existsE (n,s) (assume f) cjed_th1 |> disch f
            val p' = snd o dest_dimp o concl $ p2p'
            val p'th = assume p'
            val th2 = conjI (refl y) p'th
            val th3 = existsI (n,s) y b th2
            val r2l = disch p' th3
        in dimpI l2r r2l
        end
      | _ => raise ERR ("EXISTS_EQN_FCONV.input is not an existensial",[],[],[f])


val IN_FIB = prove_store("IN_FIB",
e0
(rw[FIB_def,PREIM_def,IN_Sing] >>
 rpt strip_tac >> 
 basic_fconv_tac no_conv EXISTS_EQN_FCONV)
(form_goal “!A B f:A->B a b. IN(a,FIB(f,b)) <=> App(f,a) = b”));


val FIB_constf_Empty = prove_store("FIB_constf_Empty",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IN_FIB,Empty_def,constf_def] >>
 flip_tac >> arw[] (*if strip then fs then # Exception-
   ERR
     ("sort of the variable to be abstract has extra variable(s)", [], [A],
      []) raised*)) 
(form_goal
 “!B b0 b:mem(B). ~(b = b0) ==>
  !A. FIB(constf(A,b0),b) = Empty(A)”));


val Upows_IMAGE_z = prove_store("Upows_IMAGE_z",
e0
(rpt strip_tac >> fs[Upows_def])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  IMAGE(z, Whole(N)) = FIB(p, O)”));

val NOT_Suc_Le = SUC_NOT_LESS_EQ;
(*
prove_store("NOT_Suc_Le",
e0
(strip_tac >> rw[NOT_LESS_EQ])
(form_goal “!n. ~(Le(Suc(n),n))”));
*)

val NOT_ex_F = prove_store("NOT_ex_F",
e0
(strip_tac >> dimp_tac >> strip_tac)
(form_goal “!A. (?a:mem(A).F) <=> F”));

val i1_eq_eq = prove_store("i1_eq_eq",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] assume_tac i1_Inj >>
 drule Inj_eq_eq >> arw[])
(form_goal “!A B a1 a2. App(i1(A,B),a1) = App(i1(A,B),a2) <=> a1 = a2”));



val i2_eq_eq = prove_store("i2_eq_eq",
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘B’] assume_tac i2_Inj >>
 drule Inj_eq_eq >> arw[])
(form_goal “!A B b1 b2. App(i2(A,B),b1) = App(i2(A,B),b2) <=> b1 = b2”));


val FIB_coPa = prove_store("FIB_coPa",
e0
(rpt strip_tac >> 
 rw[GSYM IN_EXT_iff,FIB_def,PREIM_def,IN_Sing,IN_Union,IMAGE_def] >>
 strip_tac >>
 qsspecl_then [‘x'’] strip_assume_tac i1_or_i2 (* 2*) >> 
 arw[i1_eq_eq,i2_eq_eq,i1_ne_i2,NOT_ex_F] >>
 pop_assum (K all_tac) 
 >-- (dimp_tac >> strip_tac (* 2 *)
     >-- (qexists_tac ‘a’>> arw[] >> qexists_tac ‘App(f,a)’ >>
         fs[GSYM App_App_o,coPa_def]) >>
     qexists_tac ‘x’ >> arw[GSYM App_App_o,coPa_def]) >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (disj2_tac >> qexists_tac ‘b’ >> rw[] >>
     qexists_tac ‘x’ >> fs[GSYM App_App_o,coPa_def]) 
 >-- fs[GSYM i1_ne_i2] >>
 qexists_tac ‘x’>> arw[GSYM App_App_o,coPa_def])
(form_goal
 “!A X f:A->X B g:B->X x.
  FIB(coPa(f,g),x) = Union(IMAGE(i1(A,B),FIB(f,x)),
IMAGE(i2(A,B),FIB(g,x)))”));



val Inj_IMAGE_eq_eq = prove_store("Inj_IMAGE_eq_eq",
e0
(rpt strip_tac >> drule Inj_Image_Inj >>
 fs[Inj_def] >> fs[Image_IMAGE] >> 
 dimp_tac >> strip_tac >> arw[] >>
 first_x_assum drule >> arw[])
(form_goal
 “!A B f:A->B. Inj(f) ==>
   (!s1 s2. IMAGE(f,s1) = IMAGE(f,s2) <=> s1 = s2)”));


val i1_IMAGE_eq_eq = prove_store("i1_IMAGE_eq_eq",
e0
(rpt strip_tac >> irule Inj_IMAGE_eq_eq >>
 rw[i1_Inj])
(form_goal
 “!A B.
   (!s1 s2. IMAGE(i1(A,B),s1) = IMAGE(i1(A,B),s2) <=> s1 = s2)”));



val Upows_FIB_n_Lt_Empty = prove_store("Upows_FIB_n_Lt_Empty",
e0
(rpt strip_tac >>
 qby_tac ‘IMAGE(p, Whole(X)) = Les(n)’ 
 >-- fs[Upows_def] >>
 rw[GSYM IN_EXT_iff,IN_FIB,Empty_def] >>
 strip_tac >> 
 fs[GSYM IN_EXT_iff,Les_def,Whole_def,IMAGE_def] >>
 first_x_assum (qsspecl_then [‘App(p,x)’] assume_tac) >>
 fs[ex_mem_eq] >> ccontra_tac >>
 fs[GSYM NOT_LESS])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !n1. Lt(n,n1) ==> FIB(p, n1) = Empty(X)”));

(*
val Upows_Injs_ex = prove_store("Upows_Injs_ex",
e0
cheat
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !n0. Le(n0,n) ==>
  ?A i:A->X. Inj(i) & IMAGE(i,Whole(A)) = FIB(p,n0)”));

*)


val Upows_R = prove_store("Upows_R",
e0
(rpt strip_tac >> drule $ iffLR Upows_def >>
 pop_assum strip_assume_tac >>
 first_x_assum (qspecl_then [‘x’,‘s’] accept_tac))
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  (!x:mem(X) s:mem(X). 
  Holds(R,x,s) <=> 
  (Lt(App(p,x),n) & 
  Suc(App(p,x)) = App(p,s) &
  ?A i:A->X pi:Pow(A) ->X a:mem(A) sa:mem(Pow(A)). 
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,App(p,x)) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,App(p,s)) & 
   (!a:mem(A) s. 
                Holds(R,App(i,a),App(pi,s)) <=> IN(a,s)) & 
   IN(a,sa) & App(i,a) = x & App(pi,sa) = s))”));


val Suc_Le_Lt = prove_store("Suc_Le_Lt",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (irule Lt_Le_Lt >> qexists_tac ‘Suc(a)’ >>
     arw[Lt_Suc]) >>
 ccontra_tac >> fs[NOT_LESS_EQ,Lt_Suc_Le] >> 
 qby_tac ‘Lt(a,a)’ 
 >-- (irule Lt_Le_Lt >> qexists_tac ‘b’ >> arw[]) >>
 fs[Lt_def])
(form_goal “!a b. Le(Suc(a),b) <=> Lt(a,b)”));



val Upows_R_last_clause = prove_store("Upows_R_last_clause",
e0
(rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum drule >>
     qby_tac ‘Lt(App(p, x), n)’ 
     >-- (rev_drule $ iffRL IN_EXT_iff  >>
         fs[IMAGE_def,Les_def] >> rw[GSYM Suc_Le_Lt] >>
         first_x_assum (irule o iffLR) >> qexists_tac ‘s’ >>
         arw[Whole_def]) >>
     arw[] >>
     first_x_assum drule >>
     pop_assum strip_assume_tac >>
     qexistsl_tac [‘A’,‘i’,‘pi’] >> arw[] >>
     qsuff_tac ‘?a sa. App(i,a) = x & App(pi,sa) = s’ 
     >-- (strip_tac >> qexistsl_tac [‘a’,‘sa’] >> fs[] >>
         first_x_assum (irule o iffLR) >> arw[]) >>
     drule $ iffLR IMAGE_eq_FIB >>
     first_x_assum (qsspecl_then [‘s’] assume_tac) >> rfs[] >>
     qpick_x_assum ‘IMAGE(i, Whole(A)) = FIB(p, App(p, x))’ assume_tac >>
     drule $ iffLR IMAGE_eq_FIB >> 
     first_x_assum (qsspecl_then [‘x’] assume_tac) >> fs[] >>
     qexistsl_tac [‘a'’,‘a’] >> arw[]) >>
 pop_assum mp_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
 strip_tac >> pop_assum (assume_tac o GSYM) >> arw[]) 
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  IMAGE(p:X->N,Whole(X)) = Les(n) &  
 Inj(z) &  
 IMAGE(z:N->X,Whole(N)) = FIB(p,O) & 
 (!n0. Lt(n0,n) ==>
 ?A i:A->X pi:Pow(A) ->X.
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,n0) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0))& 
   (!a:mem(A) s. 
   Holds(R,App(i,a),App(pi,s)) <=> IN(a,s))) ==>
  (!x s. Holds(R,x,s) ==> Suc(App(p,x)) = App(p,s)) ==> 
  (!x:mem(X) s:mem(X). 
  Holds(R,x,s) <=> 
  (Lt(App(p,x),n) & 
  Suc(App(p,x)) = App(p,s) &
  ?A i:A->X pi:Pow(A) ->X a:mem(A) sa:mem(Pow(A)). 
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,App(p,x)) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,App(p,s)) & 
   (!a:mem(A) s. 
                Holds(R,App(i,a),App(pi,s)) <=> IN(a,s)) & 
   IN(a,sa) & App(i,a) = x & App(pi,sa) = s))”));


val Upows_alt = prove_store("Upows_alt",
e0
(rpt strip_tac >>
 rw[Upows_def] >> dimp_tac >> strip_tac (* 2 *)
 >-- (pop_assum mp_tac >> once_arw[] >> rw[] >>
     strip_tac >>
     rpt strip_tac >>
     first_x_assum (drule o iffLR) >>
     arw[]) >>
 arw[] >>
 irule Upows_R_last_clause >> arw[] >>
 qexistsl_tac [‘z’] >> arw[])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) <=>
IMAGE(p:X->N,Whole(X)) = Les(n) &  
 Inj(z) &  
 IMAGE(z:N->X,Whole(N)) = FIB(p,O) & 
 (!n0. Lt(n0,n) ==>
 ?A i:A->X pi:Pow(A) ->X.
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,n0) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0))& 
   (!a:mem(A) s. 
   Holds(R,App(i,a),App(pi,s)) <=> IN(a,s))) & 
 (!x s. Holds(R,x,s) ==> Suc(App(p,x)) = App(p,s)) ”));

(*
val Upows_last_clause = prove_store("Upows_last_clause",
e0
(rpt strip_tac >> once_arw[] >>
 pop_assum (K all_tac) >>
 qcases ‘?x0. x  = App(i1(X,Pow(A)),x0)’ >>
 qcases ‘?s0. s  = App(i1(X,Pow(A)),s0)’ (* 4 *)
 >-- (pop_assum_list (map_every strip_assume_tac) >>
     once_arw[] >> once_rw[i1_eq_eq] >>
     once_rw[GSYM i1_ne_i2] >> rw[] >> rw[NOT_ex_F] >>
     qby_tac
     ‘(?(x' : mem(X))  (s' : mem(X)). x' = x0 & s' = s0 & Holds(R, x', s'))  <=> Holds(R,x0,s0)’ >-- cheat >>
     once_arw[] >> pop_assum (K all_tac) >>
     once_arw[GSYM App_App_o] >> once_rw[coPa_def]>>
     once_rw[FIB_coPa]>> 
     qby_tac ‘~(App(p,x0) = Suc(n))’ 
     >-- cheat >>
     drule FIB_constf_Empty >> once_arw[] >>
     qby_tac ‘~(App(p,s0) = Suc(n))’ 
     >-- cheat >>
     drule FIB_constf_Empty >> once_arw[] >>
     once_rw[IMAGE_Empty] >> once_rw[Union_Empty2] >>
     dimp_tac >> strip_tac >--
     (drule Upows_R >>
     first_x_assum (drule o iffLR) >>
     pop_assum strip_assume_tac >>
     drule Lt_Le >> once_arw[] >> rw[] >>
     qexistsl_tac [‘A'’,‘i1(X,Pow(A)) o i'’,‘i1(X,Pow(A)) o pi’,
                   ‘a’,‘sa’] >>
     once_arw[App_App_o] >> once_rw[] >> once_rw[i1_eq_eq] >>
     once_rw[IMAGE_o] >> once_rw[i1_IMAGE_eq_eq] >>
     once_rw[GSYM i1_ne_i2]  >> once_rw[] >> rw[] >>
     rw[NOT_ex_F] >> once_arw[] >> rw[] >>
     drule Inj_Inj_o >> 
     qspecl_then [‘X’,‘Pow(A)’] assume_tac i1_Inj >>
     first_x_assum drule >>
     arw[] >>
     qpick_x_assum ‘Inj(i')’ assume_tac >>
     drule Inj_Inj_o >> 
     first_x_assum drule >> arw[] >>
     qpick_x_assum ‘!a s. Holds(R,App(i',a),App(pi,s)) <=> IN(a,s)’
     assume_tac >> pop_assum (assume_tac o GSYM) >> once_arw[] >>
     pop_assum_list (map_every (K all_tac)) >>
     rpt strip_tac >> dimp_tac >> strip_tac >> fs[] >> rfs[] >>
     qexistsl_tac [‘App(i',a')’,‘App(pi,s')’] >> arw[]) >>
     drule Upows_R >>
     once_arw[] >> pop_assum (K all_tac) >>
     qby_tac ‘Lt(App(p, x0), n)’ 
     >-- cheat >> once_arw[] >> rw[] >>
     qby_tac ‘?i0.  i' = i1(X,Pow(A)) o i0’ 
     >-- cheat >> pop_assum strip_assume_tac >>
     qby_tac ‘?pi0. pi = i1(X,Pow(A)) o pi0’
     >-- cheat >> pop_assum strip_assume_tac >>
     qexistsl_tac [‘A'’,‘i0’,‘pi0’,‘a’,‘sa’] >>
     once_arw[] >> rw[] >> fs[] (*fs slow*) >>
     fs[App_App_o] >> fs[GSYM i1_ne_i2] >> fs[NOT_ex_F] >>
     fs[i1_eq_eq] >> fs[IMAGE_o,i1_IMAGE_eq_eq] >>
     drule Inj_o_Inj >> arw[] >>
     rev_drule Inj_o_Inj >> arw[] >>
     qpick_x_assum ‘!(a' : mem(A'))  (s : mem(Pow(A'))).
               (?(x : mem(X))  (s' : mem(X)).
                   x = App(i0, a') & s' = App(pi0, s) & Holds(R, x, s')) <=>
               IN(a', s)’ mp_tac >>
     pop_assum_list (map_every (K all_tac)) >>
     strip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
     rpt strip_tac >> dimp_tac >> strip_tac >> rfs[] >> fs[] >>
     qexistsl_tac [‘App(i0,a')’,‘App(pi0,s')’] >> arw[]) >--
 qby_tac ‘?s0. s = App(i2(X,Pow(A)),s0)’ >-- cheat >> 
 qpick_x_assum ‘~(?(s0 : mem(X)). s = App(i1(X, Pow(A)), s0))’
 (K all_tac) >>
 pop_assum_list (map_every strip_assume_tac) >>
 once_arw[] >> once_rw[i1_eq_eq] >>
 once_rw[App_App_o] >> once_rw[i1_eq_eq] >> once_rw[i2_eq_eq] >>
 once_rw[i1_ne_i2] >> once_rw[] >>
 rw[] >> rw[NOT_ex_F] >>
 
   

     )
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !A i:A->X. Inj(i) & IMAGE(i,Whole(A)) = FIB(p,n) ==>
  !R1.
  (!x1 s1:mem(X+Pow(A)). 
   Holds(R1,x1,s1) <=> 
   (?x s. App(i1(X,Pow(A)),x) = x1 & 
          App(i1(X,Pow(A)),s) = s1 &
          Holds(R,x,s)) |
   (?a s. App(i1(X,Pow(A)) o i,a) = x1 & 
          App(i2(X,Pow(A)),s) = s1 & 
          IN(a,s))) ==>
   !x s. Holds(R1, x, s) <=>
             Le(App(coPa(p, constf(Pow(A), Suc(n))), x), n) &
             Suc(App(coPa(p, constf(Pow(A), Suc(n))), x)) =
               App(coPa(p, constf(Pow(A), Suc(n))), s) &
             ?(A' : set)  (i : fun(A', X + Pow(A)))
             (pi : fun(Pow(A'), X + Pow(A)))  (a : mem(A'))
             (sa : mem(Pow(A'))).
               Inj(i) &
               Inj(pi) &
               IMAGE(i, Whole(A')) =
                 FIB(coPa(p, constf(Pow(A), Suc(n))),
                  App(coPa(p, constf(Pow(A), Suc(n))), x)) &
               IMAGE(pi, Whole(Pow(A'))) =
                 FIB(coPa(p, constf(Pow(A), Suc(n))),
                  App(coPa(p, constf(Pow(A), Suc(n))), s)) &
               (!(a : mem(A'))  (s : mem(Pow(A'))).
                   Holds(R1, App(i, a), App(pi, s)) <=> IN(a, s)) &
               IN(a, sa) & App(i, a) = x & App(pi, sa) = s”));

*)
val Upows_R_imp_Suc = prove_store("Upows_R_imp_Suc",
e0
(rpt strip_tac >>
 drule $ iffLR Upows_alt >>
 pop_assum strip_assume_tac >> first_x_assum irule >> arw[])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  (!x s. Holds(R,x,s) ==> Suc(App(p,x)) = App(p,s))”));

val Upows_Suc = prove_store("Upows_Suc",
e0
(rpt strip_tac >>
 rw[Upows_alt] >>
 once_rw[Lt_Suc_Le] >> 
 qby_tac ‘Inj(i1(X, Pow(A)) o z)’ 
 >-- (irule Inj_Inj_o >> rw[i1_Inj] >>
     drule Upows_z_Inj >> arw[]) >>
 qby_tac
 ‘IMAGE(coPa(p, constf(Pow(A), Suc(n))), Whole(X + Pow(A))) = Les(Suc(n))’
 >-- (rw[IMAGE_coPa_Whole,Les_Suc] >>
     qby_tac
     ‘IMAGE(constf(Pow(A), Suc(n)), Whole(Pow(A))) = 
      Sing(Suc(n))’ 
     >-- (irule IMAGE_constf >> rw[GSYM IN_EXT_iff,Whole_def,Empty_def] >> ccontra_tac >>
         qspecl_then [‘A’] strip_assume_tac Pow_NOT_EMPTY >>
         first_x_assum (qsspecl_then [‘s’] assume_tac) >>
         arw[]) >> arw[] >> once_rw[Union_comm] >>
      rw[Union_Sing] >> drule Upows_IMAGE_p >>
      arw[]) >>
 qby_tac
 ‘IMAGE(i1(X, Pow(A)) o z, Whole(N)) =
               FIB(coPa(p, constf(Pow(A), Suc(n))), O)’ 
 >-- (rw[FIB_coPa] >> 
     assume_tac $ GSYM Suc_NONZERO >>
     first_x_assum $ qspecl_then [‘n’] assume_tac >>
     drule FIB_constf_Empty >> arw[] >>
     rw[IMAGE_Empty,Union_Empty2,IMAGE_o] >>
     drule Upows_IMAGE_z >> arw[]) >>
 qby_tac
 ‘(!(n0 : mem(N)).
                 Le(n0, n) ==>
                 ?(A' : set)  (i : fun(A', X + Pow(A)))
                 (pi : fun(Pow(A'), X + Pow(A))).
                   Inj(i) &
                   Inj(pi) &
                   IMAGE(i, Whole(A')) =
                     FIB(coPa(p, constf(Pow(A), Suc(n))), n0) &
                   IMAGE(pi, Whole(Pow(A'))) =
                     FIB(coPa(p, constf(Pow(A), Suc(n))), Suc(n0)) &
                   !(a : mem(A'))  (s : mem(Pow(A'))).
                     Holds(R1, App(i, a), App(pi, s)) <=> IN(a, s))’ >--
 (rpt strip_tac >>
 rw[FIB_coPa] >> drule Le_cases >>
 pop_assum strip_assume_tac (* 2 *)
 >-- (qby_tac ‘~(n0 = Suc(n))’ 
     >-- (ccontra_tac >> fs[] >> fs[NOT_Suc_Le]) >>
     drule FIB_constf_Empty >> 
     qby_tac ‘~(Suc(n0) = Suc(n))’ 
     >-- (ccontra_tac >> fs[Suc_eq_eq,Lt_def]) >>
     drule FIB_constf_Empty >> once_arw[] >>
     once_rw[IMAGE_Empty] >> once_rw[Union_Empty2] >>
     drule Upows_Lt_i_ex >>
     first_x_assum drule >>
     pop_assum 
     (x_choosel_then ["A0","i0","pi0"] assume_tac) >> 
     qexistsl_tac [‘A0’,‘i1(X,Pow(A)) o i0’,
                   ‘i1(X,Pow(A)) o pi0’] >>
     once_rw[App_App_o] >>
     once_rw[GSYM i1_ne_i2] >> rw[] >>
     rw[NOT_ex_F] >> rw[i1_eq_eq] >>
     qby_tac ‘Inj(i1(X, Pow(A)) o i0)’ 
     >-- (irule Inj_Inj_o >> arw[i1_Inj]) >>
     qby_tac ‘Inj(i1(X, Pow(A)) o pi0)’
     >-- (irule Inj_Inj_o >> arw[i1_Inj]) >>
     once_arw[] >>
     qspecl_then [‘X’,‘Pow(A)’] assume_tac i1_Inj >>
     drule Inj_IMAGE_eq_eq >> rw[IMAGE_o] >>
     arw[]>>
     rpt strip_tac >> dimp_tac >> rpt strip_tac >> rfs[]>>
     qexistsl_tac [‘App(i0,a)’,‘App(pi0,s)’]  >>
     arw[]) >>
 fs[] >>
 qby_tac ‘FIB(p,Suc(n)) = Empty(X)’ 
 >-- (drule Upows_FIB_n_Lt_Empty >> first_x_assum irule >>
     rw[Lt_Suc]) >>
 arw[Union_Empty2] >> 
 qby_tac ‘~(n = Suc(n))’ 
 >-- rw[Suc_NEQ] >>
 drule FIB_constf_Empty >> arw[Union_Empty2,IMAGE_Empty] >>
 rw[Empty_Union,FIB_constf] >> 
 qexistsl_tac [‘A’,‘i1(X,Pow(A)) o i’,‘i2(X,Pow(A))’] >>
 once_rw[i1_ne_i2] >> rw[App_App_o] >> 
 rw[NOT_ex_F,i1_eq_eq] >> 
 rev_drule Inj_eq_eq >> arw[] >>
 rw[i2_eq_eq] >> rw[IMAGE_o] >>
 qspecl_then [‘X’,‘Pow(A)’] assume_tac i1_Inj >>
 drule Inj_IMAGE_eq_eq >> arw[] >>
 rw[i2_Inj] >>
 rev_drule Inj_Inj_o >>
 first_x_assum drule >> arw[] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> rfs[] >>
 qexistsl_tac [‘a’,‘s’] >> arw[]) >> 
 rpt strip_tac (* 5 *)
 >-- arw[] >-- arw[] >-- arw[]
 >-- (first_x_assum drule >> arw[]) >>
 first_x_assum (drule o iffLR) >>
 pop_assum (strip_assume_tac o GSYM) (* 2 *)
 >-- (once_arw[] >> rw[GSYM App_App_o,coPa_def] >> 
     drule Upows_R_imp_Suc >> first_x_assum irule >> arw[]) >>
 once_arw[] >> rw[GSYM App_App_o,coPa_def,GSYM o_assoc] >>
 rw[constf_def,Suc_eq_eq] >> 
 rev_drule $ iffLR IMAGE_eq_FIB >>
 rw[App_App_o] >>
 pop_assum (assume_tac o GSYM) >> arw[] >> qexists_tac ‘a’ >>
 rw[Whole_def])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !A i:A->X. Inj(i) & IMAGE(i,Whole(A)) = FIB(p,n) ==>
  !R1.
  (!x1 s1:mem(X+Pow(A)). 
   Holds(R1,x1,s1) <=> 
   (?x s. App(i1(X,Pow(A)),x) = x1 & 
          App(i1(X,Pow(A)),s) = s1 &
          Holds(R,x,s)) |
   (?a s. App(i1(X,Pow(A)) o i,a) = x1 & 
          App(i2(X,Pow(A)),s) = s1 & 
          IN(a,s))) ==>
  Upows(Suc(n),coPa(p,constf(Pow(A),Suc(n))),R1,i1(X,Pow(A)) o z)”));

(*
val FIB_comm = prove_store("FIB_comm",
e0
(rpt strip_tac >>
 rw[GSYM IN_EXT_iff,FIB_def,PREIM_def,IN_Sing,IMAGE_def] >>
 strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- fs[] >> )
(form_goal
 “!A B f:A->B C g:B->C h. g o f = h ==>
  !c.FIB(g,c) = IMAGE(f,FIB(h,c))
  ”));
*)
       
val IMAGE_i1_fac = prove_store("IMAGE_i1_fac",
e0
(rpt strip_tac >>
 fs[SS_def,IMAGE_def,Whole_def] >>
 assume_tac
 (P2fun |> qtinst_thm [(‘A’,‘X’),(‘B’,‘A’)] 
 |> qfVar_prpl_th1 ("P",[‘x:mem(X)’,‘a:mem(A)’],
‘App(f:X->A+B,x) = App(i1(A,B),a)’)) >>
 qby_tac ‘!x. ?!a:mem(A). App(f:X->A+B,x) = App(i1(A,B),a)’ 
 >-- (strip_tac >> uex_tac >>
     first_x_assum (qspecl_then [‘App(f,x)’] assume_tac) >>
     fs[ex_mem_eq] >> rw[i1_eq_eq] >>
     qexists_tac ‘a'’ >> rpt strip_tac >> arw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f'’ >> irule $ iffLR FUN_EXT >>
 rw[App_App_o] >> pop_assum (assume_tac o GSYM) >> arw[]
 )
(form_goal 
  “!A B X f:X->A+B. 
    SS(IMAGE(f,Whole(X)), IMAGE(i1(A,B),Whole(A))) ==>
    ?f0:X->A. f = i1(A,B) o f0”));


val IMAGE_Inj_fac = prove_store("IMAGE_Inj_fac",
e0
(rpt strip_tac >>
 fs[SS_def,IMAGE_def,Whole_def] >>
 assume_tac
 (P2fun |> qtinst_thm [(‘B’,‘X’)] 
 |> qfVar_prpl_th1 ("P",[‘a:mem(A)’,‘x:mem(X)’],
‘App(f:A->B,a) = App(i:X->B,x)’)) >>
 qby_tac ‘!a. ?!x. App(f:A->B,a) = App(i:X->B,x)’ 
 >-- (strip_tac >> uex_tac >>
     first_x_assum (qspecl_then [‘App(f,a)’] assume_tac) >>
     fs[ex_mem_eq] >> drule Inj_eq_eq >> arw[] >>
     qexists_tac ‘a'’ >> rpt strip_tac >> arw[]) >>
 first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘f'’ >> irule $ iffLR FUN_EXT >>
 rw[App_App_o] >> pop_assum (assume_tac o GSYM) >> arw[])
(form_goal 
  “!X B i:X->B. Inj(i) ==>
    !A f:A->B. SS(IMAGE(f,Whole(A)),IMAGE(i,Whole(X))) ==>
    ?f0:A->X. f = i o f0”));


val NOT_Le_Suc = prove_store("NOT_Le_Suc",
e0
(rw[NOT_LESS_EQ,Lt_Suc])
(form_goal “!n. ~(Le(Suc(n),n))”));


val IMAGE_Whole = IMAGE_def |> qspecl [‘A’,‘Whole(A)’] 
                            |> rewr_rule[Whole_def]
                            |> gen_all

val Upows_embed = prove_store("Upows_embed",
e0
(rpt strip_tac >>
 rw[Upows_alt] >>(*if rw, then very slow*) once_arw[] >> rw[] >>
 qby_tac ‘Inj(z)’
 >-- (drule Upows_z_Inj >> 
     irule Inj_o_Inj >> qexistsl_tac [‘X1’,‘inc’] >> arw[]) >>
 arw[] >>
 qby_tac ‘IMAGE(z, Whole(N)) = FIB(p, O)’ 
 >-- (rev_drule Inj_IMAGE_eq_eq >>
     first_x_assum (irule o iffLR) >> arw[GSYM IMAGE_o] >>
     drule Upows_IMAGE_z >> arw[] >>
     flip_tac >> rw[IMAGE_eq_FIB] >>
     strip_tac >> rw[FIB_def,PREIM_def,IN_Sing] >> 
     dimp_tac >> strip_tac (* 2 *)
     >-- (rfs[] >> pop_assum (assume_tac o GSYM) >> arw[GSYM App_App_o]) >>
     qby_tac ‘!x1. ~(App(p1,x1) = Suc(n)) <=> ?x. App(inc,x) = x1’ 
     >-- (flip_tac >> arw[GSYM IMAGE_Whole] >> 
         flip_tac >> rw[Whole_def,Diff_def,IN_FIB]) >>
     qsuff_tac ‘?x.App(inc,x) = b’ 
     >-- (strip_tac >> qexists_tac ‘x’ >> arw[] >>
         qexists_tac ‘O’ >> arw[] >> pop_assum (assume_tac o GSYM) >>
         fs[GSYM App_App_o] >> rfs[]) >>
     first_x_assum (irule o iffLR) >> arw[GSYM Suc_NONZERO]) >>
 arw[] >>
 qby_tac
 ‘!(x : mem(X))  (s : mem(X)).
               Holds(R1, App(inc, x), App(inc, s)) ==>
               Suc(App(p, x)) = App(p, s)’ 
 >-- (rpt strip_tac >>
     qpick_x_assum ‘p1 o inc = p’ (assume_tac o GSYM) >> arw[] >>
     rw[App_App_o] >>
     drule Upows_R_imp_Suc >> first_x_assum drule >> arw[]) >>
 arw[] >>
 rpt strip_tac >>
 qby_tac ‘Lt(n0,Suc(n))’
 >-- (irule Lt_trans >> qexists_tac ‘n’ >> arw[Lt_Suc]) >>
 drule Upows_Lt_i_ex >> first_x_assum drule >>
 pop_assum strip_assume_tac >>
 qsuff_tac
 ‘?i0:A->X pi0:Pow(A) ->  X.
   Inj(i0) & Inj(pi0) & inc o i0 = i & inc o pi0 = pi’ 
 >-- (strip_tac >>
     qexistsl_tac [‘A’,‘i0’,‘pi0’] >>
     arw[] >> arw[GSYM App_App_o] >>
     strip_tac (* 2 *)
     >-- (rw[IMAGE_eq_FIB,Whole_def] >> strip_tac >>
          dimp_tac >> strip_tac (* 2 *)
          >-- (pop_assum (assume_tac o GSYM) >> arw[] >> 
              qpick_x_assum ‘p1 o inc = p’ (assume_tac o GSYM) >> 
              arw[GSYM App_App_o] >> arw[o_assoc] >>
              qpick_x_assum ‘IMAGE(i, Whole(A)) = FIB(p1, n0)’
              assume_tac >> drule $ iffLR IMAGE_eq_FIB >>
              rw[App_App_o] >> pop_assum (assume_tac o GSYM) >> arw[] >>
              qexists_tac ‘a’ >> rw[Whole_def]) >>
           qpick_x_assum ‘p1 o inc = p’
           (assume_tac o GSYM) >> fs[App_App_o] >>
           qpick_x_assum ‘IMAGE(i, Whole(A)) = FIB(p1, n0)’
           assume_tac >> drule $ iffLR IMAGE_eq_FIB >>
           pop_assum (assume_tac o GSYM) >> fs[] >> qexists_tac ‘a’  >>
           rev_drule Inj_eq_eq >> first_x_assum $ irule o iffLR >>
           arw[GSYM App_App_o]) >>
     rw[IMAGE_eq_FIB,Whole_def] >> strip_tac >>
     dimp_tac >> strip_tac (* 2 *)
          >-- (pop_assum (assume_tac o GSYM) >> arw[] >> 
              qpick_x_assum ‘p1 o inc = p’ (assume_tac o GSYM) >> 
              arw[GSYM App_App_o] >> arw[o_assoc] >>
              qpick_x_assum ‘IMAGE(pi, Whole(Pow(A))) = FIB(p1, Suc(n0))’
              assume_tac >> drule $ iffLR IMAGE_eq_FIB >>
              rw[App_App_o] >> pop_assum (assume_tac o GSYM) >> arw[] >>
              qexists_tac ‘a’ >> rw[Whole_def]) >>
           qpick_x_assum ‘p1 o inc = p’
           (assume_tac o GSYM) >> fs[App_App_o] >>
           qpick_x_assum ‘IMAGE(pi, Whole(Pow(A))) = FIB(p1, Suc(n0))’
           assume_tac >> drule $ iffLR IMAGE_eq_FIB >>
           pop_assum (assume_tac o GSYM) >> fs[] >> qexists_tac ‘a’  >>
           rev_drule Inj_eq_eq >> first_x_assum $ irule o iffLR >>
           arw[GSYM App_App_o]) >>
 drule IMAGE_Inj_fac >>
 rev_drule IMAGE_Inj_fac >>
 fs[SS_def,IMAGE_def,Whole_def] >> 
 qsuff_tac ‘(?i0. i = inc o i0) & ?pi0. pi = inc o pi0’ 
 >-- (strip_tac >> qexistsl_tac [‘i0’,‘pi0’] >>
     arw[] >> strip_tac (* 2 *)
     >-- (fs[] >> rev_drule Inj_o_Inj >> arw[]) >>
     fs[] >> drule Inj_o_Inj >> arw[]) >> 
 strip_tac (* 2 *)
 >-- (first_x_assum irule >> rw[GSYM IMAGE_Whole] >> arw[] >>
     rw[IN_FIB,Diff_def,Whole_def] >> flip_tac >> 
     rpt strip_tac >> ccontra_tac >> fs[Lt_def]) >> 
 first_x_assum irule >> rw[GSYM IMAGE_Whole] >> arw[] >>
 rw[IN_FIB,Diff_def,Whole_def] >> flip_tac >> rpt strip_tac >>
 ccontra_tac >> fs[] >> fs[GSYM Suc_Le_Lt] >> 
 pop_assum (assume_tac o GSYM) >> fs[] >> 
 fs[NOT_Le_Suc])
(form_goal
“!n X1 p1:X1->N R1:X1~>X1 z1:N->X1. 
  Upows(Suc(n),p1,R1,z1) ==>
  !X inc:X->X1 p:X->N R:X~>X z:N->X.
  Inj(inc) & 
  IMAGE(inc,Whole(X)) = Diff(Whole(X1),FIB(p1,Suc(n))) &  
  IMAGE(p, Whole(X)) = Les(n) & 
  p1 o inc = p & 
  inc o z = z1 & 
  (!x s. Holds(R,x,s) <=> Holds(R1,App(inc,x),App(inc,s)))
  ==>
  Upows(n,p,R,z)
  ”));



val Upows_p_NOT_n_imp_Lt= prove_store("Upows_p_NOT_n_imp_Lt",
e0
(rpt strip_tac >> drule Upows_Le_n >>
 dimp_tac >> strip_tac  (* 2 *)
 >-- arw[Lt_def] >>
 ccontra_tac >> fs[Lt_def])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  (!x. ~(App(p, x) = n) <=> Lt(App(p,x),n))”));


val Upows_embed_ex = prove_store("Upows_embed_ex",
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?X inc:X->X1 p:X->N R:X~>X z:N->X.
  Inj(inc) & 
  IMAGE(inc,Whole(X)) = Diff(Whole(X1),FIB(p1,Suc(n))) &  
  IMAGE(p, Whole(X)) = Les(n) & 
  p1 o inc = p & 
  inc o z = z1 & 
  (!x s. Holds(R,x,s) <=> Holds(R1,App(inc,x),App(inc,s)))’
 >-- (strip_tac >> qexistsl_tac [‘X’,‘inc’,‘p’,‘R’,‘z’] >>
     arw[] >> irule Upows_embed >> once_arw[] >> rw[] >>
     qexistsl_tac [‘X1’,‘R1’,‘inc’,‘p1’,‘z1’] >> arw[]) >>
 assume_tac
 (Thm_2_4 |> qtinst_thm [(‘A’,‘X1’)] 
 |> qfVar_prpl_th1 ("P",[‘x:mem(X1)’],
    ‘~(App(p1:X1->N,x) = Suc(n))’)) >>
 pop_assum (x_choosel_then ["X","inc"] strip_assume_tac) >>
 qexistsl_tac [‘X’,‘inc’,‘p1 o inc’] >>
 strip_assume_tac
 (AX1_ex |> qtinst_thm [(‘A’,‘X’),(‘B’,‘X’)] 
 |> qfVar_prpl_th1 ("P",[‘x1:mem(X)’,‘x2:mem(X)’],
     ‘Holds(R1:X1~>X1,App(inc:X->X1,x1),App(inc,x2))’)) >>
 qexistsl_tac [‘R’] >> arw[] >>
 drule IMAGE_Inj_fac >>
 first_x_assum (qsspecl_then [‘z1’] assume_tac) >>
 qby_tac ‘IMAGE(p1 o inc, Whole(X)) = Les(n)’ 
 >-- (rw[GSYM IN_EXT_iff,IMAGE_def,Whole_def,Les_def] >> 
     strip_tac >>
     drule Upows_p_NOT_n_imp_Lt >> fs[Lt_Suc_Le] >>
     rw[App_App_o] >> 
     dimp_tac >> strip_tac (* 2 *)
     >-- (arw[] >> qexists_tac ‘a’ >> rw[]) >>
     drule Upows_IMAGE_p >> 
     fs[GSYM IN_EXT_iff,IMAGE_def,Whole_def,Les_def] >> 
     qby_tac ‘Le(x,Suc(n))’ 
     >-- (irule Le_trans >> qexists_tac ‘n’ >> arw[] >>
         irule Lt_Le >> rw[Lt_Suc]) >>
     first_x_assum (drule o iffRL) >>
     pop_assum strip_assume_tac >> arw[] >>
     fs[] >> rfs[] >> qexists_tac ‘b’ >> rw[]) >> arw[] >>
 qby_tac
 ‘IMAGE(inc, Whole(X)) = Diff(Whole(X1), FIB(p1, Suc(n)))’
 >-- (rw[GSYM IN_EXT_iff,IMAGE_def,Whole_def,Diff_def,IN_FIB] >>
     arw[]) >> arw[] >>
 drule IMAGE_Inj_fac >>
 flip_tac >> first_x_assum irule >>
 drule Upows_IMAGE_z >> arw[] >>
 rw[SS_def,IN_FIB,Diff_def,Whole_def] >>
 pop_assum_list (map_every (K all_tac)) >>
 rpt strip_tac >> arw[GSYM Suc_NONZERO])
(form_goal
“!n X1 p1:X1->N R1:X1~>X1 z1:N->X1. 
  Upows(Suc(n),p1,R1,z1) ==>
  ?X inc:X->X1 p:X->N R:X~>X z:N->X.
  Inj(inc) & 
  IMAGE(inc,Whole(X)) = Diff(Whole(X1),FIB(p1,Suc(n))) &  
  IMAGE(p, Whole(X)) = Les(n) & 
  p1 o inc = p & 
  inc o z = z1 & 
  (!x s. Holds(R,x,s) <=> Holds(R1,App(inc,x),App(inc,s))) &
  Upows(n,p,R,z)
  ”));

val Bij_char = prove_store("Bij_char",
e0
(rpt strip_tac >>
 rw[Bij_def,Inj_def,Surj_def] >> 
 dimp_tac >> rpt strip_tac (*2  *)
 >-- (uex_tac >>
     first_x_assum (qspecl_then [‘b’] strip_assume_tac) >>
     qexists_tac ‘a’ >> arw[] >> pop_assum (assume_tac o GSYM) >> arw[] >> 
     rpt strip_tac >> first_x_assum irule >> arw[]) 
 >-- (first_assum (qsspecl_then [‘App(f,x1)’] assume_tac) >>
     pop_assum (strip_assume_tac o uex_expand) >> rfs[] >>
     qsuff_tac ‘x1 = a & x2 = a’ >-- (strip_tac >> arw[]) >>
     strip_tac (* 2 *)
     >> (first_x_assum irule >> arw[])) >>
 first_x_assum (qsspecl_then [‘b’] assume_tac) >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘a’ >> arw[]
)
(form_goal “!A B f:A->B. Bij(f) <=> !b. ?!a. b = App(f,a)”));

val Bij_inv = prove_store("Bij_inv",
e0
(rw[Bij_char] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (drule (P2fun |> qtinst_thm [(‘A’,‘B’),(‘B’,‘A’)] 
                  |> qfVar_prpl_th1 
("P",[‘b:mem(B)’,‘a:mem(A)’],‘b = App(f:A->B,a)’)) >>
     pop_assum strip_assume_tac >>
     qexists_tac ‘f'’ >> 
     rw[GSYM FUN_EXT,Id_def,App_App_o] >> arw[] >>
     pop_assum (assume_tac o GSYM)  >>
     flip_tac >> arw[]) >>
 uex_tac >> qexists_tac ‘App(g,b)’ >>
 arw[GSYM App_App_o,Id_def] >>
 rpt strip_tac >> arw[GSYM App_App_o,Id_def])
(form_goal “!A B f:A->B. Bij(f) <=> ?g:B->A. f o g = Id(B) & g o f = Id(A)”));


val Bij_inv' = prove_store("Bij_inv'",
e0
(rw[Bij_inv] >>
 rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘g’ >> arw[] >> qexists_tac ‘f’ >>
     arw[]) >>
 qexists_tac ‘g’ >> arw[])
(form_goal “!A B f:A->B. Bij(f) <=> ?g:B->A. Bij(g) & f o g = Id(B) & g o f = Id(A)”));


val Surj_Surj_o = prove_store("Surj_Surj_o",
e0
(rpt strip_tac >> fs[Surj_def] >>
 strip_tac >> rw[App_App_o] >>
 first_x_assum (qsspecl_then [‘b’] strip_assume_tac) >> 
 first_x_assum (qsspecl_then [‘a’] strip_assume_tac) >>
 qexists_tac ‘a'’ >> arw[])
(form_goal “!A B f:A->B. Surj(f) ==> !C g:B->C. Surj(g) ==> Surj(g o f)”));


val Bij_Bij_o = prove_store("Bij_Bij_o",
e0
(rpt strip_tac >>
 fs[Bij_def] >> strip_tac (* 2 *)
 >-- (irule Inj_Inj_o >> arw[]) >>
 irule Surj_Surj_o >> arw[])
(form_goal “!A B f:A->B. Bij(f) ==> !C g:B->C. Bij(g) ==> Bij(g o f)”));



val Upows_O_iso = prove_store("Upows_O_iso",
e0
(rpt strip_tac >> fs[Upows_O] >>
 rev_drule $ iffLR Bij_inv' >>
 pop_assum strip_assume_tac >>
 qexists_tac ‘z2 o g’ >> 
 drule Bij_Bij_o >> first_x_assum drule >> arw[] >>
 arw[o_assoc,IdR] >> rw[GSYM R_EXT,Apr_def] >> arw[] >> rw[NOT_ex_F] >>
 irule $ iffLR FUN_EXT >> rw[App_App_o,constf_def])
(form_goal
 “!X1 p1:X1->N R1:X1~>X1 z1:N->X1 
     X2 p2:X2->N R2:X2~>X2 z2:N->X2. 
  Upows(O,p1,R1,z1) & Upows(O,p2,R2,z2)==>
  ?f:X1->X2.
    Bij(f) & p2 o f = p1 & R2 = Apr(f,R1) & f o z1 = z2”));


(*
val Upow_choice_independence' = prove_store(
"Upow_choice_independence'",
e0
(che)
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !n0. Lt(n0,n) ==>
   !uA ui:uA->X upi:Pow(uA) ->X.
   Inj(ui) & Inj(upi) & 
      IMAGE(ui,Whole(uA)) = FIB(p,n0) &  
      IMAGE(upi,Whole(Pow(uA))) = FIB(p,Suc(n0)) &
      (!a:mem(uA) s. 
                    Holds(R,App(ui,a),App(upi,s)) <=> IN(a,s)) ==>
   !A i:A->X pi:Pow(A) ->X.
      (Inj(i) & Inj(pi) & 
      IMAGE(i,Whole(A)) = FIB(p,n0) &  
      IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0)) &
      (!a:mem(A) s.
                  Holds(R,App(i,a),App(pi,s)) <=> IN(a,s)))==>
      ?f:uA->A. 
       Bij(f) & i o f = ui & pi o Image(f) = upi”));
*)



(*
val Bij_split = prove_store("Bij_split",
e0
cheat
(form_goal “!Y1 Y2 f:Y1->Y2. Bij(f)==>
 !X1 inc1:Y1->X1. Inj(inc1) ==>
 !X2 inc2:Y2->X2. Inj(inc2) ==>
 !g:X1->X2. 
   g o inc1 = inc2 o f & 
   (!x1. ~IN(x1,IMAGE(inc1,Whole(Y1))) ==> 
         ~IN(App(g,x1),IMAGE(inc2,Whole(Y2))) ) &
   (!x2. ~IN(x2,IMAGE(inc2,Whole(Y2))) ==> 
        ?!x1. ~IN(x1,IMAGE(inc1,Whole(Y1))) & App(g,x1) = x2) ==>
   Bij(g)”));

*)

val NE_Suc = Suc_NEQ;
(*prove_store("NE_Suc",
e0
cheat
(form_goal “!n. ~(n = Suc(n))”));*)


val Inj_same_IMAGE_Bij = prove_store("Inj_same_IMAGE_Bij",
e0
(rpt strip_tac >> assume_tac
  (Thm_2_4_unique |> qtinst_thm [(‘A’,‘X’),(‘B’,‘A1’)] 
                  |> qspecl [‘i1:A1->X’,‘A2’,‘i2:A2->X’] 
                  |> qfVar_prpl_th1 
("P",[‘x:mem(X)’],‘IN(x,IMAGE(i2:A2->X, Whole(A2)))’))  >>
 rw[Bij_inv] >>
 fs[GSYM IMAGE_Whole,IN_EXT_iff] >> rfs[] >>
 qexistsl_tac [‘f’] >> arw[] >> qexists_tac ‘g’ >> arw[])
(form_goal
 “!X A1 i1:A1->X A2 i2:A2->X. 
  Inj(i1) & Inj(i2) & IMAGE(i1,Whole(A1)) = IMAGE(i2,Whole(A2)) ==>
  ?f:A1->A2. Bij(f) & i2 o f = i1”));


val Upows_p_o_z = prove_store("Upows_p_o_z",
e0
(rpt strip_tac >> 
 qby_tac ‘IMAGE(z, Whole(N)) = FIB(p, O) ’ >-- fs[Upows_def] >> 
 fs[IMAGE_eq_FIB,Whole_def] >>
 irule $ iffLR FUN_EXT >> rw[App_App_o,constf_def] >>
 strip_tac >> first_x_assum $ irule o iffLR >>
 qexists_tac ‘a’ >> rw[])
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  p o z = constf(N,O)”));


val Upows_p_Le_n = Upows_Le_n;(* prove_store("Upows_p_Le_n",
e0
(cheat)
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !x. Le(App(p,x),n)”));*)

(*
val Upows_R_Lt = prove_store("Upows_R_Lt",
e0
(rpt strip_tac >>
 drule $ )
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !x1 x2. Holds(R,x1,x2) ==> Lt(App(p,x1),App(p,x2))”));
*)

(*
val Upows_p_NOT_Lt_imp_eq = prove_store("Upows_p_NOT_Lt_imp_eq",
e0
(cheat)
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  !x. ~Lt(App(p,x),n) ==> App(p,x) = n ”));
*)





val NOT_Suc_Lt = prove_store("NOT_Suc_Lt",
e0
(rw[NOT_LESS,LESS_EQ_SUC])
(form_goal “!n. ~Lt(Suc(n),n)”));


val NOT_Suc_Le = prove_store("NOT_Suc_Le",
e0
(rw[NOT_LESS_EQ,Lt_Suc])
(form_goal “!n. ~Le(Suc(n),n)”));





val Bij_coPa_char = prove_store("Bij_coPa_char",
e0
(rpt strip_tac >> dimp_tac >> strip_tac(* 2 *)
 >-- (fs[Bij_def,Inj_def,Surj_def] >> rpt strip_tac (* 3 *)
     >-- (first_x_assum 
         (qsspecl_then [‘App(i1(A,B),x1)’,‘App(i1(A,B),x2)’] assume_tac) >>
         fs[GSYM App_App_o,coPa_def] >> rfs[i1_eq_eq]) 
     >-- (first_x_assum 
         (qsspecl_then [‘App(i2(A,B),x1)’,‘App(i2(A,B),x2)’] assume_tac) >>
         fs[GSYM App_App_o,coPa_def] >> rfs[i2_eq_eq]) >>
     rw[IMAGE_def,Whole_def] >> dimp_tac >> strip_tac (* 2 *)
     >-- (ccontra_tac >> pop_assum strip_assume_tac >>
         first_x_assum 
         (qsspecl_then [‘App(i1(A,B),a)’,‘App(i2(A,B),a')’] assume_tac) >>
         fs[GSYM App_App_o,coPa_def] >> rfs[i1_ne_i2]) >>
     first_x_assum (qsspecl_then [‘x’] strip_assume_tac) >>
     qsspecl_then [‘a’] assume_tac i1_or_i2 >>
     pop_assum strip_assume_tac (* 2 *)
     >-- (fs[coPa_def,GSYM App_App_o] >> qexists_tac ‘a'’ >> arw[]) >>
     fs[GSYM App_App_o,coPa_def] >> 
     qsuff_tac ‘?a. x = App(j,a)’ >-- arw[] >> qexists_tac ‘b’ >> arw[]) >>
 fs[Bij_def,Inj_def,Surj_def,IMAGE_def,Whole_def] >>
 rpt strip_tac (* 2 *)
 >-- (qsspecl_then [‘x1’] assume_tac i1_or_i2 >>
     qsspecl_then [‘x2’] assume_tac i1_or_i2 >> fs[] (* 4 *)
     >-- (rw[i1_eq_eq] >> first_x_assum irule >> fs[GSYM App_App_o,coPa_def])
     >-- (fs[GSYM App_App_o,coPa_def] >> 
         first_x_assum (qsspecl_then [‘App(i,a)’] assume_tac) >>
         fs[ex_mem_eq] >> qsuff_tac ‘?a'. App(i,a) = App(j,a')’ >-- arw[] >>
         qexists_tac ‘b’ >> arw[]) 
     >-- (fs[GSYM App_App_o,coPa_def] >> 
         first_x_assum (qsspecl_then [‘App(j,b)’] assume_tac) >>
         fs[ex_mem_eq] >> qsuff_tac ‘?a. App(j,b) = App(i,a)’ >-- arw[] >>
         qexists_tac ‘a’ >> arw[]) >>
     rw[i2_eq_eq] >> first_x_assum irule >> fs[GSYM App_App_o,coPa_def]) >>
 first_x_assum (qsspecl_then [‘b’] assume_tac) >>
 qcases ‘?a. b = App(i,a)’ (* 2 *)
 >-- (fs[] >> qexists_tac ‘App(i1(A,B),a)’ >> rw[GSYM App_App_o,coPa_def])>>
 fs[] >> qexists_tac ‘App(i2(A,B),a)’ >> rw[GSYM App_App_o,coPa_def])
(form_goal “!X A i:A->X B j:B->X. Bij(coPa(i,j)) <=> 
 (Inj(i) & Inj(j) & 
  (!x.IN(x,IMAGE(i,Whole(A))) <=> ~IN(x,IMAGE(j,Whole(B)))))”));



val Bij_coPa_Bij = prove_store("Bij_coPa_Bij",
e0
(rpt strip_tac >> rw[Bij_coPa_char] >> 
 rw[IMAGE_def,App_App_o,Whole_def] >> 
 rpt strip_tac (* 3 *)
 >-- (irule Inj_Inj_o >> rw[i1_Inj] >> irule Bij_Inj >> arw[])
 >-- (irule Inj_Inj_o >> rw[i2_Inj] >> irule Bij_Inj >> arw[]) >>
 dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (rw[i1_ne_i2,NOT_ex_F]) >>
 qsspecl_then [‘x’] strip_assume_tac i1_or_i2 
 >-- (arw[i1_eq_eq] >>
     fs[Bij_def,Surj_def] >> flip_tac >> fs[]) >>
 arw[GSYM i1_ne_i2,NOT_ex_F] >> fs[i2_eq_eq] >> fs[Bij_def,Surj_def] >>
 pop_assum (K all_tac) >>
 pop_assum mp_tac >> flip_tac >> arw[])
(form_goal
 “!A1 A2 fa:A1->A2 B1 B2 fb:B1->B2. Bij(fa) & Bij(fb) ==>
  Bij(coPa(i1(A2,B2) o fa,i2(A2,B2) o fb))”));



val Upows_iso_ex_Bij_lemma = prove_store("Upows_iso_ex_Bij_lemma",
e0
(rpt strip_tac >> 
 qsspecl_then [‘fa’,‘fb’] assume_tac Bij_coPa_Bij >> rfs[] >>
 qsspecl_then [‘coPa(i1,j1)’] assume_tac Bij_inv' >>
 rfs[] >> 
 qexists_tac ‘coPa(i2, j2) o coPa(i1(A2, B2) o fa, i2(A2, B2) o fb) o g’ >>
 qby_tac
 ‘(g o coPa(i1, j1)) o i1(A1,B1) = Id(A1 + B1) o i1(A1,B1)’ 
 >-- arw[] >>
 qby_tac
 ‘(g o coPa(i1, j1)) o i2(A1,B1) = Id(A1 + B1) o i2(A1,B1)’ 
 >-- arw[] >> fs[o_assoc,coPa_def,IdL]  >> rw[coPa_def,GSYM o_assoc] >>
 irule Bij_Bij_o >> arw[] >> 
 irule Bij_Bij_o >> arw[])
(form_goal
 “!X1 A1 i1:A1->X1 B1 j1:B1->X1 
   X2 A2 i2:A2->X2 B2 j2:B2->X2 fa:A1->A2 fb:B1-> B2. 
   Inj(i1) & Inj(i2) & Inj(j1) & Inj(j2) & 
   Bij(fa) & Bij(fb) & Bij(coPa(i1,j1)) & Bij(coPa(i2,j2)) ==>
   ?g:X1->X2. Bij(g) & g o i1 = i2 o fa & g o j1 = j2 o fb”));


val Inj_Image_iff = prove_store("Inj_Image",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac  
 >-- (fs[Inj_def] >> rpt strip_tac >>
     ccontra_tac >>
     first_x_assum (qsspecl_then [‘Sing(x1)’,‘Sing(x2)’] assume_tac) >>
     fs[Image_IMAGE,IMAGE_Sing,GSYM IN_EXT_iff,IN_Sing] >>
     rfs[] >>
     first_x_assum (qsspecl_then [‘x1’] assume_tac) >> fs[]) >>
 drule Inj_Image >> arw[])
(form_goal “!A B f:A->B. Inj(Image(f)) <=> Inj(f)”));


val Surj_IMAGE_PREIM = prove_store("Surj_IMAGE_PREIM",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IMAGE_def,PREIM_def] >>
 strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- arw[] >>
 fs[Surj_def] >>
 first_x_assum (qsspecl_then [‘x’] strip_assume_tac) >>
 qexists_tac ‘a’ >> arw[] >> qexists_tac ‘x’ >> arw[])
(form_goal
 “!A B f:A->B. Surj(f) ==> !s.IMAGE(f,PREIM(f, s)) = s”));

val Surj_Image_iff = prove_store("Surj_Image",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac  
 >-- (fs[Surj_def] >> rpt strip_tac >>
     ccontra_tac >>
     first_x_assum (qsspecl_then [‘Sing(b)’] assume_tac) >>
     fs[] >>
     fs[Image_IMAGE,IMAGE_Sing,GSYM IN_EXT_iff,IN_Sing,IMAGE_def] >> 
     first_x_assum (qsspecl_then [‘b’] assume_tac) >> fs[] >>
     last_x_assum mp_tac >> rw[] >> qexists_tac ‘a'’ >> arw[]) >>
 rw[Surj_def] >> strip_tac >>
 qexists_tac ‘PREIM(f,b)’ >> rw[Image_IMAGE] >>
 drule Surj_IMAGE_PREIM >> arw[]
 )
(form_goal “!A B f:A->B. Surj(Image(f)) <=> Surj(f)”));

val Bij_Image = prove_store("Bij_Image",
e0
(rw[Bij_def,Inj_Image_iff,Surj_Image_iff] )
(form_goal “!A B f:A->B. Bij(Image(f)) <=> Bij(f)”));


val IMAGE_FIB_constfn = prove_store("IMAGE_FIB_constfn",
e0
(rpt strip_tac >> fs[IMAGE_eq_FIB] >>
 rw[GSYM FUN_EXT,constf_def,App_App_o] >> strip_tac >>
 first_x_assum $ irule o iffLR  >>
 qexists_tac ‘a’ >> rw[Whole_def])
(form_goal
 “!A B f:A->B C p:B->C b. IMAGE(f, Whole(A)) = FIB(p, b) ==> p o f = constf(A,b)”));

val constf_o = prove_store("constf_o",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT,constf_def,App_App_o])
(form_goal “!A B f:A->B C c:mem(C). constf(B,c) o f = constf(A,c)”));



val Surj_coPa_char = prove_store("Surj_coPa_char",
e0
(rpt strip_tac >> rw[Surj_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum (qsspecl_then [‘x’] assume_tac) >>
     pop_assum (x_choose_then "ab" assume_tac) >>
     qsspecl_then [‘ab’] strip_assume_tac i1_or_i2 (* 2 *)
     >-- (fs[] >> disj1_tac >> fs[GSYM App_App_o,coPa_def] >>
         qexists_tac ‘a’ >> arw[]) >> 
     fs[] >> disj2_tac >> fs[GSYM App_App_o,coPa_def] >>
     qexists_tac ‘b’ >> arw[]) >>
 first_x_assum (qsspecl_then [‘b’] strip_assume_tac) (* 2 *)
 >-- (arw[] >> qexists_tac ‘App(i1(A,B),a)’ >> 
      rw[GSYM App_App_o,coPa_def]) >>
 arw[] >> qexists_tac ‘App(i2(A,B),b')’ >> 
 rw[GSYM App_App_o,coPa_def])
(form_goal
 “!A X ia:A->X B ib:B->X. 
 Surj(coPa(ia,ib)) <=>
 !x. (?a.x = App(ia,a)) | (?b. x = App(ib,b))”));

val coPa_Surj_eq = prove_store("coPa_Surj_eq",
e0
(rw[Surj_coPa_char] >> rpt strip_tac >>
 rw[GSYM FUN_EXT] >> strip_tac >>
 first_x_assum (qsspecl_then [‘a’] strip_assume_tac) (* 2 *)
 >-- arw[GSYM App_App_o] >> arw[GSYM App_App_o])
(form_goal “!A X ia:A->X B ib:B->X. 
 Surj(coPa(ia,ib)) ==> 
 !Y f:X->Y g. f o ia = g o ia & f o ib = g o ib ==> f = g”));



(*
val coPa_Surj_Req = prove_store("coPa_Surj_Req",
e0
(rpt strip_tac >> irule $ iffLR R_EXT >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum drule >> pop_assum strip_assume_tac (* 2 *)
     >>(fs[IMAGE_def] >> fs[] >> rfs[])) >>
 first_x_assum drule >> pop_assum strip_assume_tac (* 2 *)
     >>(fs[IMAGE_def] >> fs[] >> rfs[]))
(form_goal “!A X ia:A->X B ib:B->X R1 R2. 
 (!x1 x2. Holds(R1,x1,x2) ==> 
          IN(x1,IMAGE(ia,Whole(A))) & 
          (IN(x2,IMAGE(ia,Whole(A))) | IN(x2,IMAGE(ib,Whole(B))))) & 
 (!x1 x2. Holds(R2,x1,x2) ==> 
          IN(x1,IMAGE(ia,Whole(A))) & 
          (IN(x2,IMAGE(ia,Whole(A))) | IN(x2,IMAGE(ib,Whole(B))))) ==>
  (!a1 a2. Holds(R1,App(ia,a1),App(ia,a2)) <=> 
           Holds(R2,App(ia,a1),App(ia,a2))) & 
  (!a b. Holds(R1,App(ia,a),App(ib,b)) <=> 
         Holds(R2,App(ia,a),App(ib,b))) ==> R1 = R2”));
*)




val Upows_iso_ex_Req_lemma = prove_store("Upows_iso_ex_Req_lemma",
e0
(rpt strip_tac >> irule $ iffLR R_EXT >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum drule >> pop_assum strip_assume_tac (* 2 *)
     >>(fs[IMAGE_def] >> fs[] >> rfs[])) >>
 first_x_assum drule >> pop_assum strip_assume_tac (* 2 *)
     >>(fs[IMAGE_def] >> fs[] >> rfs[]))
(form_goal “!A X ia:A->X B ib:B->X C ic:C->X R1 R2. 
 (!x1 x2. Holds(R1,x1,x2) ==> 
          (IN(x1,IMAGE(ia,Whole(A))) & IN(x2,IMAGE(ia,Whole(A)))) |
          (IN(x1,IMAGE(ib,Whole(B))) & IN(x2,IMAGE(ic,Whole(C))))) & 
 (!x1 x2. Holds(R2,x1,x2) ==> 
          (IN(x1,IMAGE(ia,Whole(A))) & IN(x2,IMAGE(ia,Whole(A)))) |
          (IN(x1,IMAGE(ib,Whole(B))) & IN(x2,IMAGE(ic,Whole(C))))) ==>
  (!a1 a2. Holds(R1,App(ia,a1),App(ia,a2)) <=> 
           Holds(R2,App(ia,a1),App(ia,a2))) & 
  (!b c. Holds(R1,App(ib,b),App(ic,c)) <=> 
         Holds(R2,App(ib,b),App(ic,c))) ==> R1 = R2”));

(*
val coPa_Surj_Req = prove_store("coPa_Surj_Req",
e0
cheat
(form_goal “!A X ia:A->X B ib:B->X. 
 Surj(coPa(ia,ib)) ==> 
 !R1 R2:X~>X.
  (!a1 a2. Holds(R1,App(ia,a1),App(ia,a2)) <=> 
           Holds(R2,App(ia,a1),App(ia,a2))) & 
  (!a b. Holds(R1,App(ia,a),App(ib,b)) <=> 
         Holds(R2,App(ia,a),App(ib,b))) ==> R1 = R2”));
*)

val conv_lemma = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> rfs[] >>
 qexistsl_tac [‘a0’,‘b0’] >> arw[]
(*fconv_tac (redepth_fconv no_conv EXISTS_EQN_FCONV) does not work here
 quantifier and corresponding eqns are not adjacent*))
(form_goal “!A B R:A~>B a0 b0. (?a b. a = a0 & b = b0 & Holds(R,a,b)) <=>
  Holds(R,a0,b0)”)

val inv_eq_iff = prove_store("inv_eq_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >> arw[GSYM App_App_o,Id_def])>>
 arw[GSYM App_App_o,Id_def])
(form_goal
 “!A B f:A->B finv:B->A. finv o f = Id(A) & f o finv = Id(B) ==>
  !a b. App(f,a) = b <=> a = App(finv,b)”)); 


val Apr_Bij_inv = prove_store("Apr_Bij_inv",
e0
(rpt strip_tac >>
 rw[Apr_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qsspecl_then [‘f’,‘finv’] assume_tac inv_eq_iff >> rfs[] >> fs[] >>
     rfs[]) >>
 qsspecl_then [‘f’,‘finv’] assume_tac inv_eq_iff >> rfs[] >>
 qexistsl_tac [‘App(finv,b1)’,‘App(finv,b2)’] >> arw[])
(form_goal
 “!A B f:A->B. Bij(f) ==>
  !finv. f o finv = Id(B) & finv o f = Id(A) ==>
  (!R b1 b2. Holds(Apr(f,R),b1,b2) <=> 
             Holds(R,App(finv,b1),App(finv,b2)))”));

val Union_Diff_Whole = prove_store("Union_Diff_Whole",
e0
(rw[GSYM IN_EXT_iff,IN_Union,Diff_def,Whole_def] >>
 rpt strip_tac >> 
 qcases ‘IN(x,s)’ >> arw[])
(form_goal “!A s. Union(Diff(Whole(A),s),s) = Whole(A)”));


val comm_inv_comm = prove_store("comm_inv_comm",
e0
(rpt strip_tac >>  
 qby_tac ‘ginv o g o c1 = ginv o c2 o f’ >-- arw[] >>
 fs[GSYM o_assoc,IdL] >> rfs[IdL,IdR] >> arw[IdR,o_assoc] )
(form_goal
 “!A B f:A->B finv:B->A. f o finv = Id(B) ==>
  !C D g:C->D ginv. ginv o g = Id(C) ==>
  !c1:A->C c2:B->D. 
  g o c1 = c2 o f ==> ginv o c2 = c1 o finv
  ”));



val Image_o = prove_store("Image_o",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT,Image_IMAGE,App_App_o,IMAGE_o] )
(form_goal
 “!A B f:A->B C g:B-> C. Image(g) o Image(f) = Image(g o f)
  ”));

(*

val inv_eq_iff = prove_store("inv_eq_iff",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *) 
 >-- (pop_assum (assume_tac o GSYM) >> arw[] >> arw[GSYM App_App_o,Id_def])>>
 arw[GSYM App_App_o,Id_def])
(form_goal
 “!A B f:A->B finv:B->A. finv o f = Id(A) & f o finv = Id(B) ==>
  !a b. App(f,a) = b <=> a = App(finv,b)”)); 
*)

val inv_tri_comm = prove_store("inv_tri_comm",
e0
(rpt strip_tac >> pop_assum (assume_tac o GSYM) >> arw[o_assoc,IdR])
(form_goal “!A B f:A->B finv.  f o finv = Id(B) ==>
 !C p1:A->C p2:B->C. p2 o f = p1 ==> p2 = p1 o finv”));

val Upows_iso_ex = prove_store("Upows_iso_ex",
e0
(ind_with N_induct >>
 rpt strip_tac (* 2 *)
 >-- (irule Upows_O_iso >> arw[]) >>
 rev_drule Upows_embed_ex >>
 pop_assum (x_choosel_then ["Y1","inc1","q1","r1","k1"] strip_assume_tac) >>
 qpick_x_assum ‘Upows(Suc(n), p2, R2, z2)’ assume_tac >>
 drule Upows_embed_ex >>
 pop_assum (x_choosel_then ["Y2","inc2","q2","r2","k2"] strip_assume_tac) >>  
 first_x_assum (qsspecl_then [‘q1’,‘r1’,‘k1’,‘q2’,‘r2’,‘k2’] assume_tac) >>
 rfs[] >>
 qby_tac ‘Lt(n,Suc(n))’ >-- rw[Lt_Suc] >>
 rev_drule Upows_Lt_i_ex >>
 first_x_assum drule >>
 pop_assum (x_choosel_then ["A1","i1","pi1"] strip_assume_tac) >>
 qpick_x_assum ‘Upows(Suc(n),p2,R2,z2)’ assume_tac >>
 drule Upows_Lt_i_ex >> first_x_assum drule >>
 pop_assum (x_choosel_then ["A2","i2","pi2"] strip_assume_tac) >>
 qby_tac ‘?i10:A1->Y1. inc1 o i10 = i1’ 
 >-- (flip_tac >> irule IMAGE_Inj_fac >> arw[] >>
     rw[SS_def,Diff_def,Whole_def,IN_FIB] >>
     rpt strip_tac >> rfs[NE_Suc]) >> 
 pop_assum strip_assume_tac >> 
 qby_tac ‘?i20:A2->Y2. inc2 o i20 = i2’ 
 >-- (flip_tac >> irule IMAGE_Inj_fac >> arw[] >>
     rw[SS_def,Diff_def,Whole_def,IN_FIB] >>
     rpt strip_tac >> rfs[NE_Suc]) >>
 pop_assum strip_assume_tac >> 
 qby_tac ‘Inj(i10)’ 
 >-- (irule Inj_o_Inj >> qexistsl_tac [‘X1’,‘inc1’]  >> arw[]) >>
 qby_tac ‘Inj(i20)’ 
 >-- (irule Inj_o_Inj >> qexistsl_tac [‘X2’,‘inc2’]  >> arw[]) >> 
 qby_tac ‘!x2. App(p2,x2) = n <=> ?a2. App(i2,a2) = x2’ 
 >-- (qpick_x_assum ‘IMAGE(i2, Whole(A2)) = FIB(p2, n)’ assume_tac >>
     drule $ iffLR IMAGE_eq_FIB >> fs[Whole_def]) >> 
 drule $ iffLR Bij_inv >>
 pop_assum (x_choosel_then ["finv"] strip_assume_tac) >>
 qby_tac ‘IMAGE(i10,Whole(A1)) = FIB(q1,n)’ 
 (*want a lemma for this*)
 >-- (rw[IMAGE_eq_FIB,Whole_def] >> strip_tac >> 
     qpick_x_assum ‘p1 o inc1 = q1’ (assume_tac o GSYM) >> arw[] >> 
     qpick_x_assum ‘Inj(inc1)’ assume_tac >>
     drule $ GSYM Inj_eq_eq >> arw[] >> pop_assum (K all_tac) >>
     arw[GSYM App_App_o] >> rw[App_App_o] >> fs[IMAGE_eq_FIB,Whole_def]) >>
 qby_tac ‘IMAGE(i20,Whole(A2)) = FIB(q2,n)’ 
 >-- (rw[IMAGE_eq_FIB,Whole_def] >> strip_tac >> 
     qpick_x_assum ‘p2 o inc2 = q2’ (assume_tac o GSYM) >> arw[] >> 
     qpick_x_assum ‘Inj(inc2)’ assume_tac >>
     drule $ GSYM Inj_eq_eq >> arw[] >> pop_assum (K all_tac) >>
     arw[GSYM App_App_o] >> rw[App_App_o] >> fs[IMAGE_eq_FIB,Whole_def]) >>
 qby_tac ‘?fa:A1->A2. Bij(fa) & i20 o fa = f o i10’
 >-- (irule Inj_same_IMAGE_Bij >> arw[] >> strip_tac (* 2 *)
     >-- (irule Inj_Inj_o >> arw[] >> irule Bij_Inj >> arw[]) >> arw[] >>
     irule Inj_o_comm >> arw[] >>
     qexists_tac ‘q1’ >> rw[]) >>
 pop_assum strip_assume_tac >>
 (*since f is Bij, compose with a inj, gives another inj with same image*)
 drule $ iffLR Bij_inv' >>
 pop_assum (x_choosel_then ["fainv"] strip_assume_tac) >> 
 qby_tac
 ‘!x1. App(p1,x1) = Suc(n) <=> ~Le(App(p1,x1),n)’ 
 >-- (rev_drule Upows_p_NOT_n_imp_Lt >> fs[Lt_Suc_Le] >>
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 qby_tac
 ‘!x2. App(p2,x2) = Suc(n) <=> ~Le(App(p2,x2),n)’ 
 >-- (drule Upows_p_NOT_n_imp_Lt >> fs[Lt_Suc_Le] >>
     pop_assum (assume_tac o GSYM) >> arw[]) >>
 qby_tac
 ‘?g. Bij(g) & inc2 o f = g o inc1 & pi2 o Image(fa) = g o pi1’ 
 >-- (flip_tac >> irule Upows_iso_ex_Bij_lemma >> arw[] >> 
     rw[Bij_Image] >> arw[] >> rw[Bij_coPa_char] >> arw[] >>
     rw[Diff_def,IN_FIB,Whole_def]) >> 
 pop_assum strip_assume_tac >> 
 qexists_tac ‘g’ >>
 qby_tac
 ‘p2 o g o inc1 = p1 o inc1’ 
 >-- (qpick_x_assum ‘inc2 o f = g o inc1’ (assume_tac o GSYM)  >>
     arw[] >> arw[GSYM o_assoc]) >>
 qby_tac ‘p1 o pi1 = constf(Pow(A1),Suc(n))’ 
 >-- (irule IMAGE_FIB_constfn >> arw[]) >>
 qby_tac ‘p2 o pi2 = constf(Pow(A2),Suc(n))’ 
 >-- (irule IMAGE_FIB_constfn >> arw[]) >>
 qby_tac 
 ‘p2 o g o pi1 = p1 o pi1’ 
 >-- (qpick_x_assum ‘pi2 o Image(fa) = g o pi1’ (assume_tac o GSYM) >>
     arw[] >> arw[GSYM o_assoc] >> 
     rw[constf_o]) >>
 qby_tac ‘p2 o g = p1’ 
 >-- (irule coPa_Surj_eq >>
      qexistsl_tac [‘Y1’,‘inc1’,‘Pow(A1)’,‘pi1’] >> arw[o_assoc] >>
      rw[Surj_coPa_char] >> rw[GSYM IMAGE_Whole] >> arw[] >>
      rw[GSYM IN_Union,Union_Diff_Whole,Whole_def]) >> arw[] >>
 qby_tac ‘g o z1 = z2’
 >-- (qpick_x_assum ‘inc1 o k1 = z1’ (assume_tac o GSYM) >> arw[] >>
     rw[GSYM o_assoc] >>
     qpick_x_assum ‘inc2 o f = g o inc1’ (assume_tac o GSYM) >> arw[] >>
     arw[o_assoc]) >> arw[] >>
 drule $ iffLR Bij_inv' >> 
 pop_assum (x_choosel_then ["ginv"] strip_assume_tac) >> 
 qby_tac ‘ginv o inc2 = inc1 o finv’ 
>-- (irule comm_inv_comm >>
    qexistsl_tac [‘f’,‘g’] >> arw[]) >> 
 qby_tac
 ‘(!y1 y2. Holds(R2,App(inc2,y1),App(inc2,y2)) <=> 
           Holds(Apr(g,R1),App(inc2,y1),App(inc2,y2)))’ 
 >-- (arw[Apr_def] >> rpt strip_tac >>
     first_x_assum (qsspecl_then [‘y1’,‘y2’] (assume_tac o GSYM)) >> arw[]>>
     first_x_assum
     (qsspecl_then [‘App(finv,y1)’,‘App(finv,y2)’] (assume_tac o GSYM)) >>
     qby_tac ‘!x1 x2. App(g,x1) = App(inc2,x2) <=> x1 = App(ginv o inc2,x2)’ 
     >-- (rw[App_App_o] >> irule inv_eq_iff >> arw[]) >>
     arw[] >> rw[conv_lemma] >> 
     arw[App_App_o] >> irule Apr_Bij_inv >> arw[]) >>
 qby_tac ‘g o i1 = i2 o fa’ 
 >-- (qpick_x_assum ‘inc1 o i10 = i1’ (assume_tac o GSYM) >>
     arw[GSYM o_assoc] >> 
     qpick_x_assum ‘inc2 o i20 = i2’ (assume_tac o GSYM) >>
     arw[GSYM o_assoc] >> arw[o_assoc] >>
     arw[GSYM o_assoc]) >> 
 qby_tac ‘ginv o i2 = i1 o fainv’ 
 >-- (irule comm_inv_comm >> qexistsl_tac [‘fa’,‘g’] >> arw[]) >>
 qby_tac ‘ginv o pi2 = pi1 o Image(fainv)’ 
 >-- (irule comm_inv_comm >> qexistsl_tac [‘Image(fa)’,‘g’] >>
     rw[Image_o] >> arw[Image_Id]) >> 
 qby_tac ‘!x1 x2. App(g, x1) = App(i2, x2) <=> x1 = App(ginv o i2,x2)’ 
 >-- (rw[App_App_o] >> irule inv_eq_iff >> arw[]) >> 
 qby_tac ‘!x1 x2. App(g, x1) = App(pi2, x2) <=> x1 = App(ginv o pi2,x2)’ 
 >-- (rw[App_App_o] >> irule inv_eq_iff >> arw[]) >> 
 qby_tac 
 ‘(!y1 y2. Holds(R2,App(i2,y1),App(pi2,y2)) <=> 
           Holds(Apr(g,R1),App(i2,y1),App(pi2,y2)))’
 >-- (rpt strip_tac >> arw[Apr_def,App_App_o] >> rw[conv_lemma] >>
     arw[GSYM App_App_o] >> arw[App_App_o] >> rw[Image_IMAGE] >>
     irule IN_IMAGE_Inj >> irule Bij_Inj >> arw[]) >>
 irule Upows_iso_ex_Req_lemma >> 
 qexistsl_tac [‘Y2’,‘inc2’,‘A2’,‘i2’,‘Pow(A2)’,‘pi2’] >>
 arw[] >> rw[Diff_def,IN_FIB,Whole_def] >> arw[] >> 
 rpt strip_tac (* 2 *)
 >-- (qcases ‘Le(App(p2, x2), n)’ >> arw[] (* 2 *)
     >-- (drule Upows_R_imp_Suc >> first_x_assum drule >>
         pop_assum (assume_tac o GSYM) >> fs[] >> fs[Suc_Le_Lt] >> 
         irule Lt_Le >> arw[]) >>
     first_x_assum (irule o iffLR) >> first_x_assum (drule o iffRL) >>
     drule Upows_R_imp_Suc >> first_x_assum drule >> rfs[Suc_eq_eq]) >>
 qby_tac ‘p2 = p1 o ginv’ 
 >-- (irule inv_tri_comm >> qexists_tac ‘g’ >> arw[]) >>
 qcases ‘Le(App(p2, x2), n)’ >> arw[] (* 2 *)
 >-- (qpick_x_assum ‘Bij(g)’ assume_tac >>
     drule Apr_Bij_inv >>
     first_x_assum (qsspecl_then [‘ginv’] assume_tac) >> rfs[] >>
     first_x_assum (drule o iffLR) >> rev_drule Upows_R_imp_Suc >>
     first_x_assum drule >> 
     pop_assum (assume_tac o GSYM) >> fs[Suc_Le_Lt,App_App_o] >>
     irule Lt_Le >> arw[]) >>
 first_x_assum (irule o iffLR) >> 
 first_x_assum (drule o iffRL) >> 
 qpick_x_assum ‘Bij(g)’ assume_tac >>
 drule Apr_Bij_inv >>
 first_x_assum (qsspecl_then [‘ginv’] assume_tac) >> rfs[] >>
 first_x_assum (drule o iffLR) >> 
 rev_drule Upows_R_imp_Suc >> 
 first_x_assum drule >> 
 pop_assum (assume_tac o GSYM) >>
 fs[Suc_Le_Lt,App_App_o] >> fs[Suc_eq_eq])
(form_goal
 “!n X1 p1:X1->N R1:X1~>X1 z1:N->X1 
     X2 p2:X2->N R2:X2~>X2 z2:N->X2. 
  Upows(n,p1,R1,z1) & Upows(n,p2,R2,z2)==>
  ?f:X1->X2.
    Bij(f) & p2 o f = p1 & R2 = Apr(f,R1) & f o z1 = z2”));


val Upows_ex = prove_store("Upows_ex",
e0
(ind_with N_induct >> strip_tac (* 2 *)
 >-- (qexistsl_tac [‘N’,‘constf(N,O)’,‘REmpty(N)’,‘Id(N)’] >> 
      rw[Upows_O_ex]) >>
 rpt strip_tac >> drule Upows_Suc >>
 x_choosel_then ["A","i"] strip_assume_tac
 (Thm_2_4 |> qtinst_thm [(‘A’,‘X’)]
 |> qfVar_prpl_th1 ("P",[‘x:mem(X)’],‘App(p:X->N,x) = n’))  >>
 first_x_assum (qsspecl_then [‘i’] assume_tac) >>
 qby_tac ‘IMAGE(i, Whole(A)) = FIB(p, n)’ 
 >-- (rw[IMAGE_eq_FIB] >> arw[Whole_def] >> strip_tac >> rflip_tac >> rw[]) >>
 rfs[] >> first_x_assum drule >>
 x_choose_then "R1" assume_tac 
 (AX1_ex |> qtinst_thm [(‘A’,‘X+ Pow(A)’),(‘B’,‘X+Pow(A)’)]
 |> qfVar_prpl_th1 ("P",[‘x1:mem(X+Pow(A))’, ‘s1:mem(X+Pow(A))’],‘(?(x : mem(X))  (s : mem(X)).
                       App(i1(X, Pow(A)), x) = x1 &
                       App(i1(X, Pow(A)), s) = s1 & Holds(R, x, s)) |
                   (?(a : mem(A))  (s : mem(Pow(A))).
                     App(i1(X, Pow(A)) o i, a) = x1 &
                     App(i2(X, Pow(A)), s) = s1 & IN(a, s))’)) >>
 first_x_assum (qsspecl_then [‘R1’] assume_tac) >>
 first_x_assum drule >>
 qexistsl_tac [‘X+Pow(A)’,‘coPa(p, constf(Pow(A), Suc(n)))’,‘R1’,‘i1(X, Pow(A)) o z’] >> first_x_assum accept_tac)
(form_goal
 “!n. ?X p:X->N R:X~>X z:N->X. Upows(n,p,R,z)”));


(*
val Upows_repl = prove_store("Upows_repl",
e0
cheat
(form_goal “(!n. ?)”));


“?wX fx:wX -> N wp:wX->N * N wz:N * N->X.
   p2(N,N) o wp = wX & w ”



val Upows_col = prove_store("Upows_col",
e0
cheat
(form_goal
 “?V q:V->N. 
   Surj(q) & 
   ?X fx:X->V p:X->V * N z: V * N -> X R: X~>X. 
   !v Xv iv:Xv->X pv:Xv->N zv:N->Xv Rv:Xv ~> Xv f.
      isset(iv,FIB(fx,v)) & 
      Pa(constf(N,v),Id(N)) o pv = p o iv & 
      z o Pa(constf(N,v),Id(N)) = iv o zv & 
      (!xv1 xv2. 
      Holds(Rv,xv1,xv2) <=> 
      Holds(R,App(iv,xv1),App(iv,xv2))) ==>
      Upows(App(q,v),pv,Rv,zv) ”));




val Upows_repl = prove_store("Upows_repl",
e0
(strip_assume_tac Upows_col >>
 )
(form_goal
 “?X fx:X->N p:X->N * N z: N * N -> X R: X~>X. 
   !n Xn xn:Xn->X pn:Xn->N zn:N->Xn Rn:Xn ~> Xn f.
      isset(xn,FIB(fx,n)) & 
      Pa(constf(N,n),Id(N)) o pn = p o xn & 
      z o Pa(constf(N,n),Id(N)) = xn o zn & 
      (!xn1 xn2. 
      Holds(Rn,xn1,xn2) <=> 
      Holds(R,App(xn,xn1),App(xn,xn2))) ==>
      Upows(n,pn,Rn,zn) ”));
*)
