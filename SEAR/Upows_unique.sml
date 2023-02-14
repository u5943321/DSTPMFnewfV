val Inj_same_IMAGE = 
prove_store("Inj_same_IMAGE",
e0
(rpt strip_tac >>
 assume_tac 
 (Thm_2_4_unique |> qspecl [‘X’] 
                   |> qsspecl [‘i1:A1->X’,‘i2:A2->X’] 
                   |> fVar_sInst_th “P(x:mem(X))”
                   “IN(x,IMAGE(i1:A1->X,Whole(A1)))”) >>
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
IN_def_P |> qspecl [‘N’] 
         |> fVar_sInst_th “P(a:mem(N))”
            “Le(a,n)”
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
   !a:mem(A) s. IN(a,s) <=>
                Holds(R,App(i,a),App(pi,s))) & 
 (!x:mem(X) s:mem(X). 
  Holds(R,x,s) <=> 
  Lt(App(p,x),n) & 
  Suc(App(p,x)) = App(p,s) &
  ?A i:A->X pi:Pow(A) ->X a:mem(A) sa:mem(Pow(A)). 
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,App(p,x)) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,App(p,s)) & 
   IN(a,sa) & App(i,a) = x & App(pi,sa) = s)’


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
 assume_tac (exists_forall_dual |> qspecl [‘A’]
|> fVar_sInst_th “P(a:mem(A))”
   “IN(a:mem(A),s)” |> GSYM) >>
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
AX1 |> qspecl [‘A’,‘A’] 
    |> fVar_sInst_th “P(a:mem(A),b:mem(A))”
       “F” 
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


val Apr_def = AX1 |> qspecl [‘A’,‘A’] |> fVar_sInst_th
 “P(a1:mem(A),a2:mem(A))” “?x1 x2. App(f:X->A,x1) = a1 & App(f,x2) =
 a2 & Holds(R0,x1,x2)” |> qsimple_uex_spec "Apr" [‘f’,‘R0’] |> gen_all


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
   (Holds(R,ax,sx) <=>
    ?a1 s1. IN(a1,s1) & App(i1,a1) = ax & App(pi1,s1)= sx)) &   IMAGE(i,Whole(A)) = IMAGE(i1, Whole(A1)) & 
  IMAGE(pi,Whole(Pow(A))) = IMAGE(pi1, Whole(Pow(A1))) ==>
  ?f:A->A1 . 
   Bij(f) &
   i1 o f = i & pi1 o Image(f) = pi”));


val Upow_choice_independence = prove_store(
"Upow_choice_independence",
e0
(rpt strip_tac >>
 qby_tac
 ‘?A i:A->X pi:Pow(A) ->X.
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,n0) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0))& 
   !a:mem(A) s. IN(a,s) <=>
                Holds(R,App(i,a),App(pi,s))’ 
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
      (!a:mem(uA) s. IN(a,s) <=>
                    Holds(R,App(ui,a),App(upi,s))) &
   !A i:A->X pi:Pow(A) ->X.
      (Inj(i) & Inj(pi) & 
      IMAGE(i,Whole(A)) = FIB(p,n0) &  
      IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0)) &
      (!a:mem(A) s. IN(a,s) <=>
                    Holds(R,App(i,a),App(pi,s))))==>
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
   !a:mem(A) s. IN(a,s) <=>
                Holds(R,App(i,a),App(pi,s))”));


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
     qexists_tac ‘a’ >> rw[] >>
     first_x_assum (irule o iffLR) >>
     rw[Whole_def]) >>
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
     >-- (dimp_tac >-- (strip_tac >> 
         qexistsl_tac [‘a’,‘s’] >>
         qsuff_tac ‘ Holds(R1, App(i, a), App(pi, s))’
         >-- (strip_tac >> arw[]) >>
         qby_tac ‘Holds(R2, App(f1 o i, a), 
                        App(f1 o pi, s))’ 
         >-- (qpick_x_assum ‘f1 o i = f2 o i’
             (assume_tac o GSYM) >> rfs[] >> fs[]) >>
         qpick_x_assum ‘R2 = Apr(f2, R1)’ (K all_tac) >>
         rfs[] >>
         qpick_x_assum ‘f1 o i = f2 o i’ 
         (assume_tac o GSYM) >> fs[] >>
         fs[App_App_o] >> irule $ iffLR Bij_Apr >>
         qexistsl_tac [‘X2’,‘f1’] >> arw[]) >>
         qpick_x_assum ‘f1 o i = f2 o i’ 
         (assume_tac o GSYM)  >> fs[] >> 
         strip_tac >> rw[App_App_o] >>
         irule $ iffRL Bij_Apr >> arw[] >>
         qsuff_tac ‘a' = a & s' = s’ 
         >-- (strip_tac >> fs[]) >>
         strip_tac (* 2 *)
         >-- (irule $ iffLR Inj_eq_eq >>
             qexistsl_tac [‘X2’,‘f1 o i’] >> arw[]) >>
         (irule $ iffLR Inj_eq_eq >>
         qexistsl_tac [‘X2’,‘f1 o pi’] >> arw[])) >>
     qpick_x_assum ‘R2 = Apr(f1, R1)’ (K all_tac) >>
     arw[] >> rw[App_App_o] >>
     drule Bij_Apr >> arw[] >> rw[GSYM App_App_o] >>
     qby_tac ‘Inj(f2 o i) & Inj(f2 o pi)’ 
     >-- (strip_tac >> irule Inj_Inj_o >> arw[] >>
         irule Bij_Inj >> arw[]) >>
     pop_assum strip_assume_tac >>
     drule Inj_eq_eq >> arw[] >>
     pop_assum (K all_tac) >> pop_assum (K all_tac) >>
     drule Inj_eq_eq >> arw[] >>
     dimp_tac >> rpt strip_tac >> fs[] >>
     qexistsl_tac [‘a1’,‘s1’] >> arw[]) >>
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


val IMAGE_coPa = prove_store("IMAGE_coPa",
e0
(cheat)
(form_goal
 “!A X f:A->X B g:B->X s. IMAGE(coPa(f,g),s) = 
  Union(IMAGE(f,PREIM(i1(A,B),s)),
        IMAGE(g,PREIM(i2(A,B),s)))”));

val IMAGE_coPa_Whole = prove_store("IMAGE_coPa_Whole",
e0
cheat
(form_goal
 “!A X f:A->X B g:B->X. IMAGE(coPa(f,g),Whole(A+B)) = 
  Union(IMAGE(f,Whole(A)),
        IMAGE(g,Whole(B)))”));


val FIB_coPa = prove_store("FIB_coPa",
e0
cheat
(form_goal
 “!A X f:A->X B g:B->X x.
  FIB(coPa(f,g),x) = Union(IMAGE(i1(A,B),FIB(f,x)),
IMAGE(i2(A,B),FIB(g,x)))”));

val Les_Suc = prove_store("Les_Suc",
e0
cheat
(form_goal “!n. Les(Suc(n)) = Ins(Suc(n),Les(n))”));

val Upows_z_Inj = prove_store("Upows_z_Inj",
e0
cheat
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==> Inj(z)”));


val Upows_IMAGE_p = prove_store("Upows_IMAGE_p",
e0
cheat
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>  IMAGE(p, Whole(X)) = Les(n)”));


val Pow_NOT_EMPTY = prove_store("Pow_NOT_EMPTY",
e0
(cheat)
(form_goal “!A. ?s:mem(Pow(A)). T”));


val Union_comm = prove_store("Union_comm",
e0
cheat
(form_goal “!A s1 s2:mem(Pow(A)). Union(s1,s2) = Union(s2,s1)”));


val FIB_constf_Empty = prove_store("FIB_constf_Empty",
e0
cheat
(form_goal
 “!B b0 b:mem(B). ~(b = b0) ==>
  !A. FIB(constf(A,b0),b) = Empty(A)”));


val Upows_IMAGE_z = prove_store("Upows_IMAGE_z",
e0
cheat
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  IMAGE(z, Whole(N)) = FIB(p, O)”));

val NOT_Suc_Le = prove_store("NOT_Suc_Le",
e0
cheat
(form_goal “!n. ~(Le(Suc(n),n))”));

val NOT_ex_F = prove_store("NOT_ex_F",
e0
cheat
(form_goal “!A. (?a:mem(A).F) <=> F”));

val i1_eq_eq = prove_store("i1_eq_eq",
e0
cheat
(form_goal “!A B a1 a2. App(i1(A,B),a1) = App(i1(A,B),a2) <=> a1 = a2”));


val i2_Inj = prove_store("i2_Inj",
e0
cheat
(form_goal “!A B. Inj(i2(A,B))”));





val i2_eq_eq = prove_store("i2_eq_eq",
e0
cheat
(form_goal “!A B b1 b2. App(i2(A,B),b1) = App(i2(A,B),b2) <=> b1 = b2”));


val Inj_IMAGE_eq_eq = prove_store("Inj_IMAGE_eq_eq",
e0
cheat
(form_goal
 “!A B f:A->B. Inj(f) ==>
   (!s1 s2. IMAGE(f,s1) = IMAGE(f,s2) <=> s1 = s2)”));


val i1_IMAGE_eq_eq = prove_store("i1_IMAGE_eq_eq",
e0
cheat
(form_goal
 “!A B.
   (!s1 s2. IMAGE(i1(A,B),s1) = IMAGE(i1(A,B),s2) <=> s1 = s2)”));



val Upows_FIB_n_Lt_Empty = prove_store("Upows_FIB_n_Lt_Empty",
e0
cheat
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
cheat
(form_goal
 “!n X p:X->N R:X~>X z:N->X. 
  Upows(n,p,R,z) ==>
  (!x:mem(X) s:mem(X). 
  Holds(R,x,s) <=> 
  Lt(App(p,x),n) & 
  Suc(App(p,x)) = App(p,s) &
  ?A i:A->X pi:Pow(A) ->X a:mem(A) sa:mem(Pow(A)). 
   Inj(i) & Inj(pi) & 
   IMAGE(i,Whole(A)) = FIB(p,App(p,x)) &  
   IMAGE(pi,Whole(Pow(A))) = FIB(p,App(p,s)) & 
   IN(a,sa) & App(i,a) = x & App(pi,sa) = s)”));




val Upows_Suc = prove_store("Upows_Suc",
e0
(rpt strip_tac >>
 rw[Upows_def] >>
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
 ‘!(n0 : mem(N)).
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
                     IN(a, s) <=> Holds(R1, App(i, a), App(pi, s))’ >--
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
 qsspecl_then [‘x’] assume_tac i1_or_i2 >>
 pop_assum $ disj_cases_then assume_tac (* 2 *) >-- 
 pop_assum (x_choosel_then ["x0"] assume_tac) >>
 qsspecl_then [‘s’] assume_tac i1_or_i2 >>
 pop_assum $ disj_cases_then assume_tac (* 2 *)
 >-- (pop_assum (x_choosel_then ["s0"] assume_tac) >>
     once_arw[] >> once_rw[GSYM App_App_o] >>
     once_rw[coPa_def] >> once_arw[] >>
     once_rw[i1_eq_eq] >> once_rw[App_App_o] >>
     once_rw[i1_eq_eq] >> once_rw[GSYM i1_ne_i2] >>
     rw[NOT_ex_F] >> 
     qby_tac ‘(?(x' : mem(X))  (s' : mem(X)). x' = x0 & s' = s0 & Holds(R, x', s')) <=> Holds(R,x0,s0)’ 
     >-- (dimp_tac >> strip_tac >> rfs[] >>
         qexistsl_tac [‘x0’,‘s0’] >> arw[]) >>
     arw[]>> pop_assum (K all_tac) >>
     once_rw[FIB_coPa] >> 
     qby_tac ‘~(App(p, s0) = Suc(n))’ 
     >-- cheat >> (*only ones from i2 sent to Suc n*)
     drule FIB_constf_Empty >> 
     qby_tac ‘~(App(p, x0) = Suc(n))’ 
     >-- cheat >> (*only ones from i2 sent to Suc n*)
     drule FIB_constf_Empty >> 
     once_arw[Union_Empty2] >> once_rw[IMAGE_Empty] >>
     once_rw[Union_Empty2] >> drule Upows_R >>
     arw[] >> dimp_tac >> strip_tac >> arw[] (* 2 *)
     >-- (drule Lt_Le >> arw[] >>
         qexistsl_tac [‘A'’,‘i1(X,Pow(A)) o i'’,
                       ‘i1(X,Pow(A)) o pi’] >>
         qspecl_then [‘X’,‘Pow(A)’] assume_tac
         rw[IMAGE_o,i1_IMAGE_eq_eq,App_App_o,i1_eq_eq] >>
         qexistsl_tac [‘a’,‘sa’] >> arw[] >>
         strip_tac >> irule Inj_Inj_o >> arw[i1_Inj]) >>
     (* Lt(App(p, x0), n) since its suc is le s0, still in p's image*)
     qby_tac ‘Lt(App(p, x0), n)’ >-- cheat >> arw[] >>
     qby_tac ‘?i0. i' = i1(X, Pow(A)) o i0’
     >-- cheat >>
     pop_assum strip_assume_tac >>
     qby_tac ‘?pi0. pi = i1(X, Pow(A)) o pi0’
     >-- cheat >>
     pop_assum strip_assume_tac >>
     qexistsl_tac [‘A'’,‘i0’,‘pi0’,‘a’,‘sa’] >> 
     fs[i1_IMAGE_eq_eq,IMAGE_o] >> 
     fs[App_App_o,i1_eq_eq]>>
     strip_tac >> irule Inj_o_Inj 
     >-- (qexistsl_tac [‘X + Pow(A)’,‘i1(X,Pow(A))’] >> 
         arw[]) >>
     qexistsl_tac [‘X + Pow(A)’,‘i1(X,Pow(A))’] >> arw[])>>
 pop_assum (x_choosel_then ["s0"] assume_tac) >>
 once_arw[] >> once_arw[GSYM App_App_o] >>
 once_rw[coPa_def] >> once_rw[App_App_o] >>
 once_rw[i1_eq_eq] >> once_rw[i2_eq_eq] >>
 rw[NOT_ex_F,i1_ne_i2] >> once_rw[constf_def] >>
 once_rw[Suc_eq_eq] >> 
 once_rw[FIB_coPa] >> once_rw[FIB_constf] >>
 qby_tac ‘FIB(p, Suc(n)) = Empty(X)’ 
 >-- (drule Upows_FIB_n_Lt_Empty >> first_x_assum irule >>
     rw[Lt_Suc]) >>
 once_arw[] >>  
 qby_tac ‘~(App(p,x0) = Suc(n))’ 
 >-- cheat >>
 drule FIB_constf_Empty >> once_arw[] >>
 once_arw[IMAGE_Empty] >> once_arw[Union_Empty2] >>
 once_arw[Empty_Union] >> 
 qby_tac ‘Le(App(p,x0),n)’ 
 >-- cheat >> arw[] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (qby_tac ‘App(p, x0) = n’ >-- cheat 
     (*because IMAGE(i, Whole(A)) = FIB(p, n)*) >>
     arw[] >> 
     qexistsl_tac [‘A’,‘i1(X,Pow(A)) o i’,‘i2(X,Pow(A))’,
                   ‘a’,‘s0’] >>
     arw[App_App_o] >> rfs[] >>
     rw[IMAGE_o] >> arw[] >>
     rw[i2_Inj] >> irule Inj_Inj_o >> arw[i1_Inj]) >>
 qby_tac
 ‘?f:A'->A. Bij(f) & i1(X,Pow(A)) o i o f = i' & 
            i2(X,Pow(A)) o Image(f) = pi’ 
 >-- 





 qby_tac ‘?f. i' = i1(X,Pow(A)) o i o f’ 
 >-- cheat >>
 pop_assum strip_assume_tac >> 
 qexistsl_tac [‘App(f,a)’,‘s0’] >>  rw[] >>
 qby_tac ‘App(i, App(f, a)) = x0’ 
 >-- (qspecl_then [‘X’,‘Pow(A)’] assume_tac i1_Inj >>
     drule Inj_eq_eq >> first_x_assum $ irule o iffLR >>
     pop_assum (K all_tac) >> 
     pop_assum (assume_tac o GSYM) >> arw[GSYM App_App_o] >>
     arw[o_assoc]) >>  arw[] >>
 qsuff_tac ‘s0 = IMAGE(f,sa)’ 
 >-- (strip_tac >> arw[] >> cheat) >>
 
 
 
 
     
     Inj_Pow_choice_independence
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
  Upows(Suc(n),coPa(p,constf(Pow(A),Suc(n))),R1,i1(X,Pow(A)) o z)”));
