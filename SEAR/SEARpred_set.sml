
val tof_Tpm_inv = prove_store("tof_Tpm_inv",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT] >>
 rw[GSYM tof_def,Tpm_def])
(form_goal
 “!A B f:A->B. tof(Tpm(f))  = f”));


val Tpm_tof_inv = prove_store("Tpm_tof_inv",
e0
(flip_tac >> rpt strip_tac >> irule is_Tpm >>
 rw[tof_def])
(form_goal
 “!A B f:mem(Exp(A,B)). Tpm(tof(f))  = f”));


val Tpm_eq_eq = prove_store("Tpm_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] >> 
 irule $ iffLR FUN_EXT >>
 once_rw[GSYM Tpm_def] >> arw[])
(form_goal “!A B f1:A->B f2. Tpm(f1) = Tpm(f2) <=> f1 = f2”));


val tof_eq_eq = prove_store("tof_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘Tpm(tof(f)) = Tpm(tof(g))’ >-- arw[]>> fs[Tpm_tof_inv] )
(form_goal
 “!A B f:mem(Exp(A,B)) g. tof(f)  = tof(g) <=> f = g”));



val IN_Sing = prove_store("IN_Sing",
e0
(rw[Sing_def,Sg_def])
(form_goal “!A a0 a:mem(A). IN(a,Sing(a0)) <=> a = a0”));

 
val EMPTY_def = qdefine_psym("EMPTY",[‘A’])
‘!x:mem(A).F’

val BU_ex = prove_store("BU_ex",
e0
(strip_tac >>
 qsuff_tac
 ‘?BU:Pow(Pow(A)) -> Pow(A). 
  !sss a:mem(A). IN(a,App(BU,sss)) <=>
  ?ss.IN(ss,sss) & IN(a,ss)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘BU’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >> strip_tac >>
     irule IN_EXT >> arw[]) >>
 irule 
 (P2fun' |> qtinst_thm [(‘A’,‘Pow(Pow(A))’),(‘B’,‘Pow(A)’)] |> qfVar_prpl_th1 ("P",[‘sss:mem(Pow(Pow(A)))’,‘u:mem(Pow(A))’],‘!a:mem(A). IN(a,u) <=>
           (?ss.IN(ss,sss) & IN(a,ss))’)) >>
 strip_tac >>
 accept_tac (IN_def_P |> 
 qfVar_prpl_th1 ("P",[‘a:mem(A)’],‘ (?ss.IN(ss,x) & IN(a:mem(A),ss))’))
 )
(form_goal
 “!A. ?!BU:Pow(Pow(A)) -> Pow(A). 
  !sss a:mem(A). IN(a,App(BU,sss)) <=>
  ?ss.IN(ss,sss) & IN(a,ss)”));
 

val BU_def = BU_ex |> spec_all |> qsimple_uex_spec "BU" [‘A’]
                         |> gen_all
                         |> store_as "BU_def"; 


val BIGUNION_def = qdefine_fsym("BIGUNION",[‘sss:mem(Pow(Pow(A)))’])
‘App(BU(A),sss)’ |> gen_all |> store_as "BIGUNION_def";


val IN_BIGUNION = BU_def |> rewr_rule[GSYM BIGUNION_def] 
                         |> store_as "IN_BIGUNION";

 


val Inj_ex_uex = prove_store("Inj_ex_uex",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- first_x_assum (accept_tac o uex2ex_rule) >>
 uex_tac >> qexists_tac ‘a’ >> arw[] >> rpt strip_tac >>
 fs[Inj_def] >> first_x_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !b. (?!a.App(f,a) = b) <=> (?a.App(f,a) = b)”)); (**)


val IMAGE_o = prove_store("IMAGE_o",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IMAGE_def] >> strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qexists_tac ‘App(f,a)’ >> arw[GSYM App_App_o] >>
     qexists_tac ‘a’ >> arw[]) >>
 qexists_tac ‘a'’ >> arw[App_App_o])
(form_goal “!A B f:A->B C g:B->C s:mem(Pow(A)). IMAGE(g o f,s) = IMAGE(g,IMAGE(f,s))”));



val ex_eq_IMAGE = prove_store("ex_eq_IMAGE",
e0
(rpt strip_tac >>
 strip_assume_tac
 (IN_def_P_ex |> qfVar_prpl_th1 ("P",[‘a:mem(A)’],
‘IN(App(f:A->B,a),s)’)) >>
 qexists_tac ‘s'’ >>
 pop_assum (assume_tac o GSYM) >>
 rw[GSYM IN_EXT_iff] >> strip_tac >> 
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (rw[IMAGE_def] >> arw[] >> 
     first_x_assum drule >>
     pop_assum strip_assume_tac >> 
     qexists_tac ‘a’ >> fs[]) >>
 fs[IMAGE_def] >> rfs[])
(form_goal “!A B f:A->B s:mem(Pow(B)).
 (!b. IN(b,s) ==> ?a. b = App(f,a)) ==>
 ?s0:mem(Pow(A)). s = IMAGE(f,s0) ”));

val App_IN_IMAGE = prove_store("App_IN_IMAGE",
e0
(rw[IMAGE_def] >> rpt strip_tac >>
 qexists_tac ‘a’ >> arw[])
(form_goal “!A B f:A->B s a. IN(a,s) ==> IN(App(f,a),IMAGE(f,s))”));


val IMAGE_BIGUNION = prove_store("IMAGE_BIGUNION",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IMAGE_def,IN_BIGUNION,Image_def] >>
 strip_tac >> dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (qexists_tac ‘IMAGE(f,ss')’ >> rw[IMAGE_def] >> strip_tac (* 2 *)
     >-- (qexists_tac ‘ss'’ >> arw[]) >>
     qexists_tac ‘a’ >> arw[]) >>
 first_assum (drule o iffLR) >>
 pop_assum strip_assume_tac >> arw[] >> qexists_tac ‘a'’ >> arw[] >>
 qexists_tac ‘a’ >> arw[])
(form_goal
 “!A B f:A->B ss.IMAGE(f,BIGUNION(ss)) = BIGUNION(IMAGE(Image(f),ss))”));

(*
(*Parallel product arrow*)
val Prla_def = 
    qdefine_fsym ("Prla",[‘f:A->B’,‘g:C->D’])
    ‘Pa(f o p1(A,C),g o p2(A,C))’
    |> gen_all |> store_as "Prla_def";(**)
*)

val Prla_Inj = prove_store("Prla_Inj",
e0
(rpt strip_tac >> fs[Inj_def,Prla_def] >> 
 fconv_tac (depth_fconv no_conv forall_cross_fconv) >>
 rw[App_Pa,Pair_eq_eq,App_App_o,p12_of_Pair] >>
 rpt strip_tac >> first_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==>
 !C D g:C->D. Inj(g) ==>
 Inj(Prla(f,g))”));


val Id_Inj = prove_store("Id_Inj",
e0
(rw[Inj_def,Id_def])
(form_goal
 “!X. Inj(Id(X))”));




val App_Pa_distr = prove_store("App_Pa_distr",
e0
(rpt strip_tac >> 
 qsspecl_then [‘ App(Pa(f, g), x)’] (assume_tac o GSYM) Pair_component >> 
 once_arw[] >> rw[Pair_eq_eq,GSYM App_App_o,p12_of_Pa])
(form_goal
“!X A f:X->A B g:X->B x. App(Pa(f:X->A,g:X->B),x) = Pair(App(f,x),App(g,x))”));(**)


val App_Pa_Pair = App_Pa_distr |> store_as "App_Pa_Pair";(**)

val App_Prla = prove_store("App_Prla",
e0
(rpt strip_tac >> rw[Prla_def,App_Pa_Pair] >>
 rw[App_App_o,p12_of_Pair] )
(form_goal “!A B f:A->B X Y g:X->Y a x.App(Prla(f,g),Pair(a,x)) = 
Pair(App(f,a),App(g,x))”)); (**)


(*
val o_assoc = prove_store("o_assoc",
e0
(rw[GSYM FUN_EXT,App_App_o])
(form_goal
 “!A B f:A->B C g:B->C D h:C->D.
  (h o g) o f = h o g o f”));
*)

val Pa_distr = prove_store("Pa_distr",
e0
(rpt strip_tac >> irule is_Pa >> 
 rw[p12_of_Pa,GSYM o_assoc])
(form_goal
“!A X a1:X ->A B a2:X->B.
  !X0 x:X0->X. Pa(a1,a2) o x = Pa(a1 o x,a2 o x) ”));


val Pa_eq_eq = prove_store("Pa_eq_eq",
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘p1(A,B) o Pa(f1, g1) = p1(A,B) o Pa(f2, g2) &
          p2(A,B) o Pa(f1, g1) = p2(A,B) o Pa(f2, g2)’
 >-- arw[] >>
 qsspecl_then [‘f1’,‘g1’] assume_tac p12_of_Pa >> 
 qsspecl_then [‘f2’,‘g2’] assume_tac p12_of_Pa >> 
 rfs[])
(form_goal
 “!A X f1:X->A f2:X->A B g1:X->B g2:X->B. 
  (Pa(f1,g1) = Pa(f2,g2) <=> f1 = f2 & g1 = g2)”));




val p2_comm = prove_store("p2_comm",
e0
(rw[GSYM FUN_EXT] >>
 rpt strip_tac >>
 qsspecl_then [‘a’] strip_assume_tac Pair_has_comp >>
 arw[App_App_o,App_Prla,p12_of_Pair])
(form_goal “!A B C f:B->C. f o p2(A,B) = p2(A,C) o Prla(Id(A),f)”));


val p1_comm = prove_store("p1_comm",
e0
(rw[GSYM FUN_EXT] >>
 rpt strip_tac >>
 qsspecl_then [‘a’] strip_assume_tac Pair_has_comp >>
 arw[App_App_o,App_Prla,p12_of_Pair])
(form_goal “!A B C f:A->C. f o p1(A,B) = p1(C,B) o Prla(f,Id(B))”));



val p1_Prla = prove_store("p1_Prla",
e0
(rw[p1_comm] >> rpt strip_tac >> once_rw[Prla_def] >> rw[p12_of_Pa])
(form_goal “!A X f:A->X B Y g:B->Y. p1(X,Y) o Prla(f,g) = f o p1(A,B)”));


fun exists_cross_fconv f = 
    let val (pv as (n,s),b) = dest_exists f 
        val pset = s |> dest_sort |> #2  |> hd
        val (A,B) = dest_cross pset 
        val pt = mk_var pv
        val eth = Pair_has_comp |> specl [A,B,pt]
        val (ocv1 as (ocn1,ocs1),ob1) = dest_exists (concl eth) 
        val (ocv2 as (ocn2,ocs2),ob2) = dest_exists ob1
        val avoids = fvf b
        val ct1 = pvariantt avoids (mk_var ocv1)
        val ct2 = pvariantt avoids (mk_var ocv2)
        val (cv1 as (cn1,cs1)) = dest_var ct1
        val (cv2 as (cn2,cs2)) = dest_var ct2
        val b1 = substf (ocv1,ct1) ob1
        val b2 = substf (ocv2,ct2) (substf (ocv1,ct1) ob2)
        val pair = mk_Pair ct1 ct2 
        val b' = substf (pv,pair) b
        val new0 = (mk_exists cn2 cs2 b')
        val new = mk_exists cn1 cs1 (mk_exists cn2 cs2 b')
        val l2r = b |> assume 
                    |> conv_rule (basic_fconv (rewr_conv (assume b2)) no_fconv)
                    |> existsI cv2 ct2 b'
                    |> existsI cv1 ct1 new0
                    |> existsE cv2 (assume b1)
                    |> existsE cv1 eth
                    |> existsE pv (assume f)
                    |> disch f
        val r2l = b'|> assume 
                    |> existsI pv pair b
                    |> existsE cv2 (assume new0)
                    |> existsE cv1 (assume new)
                    |> disch new
    in dimpI l2r r2l
    end


val IMAGE_Prla = prove_store("IMAGE_Prla",
e0
(rpt strip_tac >> rw[IMAGE_def] >> 
 fconv_tac (redepth_fconv no_conv exists_cross_fconv) >>
 rw[App_Prla,Pair_eq_eq])
(form_goal “!A X f:A->X B Y g:B->Y x y s.
 IN(Pair(x,y), IMAGE(Prla(f,g),s)) <=> 
 ?a b. IN(Pair(a,b),s) & x = App(f,a) & y = App(g,b)”));

val Image_IMAGE = prove_store("Image_IMAGE",
e0
(rw[GSYM IN_EXT_iff,IMAGE_def,Image_def])
(form_goal “!A B f:A->B s. App(Image(f),s) = IMAGE(f,s)”));



val IMAGE_Empty = prove_store("IMAGE_Empty",
e0
(rpt strip_tac >> rw[GSYM IN_EXT_iff,IMAGE_def] >> 
 strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- fs[Empty_def] >> fs[Empty_def])
(form_goal “!A B f:A->B. IMAGE(f,Empty(A)) = Empty(B)”));



val IN_NONEMPTY = prove_store("IN_NONEMPTY",
e0
(rw[GSYM IN_EXT_iff,Empty_def] >> rpt strip_tac >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[]) >>
 ccontra_tac >>
 qsuff_tac ‘!a. ~IN(a,s)’ >-- arw[] >>
 strip_tac >> ccontra_tac >>
 qsuff_tac ‘?a. IN(a,s)’ >--arw[] >>
 qexists_tac ‘a’ >> arw[])
(form_goal “!A s. (?a. IN(a,s)) <=> ~(s = Empty(A))”));


val IMAGE_Empty_Empty = prove_store("IMAGE_Empty_Empty",
e0
(rpt strip_tac >> qcases ‘s = Empty(A)’ >> arw[] (* 2 *)
 >-- rw[IMAGE_Empty] >>
 fs[GSYM IN_NONEMPTY] >> qexists_tac ‘App(f,a)’ >> rw[IMAGE_def] >>
 qexists_tac ‘a’ >> arw[])
(form_goal “!A B f:A->B s. IMAGE(f,s) = Empty(B) <=> s = Empty(A)”));


val BIGUNION_Empty_Empty = prove_store("BIGUNION_Empty_Empty",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (fs[GSYM IN_EXT_iff,IN_BIGUNION,Empty_def] >>
     strip_tac >> ccontra_tac >>
     qby_tac ‘?ss'. IN(ss',ss) & IN(x,ss')’ 
     >-- (qexists_tac ‘s’ >> arw[]) >>
     rfs[]) >>
 fs[GSYM IN_EXT_iff,IN_BIGUNION,Empty_def] >>
 strip_tac >> ccontra_tac >> pop_assum strip_assume_tac >>
 first_assum drule >> fs[])
(form_goal “!A ss. BIGUNION(ss) = Empty(A) <=> 
 (!s. IN(s,ss) ==> s = Empty(A))”));

val BIGUNION_NONEMPTY = 
prove_store("BIGUNION_NONEMPTY",
e0
(rw[GSYM IN_NONEMPTY,IN_BIGUNION] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac(* 2 *)
 >-- (qexists_tac ‘ss'’ >> arw[] >> qexists_tac ‘a’ >>
     arw[]) >>
 qexistsl_tac [‘a’,‘s’] >> arw[])
(form_goal
 “!A ss. ~(BIGUNION(ss) = Empty(A)) <=> 
 (?s. IN(s,ss) & ~(s = Empty(A)))”));


val BIGUNION_Empty_Empty' = prove_store("BIGUNION_Empty_Empty'",
e0
(rpt strip_tac >> dimp_tac >-- (rpt strip_tac >>
 last_x_assum (assume_tac o GSYM) >> drule $ iffLR BIGUNION_Empty_Empty >>
 first_assum drule >> arw[]) >>
 rpt strip_tac >> 
 drule $ iffRL BIGUNION_Empty_Empty >> arw[])
(form_goal “!A ss. Empty(A) = BIGUNION(ss)  <=> 
 (!s. IN(s,ss) ==> s = Empty(A))”));



val INTER_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qtinst_thm [(‘A’,‘Pow(A) * Pow(A)’),
                           (‘B’,‘Pow(A)’)]
            |> qfVar_prpl_th1 
 ("P",[‘s12:mem(Pow(A) * Pow(A))’,‘s:mem(Pow(A))’],
      ‘!a. IN(a,s) <=> IN(a:mem(A),Fst(s12)) & IN(a,Snd(s12))’)
           |> conv_rule (depth_fconv no_conv forall_cross_fconv)
           |> rewr_rule[Pair_def']) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P 
 |> qfVar_prpl_th1 ("P",[‘a':mem(A)’],‘IN(a':mem(A),a) & IN(a',b)’)) >> arw[])
(form_goal “!A. ?!f:Pow(A) * Pow(A) -> Pow(A).
 !s1 s2 a. IN(a,App(f,Pair(s1,s2))) <=> IN(a,s1) & IN(a,s2)”)
|> spec_all |> qsimple_uex_spec "INTER" [‘A’]

val Inter_def = qdefine_fsym("Inter",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘App(INTER(A),Pair(s1,s2))’ 



val UNION_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qtinst_thm [(‘A’,‘Pow(A) * Pow(A)’),
                           (‘B’,‘Pow(A)’)]
            |> qfVar_prpl_th1 
 ("P",[‘s12:mem(Pow(A) * Pow(A))’,‘s:mem(Pow(A))’],
      ‘!a. IN(a,s) <=> IN(a:mem(A),Fst(s12)) | IN(a,Snd(s12))’)
           |> conv_rule (depth_fconv no_conv forall_cross_fconv)
           |> rewr_rule[Pair_def']) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P
  |> qfVar_prpl_th1 ("P",[‘a':mem(A)’],‘IN(a':mem(A),a) | IN(a',b)’)) >> arw[])
(form_goal “!A. ?!f:Pow(A) * Pow(A) -> Pow(A).
 !s1 s2 a. IN(a,App(f,Pair(s1,s2))) <=> IN(a,s1) | IN(a,s2)”)
|> spec_all |> qsimple_uex_spec "UNION" [‘A’]

val IN_Inter = prove_store("IN_Inter",
e0
(rw[Inter_def,INTER_def])
(form_goal “!A s1 s2 a. IN(a:mem(A),Inter(s1,s2)) <=> IN(a,s1) & IN(a,s2)”));


val COMPL_def = proved_th $ 
e0
(strip_tac >>
 assume_tac
 (P2fun_uex |> qtinst_thm ([(‘A’,‘Pow(A)’),(‘B’,‘Pow(A)’)]) |> qfVar_prpl_th1 ("P",[‘s0:mem(Pow(A))’,‘s:mem(Pow(A))’],‘!a. IN(a,s) <=> ~IN(a:mem(A),s0)’)) >>
 first_x_assum irule >> rpt strip_tac >>
 assume_tac
 (IN_def_P 
 |> qfVar_prpl_th1 ("P",[‘a':mem(A)’],‘~IN(a':mem(A),x)’)) >> arw[])
(form_goal “!A. ?!f:Pow(A) -> Pow(A).
 !s a. IN(a,App(f,s)) <=> ~IN(a,s)”)
|> spec_all |> qsimple_uex_spec "COMPL" [‘A’]

val Compl_def = qdefine_fsym("Compl",[‘s:mem(Pow(A))’])
‘App(COMPL(A),s)’

val IN_Compl = prove_store("IN_Compl",
e0
(rw[Compl_def,COMPL_def])
(form_goal “!A s a. IN(a:mem(A),Compl(s)) <=> ~IN(a,s)”));


val Union_def = qdefine_fsym("Union",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘App(UNION(A),Pair(s1,s2))’



val m2r_def = AX1 |> qtinst_thm [(‘B’,‘A’)]
                  |> qfVar_prpl_th1 
 ("P",[‘x:mem(A)’,‘y:mem(A)’],‘IN(Pair(x,y),od:mem(Pow(A * A)))’)      |> qsimple_uex_spec "m2r" [‘od’] 
                  |> qspecl [‘a1:mem(A)’,‘a2:mem(A)’]
                  |> gen_all

val r2m_def = 
    IN_def_P |> qtinst_thm [(‘A’,‘A * A’)] 
             |> qfVar_prpl_th1 
 ("P",[‘a12:mem(A*A)’],
             ‘Holds(R:A~>A,Fst(a12),Snd(a12))’)
             |> qsimple_uex_spec "r2m" [‘R’] 
             |> qspecl [‘Pair(a1:mem(A),a2:mem(A))’]
             |> rewr_rule [Pair_def']
             |> gen_all

val IN_Union = prove_store("IN_Union",
e0
(rw[Union_def,UNION_def])
(form_goal “!A s1 s2 a:mem(A). IN(a,Union(s1,s2)) <=> IN(a,s1) | IN(a,s2)”));
 
val Union_Empty_Empty = prove_store("Union_Empty_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Union,Empty_def])
(form_goal “!A. Union(Empty(A),Empty(A)) = Empty(A)”));


val SS_Refl = prove_store("SS_Refl",
e0
(rw[SS_def])
(form_goal “!A s:mem(Pow(A)). SS(s,s)”));


val NONE_def = qdefine_fsym("NONE",[‘X’])
‘App(i2(X,1),dot)’

val Null_def = proved_th $
e0
(strip_tac >> rw[GSYM NONE_def] >>
 qsuff_tac
 ‘?f:N->X+1.!n. App(f,n) = NONE(X)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rw[GSYM FUN_EXT] >> rpt strip_tac >> arw[]) >>
 assume_tac (P2fun' |> qtinst_thm [(‘A’,‘N’),(‘B’,‘X+1’)]
                    |> qfVar_prpl_th1 ("P",[‘n:mem(N)’,‘x1:mem(X+1)’],‘x1 = NONE(X)’)) >>
 first_x_assum irule >> strip_tac >> uex_tac >> qexists_tac ‘NONE(X)’ >>
 rw[] >> rpt strip_tac >> arw[])
(form_goal “!X. ?!f:N->X+1.!n. App(f,n) = App(i2(X,1),dot)”)
|> spec_all |> qsimple_uex_spec "Null" [‘X’]
|> gen_all


val SOME_def = qdefine_fsym("SOME",[‘a:mem(A)’])
‘App(i1(A,1),a)’ |> gen_all



val PREIM_def = proved_th $
e0
(rpt strip_tac >>
 assume_tac
 (IN_def_P
 |> qfVar_prpl_th1 ("P",[‘a:mem(A)’],
‘?b. IN(b,s) & App(f:A->B,a) = b’)) >>
 arw[])
(form_goal “!A B f:A->B s.?!s0.
 !a. IN(a,s0) <=> ?b. IN(b,s) & App(f,a) = b ”)
|> spec_all |> qsimple_uex_spec "PREIM" [‘f’,‘s’]
|> gen_all


val Surj_Epi = prove_store("Surj_Epi",
e0
(rpt strip_tac >> fs[Surj_def,GSYM FUN_EXT,App_App_o] >>
 rpt strip_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 pop_assum (assume_tac o GSYM) >> arw[])
(form_goal “!A B f:A->B. Surj(f) ==>
 !C g1:B->C g2. g1 o f = g2 o f ==> g1 = g2”));


val true_def = qdefine_fsym("true",[]) ‘App(i2(1,1),dot)’

val false_def = qdefine_fsym("false",[]) ‘App(i1(1,1),dot)’


val i1_ne_i2 = prove_store("i1_ne_i2",
e0
(rpt strip_tac >>
 qsspecl_then [‘App(i1(A,B),a)’] assume_tac 
 i1_xor_i2  >> ccontra_tac >>
 qby_tac ‘?a'. App(i1(A, B), a) = App(i1(A, B), a')’ 
 >-- (qexists_tac ‘a’ >> rw[]) >>
 qby_tac ‘?b. App(i1(A,B),a) = App(i2(A,B),b)’ 
 >-- (qexists_tac ‘b’ >> arw[]) >>
 first_x_assum (drule o iffRL) >> fs[])
(form_goal “!A B a b.~(App(i1(A,B),a)= App(i2(A,B),b))”));

 
val true_ne_false = prove_store("true_ne_false",
e0
(rw[true_def,false_def,GSYM i1_ne_i2])
(form_goal “~(true = false)”));

val true_or_false = prove_store("true_xor_false",
e0
(rw[true_def,false_def] >> strip_tac >>
 qsspecl_then [‘tv’] assume_tac i1_or_i2 >> fs[dot_def] )
(form_goal “!tv. tv= true | tv = false”));


val true_xor_false = prove_store("true_xor_false",
e0
(strip_tac >> 
 qsspecl_then [‘tv’] strip_assume_tac true_or_false >> arw[GSYM true_ne_false] >>
 rw[true_ne_false])
(form_goal “!tv. ~(tv= true) <=> tv = false”)); 


val false_xor_true = prove_store("false_xor_true",
e0
(strip_tac >>  
 qcases ‘tv = true’ >> arw[true_ne_false] >> fs[true_xor_false])
(form_goal “!tv. ~(tv= false) <=> tv = true”)); 


val tv_eq_true = prove_store("tv_eq_true",
e0
(rpt strip_tac >>
 qcases ‘tv1 = true’ >> qcases ‘tv2 = true’ >> fs[true_xor_false] >>
 rw[true_ne_false] >> rw[GSYM true_ne_false])
(form_goal “!tv1 tv2. tv1 = tv2 <=>
 (tv1 = true <=> tv2 = true)”));

val tf_eq_true = prove_store("tf_eq_true",
e0
(rw[GSYM FUN_EXT] >> rpt strip_tac >>
 rw[GSYM tv_eq_true] )
(form_goal “!A tf1 tf2. tf1 = tf2 <=>
 (!a:mem(A). App(tf1,a) = true <=> App(tf2,a) = true)”));



fun basic_fconv_tac c fc = fconv_tac $ basic_fconv c fc
fun depth_fconv_tac c fc = fconv_tac $ depth_fconv c fc

val forall_cross_tac =  depth_fconv_tac no_conv forall_cross_fconv;

use "lambda.sml";


val r2f_def = 
proved_th $
e0
(strip_tac >>
 qsuff_tac
 ‘?f:A * B -> 1+1.
 !a b. App(f,Pair(a,b)) = App(i2(1,1),dot)  <=> Holds(R,a,b)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >> irule $ iffRL tf_eq_true >> 
     forall_cross_tac >> arw[true_def]) >>
 assume_tac
 (define_lambda 
“!ab.(Holds(R:A~>B,Fst(ab),Snd(ab)) ==> App(f,ab) = App(i2(1,1),dot)) &
     (ELSE ==> App(f,ab) = App(i1(1,1),dot))”) >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 qexists_tac ‘f’ >> rpt strip_tac >>
 first_x_assum (qsspecl_then [‘Pair(a,b)’] assume_tac) >> 
 fs[Pair_def'] >> 
 qcases ‘Holds(R,a,b)’ >> arw[] (* 2 *)
 >-- (first_x_assum drule >> arw[]) >>
 first_x_assum drule >> arw[] >>
 rw[GSYM true_def,GSYM false_def,GSYM true_ne_false])
(form_goal “!R:A~>B. ?!f:A * B -> 1+1.
 !a b. App(f,Pair(a,b)) = App(i2(1,1),dot)  <=> Holds(R,a,b)”)
|> spec_all |> qsimple_uex_spec "r2f" [‘R’] |> gen_all




val OR_def = proved_th $
e0
(qsuff_tac
 ‘?f:(1+1) * (1+1) -> 1+1. 
 App(f,Pair(true,true)) = true & 
 App(f,Pair(true,false)) = true &
 App(f,Pair(false,true)) = true &
 App(f,Pair(false,false)) = false’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >>
     forall_cross_tac >> rpt strip_tac >>
     qcases ‘a' = true’ >> qcases ‘b = true’ >> fs[true_xor_false]) >>
 strip_assume_tac $ uex2ex_rule $
 define_lambda
 “!tv12. (tv12 = Pair(false,false) ==> App(f,tv12) = false) &
         (ELSE ==> App(f,tv12) = true)” >>
 qexists_tac ‘f’ >> rpt strip_tac (* 4 *)
 >-- (first_x_assum (qsspecl_then [‘Pair(true,true)’] strip_assume_tac) >>
     first_x_assum irule  >> rw[Pair_eq_eq,true_ne_false]) 
 >-- (first_x_assum (qsspecl_then [‘Pair(true,false)’] strip_assume_tac) >>
     first_x_assum irule  >> rw[Pair_eq_eq,true_ne_false])
 >-- (first_x_assum (qsspecl_then [‘Pair(false,true)’] strip_assume_tac) >>
     first_x_assum irule  >> rw[Pair_eq_eq,true_ne_false]) >>
 first_x_assum (qsspecl_then [‘Pair(false,false)’] strip_assume_tac) >>
 fs[])
(form_goal “?!f:(1+1) * (1+1) -> 1+1. 
 App(f,Pair(true,true)) = true & 
 App(f,Pair(true,false)) = true &
 App(f,Pair(false,true)) = true &
 App(f,Pair(false,false)) = false”)
|> qsimple_uex_spec "OR" [] 


val NOT_def = proved_th $
e0
(qsuff_tac
 ‘?f:1+1 -> 1+1. 
App(f,true) = false & App(f,false) = true’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
      rpt strip_tac >> irule $ iffLR FUN_EXT >> strip_tac >>
      qcases ‘a = true’ >> fs[true_xor_false]) >>
 strip_assume_tac $ uex2ex_rule $ define_lambda
 “!tv. (tv = true ==> App(f,tv) = false) &
       (ELSE ==> App(f,tv) = true)” >>
 qexists_tac ‘f’ >> strip_tac (* 2 *)
 >-- (first_x_assum (qsspecl_then [‘true’] strip_assume_tac) >>
     fs[]) >>
 first_x_assum (qsspecl_then [‘false’] strip_assume_tac) >>
 fs[GSYM true_ne_false])
(form_goal “?!f:1+1 -> 1+1. 
App(f,true) = false & App(f,false) = true”)
|> qsimple_uex_spec "NOT" [] 


val f2r_def = proved_th $
e0
(rpt strip_tac >>
 assume_tac
 (AX1|> qfVar_prpl_th1 ("P",[‘a:mem(A)’,‘b:mem(B)’],
‘App(f:A * B-> 1+1,Pair(a,b)) = true’)) >> arw[])
(form_goal “!A B f:A * B -> 1+1.?!R:A~>B.
 !a b. Holds(R,a,b) <=> App(f,Pair(a,b)) = true”)
|> spec_all |> qsimple_uex_spec "f2r" [‘f’] |> gen_all


val ss2f = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac
 ‘?f:A -> 1+1.
  !a. App(f,a) = true <=> IN(a,s)’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >> strip_tac >>
     qcases ‘IN(a,s)’ (* 2 *)
     >-- (first_x_assum (drule o iffRL) >>
         first_x_assum (drule o iffRL) >> arw[]) >>
     first_x_assum (qspecl_then [‘a’] assume_tac) >>
     first_x_assum (qspecl_then [‘a’] assume_tac) >> rfs[true_xor_false]) >>
 strip_assume_tac $ uex2ex_rule $ define_lambda
 “!a. (IN(a:mem(A),s) ==> App(f,a) = true) &
 (ELSE ==> App(f,a) = false)” >>
 qexists_tac ‘f’ >>  strip_tac >>
 first_x_assum (qspecl_then [‘a’] strip_assume_tac) >>
 qcases ‘IN(a,s)’ >> first_x_assum drule >> arw[] >>
 rw[GSYM true_ne_false])
(form_goal “!A s:mem(Pow(A)).?!f:A -> 1+1.
 !a. App(f,a) = true <=> IN(a,s)”)
|> spec_all |> qsimple_uex_spec "ss2f" [‘s’]
 

val r2f_def' = r2f_def |> rewr_rule[GSYM true_def]


val constf_def = fun_tm_compr_uex 
                       (dest_var (rastt "a:mem(A)"))
                       (rastt "b:mem(B)")
                       |> qsimple_uex_spec "constf" [‘A’,‘b’]
                       |> gen_all
                       |> store_as "constf_def";


val FIB_def = qdefine_fsym("FIB",[‘f:A->B’,‘b:mem(B)’])
‘PREIM(f,Sing(b))’


(*fibre is preimage of a *)
val mFIB_def = qdefine_fsym("mFIB",[‘f:mem(Exp(A,B))’,‘b:mem(B)’])
‘PREIM(tof(f),Sing(b))’

val mApp_def = qdefine_fsym("mApp",[‘f:mem(Exp(A,B))’,‘a:mem(A)’]) ‘App(tof(f),a)’ |> gen_all


val Inj_Image_Inj = prove_store("Inj_Image_Inj",
e0
(rw[Inj_def] >> rpt strip_tac >>
fs[GSYM IN_EXT_iff,Image_def] >>
strip_tac >> dimp_tac >> strip_tac (* 2 *)
>-- (first_x_assum 
    (qspecl_then [‘App(i,x)’] assume_tac) >>
    qby_tac
    ‘?a. IN(a, x1) & App(i, x) = App(i, a)’ 
    >-- (qexists_tac ‘x’ >> arw[]) >>
    first_x_assum (drule o iffLR) >>
    pop_assum strip_assume_tac >>
    first_x_assum drule >> fs[]) >>
first_x_assum 
 (qspecl_then [‘App(i,x)’] assume_tac) >>
qby_tac
‘?a. IN(a, x2) & App(i, x) = App(i, a)’ 
>-- (qexists_tac ‘x’ >> arw[]) >>
first_x_assum (drule o iffRL) >>
pop_assum strip_assume_tac >>
first_x_assum drule >> fs[])
(form_goal
     “!A B i:A->B. 
        Inj(i:A->B) ==> Inj(Image(i))”));



val Compl_Whole = prove_store("Compl_Whole",
e0
(rw[GSYM IN_EXT_iff,IN_Compl,Whole_def,Empty_def])
(form_goal “!A. Compl(Whole(A)) = Empty(A)”));

val Compl_Empty = prove_store("Compl_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Compl,Whole_def,Empty_def])
(form_goal “!A. Compl(Empty(A)) = Whole(A)”));


val neg_or_distr = proved_th $
e0
(dimp_tac >> strip_tac (* 2 *)
 >-- (qcases ‘A’ >> fs[]) >>
 arw[])
(form_goal “(~(A | B)) <=> (~A & ~B)”)

val Inter_Compl_Compl = prove_store("Inter_Compl_Compl",
e0
(rw[GSYM IN_EXT_iff,Inter_def,INTER_def,Compl_def,COMPL_def,
    UNION_def,Union_def,neg_or_distr])
(form_goal “Inter(Compl(s1:mem(Pow(J))), Compl(s2)) = 
 Compl(Union(s1,s2))”));

val SS_Union = prove_store("SS_Union",
e0
(rw[SS_def,Union_def,UNION_def] >> rpt strip_tac >> arw[])
(form_goal “(!A a:mem(Pow(A)) b.SS(a,Union(a,b))) &
            (!A a:mem(Pow(A)) b.SS(a,Union(b,a)))”));

val SS_Union1 = SS_Union |> conjE1
val SS_Union2 = SS_Union |> conjE2;


val Ins_def = IN_def_P |> qtinst_thm [(‘A’,‘X’)]
                       |> qfVar_prpl_th1 
("P",[‘x:mem(X)’],‘x:mem(X) = x0 | IN(x,s0)’)
                       |> qsimple_uex_spec "Ins" [‘x0’,‘s0’]
                       |> qgen ‘s0’ |> qgen ‘x0’ |> qgen ‘X’
                       |> store_as "Ins_def";




val Union_Sing = prove_store("Union_Sing",
e0
(rw[GSYM IN_EXT_iff,IN_Union,IN_Sing,Ins_def])
(form_goal “!A a s.Union(Sing(a:mem(A)),s) = Ins(a,s)”));

val SS_Ins = prove_store("SS_Ins",
e0
(rw[SS_def,Ins_def] >> rpt strip_tac >> arw[])
(form_goal “!A a:mem(A) s. SS(s,Ins(a,s))”));

val BIGINTER_Sing = prove_store("BIGINTER_Sing",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,IN_Sing] >> 
 rw[IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (first_x_assum irule >> arw[]) >>
 arw[])
(form_goal “!A s:mem(Pow(A)). BIGINTER(Sing(s)) = s”));

val Whole_Inter = prove_store("Whole_Inter",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Whole_def])
(form_goal “!A s.Inter(Whole(A),s) = s”));


val Inter_Whole = prove_store("Inter_Whole",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Whole_def])
(form_goal “!A s.Inter(s,Whole(A)) = s”));


val IN_Inter = prove_store("IN_Inter",
e0
(rw[Inter_def,INTER_def])
(form_goal “!A s1:mem(Pow(A)) s2 a. IN(a,Inter(s1,s2)) <=> IN(a,s1) & IN(a,s2)”));

val Empty_SS = prove_store("Empty_SS",
e0
(rw[SS_def,Empty_def])
(form_goal “!A s. SS(Empty(A),s)”));

val BIGINTER_Empty = prove_store("BIGINTER_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,Whole_def,Empty_def])
(form_goal “BIGINTER(Empty(Pow(A))) = Whole(A)”));

val BIGINTER_Ins_Empty = prove_store("BIGINTER_Ins_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,Ins_def,Empty_def] >>
 rw[IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (first_x_assum irule >> arw[]) >>
 rpt strip_tac >> arw[])
(form_goal “!A x.BIGINTER(Ins(x, Empty(Pow(A)))) = x”));

val Inter_same = prove_store("Inter_same",
e0
(rw[GSYM IN_EXT_iff,IN_Inter] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal “!A x:mem(Pow(A)).Inter(x,x) = x”));


val BIGINTER_Ins = prove_store("BIGINTER_Ins",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,IN_Inter,Ins_def] >>
 rw[IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] (* 2 *)
 >-- (first_assum (qspecl_then [‘x’] assume_tac) >>
     fs[] >>
     rpt strip_tac >> first_x_assum irule >> arw[]) >>
 rpt strip_tac (* 2 *)
 >-- arw[] >>
 first_x_assum irule >> arw[])
(form_goal “!A x:mem(Pow(A)) xs0. BIGINTER(Ins(x, xs0)) = 
 Inter(x,BIGINTER(xs0))”));


val imp_or_distr = prove_store("imp_or_distr",
e0
(dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum irule >> arw[]) 
 >-- (first_x_assum irule >> arw[]) 
 >-- (first_x_assum drule >> arw[]) >>
 first_x_assum drule >> arw[])
(form_goal “(A | B ==> C) <=> (A ==> C) & (B ==> C)”));
 

val BIGINTER_Union = prove_store("BIGINTER_Union",
e0
(rw[GSYM IN_EXT_iff,IN_BIGINTER,IN_Union,IN_Inter] >>
 rpt strip_tac >> rw[imp_or_distr] >>
 dimp_tac >> strip_tac >> arw[])
(form_goal 
     “!A s1 s2:mem(Pow(Pow(A))).
BIGINTER(Union(s1,s2)) = Inter(BIGINTER(s1),BIGINTER(s2))”));


val Empty_Inter = prove_store("Empty_Inter",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Empty_def])
(form_goal “!A s. Inter(Empty(A),s) = Empty(A)”));

val Union_EMPTY = prove_store("Union_EMPTY",
e0
(rw[GSYM IN_EXT_iff,IN_Union,Empty_def] >>
 rw[neg_or_distr] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal “!A s1 s2. Union(s1,s2) = Empty(A) <=> 
    s1 = Empty(A) & s2 = Empty(A)”));

val neg_and_distr = prove_store("neg_and_distr",
e0
(dimp_tac >> strip_tac (* 3 *)
 >> qcases ‘A’ >> fs[])
(form_goal “~(A & B) <=> (~A | ~B)”));

 
val SS_Union_split = prove_store("SS_Union_split",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *) >--
 (x_choose_then "s1" assume_tac
 (IN_def_P_ex |> qtinst_thm [(‘A’,‘W’)]
 |> qfVar_prpl_th1 ("P",[‘a:mem(W)’],‘IN(a,s) & IN(a,A:mem(Pow(W)))’)) >> 
 x_choose_then "s2" assume_tac
 (IN_def_P_ex |> qtinst_thm [(‘A’,‘W’)]
              |> qfVar_prpl_th1 ("P",[‘a:mem(W)’],
                                 ‘IN(a,s) & IN(a,B:mem(Pow(W)))’)) >>
 qexistsl_tac [‘s1’,‘s2’] >>
 qby_tac ‘SS(s1,A)’
 >-- (rw[SS_def] >> rpt strip_tac >>
     first_x_assum (drule o iffRL) >> arw[]) >>
 qby_tac ‘SS(s2,B)’
 >-- (rw[SS_def] >> rpt strip_tac >>
     first_x_assum (drule o iffRL) >> arw[]) >> arw[] >>
 rw[GSYM IN_EXT_iff,IN_Union] >> strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (fs[SS_def,IN_Union] >> 
     first_x_assum drule >> pop_assum strip_assume_tac (* 2 *)
     >-- (disj1_tac >> first_x_assum (irule o iffLR) >> arw[]) >>
     disj2_tac >> first_x_assum (irule o iffLR) >> arw[]) >>
 first_x_assum (drule o iffRL) >> arw[]) >>
 rw[SS_def,IN_Union] >> rpt strip_tac >>
 fs[GSYM IN_EXT_iff,IN_Union] >>
 first_x_assum (drule o iffLR) >> pop_assum strip_assume_tac (* 2 *)
 >-- (fs[SS_def] >> disj1_tac >> first_x_assum irule >> arw[]) >>
 fs[SS_def] >> disj2_tac >> first_x_assum irule >> arw[] )
(form_goal “!W A B:mem(Pow(W)) s. SS(s,Union(A,B)) <=>
  ?s1 s2. SS(s1,A) & SS(s2,B) & s = Union(s1,s2) ”));


val Inter_Empty = prove_store("Inter_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,Empty_def])
(form_goal “!A s. Inter(s,Empty(A)) = Empty(A)”));


val SS_Sing = prove_store("SS_Sing",
e0
(rw[SS_def,IN_Sing] >> rpt strip_tac >> dimp_tac >>
 rpt strip_tac >> arw[] (* 3 *)
 >-- (qcases ‘?a. IN(a,s)’ (* 2 *)
     >-- (disj1_tac >> rw[GSYM IN_EXT_iff,IN_Sing] >>
         strip_tac >> dimp_tac >> arw[] >> strip_tac >>
         fs[] >> first_x_assum drule >> fs[]) >>
     disj2_tac >> fs[IN_NONEMPTY])
 >-- rfs[IN_Sing] >>
 rfs[Empty_def])
(form_goal “!A a s. SS(s,Sing(a)) <=> s = Sing(a) | s = Empty(A)”));

val Empty_Union = prove_store("Empty_Union",
e0
(rw[GSYM IN_EXT_iff,IN_Union,Empty_def])
(form_goal “!A s. Union(Empty(A),s) = s”));


val SS_Empty = prove_store("SS_Empty",
e0
(rw[GSYM IN_EXT_iff,Empty_def,SS_def])
(form_goal “!A s. SS(s,Empty(A)) <=> s = Empty(A)”));



val disj_assoc = prove_store("disj_assoc",
e0
(dimp_tac >> qcases ‘A’ >> fs[])
(form_goal “(A | B) | C <=> A | B | C”));

val Union_assoc = prove_store("Union_assoc",
e0
(rw[GSYM IN_EXT_iff,IN_Union,disj_assoc])
(form_goal “!A s1:mem(Pow(A)) s2 s3. Union(Union(s1,s2),s3) = Union(s1,Union(s2,s3))”));

val Inter_Whole_Whole = prove_store("Inter_Whole_Whole",
e0
(rpt strip_tac >> dimp_tac >> arw[] >> rpt strip_tac (* 3 *)
 >> fs[GSYM IN_EXT_iff,Whole_def,IN_Inter])
(form_goal “!A s1:mem(Pow(A)) s2. Inter(s1,s2) = Whole(A) <=> s1 = Whole(A) & s2 = Whole(A)”));

val Union_SS1 = prove_store("Union_SS1",
e0
(rpt strip_tac >> rw[SS_def,IN_Union,imp_or_distr] >>
 dimp_tac >> strip_tac >> arw[])
(form_goal “!A s1 s2 s:mem(Pow(A)). SS(Union(s1,s2),s) <=>
 SS(s1,s) & SS(s2,s)”));


val Union_Empty = Union_EMPTY

val SS_Inter = prove_store("SS_Inter",
e0
(rw[SS_def,IN_Inter] >> rpt strip_tac >> 
 dimp_tac >> rpt strip_tac (* 4 *)
 >-- (first_x_assum drule >> arw[])
 >-- (first_x_assum drule >> arw[]) 
 >-- (first_x_assum irule >> arw[]) >>
 first_x_assum irule >> arw[])
(form_goal “!A s1 s2:mem(Pow(A)) s. SS(s,Inter(s1,s2)) <=>
 SS(s,s1) & SS(s,s2)”));
 
val Inter_SS = prove_store("Inter_SS",
e0
(rw[SS_def,IN_Inter] >> rpt strip_tac)
(form_goal “!A s1 s2:mem(Pow(A)). SS(Inter(s1,s2),s1) & SS(Inter(s1,s2),s2)”));

val Whole_SS = prove_store("Whole_SS",
e0
(rw[SS_def,Whole_def,GSYM IN_EXT_iff])
(form_goal “!A X.SS(Whole(A),X) ==> X = Whole(A)”));

val SS_Whole = prove_store("SS_Whole",
e0
(rw[SS_def,Whole_def])
(form_goal “!A X. SS(X,Whole(A))”));


val Sing_Ins_Empty = prove_store("Sing_Ins_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Sing,Ins_def,Empty_def])
(form_goal “!A a:mem(A). Sing(a) = Ins(a,Empty(A))”));

val EMPTY_Empty_Whole = prove_store("EMPTY_Empty_Whole",
e0
(rw[GSYM IN_EXT_iff,Empty_def,Whole_def,EMPTY_def])
(form_goal “!A. EMPTY(A) <=> Empty(A) = Whole(A)”));

val NOT_EMPTY = prove_store("NOT_EMPTY",
e0
(rw[EMPTY_Empty_Whole] >> flip_tac >>
 rw[GSYM IN_NONEMPTY,Whole_def])
(form_goal “!A. ~EMPTY(A) <=> ?a:mem(A). T”));



val PSS_def = qdefine_psym("PSS",[‘s1:mem(Pow(A))’,‘s2:mem(Pow(A))’])
‘SS(s1:mem(Pow(A)),s2) & ~(s1 = s2)’



val NEQ_IN = prove_store("NEQ_IN",
e0
(rw[GSYM IN_EXT_iff] >> rpt strip_tac >> dimp_tac >> strip_tac (* 3 *)
 >-- (qcases ‘?a:mem(A).IN(a,s1) & ~IN(a,s2)’ >> arw[] >>
     ccontra_tac >> 
     qsuff_tac ‘!x.IN(x,s1) <=> IN(x,s2)’ >-- arw[] >>
     strip_tac >> last_x_assum (K all_tac) >>
     qcases ‘IN(x,s1)’ >> arw[] (* 2 *)
     >-- (ccontra_tac >>
         (*how can HOL realise it from here?*)
         qsuff_tac ‘?a. IN(a,s1) & ~IN(a,s2)’ >-- arw[] >>
         qexists_tac ‘x’ >> arw[]) >>
     ccontra_tac >>
     qsuff_tac ‘?a. IN(a,s2) & ~IN(a,s1)’ >-- arw[] >>
     qexists_tac ‘x’ >> arw[]) 
 >> ccontra_tac >> fs[])
(form_goal “!A s1 s2. ~(s1 = s2) <=> 
 (?a:mem(A).IN(a,s1) & ~IN(a,s2)) | (?a. IN(a,s2) & ~IN(a,s1))”));
 
val PSS_alt = prove_store("PSS_alt",
e0
(rw[PSS_def] >> rpt strip_tac >> dimp_tac >> rpt strip_tac >> arw[] (* 2 *)
 >-- (fs[NEQ_IN,SS_def] (*2 *)
     >-- (first_x_assum drule >> fs[]) >>
     qexists_tac ‘a’ >> arw[]) >>
 ccontra_tac >> fs[])
(form_goal “!A s1 s2:mem(Pow(A)).PSS(s1,s2) <=> 
 SS(s1,s2) & ?a. IN(a,s2) & ~IN(a,s1)”));


val Inter_Compl = prove_store("Inter_Compl",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,IN_Compl,Empty_def] >> rpt strip_tac >> rw[] >>
 ccontra_tac >> fs[])
(form_goal “!A a:mem(Pow(A)). Inter(a,Compl(a)) = Empty(A)”));


val neg_iff = prove_store("neg_iff",
e0
(dimp_tac >> strip_tac >> qcases ‘A’ >> fs[])
(form_goal “~(A <=> B) <=> (A & ~B) | (B & ~A)”));



val Union_Empty2 = prove_store("Union_Empty2",
e0
(rw[IN_Union,GSYM IN_EXT_iff,Empty_def])
(form_goal “!A s. Union(s,Empty(A)) = s”));

val Inter_eq_Empty = prove_store("Inter_eq_Empty",
e0
(rw[GSYM IN_EXT_iff,IN_Inter,SS_def,IN_Compl,Empty_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac >> ccontra_tac >>
 fs[] (* 2 *)
 >-- (first_x_assum (qspecl_then [‘a’] assume_tac) >>
     rfs[]) >>
 first_x_assum drule >> fs[])
(form_goal 
 “!W s1 s2.
 Inter(s1,s2) = Empty(W) <=> SS(s2,Compl(s1))”));



val PSS_SS = prove_store("PSS_SS",
e0
(rpt strip_tac >> fs[PSS_def])
(form_goal “!A s1:mem(Pow(A)) s2. PSS(s1,s2) ==> SS(s1,s2)”));

val SS_BIGUNION = prove_store("SS_BIGUNION",
e0
(rw[SS_def,IN_BIGUNION] >> rpt strip_tac >>
 qexists_tac ‘s0’ >> arw[] >> first_x_assum irule >> arw[])
(form_goal “!A s:mem(Pow(Pow(A))) ss s0. IN(s0,ss) & SS(s,s0) ==>
  SS(s,BIGUNION(ss))”));


val IMAGE_eq_Empty = prove_store("IMAGE_eq_Empty",
e0
(rw[GSYM IN_EXT_iff,IMAGE_def,Empty_def] >> rpt strip_tac >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (ccontra_tac >> 
     first_x_assum (qspecl_then [‘App(f,x)’] assume_tac) >>
     qsuff_tac ‘?a. IN(a,s) & App(f,x) = App(f,a)’
     >-- arw[] >> qexists_tac ‘x’>> arw[]) >>
 ccontra_tac >> fs[] >> rfs[])
(form_goal “!A B f:A->B s. IMAGE(f,s) = Empty(B) <=> 
 s = Empty(A)”));


(*c for component*)
val c31_def = qdefine_fsym("c31",[‘abc:mem(A * B * C)’]) ‘Fst(abc)’
val c32_def = qdefine_fsym("c32",[‘abc:mem(A * B * C)’]) ‘Fst(Snd(abc))’
val c33_def = qdefine_fsym("c33",[‘abc:mem(A * B * C)’]) ‘Snd(Snd(abc))’




val Del_def = IN_def_P |> qtinst_thm [(‘A’,‘X’)]
                       |> qfVar_prpl_th1
 ("P",[‘x:mem(X)’],‘IN(x,s0) & (~(x:mem(X) = x0))’)
                       |> qsimple_uex_spec "Del" [‘s0’,‘x0’]
                       |> qgen ‘x0’ |> qgen ‘s0’ |> qgen ‘X’
                       |> store_as "Del_def";

val Del_Ins = prove_store("Del_Ins",
e0
(rpt strip_tac >> irule IN_EXT >> 
 arw[Ins_def,Del_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >> ccontra_tac >> fs[])
(form_goal “!X x0:mem(X) xs0. (~IN(x0,xs0)) ==> Del(Ins(x0,xs0),x0) =xs0”));




val Ins_absorb = prove_store("Ins_absorb",
e0
(rpt strip_tac >> irule IN_EXT >> rw[Ins_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[])
(form_goal “!X x0:mem(X) xs0. IN(x0,xs0) ==> Ins(x0,xs0) =xs0”));


val Ins_Del = prove_store("Ins_Del",
e0
(rw[GSYM IN_EXT_iff,Ins_def,Del_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- arw[] >>
 arw[] >> 
 qcases ‘x = a’ >> arw[])
(form_goal “!A s a:mem(A). IN(a,s) ==>Ins(a, Del(s, a)) = s ”));


val IMAGE_eq_Empty = prove_store("IMAGE_eq_Empty",
e0
(rw[IMAGE_Empty_Empty])
(form_goal “!A B f:A->B ss. IMAGE(f,ss) = Empty(B) <=>
 ss = Empty(A)”));


val NOTIN_Del = prove_store("NOTIN_Del",
e0
(rw[GSYM IN_EXT_iff,Del_def] >>
 rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 ccontra_tac >> fs[])
(form_goal “!A a:mem(A) s. ~IN(a,s) ==> Del(s,a) = s”));


val Inj_IMAGE_Del = prove_store("Inj_IMAGE_Del",
e0
(rw[GSYM IN_EXT_iff,Del_def,IMAGE_def] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 3 *)
 >-- (arw[] >> qexists_tac ‘a'’ >> arw[]) 
 >-- (ccontra_tac >> fs[Inj_def] >>
     first_x_assum drule >> fs[]) >>
 qexists_tac ‘a'’ >> arw[] >> ccontra_tac >> fs[]
)
(form_goal “!A B f:A->B ss a.Inj(f) ==> IMAGE(f, Del(ss, a)) = 
 Del(IMAGE(f,ss),App(f,a)) ”));


fun exists_forall (n,s) = 
    let 
        val f0 = mk_fvar "f0" [(n,s)] [mk_var (n,s)]
        val af0 = mk_forall n s (mk_neg f0)
        val ef0 = mk_exists n s f0
        val d1 = (C negI)
                     (existsE (n,s) (assume ef0)
                 (negE (assume f0) 
                   ((C allE) (assume af0) (mk_var(n,s)))))
                 af0 |>
                 disch ef0
        val d2 = elim_double_neg
                     ((C negI)
                          (negE
                               (allI (n,s)
                                     ((C negI)
                                          (negE
                                               (existsI (n,s) (mk_var(n,s)) f0 ((C add_cont) (assume f0) (HOLset.add(essps,(n,s))))
                                                        )
                                               (assume (mk_neg ef0)))
                                          f0))
                               (assume (mk_neg af0))
)
                          (mk_neg ef0))|>
                     disch (mk_neg af0)
    in dimpI d1 d2
    end

val exists_forall_th = exists_forall ("a",mem_sort (rastt "A"))

val disj_not_imp = prove_store("disj_not_imp",
e0
(dimp_tac >> qcases ‘A’ >> fs[])
(form_goal “(A | ~B) <=> (B ==>A)”));


val not_disj_imp = prove_store("not_disj_imp",
e0
(dimp_tac >> qcases ‘A’ >> fs[])
(form_goal “(~B | A) <=> (B ==>A)”));


val set_NEQ = prove_store("set_NEQ",
e0
(rpt strip_tac >> dimp_tac >> strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[neg_or_distr] >>
     assume_tac $
     (exists_forall_th |> 
     qfVar_prpl_th1 ("f0",[‘a:mem(A)’],
‘IN(a,s1) & ~IN(a:mem(A),s2)’)) >> fs[] >>
     assume_tac $
     (exists_forall_th |> 
     qfVar_prpl_th1 ("f0",[‘a:mem(A)’],
‘~IN(a,s1) & IN(a:mem(A),s2)’)) >> fs[] >>
     fs[neg_and_distr] >> fs[disj_not_imp,not_disj_imp] >>
     qsuff_tac ‘s1 = s2’ 
     >-- arw[] >>
     irule $ IN_EXT >> strip_tac >> dimp_tac >> strip_tac >>
     first_x_assum drule >> arw[]) >>
 ccontra_tac >> fs[])
(form_goal “!A s1:mem(Pow(A)) s2. ~(s1 = s2) <=> (?a. IN(a,s1) & ~IN(a,s2)) |
 (?a. ~IN(a,s1) & IN(a,s2))”));


val Pa_Inj = prove_store("Pa_Inj",
e0
(rpt strip_tac >> rw[Inj_def] >> rw[App_Pa_Pair] >> rw[Pair_eq_eq] >>
 fs[Inj_def] >> rpt strip_tac >> first_x_assum irule >> arw[])
(form_goal “!X A f:X->A. Inj(f) ==> !B g:X->B. Inj(Pa(g,f))”));


val o_Inj_Inj = prove_store("o_Inj_Inj",
e0
(rpt strip_tac >> fs[Inj_def] >> rpt strip_tac >> fs[App_App_o] >>
 first_x_assum irule >> first_x_assum irule >> arw[])
(form_goal “!A B f:A->B. Inj(f) ==> !C g:B->C. Inj(g) ==> Inj(g o f)”));


(*think about how quo related to this*)
val Inj_restrict = prove_store("Inj_restrict",
e0
(rpt strip_tac >>
 assume_tac (P2fun_uex |> qtinst_thm [(‘A’,‘D’),(‘B’,‘C’)] |> qfVar_prpl_th1 ("P",[‘d:mem(D)’,‘c:mem(C)’],‘App(f0:D0->C0 o i1:D->D0, d) = App(i2:C->C0, c)’)) >>
 first_x_assum drule >> flip_tac >>
 fs[GSYM App_App_o,FUN_EXT])
(form_goal 
 “!D D0 i1:D->D0. Inj(i1) ==> 
  !C C0 i2:C->C0. Inj(i2) ==>
  !f0:D0->C0.
   (!d.?!c. App(f0 o i1,d) = App(i2,c)) ==>
  ?!f:D->C.i2 o f = f0 o i1”));

val SS_Del = prove_store("SS_Del",
e0
(rw[SS_def,Del_def] >> rpt strip_tac >> fs[])
(form_goal “!A a:mem(A) s. SS(Del(s,a),s)”));

val Inj_o_Inj = prove_store("Inj_o_Inj",
e0
(rpt strip_tac >> fs[Inj_def,App_App_o] >> rpt strip_tac >>
 first_x_assum irule >> arw[])
(form_goal “!A B f:A->B C g:B->C. Inj(g o f) ==> Inj(f) ”));


val SS_Ins_Del = prove_store("SS_Ins_Del",
e0
(rw[SS_def,Ins_def,Del_def] >> 
 rpt strip_tac >> first_x_assum drule >> rfs[])
(form_goal “!A a:mem(A) ss G.SS(ss, Ins(a, G)) ==> SS(Del(ss, a), G)
”));



val SOME_eq_eq = prove_store("SOME_eq_eq",
e0
(rw[SOME_def] >> rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 assume_tac i1_Inj >> fs[Inj_def] >> 
 first_x_assum drule >> arw[])
(form_goal “!X x1:mem(X) x2. SOME(x1) = SOME(x2) <=> x1 = x2”));


val option_xor = prove_store("option_xor",
e0
(rpt strip_tac >> rw[NONE_def,SOME_def] >> dimp_tac >> rpt strip_tac (* 2 *)
 >-- (qsuff_tac ‘?a0. a1 = App(i1(A,1),a0)’ 
     >-- (strip_tac >> uex_tac >> qexists_tac ‘a0’ >> arw[] >>
         qspecl_then [‘A’,‘1’] assume_tac i1_Inj >> fs[Inj_def] >>
         rpt strip_tac >> first_x_assum irule >> arw[]) >>
     rw[GSYM i2_xor_i1] >> ccontra_tac >> fs[dot_def]) >>
 pop_assum (assume_tac o uex2ex_rule) >> 
 drule $ iffRL i2_xor_i1 >> ccontra_tac >>
 qsuff_tac ‘?b. a1 = App(i2(A, 1), b)’ >-- arw[] >>
 qexists_tac ‘dot’ >> arw[])
(form_goal “!A a1:mem(A+1). ~(a1 = NONE(A)) <=> ?!a0. a1 = SOME(a0)”));

val NOT_true_iff_false = prove_store("NOT_true_iff_false",
e0
(strip_tac >>
 qcases ‘tv = false’ >> arw[NOT_def] >>
 fs[false_xor_true,NOT_def,GSYM true_ne_false])
(form_goal “!tv. App(NOT,tv) = true <=> tv = false”));


val SOME_NOTNONE = prove_store("SOME_NOTNONE",
e0
(rpt strip_tac >> rw[SOME_def,NONE_def] >> rw[i1_ne_i2])
(form_goal “!X x.~(SOME (x) = NONE(X)) ”));


val OM_def = proved_th $
e0
(rpt strip_tac >> 
 qsuff_tac
 ‘?om:A+1 -> B + 1.
   App(om,NONE(A)) = NONE(B) &
  (!a. App(om,SOME(a)) = SOME(App(f,a)))’
 >-- (strip_tac >> uex_tac >> qexists_tac ‘om’ >> arw[] >>
     rpt strip_tac >> rw[GSYM FUN_EXT] >> strip_tac >>
     qcases ‘a = NONE(A)’ (* 2 *)
     >-- arw[] >>
     fs[option_xor] >> pop_assum (strip_assume_tac o uex2ex_rule) >>
     arw[]) >>
 assume_tac 
 (P2fun' |> qtinst_thm [(‘A’,‘A+1’),(‘B’,‘B+1’)]
         |> qfVar_prpl_th1 ("P",[‘a1:mem(A+1)’,‘b1:mem(B+1)’],‘(a1 = NONE(A) & b1 = NONE(B)) |
          (?a.a1 = SOME(a) & b1 = SOME(App(f:A->B,a)))’)) >>
 qsuff_tac
 ‘?f':A+1->B+1. 
 !a1. (a1 = NONE(A) & App(f',a1) = NONE(B)) | 
(?a.a1 = SOME(a) & App(f',a1) = SOME(App(f,a)))’
 >-- (strip_tac >> qexists_tac ‘f'’ >> 
     first_assum (qspecl_then [‘NONE(A)’] assume_tac) >>
     fs[GSYM SOME_NOTNONE] >> strip_tac >>
     first_x_assum (qspecl_then [‘SOME(a)’] assume_tac) >> 
     fs[SOME_NOTNONE,SOME_eq_eq]) >>
 first_x_assum irule >>
 strip_tac >> uex_tac >>
 qcases ‘x = NONE(A)’ >> arw[GSYM SOME_NOTNONE] (* 2 *)
 >-- (qexists_tac ‘NONE(B)’ >> rw[] >> rpt strip_tac >> arw[]) >>
 fs[option_xor] >>
 pop_assum (strip_assume_tac o uex2ex_rule) >>
 arw[SOME_eq_eq] >> qexists_tac ‘SOME(App(f,a0))’ >> 
 rpt strip_tac >> arw[] >>
 qexists_tac ‘a0’ >> arw[])
(form_goal
 “!A B f:A->B. ?!om:A+1 -> B + 1.
   App(om,NONE(A)) = NONE(B) &
  (!a. App(om,SOME(a)) = SOME(App(f,a)))”)
|> spec_all |> qsimple_uex_spec "OM" [‘f’]

val Prla_split = prove_store("Prla_split",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT] >>
 strip_tac >>
 qsspecl_then [‘a’] (x_choosel_then ["a1","b1"] assume_tac) Pair_has_comp >>
 arw[App_App_o,App_Prla])
(form_goal “∀A1 A2 f1:A1-> A2 A3 f2:A2->A3 B1 B2 g1:B1->B2 B3 g2:B2->B3.
 Prla(f2 o f1,g2 o g1) = Prla(f2,g2) o Prla(f1,g1)”));(**)

 
val Prla_lsplit1 = prove_store("Prla_lsplit1",
e0
(rpt strip_tac >>
 qsspecl_then [‘f1’,‘f2’,‘Id(B1)’,‘g’] assume_tac Prla_split >>
 fs[IdR])
(form_goal “∀A1 A2 f1:A1-> A2 A3 f2:A2->A3 B1 B2 g:B1->B2.
 Prla(f2 o f1,g) = Prla(f2,g) o Prla(f1,Id(B1))”));(**)


val Prla_lsplit2 = prove_store("Prla_lsplit2",
e0
(rpt strip_tac >>
 qsspecl_then [‘f1’,‘f2’,‘g’,‘Id(B2)’] assume_tac Prla_split >>
 fs[IdL])
(form_goal “∀A1 A2 f1:A1-> A2 A3 f2:A2->A3 B1 B2 g:B1->B2.
 Prla(f2 o f1,g) = Prla(f2,Id(B2)) o Prla(f1,g)”));(**)

val Prla_rsplit2 = 
Prla_split |> qsspecl [‘f:A1->A2’,‘Id(A2)’,‘g1:B1->B2’,‘g2:B2->B3’] 
           |> rewr_rule[IdL] |> gen_all(**)


val Prla_rsplit1 = 
Prla_split |> qsspecl [‘Id(A1)’,‘f:A1->A2’,‘g1:B1->B2’,‘g2:B2->B3’] 
           |> rewr_rule[IdR] |> gen_all(**)

val Prla_Id = prove_store("Prla_Id",
e0
(rpt strip_tac >> rw[GSYM FUN_EXT] >> strip_tac >>
 qsspecl_then [‘a’] strip_assume_tac Pair_has_comp >>
 arw[App_Prla,Id_def])
(form_goal “∀A B.Prla(Id(A),Id(B)) = Id(A*B)”)); (**)

(*qsuff breaks*)
val P2fun_uex' = prove_store("P2fun_uex'",
e0
(rpt strip_tac >>
 suffices_tac
 “?f:A->B. !a:mem(A). P[a:mem(A),b:mem(B)](a, App(f,a))” 
 >-- (strip_tac >>
     uex_tac >> qexists_tac ‘f’ >> arw[] >>
     rpt strip_tac >> irule $ iffLR FUN_EXT >>
     rpt strip_tac >>
     first_x_assum (qspecl_then [‘a’] assume_tac)>>
     first_x_assum (qspecl_then [‘a’] assume_tac) >>
     first_x_assum (qspecl_then [‘a’] (strip_assume_tac o uex_expand)) >>
     qsuff_tac ‘App(f',a) = y & App(f,a) = y’ 
     >-- (rpt strip_tac >> arw[]) >>
     rpt strip_tac >> first_x_assum irule >> arw[]) >>
 drule P2fun' >> arw[])
(form_goal “(!x:mem(A). ?!y:mem(B). P[a:mem(A),b:mem(B)](x,y)) ==>
 ?!f:A->B. !a:mem(A). P[a:mem(A),b:mem(B)](a, App(f,a))”));


val Thm_2_4_unique = proved_th $
e0
(rpt strip_tac >>
 qby_tac
 ‘∀b. ?!b'. App(i,b) = App(i',b')’ 
 >-- (strip_tac >> flip_tac >> irule $ iffRL Inj_ex_uex >>
     arw[] >> flip_tac >> pop_assum (assume_tac o GSYM) >> arw[] >>
     qexists_tac ‘b’ >> rw[]) >>
 drule (P2fun |> qtinst_thm [(‘A’,‘B’),(‘B’,‘B'’)]
              |> qfVar_prpl_th1 
              ("P",[‘b:mem(B)’,‘b':mem(B')’],
               ‘App(i:B->A,b) = App(i':B'->A,b')’)) >>
 pop_assum strip_assume_tac >>
 qby_tac
 ‘∀b'. ?!b. App(i,b) = App(i',b')’ 
 >-- (strip_tac >>  irule $ iffRL Inj_ex_uex >>
     arw[] >> flip_tac >> 
     last_x_assum (K all_tac) >>
     last_x_assum (assume_tac o GSYM) >> arw[] >>
     qexists_tac ‘b'’ >> rw[]) >>
 drule (P2fun |> qtinst_thm [(‘A’,‘B'’)]
              |> qfVar_prpl_th1 
("P",[‘b':mem(B')’,‘b:mem(B)’],
‘App(i:B->A,b) = App(i':B'->A,b')’)) >>
 pop_assum strip_assume_tac >> 
 qexistsl_tac [‘f’,‘f'’] >> rw[GSYM FUN_EXT,App_App_o,Id_def] >>
 arw[] >>
 qsuff_tac
 ‘(!a. App(i, App(f', a)) = App(i', a)) &
  (!a. App(i, a) = App(i', App(f, a)))’ 
 >-- (rpt strip_tac >> arw[]) >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 pop_assum (assume_tac o GSYM) >> arw[] >>
 qpick_x_assum
 ‘∀a b. App(f,a) = b ⇔ App(i,a) = App(i',b)’ (assume_tac o GSYM) >>
 arw[])
(form_goal “
 ∀i:B->A B' i'.
 (Inj(i) &
      (∀a. P[a:mem(A)](a) <=> ∃b:mem(B). a = App(i,b))) & 
 (Inj(i') & 
      (∀a. P[a:mem(A)](a) ⇔ ∃b:mem(B'). a = App(i',b))) ⇒
  ∃f:B -> B' g:B' -> B. 
     f o g = Id(B') &
     g o f = Id(B) &
     i' o f = i & i o g = i'”)


val Thm_2_4' = proved_th $
e0
(strip_assume_tac Thm_2_4 >> 
  qexistsl_tac [‘B’,‘i’] >> arw[] >>
 rpt strip_tac >>
 match_mp_tac Thm_2_4_unique >> arw[])
(form_goal 
 “
    ∃B i:B->A. 
     (Inj(i) &
      (∀a. P[a:mem(A)](a) <=> ∃b:mem(B). a = App(i,b))) &
     (∀B' i':B'->A.
      Inj(i') & 
      (∀a. P[a:mem(A)](a) ⇔ ∃b:mem(B'). a = App(i',b)) ⇒
     ∃f:B -> B' g:B' -> B. 
     f o g = Id(B') &
     g o f = Id(B) &
     i' o f = i & i o g = i')”)



val T24_ts_ex = proved_th $
e0
(strip_tac >> qexistsl_tac [‘A’,‘Id(A)’] >> rw[])
(form_goal “!A. ?B i:B->A. T”)

val Rrefl = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘Id(B)’,‘Id(B)’] >> rw[IdR,IdL])
(form_goal 
 “∀B i:B->A. 
  ∃f:B ->B g:B->B. f o g = Id(B) & g o f = Id(B) &
    i o f = i & i o g = i”)

val Rsym = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘g’,‘f’] >> arw[])
(form_goal 
“∀B i:B ->A B' i':B' -> A. 
 (∃f:B->B' g:B'->B.
  f o g = Id(B') & g o f = Id(B) &
  i' o f = i & i o g = i') ⇒ 
 (∃f:B'->B g:B->B'.
  f o g = Id(B) & g o f = Id(B') &
  i o f = i' & i' o g = i)”)


val Rtrans = proved_th $
e0
(rpt strip_tac >> qexistsl_tac [‘f' o f’,‘g o g'’] >> arw[] >>
 arw[GSYM o_assoc] >> 
 qsuff_tac
 ‘f' o (f o g) o g' = Id(B'') & g o (g' o f') o f = Id(B)’ 
 >-- rw[o_assoc] >>
 arw[IdL,IdR])
(form_goal 
“∀B i:B ->A B' i':B' -> A B'' i'':B''->A. 
 (∃f:B->B' g:B'->B.
  f o g = Id(B') & g o f = Id(B) &
  i' o f = i & i o g = i') & 
 (∃f:B'->B'' g:B''->B'.
  f o g = Id(B'') & g o f = Id(B') &
  i'' o f = i' & i' o g = i'') ⇒
 (∃f:B->B'' g:B''->B.
  f o g = Id(B'') & g o f = Id(B) &
  i'' o f = i & i o g = i'')”)

val T24_eqv = conjI Rrefl (conjI Rsym Rtrans)


val set_spec_eqv = T24_eqv |> gen_all

val set_spec_arg12eqr0 = 
([("B",set_sort),("i",fun_sort (rastt "B") (rastt "A"))],
 [("B'",set_sort),("i'",fun_sort (rastt "B'") (rastt "A"))],
 “(∃f:B->B' g:B'->B.
           f o g = Id(B') & g o f = Id(B) &
           i' o f = i & i o g = i':B'->A)”)


fun set_spec oriset sname iname fvs uexth = 
    let val cuexth = concl uexth 
        val (buexth,arg) = strip_exists cuexth 
        val (Q,_) = dest_conj buexth
        val argQ = (arg,Q) 
        val tenv = mk_tinst [(("A",set_sort),oriset)]
        val arg12eqr = 
            (List.map (dest_var o (inst_term (vd_of tenv)) o mk_var) 
                      (#1 set_spec_arg12eqr0),
            List.map (dest_var o (inst_term (vd_of tenv)) o mk_var) 
                      (#2 set_spec_arg12eqr0),
            inst_form tenv (#3 set_spec_arg12eqr0))
        val eth = T24_ts_ex |> allE oriset
        val eqvth = set_spec_eqv |> allE oriset
    in new_spec argQ arg12eqr [sname,iname] fvs eth eqvth uexth
    end



val Diff_def = 
IN_def_P 
|> qfVar_prpl_th1 ("P",[‘a:mem(A)’],
‘IN(a:mem(A),s1) & ~IN(a,s2)’)
|> qsimple_uex_spec "Diff" [‘s1’,‘s2’] |>gen_all

val Inter_Sing_NONEMPTY =
 prove_store("Inter_Sing_NONEMPTY",
e0
(rpt strip_tac >>
 rw[GSYM IN_EXT_iff,Empty_def,IN_Inter,IN_Sing] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (ccontra_tac >>
     qsuff_tac
     ‘!x. ~(IN(x,s) & x = a)’
     >-- arw[] >>
     rpt strip_tac >> ccontra_tac >> rfs[] >> fs[])
     >>
 ccontra_tac >>
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 fs[])
(form_goal
 “!A s:mem(Pow(A)) a.
   ~(Inter(s,Sing(a)) = Empty(A)) <=> 
   IN(a,s)”));

val Diff_Empty = prove_store("Diff_Empty",
e0
(rw[GSYM IN_EXT_iff,Diff_def,Empty_def])
(form_goal “!A s. Diff(s,Empty(A)) = s”));


val Diff_Empty_SS = prove_store("Diff_Empty_SS",
e0
(rw[GSYM IN_EXT_iff,Empty_def,Diff_def,SS_def,neg_and_distr] >> rpt strip_tac >> dimp_tac >> rpt strip_tac (*2*)
 >-- (first_x_assum (qspecl_then [‘a’] assume_tac) >>
     fs[]) >>
 qcases ‘~IN(x, s1)’ >> fs[] >>
 first_x_assum drule >> arw[])
(form_goal
 “!A s1 s2. Diff(s1,s2) = Empty(A) <=>
 SS(s1,s2)”));

val Ins_Union = prove_store("Ins_Union",
e0
(rw[GSYM IN_EXT_iff,IN_Union,Ins_def,IN_Sing])
(form_goal
 “!A a:mem(A) s. Ins(a,s) = Union(Sing(a),s)”));

val Union_Empty_both_Empty = prove_store
("Union_Empty_both_Empty",
e0
(rw[GSYM IN_EXT_iff,Empty_def,IN_Union] >>
 rpt strip_tac >> dimp_tac >> rpt strip_tac (* 3 *)
 >-- (ccontra_tac>> 
     first_x_assum (qspecl_then [‘x’] assume_tac) >>
     rfs[]) 
 >-- (ccontra_tac >>
     first_x_assum (qspecl_then [‘x’] assume_tac)>>
     rfs[]) >>
 first_x_assum (qspecl_then [‘x’] assume_tac) >>
  first_x_assum (qspecl_then [‘x’] assume_tac)>>
 arw[])
(form_goal
 “!A s1 s2. Union(s1,s2) = Empty(A) <=>
            s1 = Empty(A) & s2 = Empty(A)”));

val Inter_Union = prove_store("Inter_Union",
e0
(rpt strip_tac >> 
 rw[GSYM IN_EXT_iff,IN_Inter,IN_Union] >>
 strip_tac >> dimp_tac >> rpt strip_tac (* 6 *)
 >> arw[])
(form_goal
 “!A s1 s2 s3:mem(Pow(A)). Inter(s1,Union(s2,s3)) = 
  Union(Inter(s1,s2),Inter(s1,s3))”));

val Inter_Diff_Sing_NONEMPTY = 
prove_store("Inter_Diff_Sing_NONEMPTY",
e0
(rpt strip_tac >>
 rw[GSYM IN_EXT_iff,IN_Inter,Empty_def,IN_Sing] >>
 dimp_tac >> rpt strip_tac (* 2 *)
 >-- (ccontra_tac >> fs[neg_and_distr] >>
     qby_tac
     ‘!x'. ~IN(x', Diff(s1, s2)) | ~(x' = x)’
     >-- (strip_tac >> qcases ‘x' = x’ >> arw[]) >>
     fs[]) >>
ccontra_tac >> 
first_x_assum (qspecl_then [‘x’] assume_tac) >>
fs[])
(form_goal
 “!A s1 s2 x.
  ~(Inter(Diff(s1, s2), Sing(x)) = Empty(A)) <=> 
   IN(x,Diff(s1,s2))”));

val Diff_Ins_NONEMPTY = prove_store("Diff_Ins_NONEMPTY",
e0
(rpt strip_tac >> 
 rw[Ins_Union,Inter_Union,Union_Empty_both_Empty] >>
 rw[neg_and_distr,Inter_Diff_Sing_NONEMPTY] >>
 dimp_tac >> rpt strip_tac (* 4 *)>> arw[] )
(form_goal
 “!A s1 s2 s3 x:mem(A).
  ~(Inter(Diff(s1,s2),Ins(x,s3)) = Empty(A)) <=>
  ~(Inter(Diff(s1,s2),s3) = Empty(A))| IN(x,Diff(s1,s2))”));

val Inter_Empty2 = prove_store("Inter_Empty2",
e0
(rpt strip_tac >> ccontra_tac >>
 fs[GSYM IN_EXT_iff,Empty_def,IN_Inter] >> 
 first_x_assum (qspecl_then [‘a’] assume_tac) >>
 rfs[])
(form_goal 
 “!A s1 s2. Inter(s1,s2) = Empty(A) ==>
  !a.IN(a,s2) ==> ~IN(a,s1)”));

val Inter_both_NONEMPTY = prove_store("Inter_both_NONEMPTY",
e0
(rpt strip_tac >> ccontra_tac >>
 fs[Inter_Empty,Empty_Inter])
(form_goal
 “!A s1 s2. ~(Inter(s1,s2) = Empty(A)) ==>
   ~(s1 = Empty(A)) & ~(s2 = Empty(A))”));


val neg_imp_conj = prove_store("neg_imp_conj",
e0
(dimp_tac >> strip_tac (* 2 *)
 >-- (strip_tac (* 2 *) >--
     (ccontra_tac >> fs[]) >>
     ccontra_tac >> fs[]) >>
 ccontra_tac >> first_x_assum drule >> fs[])
(form_goal “~(A ==> B) <=> A & ~B”)); 



val forall_exists_dual = prove_store("forall_exists_dual",
e0
(dimp_tac >> strip_tac (* 2 *)
 >-- (ccontra_tac >> rfs[]) >>
 strip_tac >> ccontra_tac >>
 suffices_tac “?a:mem(A). ~P[a:mem(A)](a)” >-- arw[] >> 
 qexists_tac ‘a’ >> arw[])
(form_goal “ (!a:mem(A).P[a:mem(A)](a)) <=>
 ~(?a:mem(A).~P[a:mem(A)](a))”));


val neg_conj_imp = prove_store("neg_conj_imp",
e0
(dimp_tac >> strip_tac (* 2 *)
 >-- (strip_tac >> ccontra_tac >>
     qby_tac ‘A & B’ >-- (strip_tac >> arw[]) >>
     rfs[]) >>
 ccontra_tac >>
 fs[])
(form_goal “~(A & B) <=> (A ==> ~B)”));
