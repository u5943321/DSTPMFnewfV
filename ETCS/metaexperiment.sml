(*orginal ETCS*)

val _ = new_sort "ob" [] 
val _ = new_sort "ar" [("A",mk_sort "ob" []),("B",mk_sort "ob" [])];
val _ = EqSorts := "ar" :: (!EqSorts);
val ob_sort = mk_sort "ob" [];
fun ar_sort A B = mk_sort "ar" [A,B];


fun mk_ob name = mk_var (name,ob_sort);
fun mk_ar name dom cod = mk_var (name,ar_sort dom cod);

val _ = new_fun "eo" (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])],[("f",mk_sort "ar" [mk_var("B",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])]),("g",mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("B",mk_sort "ob" [])])])


val _ = new_fun "I" 
       (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("A",mk_sort "ob" [])],
        [("A",mk_sort "ob" [])])


val IL = store_ax("IL", “!B A f:ar(B,A). eo(I(A),f) = f”);

val IR = store_ax("IR",“!A B f:ar(A,B). eo(f,I(A)) = f”);

val eo_assoc = store_ax("o_assoc",“!A.!B.!f: ar(A,B).!C.!g:ar(B,C).!D.!h:ar(C,D).eo(eo(h,g),f) = eo(h,eo(g,f))”);

(*translating ETCS*)

val _ = trfsym "I";
val _ = trfsym "eo";

val ds_ar = create_ds "ar";
val dfsym_I = mk_dfsym_ax "I" |> rewr_rule[]; 
val dfsym_eo = mk_dfsym_ax "eo" |> rewr_rule[];

val eo0_assoc = translate(concl eo_assoc) 
                         |> rewr_rule[eo_assoc];

val IL0 = translate(concl IL) |> rewr_rule[IL];
val IR0 = translate(concl IR) |> rewr_rule[IR];


(*@ issue..., should not be an axiom, just redefine,
 TODO: define_fsym should check output sort, and check has equality, instead of just allowing one sort for each workspace*)

(*
fun clear_fun (fd:fsymd) f = Binarymap.remove (fd,f)
val _ = clear_fun (!fsyms) "oa"
lookup_fun (!fsyms) "oa" why not work
*)



val oa_new = store_ax("oa_new",
“!A f g:2->A. oa(g,f) = g @ f”)

(*define mono and iso, cheat for the fact that all iso is mono, want to apply it to ETCS*)

val cmono_def = define_psym("cmono",[("f",fun_sort (mk_fun "2" []) (mk_cat "A"))])
“!g1 g2:2->A. 
 dom(g1) = dom(g2) & cpsb(f,g1) & cpsb(f,g2) & 
 oa(f,g1) = oa(f,g2) ==> g1 = g2”;
val cmono_def = cmono_def |> gen_all; 


val ciso_def = define_psym("ciso",[("f",fun_sort (mk_fun "2" []) (mk_cat "A"))])
“?g:2->A. 
 cpsb(f,g) & cpsb(g,f) & 
 oa(f,g) = id(dom(g)) & oa(g,f) = id(dom(f))”|> gen_all;


val iso_is_mono = proved_th $
e0
cheat
(form_goal “!A f:2->A. ciso(f) ==> cmono(f)”);


(*translate setttings of CCAF*)


val _ = trfsym "id";
val _ = trfsym "oa";

val ds_fun = create_ds "fun";
val dfsym_I = mk_dfsym_ax "id" |> rewr_rule[]; 
val dfsym_oa = mk_dfsym_ax "oa" |> rewr_rule[];


val ao_assoc = Thm8 |> rewr_rule[GSYM oa_new];
val ao0_assoc = translate(concl ao_assoc) 
                         |> rewr_rule[ao_assoc];

val idL' = idL |> rewr_rule[GSYM oa_new];
val idL0 = translate(concl idL') |> rewr_rule[idL'];

val idR' = idR |> rewr_rule[GSYM oa_new];
val idR0 = translate(concl idR') |> rewr_rule[idR'];


(*translated CCAF def/thm*)
val ciso0_def = (translate (concl ciso_def))
                     |> rewr_rule[ciso_def]

val cmono0_def = (translate (concl cmono_def))
                     |> rewr_rule[cmono_def]

val iso_is_mono0 = (translate (concl iso_is_mono))
                     |> rewr_rule[iso_is_mono]

(*defining iso and mono in ETCS*)


val eiso_def = qdefine_psym("eiso",[‘f: ar(A:ob,B:ob)’])
‘?g:ar(B:ob,A:ob). eo(g,f) = I(A) & eo(f,g) = I(B)’
|> qgenl[‘A’,‘B’,‘f’] |> store_as "eiso_def";

(*
val eiso_def = proved_th $
e0
cheat
(form_goal
 “eiso(f) <=> ?g:ar(B:ob,A:ob). eo(g,f) = I(A) & eo(f,g) = I(B)”) |> gen_all
*)


val emono_def = qdefine_psym("emono",[‘f: ar(A:ob,B:ob)’])
‘!X:ob g:ar(X:ob,A:ob) h. eo(f,g) = eo(f,h) ==> g = h’
|> qgenl[‘A’,‘B’,‘f’] |> store_as "emono_def";

(*translating ETCS*)

val eiso0_def = translate (concl eiso_def) |> rewr_rule[eiso_def];

val emono0_def = translate (concl emono_def) |> rewr_rule[emono_def];

(*goal is*)

val final_goal = “!A B f:ar(A,B). eiso(f) ==> emono(f)”;

val iff_thm = translate (“!A B f:ar(A,B). eiso(f) ==> emono(f)”) |> rewr_rule[] 

(*therefore, it is sufficient to prove the RHS*)

val to_be_proved = “!A:ob0 B:ob0 f:ar0. dar1(f) = A & dar2(f) = B ==>
 eiso0(f) ==> emono0(f)”

(*it is possible to use the eiso and emono defs within ETCS to prove every iso is mono, but here we want to experiment we can do this in an alternative way by establishing the correspondence between definitions and get this theorem from CCAF version.*)

(*Axioms embedding ETCS into CCAF*)

(*translation function symbols are entirely in the meta logic, i.e., the workspace with strictly no sort dependency*)

val ob0_sort = mk_sort "ob0" [];
val cat0_sort = mk_sort "cat0" [];
val fun0_sort = mk_sort "fun0" [];
val ar0_sort = mk_sort "ar0" [];

val _ = new_fun "eob" (ob0_sort,[("s",fun0_sort)])
val _ = new_fun "cob" (fun0_sort,[("s",ob0_sort)])

val _ = new_fun "ETCS0" (mk_sort "cat0" [],[]:  (string * sort) list)

(*for object translation*)
val eob_of_cob = store_ax("eob_of_cob",
“!a:ob0. eob(cob(a)) = a”)

val cob_of_eob = store_ax("cob_of_eob",
“!a:fun0. dfun1(a) = 10 & dfun2(a) = ETCS0 ==> cob(eob(a)) = a”)

val dfun12_cob = store_ax("dfun12_cob",
“!a:ob0. dfun1(cob(a)) = 10 & dfun2(cob(a)) = ETCS0”);

(*for ar translation*)

val _ = new_fun "ear" (ar0_sort,[("f",fun0_sort)])
val _ = new_fun "cfun" (fun0_sort,[("f",ar0_sort)])

val cfun_of_ear = store_ax("cfun_of_ear",
“!f:fun0. dfun1(f) = 20 & dfun2(f) = ETCS0 ==> cfun(ear(f)) = f”);

val ear_of_cfun = store_ax("ear_of_cfun",
“!f:ar0. ear(cfun(f)) = f”);

val dfun12_cfun = store_ax("dfun12_cfun",
“!f:ar0. dfun1(cfun(f)) = 20 & dfun2(cfun(f)) = ETCS0”);

val dom0_def = translate (concl dom_def) |> rewr_rule[dom_def];
val cod0_def = translate (concl cod_def) |> rewr_rule[cod_def]


val dar12_ear = store_ax("dar12_ear",
“!f:fun0. dfun1(f) = 20 & dfun2(f) = ETCS0 ==>
  dar1(ear(f)) = eob(dom0(f)) & dar2(ear(f)) = eob(cod0(f))”);



val eob_eq_eq = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘cob(eob(a1)) = cob(eob(a2))’ >-- arw[] >>
 qby_tac ‘cob(eob(a1)) = a1’ >-- (irule cob_of_eob >> arw[]) >>
 qby_tac ‘cob(eob(a2)) = a2’ >-- (irule cob_of_eob >> arw[]) >>
 fs[])
(form_goal 
 “!a1:fun0 a2:fun0.
   dfun1(a1) = 10 & dfun2(a1) = ETCS0 &
   dfun1(a2) = 10 & dfun2(a2) = ETCS0 ==>
   (eob(a1) = eob(a2) <=> a1 = a2)”);


val cpsb0_def = translate (concl cpsb_def) |> rewr_rule[cpsb_def];


val dar1_dom0 = proved_th $
e0
(strip_tac >>
 qsuff_tac ‘dar1(ear(cfun(f))) = eob(dom0(cfun(ear(cfun(f)))))’ 
 >-- rw[ear_of_cfun] >>
 qspecl_then [‘cfun(f)’] assume_tac dar12_ear >>
 fs[dfun12_cfun] >> rw[ear_of_cfun])
(form_goal “!f:ar0. dar1(f) = eob(dom0(cfun(f)))”)


val dar2_cod0 = proved_th $
e0
(strip_tac >>
 qsuff_tac ‘dar2(ear(cfun(f))) = eob(cod0(cfun(ear(cfun(f)))))’ 
 >-- rw[ear_of_cfun] >>
 qspecl_then [‘cfun(f)’] assume_tac dar12_ear >>
 fs[dfun12_cfun] >> rw[ear_of_cfun])
(form_goal “!f:ar0. dar2(f) = eob(cod0(cfun(f)))”)


val dfun12_dom0 = mk_dfsym_ax "dom" |> gen_all;
val dfun12_cod0 = mk_dfsym_ax "cod" |> gen_all;



val cpsb0_cfun = proved_th $
e0
(rpt strip_tac >>
 qspecl_then [‘f’] assume_tac dfun12_cfun >>
 drule cpsb0_def >>
 qspecl_then [‘g’] assume_tac dfun12_cfun >>
 first_x_assum drule >> arw[] >>
 rw[dar1_dom0,dar2_cod0] >> irule eob_eq_eq >>
 qspecl_then [‘ETCS0’,‘cfun(g)’] assume_tac dfun12_dom0 >> 
 qspecl_then [‘ETCS0’,‘cfun(f)’] assume_tac dfun12_cod0 >> rfs[])
(form_goal “!f:ar0 g:ar0. dar1(g) = dar2(f) <=> 
 cpsb0(cfun(g),cfun(f))”)


val cfun_eo0 = store_ax("cfun_eo0",“!f g:ar0. dar1(g) = dar2(f) ==>
 cfun(eo0(g,f)) = oa0(cfun(g),cfun(f))”)

val oa0_cfun = proved_th $
e0
(rpt strip_tac >> flip_tac >> irule cfun_eo0 >> arw[])
(form_goal
 “!f g:ar0. dar1(g) = dar2(f) ==>
 oa0(cfun(g),cfun(f)) = cfun(eo0(g,f))”)

val dfsym_oa0 = mk_dfsym_ax "oa";

val eo0_ear_cfun_oa0 = proved_th $
e0
(rpt strip_tac >>
 qsuff_tac ‘cfun(eo0(ear(g),ear(f))) = cfun(ear(oa0(g,f)))’ 
 >-- rw[cfun_eq_eq] >>
 qspecl_then [‘ear(f)’,‘ear(g)’] assume_tac cfun_eo0 >>
 fs[cpsb0_cfun] >>
 qby_tac 
 ‘cfun(ear(g)) = g’ >-- (irule cfun_of_ear >> arw[]) >>
 qby_tac 
 ‘cfun(ear(f)) = f’ >-- (irule cfun_of_ear >> arw[]) >>
 fs[] >> rfs[] >>
 flip_tac >>
 irule cfun_of_ear >>
 irule dfsym_oa0 >> arw[])
(form_goal “!f:fun0. dfun1(f) = 20 & dfun2(f) = ETCS0 ==>
 !g:fun0. dfun1(g) = 20 & dfun2(g) = ETCS0 ==>
 cpsb0(g,f) ==>
 eo0(ear(g),ear(f)) = ear(oa0(g,f))”)

val cfun_I0 = store_ax("cfun_I0",“!A:ob0. cfun(I0(A)) = id0(cob(A)) ”)

val cfun_eq_eq = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qspecl_then [‘f1’] assume_tac ear_of_cfun>> 
 qspecl_then [‘f2’] assume_tac ear_of_cfun>> rfs[])
(form_goal “!f1:ar0 f2. cfun(f1) = cfun(f2) <=> f1 = f2 ”)

val I0_ear_id0_cob = proved_th $
e0
(rpt strip_tac >>
 irule $ iffLR cfun_eq_eq >> rw[cfun_I0] >>
 flip_tac >>
 irule cfun_of_ear >> rw[GSYM cfun_I0,dfun12_cfun])
(form_goal “!A:ob0. I0(A) = ear(id0(cob(A)))”)



val dom0_cfun = proved_th $
e0
(rpt strip_tac >>
 irule $ iffLR eob_eq_eq >> 
 rw[dfun12_cob] >>
 qby_tac ‘ dfun1(dom0(cfun(f))) = 10 &
             dfun2(dom0(cfun(f))) = ETCS0 ’ 
 >-- (irule dfun12_dom0>> rw[dfun12_cfun]) >> arw[] >>
 rw[GSYM dar1_dom0]>> rw[eob_of_cob] )
(form_goal “!f:ar0. dom0(cfun(f)) = cob(dar1(f))”)

val dom0_cob = proved_th $
e0
(rpt strip_tac >>
 qspecl_then [‘f’] assume_tac cfun_of_ear  >> rfs[] >>
 qspecl_then [‘ear(f)’] assume_tac dom0_cfun >>
 rfs[])
(form_goal “!f:fun0. dfun1(f) = 20 & dfun2(f) = ETCS0 ==> 
 dom0(f) = cob(dar1(ear(f)))”)

val eiso0_ciso0 = proved_th $
e0
(rpt strip_tac >>
 qabbrev_tac ‘dar1(f) = A’ >>
 qabbrev_tac ‘dar2(f) = B’ >> 
 qspecl_then [‘A’,‘B’,‘f’] assume_tac eiso0_def >> rfs[] >>
 qspecl_then [‘ETCS0’,‘cfun(f)’] assume_tac ciso0_def >>
 fs[dfun12_cfun] >>  
 dimp_tac >> strip_tac (* 2 *)
 >-- (qexists_tac ‘cfun(g)’ >>
     rw[dfun12_cfun] >> arw[GSYM cpsb0_cfun] >>
     qspecl_then [‘g’,‘f’] assume_tac oa0_cfun >>
     rfs[] >>
     qspecl_then [‘f’,‘g’] assume_tac oa0_cfun >> rfs[] >>
     rw[cfun_I0] >> 
     qsuff_tac
     ‘cob(B) = dom0(cfun(g)) & cob(A) = dom0(cfun(f))’ 
     >-- (strip_tac >> arw[]) >> rw[dom0_cfun] >> arw[]) >>
 qexists_tac ‘ear(g)’ >>
 qby_tac ‘dar1(ear(g)) = B & dar2(ear(g)) = A’ 
 >-- (qspecl_then [‘g’] assume_tac dar12_ear >>
     rfs[] >> 
     qspecl_then [‘g’] assume_tac cfun_of_ear >> rfs[] >>
     qby_tac ‘cpsb0(cfun(f), cfun(ear(g)))’ 
     >-- arw[] >> 
     fs[GSYM cpsb0_cfun] >> 
     qby_tac ‘cpsb0(cfun(ear(g)), cfun(f))’ 
     >-- arw[] >>
     fs[GSYM cpsb0_cfun]) >> arw[] >>
 strip_tac (* 2 *)
 >-- (irule $ iffLR cfun_eq_eq >> rw[I0_id0] >>
     qspecl_then [‘f’,‘ear(g)’] assume_tac cfun_eo0 >>
     rfs[] >> 
     qspecl_then [‘g’] assume_tac cfun_of_ear >> rfs[] >>
     rw[dom0_cfun] >> arw[]) >>
 irule $ iffLR cfun_eq_eq >> rw[I0_id0] >>
 qspecl_then [‘ear(g)’,‘f’] assume_tac cfun_eo0 >>
 rfs[] >> 
 qspecl_then [‘g’] assume_tac cfun_of_ear >> rfs[] >>
 qsuff_tac ‘dom0(g) = cob(B)’ 
 >-- (strip_tac >> arw[]) >>
 qsuff_tac ‘dom0(g) = cob(dar1(ear(g)))’
 >-- arw[] >>
 irule dom0_cob >> arw[])
(form_goal
 “!f:ar0. eiso0(f) <=> ciso0(cfun(f))”)

val ear_eq_eq = proved_th $
e0
(rpt strip_tac >> dimp_tac >> strip_tac >> arw[] >>
 qby_tac ‘cfun(ear(f1)) = cfun(ear(f2))’ >-- fs[] >>
 qsuff_tac ‘cfun(ear(f1)) = f1 & cfun(ear(f2)) = f2’
 >-- (strip_tac >> fs[]) >>
 strip_tac (* 2 *)
 >> irule cfun_of_ear >> arw[])
(form_goal 
 “!f1 f2:fun0. dfun1(f1) = 20 & dfun2(f1) = ETCS0 & 
               dfun1(f2) = 20 & dfun2(f2) = ETCS0 ==>
   (ear(f1) = ear(f2) <=> f1 = f2)”)

val emono0_cmono0 = proved_th $
e0
(rpt strip_tac >> 
 qabbrev_tac ‘dar1(f) = A’ >>
 qabbrev_tac ‘dar2(f) = B’ >> 
 qspecl_then [‘A’,‘B’,‘f’] assume_tac emono0_def >> rfs[] >> 
 qspecl_then [‘ETCS0’,‘cfun(f)’] assume_tac cmono0_def >> 
 fs[dfun12_cfun] >>
 dimp_tac >> strip_tac (* 2 *)
 >-- (rpt strip_tac >> 
     irule $ iffLR ear_eq_eq >> arw[] >>
     qabbrev_tac ‘eob(dom0(g2)) = X’ >>
     first_x_assum
      (qspecl_then [‘X’,‘ear(g1)’] assume_tac) >>
     qby_tac ‘dar1(ear(g1)) = X & dar2(ear(g1)) = A’ 
     >-- (qspecl_then [‘g1’] assume_tac dar12_ear >>
         qby_tac ‘cfun(ear(g1)) = g1’ 
         >-- (irule cfun_of_ear >> arw[]) >> rfs[] >>
         qspecl_then [‘ear(g1)’,‘f’] assume_tac cpsb0_cfun >>
         rfs[]) >> 
     first_x_assum drule >>
     first_x_assum
      (qspecl_then [‘ear(g2)’] assume_tac) >>
     qby_tac ‘dar1(ear(g2)) = X & dar2(ear(g2)) = A’ 
     >-- (qspecl_then [‘g2’] assume_tac dar12_ear >>
         qby_tac ‘cfun(ear(g2)) = g2’ 
         >-- (irule cfun_of_ear >> arw[]) >> rfs[] >>
         qspecl_then [‘ear(g2)’,‘f’] assume_tac cpsb0_cfun >>
         rfs[]) >>
     first_x_assum drule >>
     first_x_assum irule >> irule $ iffLR cfun_eq_eq >>
     qspecl_then [‘ear(g1)’,‘f’] assume_tac oa0_cfun >>
     qby_tac ‘cfun(ear(g1)) = g1’ 
     >-- (irule cfun_of_ear >> arw[]) >> fs[] >> 
     qspecl_then [‘ear(g2)’,‘f’] assume_tac oa0_cfun >>
     qby_tac ‘cfun(ear(g2)) = g2’ 
     >-- (irule cfun_of_ear >> arw[]) >> fs[] >>  
     rfs[]) >>
 rpt strip_tac >>
 irule $ iffLR cfun_eq_eq >>
 first_x_assum (qspecl_then [‘cfun(g)’] assume_tac)>>
 fs[dfun12_cfun] >>
 first_x_assum (qspecl_then [‘cfun(h)’] assume_tac)>>
 fs[dfun12_cfun]>>
 first_x_assum irule >>
 rw[GSYM cpsb0_cfun] >> arw[] >>
 arw[dom0_cfun] >>
 qspecl_then [‘g’,‘f’] assume_tac oa0_cfun >>
 qspecl_then [‘h’,‘f’] assume_tac oa0_cfun >> 
 rfs[])
(form_goal
 “!f:ar0. emono0(f) <=> cmono0(cfun(f))”)

val to_be_proved = proved_th $
e0
(rpt strip_tac >> fs[eiso0_ciso0] >>
 qspecl_then [‘ETCS0’,‘cfun(f)’] assume_tac iso_is_mono0 >>
 fs[dfun12_cfun] >> rfs[] >> arw[emono0_cmono0])
(form_goal “!A:ob0 B:ob0 f:ar0. dar1(f) = A & dar2(f) = B ==>
 eiso0(f) ==> emono0(f)”)

