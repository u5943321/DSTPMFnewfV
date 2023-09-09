val Listn_def =
    Thm_2_4' |> qtinst_thm [(‘A’,‘List(A)’)]
             |> qfVar_prpl_th1 
             ("P",[‘l:mem(List(A))’],
              ‘Length(l:mem(List(A))) = n’)     
             |> set_spec (rastt "List(A)") "Listn" "iLn" [("A",set_sort),("n",mem_sort (rastt "N"))]
             |> gen_all


(*1.can pick a base point, and use inverse *)
(*2.can directly prove unique existence, since existence of list items implies existence of term*)

val RepLn_def = qdefine_fsym ("RepLn",[‘ln:mem(Listn(A,n:mem(N)))’])
                            ‘App(iLn(A,n),ln)’
                            |> gen_all |> store_as "RepLn_def";




val LnNil_def = proved_th $
e0
(strip_tac >> uex_tac >>
 qspecl_then [‘A’] strip_assume_tac Listn_def >>
 first_assum (qspecl_then [‘O’] strip_assume_tac) >>
 first_assum (qspecl_then [‘Nil(A)’] assume_tac) >>
 fs[Length_Nil] >>
 qexists_tac ‘b’ >> arw[RepLn_def] >>
 fs[Inj_def])
(form_goal “!A. ?!ln:mem(Listn(A,O)).RepLn(ln) = Nil(A)”)
|> spec_all |> qsimple_uex_spec "LnNil" [‘A’] |> gen_all
|> store_as "LnNil_def";



(*
val om0_def = qfun_compr ‘f:mem(Exp(A,B))’ ‘Tpm((f0:B->C) o tof(f))’
                               |>  qsimple_uex_spec "om0" [‘f0’,‘A’] |> gen_all
*)


val CONSe_def =  qfun_compr ‘l:mem(List(A))’ ‘Cons(a,l)’
                               |>  qsimple_uex_spec "CONSe" [‘a:mem(A)’] |> gen_all

val aprecf_def = 
qfun_compr ‘af:mem(A * Exp(List(A),List(A)))’ 
‘Tpm(CONSe(Fst(af)) o tof(Snd(af)))’
|> qsimple_uex_spec "aprecf" [‘A’] |> gen_all


val APPEND0_def = qdefine_fsym ("APPEND0",[‘A’]) ‘Lrec(Tpm(Id(List(A))),aprecf(A))’ |> gen_all

val Append_def = 
qdefine_fsym ("Append",[‘l1:mem(List(A))’,‘l2:mem(List(A))’])
                            ‘App(tof(App(APPEND0(A),l1)),l2)’
                            |> gen_all |> store_as "Append_def";


val Length_RepLn = proved_th $
e0
(rpt strip_tac >>
 qspecl_then [‘A’,‘n’,‘l’] assume_tac RepLn_def >>
 arw[] >>
 qspecl_then [‘A’,‘n’] strip_assume_tac Listn_def >>
 arw[] >> qexists_tac ‘l’ >> rw[])
(form_goal “!A n l:mem(Listn(A,n)). Length(RepLn(l)) = n”)

val RepLn_Listn_LENGTH_eq = proved_th $
e0
(rpt strip_tac >> 
 qby_tac ‘Length(RepLn(l1)) =Length(RepLn(l2))’  
 >-- arw[] >>
 fs[Length_RepLn])
(form_goal “!A n1 n2 l1:mem(Listn(A,n1)) l2:mem(Listn(A,n2)). RepLn(l1) = RepLn(l2) ==> n1 = n2”)

val APPEND_def = 
    qfun_compr ‘l1l2:mem(List(A) * List(A))’
                        ‘Append(Fst(l1l2),Snd(l1l2))’ 
     |> qsimple_uex_spec "APPEND" [‘l1l2 :mem(List(A) * List(A))’,‘A’]
     |> gen_all


val APPEND0_Nil = proved_th $
e0
(rw[APPEND0_def,Lrec_Nil])
(form_goal “App(APPEND0(A),Nil(A)) = Tpm(Id(List(A)))”)


val APPEND0_Cons = proved_th $
e0
(rw[APPEND0_def,Lrec_Cons,aprecf_def,Pair_def'])
(form_goal “App(APPEND0(A),Cons(h,t)) = 
 Tpm(CONSe(h) o tof(App(APPEND0(A),t)))”)



val Append_Nil = proved_th $
e0
(rw[Append_def,APPEND0_Nil,tof_Tpm_inv,App_Id])
(form_goal “Append(Nil(X),l) = l”)

val Append_Cons = proved_th $
e0
(rw[Append_def,APPEND0_Cons,tof_Tpm_inv,App_App_o,CONSe_def])
(form_goal “Append(Cons(h:mem(X),t),l) = Cons(h, Append(t,l))”)




(*ind_with need name to be X, lame...*)
val Length_Append = proved_th $
e0
(ind_with List_induct >> rpt strip_tac (* 2 *)
 >-- (rw[Length_Nil,Add_O2,Append_Nil]) >>
 arw[Append_Cons,Length_Cons,Add_Suc1]
 )
(form_goal
 “!l1:mem(List(X)) l2. Length(Append(l1,l2)) = Add(Length(l1),Length(l2))”)

val RepLn_eq_eq = proved_th $
e0
(rpt strip_tac >>
  qspecl_then [‘A’,‘n’] strip_assume_tac Listn_def >> 
  fs[Inj_def,RepLn_def] >>
  first_assum irule >> arw[])
(form_goal “!A n l1:mem(Listn(A,n)) l2. RepLn(l1) = RepLn(l2) ==> l1 = l2”)



val Appendn_ex = proved_th $
e0
(rpt strip_tac >>
 uex_tac >>
 qspecl_then [‘A’,‘Add(n1,n2)’] strip_assume_tac Listn_def >>
 first_x_assum $ qspecl_then [‘Append(RepLn(l1),RepLn(l2))’] assume_tac >>
 fs[Length_Append,Length_RepLn] >>
 qexists_tac ‘b’ >> rw[RepLn_def] >>
 rpt strip_tac >>
 irule RepLn_eq_eq >> arw[RepLn_def])
(form_goal 
“!A n1:mem(N) l1:mem(Listn(A,n1)) n2:mem(N) l2:mem(Listn(A,n2)). 
?!l1l2:mem(Listn(A, Add(n1,n2))). 
 Append(RepLn(l1),RepLn(l2)) = RepLn(l1l2)”)


val Appendn_def = 
Appendn_ex
|> spec_all
|> qsimple_uex_spec "Appendn" [‘l1’,‘l2’] |> gen_all


(*
val Lnabs_def = 
Abs maps a list to Listn(A,Length(l)).



val Length_Cons = prove_store("Length_Cons",
e0
(rw[Length_def,LENGTH_def,Lrec_Cons,App_App_o,p12_of_Pair,
    Suc_def])
(form_goal
“!A l1:mem(Listn(A,n)) l2:mem(Listn(A,m)). 
 ?!l12:mem(Listn(A,n+m)). RepLn(l1) 
 Abs”));
*)
