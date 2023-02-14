

val Les_def = 
IN_def_P |> qspecl [‘N’] 
         |> fVar_sInst_th “P(a:mem(N))”
            “Le(a,n)”
            |> qsimple_uex_spec "Les" [‘n’]

val Les_def = Les_def |> gen_all

val Iso_def = qdefine_psym("Iso",[‘i:X->Y’])
‘?j:Y->X. j o i = Id(X) & i o j = Id(Y)’

val Upows_def = qdefine_psym("Upows",[‘n:mem(N)’,‘p:X->N’,‘R:X~>X’,‘z:N->X’])
‘IMAGE(p,Whole(X)) = Les(n) &  
 Iso(z) & 
 IMAGE(z,Whole(N)) = FIB(p,O) & 
 !n0. Lt(n0,n) ==>
      ?A i:A->X pi:Pow(A) -> X. 
        Inj(i) & Inj(pi) & 
        IMAGE(i,Whole(A)) = FIB(p,n0) &  
        IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0))& 
        !a:mem(A) s. IN(a,s) <=>
          Holds(R,App(i,a),App(pi,s))’



(*
val Upows_def = proved_th $
e0
cheat
(form_goal
 “!n X p:X->N z:N->X R:X~>X.
  Upows(n,p,R,z) <=> 
  IMAGE(p,Whole(X)) = Les(n) &  
 Iso(z) & 
 IMAGE(z,Whole(N)) = FIB(p,O) & 
 !n0. Lt(n0,n) ==>
      ?A i:A->X pi:Pow(A) -> X. 
        Inj(i) & Inj(pi) & 
        IMAGE(i,Whole(A)) = FIB(p,n0) &  
        IMAGE(pi,Whole(Pow(A))) = FIB(p,Suc(n0))& 
        !a:mem(A) s. IN(a,s) <=>
          Holds(R,App(i,a),App(pi,s))”)
*)

val Les_O_Sing = prove_store("Les_O_Sing",
e0
(irule IN_EXT >> rw[IN_Sing,Les_def] >>
 rw[Le_O_iff])
(form_goal “Les(O) = Sing(O)”));

val REmpty_def = 
AX1 |> qspecl [‘A’,‘A’] 
    |> fVar_sInst_th “P(a:mem(A),b:mem(A))”
       “F” 
    |> rewr_rule[] 
    |> qsimple_uex_spec "REmpty" [‘A’]
    |> gen_all


(*(?(a : mem(A)). IN(a#, s) & x' = x)
TODO: a conv for this

*)
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


val Iso_Id = prove_store("Iso_Id",
e0
(rw[Iso_def] >> rpt strip_tac >>
 qexists_tac ‘Id(A)’ >> rw[IdL,IdR])
(form_goal “!A. Iso(Id(A))”));
 
val IMAGE_Id = prove_store("IMAGE_Id",
e0
(cheat)
(form_goal “!A s. IMAGE(Id(A),s) = s”));

(*
val IMAGE_Whole_constf = prove_store("IMAGE_Whole_constf",
e0
cheat
(form_goal “”));
*)

val Upows_O = prove_store("Upows_O",
e0
(rw[Upows_def,Iso_Id,FIB_constf,
    IMAGE_Id,Les_O_Sing] >>  
 qby_tac ‘IMAGE(constf(N, O), Whole(N)) = Sing(O)’
 >-- (irule IMAGE_constf >>
     rw[GSYM IN_EXT_iff,Whole_def,Empty_def] >>
     ccontra_tac >> 
     first_x_assum (qspecl_then [‘O’] assume_tac) >>
     fs[]) >> arw[] >>
 rw[NOT_Lt_O])
(form_goal “Upows(O,constf(N,O),REmpty(N),Id(N))”));

rpt gen_tac >> strip_tac >>
ind_with N_induct >>
rw[O_LESS_EQ,Le_O_iff] >> 
“!n X p:X->N z:N->X R:X~>X.
  Upows(n,p,R,z) ==> 
  !n0. Le(n0,n) ==> 
  !X0 i:X0 -> X p0:X0->N z0:N->X0 R0:X0~>X0. 
   Inj(i) & 
   (!x. Le(App(p,x),n0) ==> ?x0. App(i,x0) = x) &
   p o i = p0 & z = i o z0 & 
   (!x0 s0. Holds(R0,x0,s0) <=> 
            Holds(R,App(i,x0),App(i,s0))) ==>
  Upows(n0,p,R,z)”


p(x) = O <=> ?n. x = App(z,n)
val Upows_nPow = prove_store("Upows_nPow",
e0
(ind_with N_induct >>
 rpt strip_tac (* 2 *)
 >-- drule Le_O >> arw[] >> 
     qsuff_tac ‘cardeq(FIB(p, O), Whole(Pn(N, O)))’ 
     >-- cheat >>
     cheat >>

 )
(form_goal
 “!n X p:X->N z:N->X R:X~>X.
  Upows(n,p,R,z) ==> 
  !n0. Le(n0,n) ==> 
  cardeq(FIB(p,n0),Whole(Pn(N,n0)))”));




val from1_def= qdefine_fsym("from1",[‘a:mem(A)’,‘B’])
‘App(i1(A,B),a)’ |> gen_all


val from2_def= qdefine_fsym("from2",[‘A’,‘b:mem(B)’])
‘App(i2(A,B),b)’ |> gen_all

val Surj_Image_Surj = prove_store("Surj_Image_Surj",
e0
()
());


val Bij_Image_Bij = prove_store("Bij_Image_Bij",
e0
()
(form_goal “”));

val Inj_Pow_uex_lemma = prove_store
("Inj_Pow_uex_lemma",
e0
(rpt strip_tac >> dimp_tac >> rpt strip_tac >>
 arw[] 
 >-- irule $ iffLR FUN_EXT >>
     rw[Image_IMAGE,GSYM IN_EXT_iff,IMAGE_def] >>
     arw[] >> rpt strip_tac >>
     dimp_tac >> strip_tac (* 2 *)
     >-- 

 
 P2fun |> qspecl [‘Pow(X)’,‘Pow(A)’]
 |> fVar_sInst_th “R(sx:mem(Pow(X)),sa:mem(Pow(A)))”
    “”
 )
(form_goal
 “!X A i:X->A. Bij(i) ==>
  !f:Pow(X) -> Pow(A). 
   (Inj(f) & 
   (!a:mem(A) sa:mem(Pow(A)).
    IN(a,sa) <=> )
   (!x s. IN(x,s) <=> IN(App(i,x),App(f,s)))) <=> 
   f = Image(i)”));
(*this fun is image*)


val Upows_O = prove_store("Upows_O",
e0
(rw[Upows_def,Iso_Id,FIB_constf,
    IMAGE_Id,Les_O_Sing] >>  
 qby_tac ‘IMAGE(constf(N, O), Whole(N)) = Sing(O)’
 >-- (irule IMAGE_constf >>
     rw[GSYM IN_EXT_iff,Whole_def,Empty_def] >>
     ccontra_tac >> 
     first_x_assum (qspecl_then [‘O’] assume_tac) >>
     fs[]) >> arw[] >>
 rw[NOT_Lt_O])
(form_goal 
 “!n X0 p0:X0->N z0:N->X0 R0:X0~>X0.
    Upows(n,p0,R0,z0)  ==>
     !pnN i:pnN -> X0. 
      Inj(i) & IMAGE(i,Whole(pnN)) = FIB(p0,n) ==>
      !R:X0 + Pow(Pn) ~> X0 + Pow(pnN).
      (!x s. Holds(R,from1(x,Pow(Pn)),
                     from1(s,Pow(Pn))) <=> 
             Holds(R0,x,s)) & 
      (!x s. Holds(R,from1(x,Pow(Pn)),
                     from2(X0,s)) <=>
             IN()
            )
      Upows(Suc(n),coPa(p0,constf(pnN,Suc(n))),
                  ,i1(X0,pnN) o z0)
    !X p:X->N z:N->X R:X~>X. 
    
    ==> Upows(Suc(n),p,R,z)
    

”));




val Upows_unique = proved_th $
e0
(ind_with N_induct >>
 strip_tac (* 2 *)
 >-- rpt strip_tac >>
     fs[Upows_def] >> fs[NOT_Lt_O,Les_O_Sing] >> 
     cheat >>
 rpt strip_tac >>  
 
 
     )
(form_goal
 “!n. 
   !X1 p1:X1->N z1:N->X1 R1:X1~>X1
    X2 p2:X2->N z2:N->X2 R2:X2~>X2. 
   Upows(n,p1,R1,z1) & Upows(n,p2,R2,z2) ==>
   ?!iso: X1->X2. 
     Bij(iso) & p2 o iso = p1 & iso o z1 = z2 & 
     !a b. Holds(R1,a,b) <=> 
         Holds(R2,App(iso,a),App(iso,b))” )

val replacement0 = proved_th $
e0
cheat
(form_goal
 “!U.
    (!u:mem(U).
      ?X p:X->U r:X * X -> 1+1 z: U ->X. 
       phi(U,u,X,p,r,z) & 
      !X' p':X'->U r':X' * X'->1+1 z':U->X'. 
       phi(U,u,X',p',r',z') ==>
      ?!i:X->X'. 
        iso(i) & p' o i = p &
        r' o Prla(i,i) = r & i o z = z')”)

replacement0 |> qspecl [‘N’] 
|> fVar_sInst_th 
   “phi(X,u:1->N, X,p:X->N, r:X * X->2, z:U->X)”
    “T”
