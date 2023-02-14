

fun translates s = 
    let val s0 = #1 (dest_sort s) 
        val _ = new_sort (s0^"0") []
        val _ = EqSorts := (s0^"0") :: (!EqSorts)
    in mk_sort (s0^"0") []
    end


fun trfsym f = 
    let val (output,inputs) = 
            case lookup_fun (!fsyms) f of 
                SOME (s,vl)  => (s,vl)
              | _ =>  raise simple_fail ("trfsym.not a function: "^f)
        val _ = new_fun (f^"0") (translates output,
                        List.map (fn (n,s) => (n,translates s)) inputs)
    in ()
    end

(*
val t = (rastt "(f:B->C) o (g:A->B)")

dest_fun t
val (f,s,tl) = it
*)

fun translatet tm = 
    case view_term tm of 
        vVar(n,s) => mk_var(n,translates s)
      | vFun(f,s,tl) => 
        let val _ = trfsym f
            val f0 = f^"0"
        in mk_fun f0 (List.map translatet tl)
        end


fun label_list l = 
    case l of [] => []
            | h :: t => 
              let val l0 = label_list t 
                  val l1 = List.map (fn (n,a) => (n + 1,a)) l0
              in (1,h) :: l1
              end

fun numlist n = 
    case n of 0 => []
            | _ => List.rev (n :: (List.rev (numlist (n - 1))))

(*
val t = rastt "f:A->B";
val tt = translatet t;
*)



(*trfsym "dom" 
rastt "dom0(a)" *)

fun create_ds s = 
    let val dts =
            case Binarymap.peek(!SortDB,s) of
                SOME pair => pair
              | _ => raise simple_fail ("create_ds.not a sort: "^ s)
        val dfnames = List.map (fn n => "d"^ s ^ (Int.toString n))
                               (numlist (length dts))
        val dfsorts = List.map (translates o #2) dts
        val tocreate = zip dfnames dfsorts
        val sv0 = (s^"genvar",mk_sort (s^"0") [])
        val create = List.map 
                         (fn (dfname,dfsort) => new_fun dfname (dfsort,[sv0]))
                         tocreate
    in ()
    end

(*rastt "dfun1(a)" *)


(*val (n,s) = ("f",ar(A,B)) *)

fun vceq (n,s) = 
    let val dtl = List.map translatet (#2 (dest_sort s))
        val sn = #1 (dest_sort s)
        val dfnames = List.map (fn n => "d"^ sn ^ (Int.toString n))
                               (numlist (length dtl))
        val pairl = zip dfnames dtl 
        val n0 = translatet (mk_var(n,s))
        val eql = List.map (fn (fname,t) => mk_eq (mk_fun fname [n0]) t) pairl
    in mk_conjl eql
       handle _ => TRUE
    end



fun ceq t = 
    let val s = sort_of t
        val sn = s |> dest_sort |> #1
        val dtl = List.map translatet (#2 (dest_sort s))
        val dfnames = List.map (fn n => "d"^ sn ^ (Int.toString n))
                               (numlist (length dtl))
        val pairl = zip dfnames dtl 
        val n0 = translatet t
        val eql = List.map (fn (fname,t) => mk_eq (mk_fun fname [n0]) t) pairl
    in mk_conjl eql        
       handle _ => TRUE
    end


(*ceqs (rastt "(f:B->C) o (g:A->B)") *)
fun mk_dfsym_ax f = 
    let val (output,inputs) = 
            case lookup_fun (!fsyms) f of 
                SOME (s,vl)  => (s,vl)
              | _ =>  raise simple_fail ("trfsym.not a function: "^f)
        val ft = mk_fun f (List.map mk_var inputs)
        val inputvars0 = List.map (translatet o mk_var) inputs
        val outputt0 = mk_fun (f^"0") inputvars0
        (*should outputt0 be translatet instead?*)
        val inputvceqs = List.map vceq inputs 
        val ante = mk_conjl inputvceqs handle _ => TRUE
        val concl = ceq ft
        val thf = mk_imp ante concl 
    in mk_thm(fvf thf,[],thf)
    end


(*should translation of P take precondition as well?*)
fun trpsym P = 
    let val inputs = 
            case lookup_pred (!psyms) P of 
                SOME tl => tl
              | _ =>  raise simple_fail ("trpsym.not a predicate: "^P)
    in new_pred (P^"0") (List.map (fn (n,s) => (n,translates s)) inputs)
    end

(*trpsym "isEq" *)

(*
val fm = “!f:ar(A:ob,B:ob).T”    

val ((n,s),b) = dest_forall fm ;

val (n,s) = 
*)
                      
fun translatef fm = 
    case view_form fm of
        vQ(q,n,s,b) =>
        let 
            val ceq = vceq (n,s)
            val tb = translatef b
        in if q = "!" then mk_forall n (translates s) (mk_imp ceq tb) else
           if q = "?" then mk_exists n (translates s) (mk_conj ceq tb) else
           if q = "?!" then mk_uex n (translates s) (mk_conj ceq tb) else
           raise simple_fail ("translatef.not a quantifier: "^ q)
        end
      | vConn(co,fl) => mk_conn co (List.map translatef fl)
      | vPred(P,false,tl) => mk_fvar P (List.map translatet tl)
      | vPred("=",true,[t1,t2]) => mk_eq (translatet t1) (translatet t2)
      | vPred("T",true,[]) => TRUE
      | vPred("F",true,[]) => FALSE
      | vPred(P,true,tl) => 
        let val _ = trpsym P in
            mk_pred (P^"0") (List.map translatet tl)
        end


fun translate f = 
    if HOLset.equal(fvf f,essps) then
        mk_thm (essps,[],mk_dimp f (translatef f))
    else raise ERR("translate.input has free variables",[],[],[f])





val fun0_sort = mk_sort "fun0" [];
val cat0_sort = mk_sort "cat0" [];
val ob0_sort = mk_sort "ob0" [];
val ar0_sort = mk_sort "ar0" [];
(*every monomorphism is an injection*)
val _ = new_fun "eob" (ob0_sort,[("s",fun0_sort)])
val _ = new_fun "cob" (fun0_sort,[("s",ob0_sort)])

val _ = new_fun "ETCS0" (mk_sort "cat0" [],[]:  (string * sort) list)

(*trivial example: every iso within a category is a mono, so every isomorphism is injective on elements *)

val mono_def = qdefine_psym("mono",[‘f:2->A’])
‘!g1 g2:2->A. 
 dom(g1) = dom(g2) & cpsb(f,g1) & cpsb(f,g2) & 
 f @ g1 = f @ g2 ==> g1 = g2’ |> gen_all

val iso_is_mono = proved_th $
e0
cheat
(form_goal “!C f:2->C. iso(f) ==> mono(f)”);


val iso_is_mono0 =
translate ((#3 o dest_thm) iso_is_mono) |> rewr_rule[iso_is_mono]

          
val iso_is_mono0_ETCS0 = 
iso_is_mono0 |> qspecl [‘ETCS0’]

val _ = new_fun "eob" (ob0_sort,[("s",fun0_sort)])
val _ = new_fun "cob" (fun0_sort,[("s",ob0_sort)])

val eob_of_cob = store_ax("eob_of_cob",
“!a:ob0. eob(cob(a)) = a”)

val cob_of_eob = store_ax("cob_of_eob",
“!a:fun0. dfun1(a) = 10 & dfun2(a) = ETCS0 ==> cob(eob(a)) = a”)


val dfun12_cob = store_ax("dfun12_cob",
“!a:ob0. dfun1(cob(a)) = 10 & dfun2(cob(a)) = ETCS0”);




val dfun12_fun = store_ax("dfun12_cob",
“!a:ob0. dfun1(cob(a)) = 10 & dfun2(cob(a)) = ETCS0”);

val _ = new_fun "ear" (ar0_sort,[("f",fun0_sort)])
val _ = new_fun "cfun" (fun0_sort,[("f",ar0_sort)])

val cfun_of_ear = store_ax("cfun_of_ear",
“!f:fun0. cfun(ear(f)) = f”);

val ear_of_cfun = store_ax("ear_of_cfun",
“!f:ar0. ear(cfun(f)) = f”);

val dfun12_cfun = store_ax("dfun12_cfun",
“!f:ar0. dfun1(cfun(f)) = 20 & dfun2(cfun(f)) = ETCS0”);

val dom0_def = translate (concl dom_def) |> rewr_rule[dom_def];
val cod0_def = translate (concl cod_def) |> rewr_rule[cod_def]

val dar12_ear = store_ax("dar12_ear",
“!f:fun0. dfun1(f) = 20 & dfun2(f) = ETCS0 ==>
  dar1(ear(f)) = eob(dom0(f)) & dar2(ear(f)) = eob(cod0(f))”);


(*

val cat_of_ETCS = 
store_ax("cat_of_ETCS",
“(!s:ob0. dfun1(cob(s)) = 10 & dfun2(cob(s)) = ETCS0) &
 (!A:ob0 B:ob0 f:ar0. 
  dar1(f) = A & dar2(f) = B ==>
  
  ”)
*)

val _ = new_sort "ob" [] 
val _ = new_sort "ar" [("A",mk_sort "ob" []),("B",mk_sort "ob" [])];
val _ = EqSorts := "ar" :: (!EqSorts);
val ob_sort = mk_sort "ob" [];
fun ar_sort A B = mk_sort "ar" [A,B];


fun mk_ob name = mk_var (name,ob_sort);
fun mk_ar name dom cod = mk_var (name,ar_sort dom cod);

val _ = new_fun "O" (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])],[("f",mk_sort "ar" [mk_var("B",mk_sort "ob" []),mk_var("C",mk_sort "ob" [])]),("g",mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("B",mk_sort "ob" [])])])

val (pname,ql)  = ("emono",[‘f: ar(A:ob,B:ob)’]);
val qf = ‘!X g:ar(X:ob,A) h. O(f,g) = O(f,h) ==> g = h’

val emono_def = qdefine_psym("emono",[‘f: ar(A:ob,B:ob)’])
‘!X:ob g:ar(X:ob,A:ob) h. O(f,g) = O(f,h) ==> g = h’
|> qgenl[‘A’,‘B’,‘f’] |> store_as "emono_def";

val emonof= “!f: ar(A:ob,B:ob). emono(f) <=> (!X:ob g:ar(X:ob,A:ob) h. O(f,g) = O(f,h) ==> g = h)”;
val emono_def = mk_thm(fvf emonof,[],emonof) |> gen_all
val emono0_def = translate (concl emono_def) |> rewr_rule[emono_def];


val _ = new_fun "I" 
       (mk_sort "ar" [mk_var("A",mk_sort "ob" []),mk_var("A",mk_sort "ob" [])],
        [("A",mk_sort "ob" [])])


val eiso_def = qdefine_psym("eiso",[‘f: ar(A:ob,B:ob)’])
‘?g:ar(B:ob,A:ob) h. O(g,f) = I(A) ==> O(f,g) = I(B)’
|> qgenl[‘A’,‘B’,‘f’] |> store_as "eiso_def";

val eisof= “!f. eiso(f) <=> ?g:ar(B:ob,A:ob) h. O(g,f:ar(A:ob,B:ob)) = I(A) ==> O(f,g) = I(B)”
val eiso_def = mk_thm(fvf eisof,[],eisof) |> gen_all

val desired = “!A:ob B:ob f:ar(A:ob,B:ob).eiso(f) ==> emono(f) ” 

val concl = #3 o dest_thm
val eiso0_def = translate (concl eiso_def) |> rewr_rule[eiso_def];


val _ = translates (s)

val _ = create_ds "ar"

translate desired |> rewr_rule[]

val eiso0_def = eiso_def

val mono0_def = translate (concl mono_def) |> rewr_rule[mono_def] ;
val iso0_def = translate (concl iso_def) |> rewr_rule[iso_def];

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


val o0_oa0 = store_ax("o0_oa0",“!f g:ar0. dar1(g) = dar2(f) ==>
 cfun(o0(g,f)) = @0(cfun(g),cfun(f))”)

(*
val oa0_def = define_fsym("oa0",[("g",fun0_sort),("f",fun0_sort)])
(mk_fun "@0" [rastt "g:fun0",rastt "f:fun0"])

cannot do this since define_fsym is defined in this way...
*)

val _ = new_fun "oa0" (fun0_sort,[("g",fun0_sort),("f",fun0_sort)])

(*translatef translate “!A B f:ar(A,B) g:ar(B,C). g o f = g o f” 
does not raise ERR AQ.
*)

val f = “!A B f:ar(A,B) X g:ar(B,C). g o f = g o f”

val oa0_def = store_ax("oa0_def",
mk_forall "f" fun0_sort $ mk_forall "g" fun0_sort $ (mk_eq (mk_fun "@0" [rastt "g:fun0",rastt "f:fun0"])
 (rastt "oa0(g,f)")) ) |> gen_all

(* lex "@0(cfun(f), cfun(g))" *)

val _ = new_fun "o" (ar_sort (rastt "A:ob") (rastt "C:ob"),[("g",ar_sort (mk_ob "B") (mk_ob "C")),("f",ar_sort (mk_ob "A") (mk_ob "B"))])

val o0_oa0 = store_ax("o0_oa0",
“!f g:ar0. dar1(g) = dar2(f) ==> cfun(o0(g,f)) = oa0(cfun(g),cfun(f))”)

val _ = new_fun "I" (ar_sort (mk_ob "A") (mk_ob "A"),
[("A",ob_sort)])

val _ = trfsym "I";
val _ = mk_dfsym_ax "I";
val I0_id0 = store_ax("I0_id0",“!A:ob0. cfun(I0(A)) = id0(cob(A))”)

val concl = #3 o dest_thm
val id0_def = translate (concl id_def)

val to_be_proved = proved_th $
e0
(assume_tac iso_is_mono0 >>
 first_x_assum (qspecl_then [‘ETCS0’] assume_tac) >>
 rpt gen_tac >> disch_tac >>
 drule emono0_def >> drule eiso0_def >>
 once_arw[] >>
 last_x_assum mp_tac >> strip_tac >>
 first_x_assum (qspecl_then [‘cfun(f)’] assume_tac) >>
 strip_tac >> 
 qby_tac ‘dfun1(cfun(f)) = 20 & dfun2(cfun(f)) = ETCS0’ 
 >-- rw[dfun12_cfun] >> 
 qby_tac ‘cpsb0(cfun(f),cfun(g))’ 
 >-- (rw[GSYM cpsb0_cfun] >> arw[]) >>
 qby_tac ‘cpsb0(cfun(g),cfun(f))’ 
 >-- (rw[GSYM cpsb0_cfun] >> arw[]) >>
 drule cpsb0_def >>
 qspecl_then [‘g’] assume_tac dfun12_cfun >>
 first_x_assum drule >> pop_assum (assume_tac o GSYM) >>
 drule cpsb0_def >> 
 first_x_assum (rev_drule) >> 
 pop_assum (assume_tac o GSYM) >>
 qby_tac ‘iso0(cfun(f))’ 
 >-- rev_drule iso0_def >> once_arw[] >>
     qexists_tac ‘cfun(g)’ >>
     rw[dfun12_cfun] >> arw[] >> rw[oa0_def] >>
     strip_tac (* 2 *)
     >-- 
     
     

 )
(form_goal “!A:ob0 B:ob0 f:ar0. dar1(f) = A & dar2(f) = B ==>
 eiso0(f) ==> emono0(f)”)

(*
translatet (rastt "(f:B->C) o (g:A->B)")


 “p:AB->A o fg:X->AB = p:AB->A o fg:X->AB”

 “isPr(p1:AB->A,p2:AB->B)”
*)



(*
val fm = (concl ZERO_prop)
val fm = concl isPr_def
*)


(*
translatef (concl Tp_def)
translatef “Ev(X, Y) o Pa(Id(X), f o To1(X)) = Tp0(f)”

problematic since Tp is translated to give a name Tp0
*)
(*
translatef (concl Tp1_def)
(concl Tp0_def)
*)
