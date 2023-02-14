
val repl_Upows0 = store_ax("repl_Upows0",
“!U u:mem(U).
 (?X p:X->U R:X~>X z:N->X. P(U,u,X,p,R,z) & 
 !X' p':X'->U R':X'~>X' z':N->X'. P(U,u,X',p',R',z') ==>
 ?!f:X->X'. p = p' o f & R' = Apr(f,R) & z' = f o z) ==>
 ?X Xf:X -> N pf:X -> N * N ”)


val repl_Upows0 = store_ax("repl_Upows0",
“!U u:mem(U).
 (?X p:X->U R:X~>X z:N->X. P(X,p,R,z) & 
 !X' p':X'->U R':X'~>X' z':N->X'. P(X',p',R',z') ==>
 ?!f:X->X'. p = p' o f & R' = Apr(f,R) & z' = f o z)”)

val f =                  
“(?X p:X->N R:X~>X z:N->X. P(X,p,R,z) & 
 !X' p':X'->N R':X'~>X' z':N->X'. P(X',p',R',z') ==>
 ?!f:X->X'. p = p' o f & R' = Apr(f,R) & z' = f o z)
”
val repl_Upows1  = repl_Upows0 |> qspecl [‘N’,‘n:mem(N)’]

repl_Upows1 |> fVar_sInst_th “P(X,p:X->N,R:X~>X,z:N->X)”
               “Upows(n,p:X->N,R:X~>X,z)”

val vl = “P(X,p:X->N,R:X~>X,z:N->X)” |> dest_fvar |> #2 
       |> List.map dest_var

fVar_Inst_f ("P",
             (vl,
               “Upows(n,p:X->N,R:X~>X,z)”))
            “?p R z.P(X,p:X->N,R:X~>X,z:N->X)”


fVar_Inst_f ("P",
             (vl,
               “Upows(n,p:X->N,R:X~>X,z)”))
            “?X p R z.P(X,p:X->N,R:X~>X,z:N->X)”

val pair = (vl,
               “Upows(n,p:X->N,R:X~>X,z)”)

mk_forall "B" set_sort $
fVar_Inst_f0 [set_sort] ("P",
             ([("X",set_sort),("Y",set_sort),("f",fun_sort (mk_set "X") (mk_set "Y"))],
               “Inj(f:X->Y)”))
            “!f.P(A,B,f:A->B)”



fun fVar_Inst_f0 bs (pair as (P,(argl:(string * sort) list,Q))) f = 
    let val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q) argl
    in
    case view_form f of
        vPred(P0,false,args0) => fVar_Inst_P bs pair f
      | Conn(co,[f1,f2]) => 
        (let val f1' = fVar_Inst_f0 bs pair f1
         in Conn(co,[f1',fVar_Inst_f0 bs pair f2])
            handle _ => Conn(co,[f1',f2])
         end 
         handle _ => Conn(co,[f1,fVar_Inst_f0 bs pair f2]))
      | Conn("~",[f1]) => 
        Conn("~",[fVar_Inst_f0 bs pair f1])
      | Pred(_,true,_) =>(* Should be just be f  *)raise ERR ("fVar_Inst_f0.Pred cannot be fVar insted",[],[],[f])
      | Quant(q,n,s,b) => Quant(q,n,s,fVar_Inst_f0 (s :: bs) pair b)
    end


fVar_Inst_f0 [] ("P",
             ([("X",set_sort),("Y",set_sort),("f",fun_sort (mk_set "X") (mk_set "Y"))],
               “Inj(f:X->Y)”))
            “!B f.P(A,B,f:A->B)”

fVar_Inst_f0 [] pair “!B g.P(A,B,g:A->B)”

val fb = mk_fvar "P"

val f = mk_forall "B" set_sort 
(mk_forall "f" (fun_sort (mk_set "A") (mk_set "B"))  
 (mk_fvar "P" [mk_set "A",mk_set "B",mk_func "f" (mk_set "A") (mk_set "B")]))


val bs = []:sort list;

val s = set_sort

val b = view_form f

view_form 


dest_forall 

view_form 
dest_forall (mk_forall "B" set_sort “!g:A->B.P(A,B,g)”)
(*
val (pair as (P,(argl:(string * sort) list,Q))) = 
("P",
             ([("X",set_sort),("Y",set_sort),("f",fun_sort (mk_set "X") (mk_set "Y"))], 
               “Q(X,Y,f:X->Y)”));

val ((n,s),b) = view_form f 
*)



val bs = []:sort list;

val (pair as (P,(argl:(string * sort) list,Q))) = 
("P",
             ([("X",set_sort),("Y",set_sort),("f",fun_sort (mk_set "X") (mk_set "Y"))], mk_fvar "Q" [mk_var("f",fun_sort (mk_set "X") (mk_set "Y"))])); (*also test with Q (a, b), with a b constants*)

val f = mk_forall "B" set_sort 
(mk_forall "f" (fun_sort (mk_set "A") (mk_set "B"))  
 (mk_fvar "P" [mk_set "A",mk_set "B",mk_func "f" (mk_set "A") (mk_set "B")]))

fVar_Inst_f pair f




val ((n,s),b) = dest_forall0 f 

fVar_Inst_f0 [recover_s 1 s] pair b

val ((n1,s1),b1) = dest_forall0 b

fVar_Inst_P [recover_s 1 s1,recover_s 1 s] pair b1


val (bs,pair,f) = ([recover_s 1 s1,recover_s 1 s], pair, b1) 

fVar_Inst_P bs pair f 

val (P0,args0) = dest_fvar f

pinst_f venv Q

val (vd,f) = (venv,Q)


not really use quant clause for pinst_f







val bs = []:sort list;

val (pair as (P,(argl:(string * sort) list,Q))) = 
("P",
             ([("X",set_sort),("Y",set_sort),("f",fun_sort (mk_set "X") (mk_set "Y"))],
 mk_forall "a" set_sort $ mk_fvar "Q" [mk_var("f",fun_sort (mk_set "X") (mk_set "Y"))])); (*also test with Q (a, b), with a b constants*)

val f = mk_forall "A" set_sort 
(mk_forall "B" set_sort 
(mk_forall "f" (fun_sort (mk_set "A") (mk_set "B"))  
 (mk_fvar "P" [mk_set "A",mk_set "B",mk_func "f" (mk_set "A") (mk_set "B")])))

fVar_Inst_f pair f









val args0 = [Var ("A", srt ("set", [])),Bound 1, Bound 0];






val _ = new_pred "Inj" [("f",fun_sort (mk_set "A") (mk_set "B"))]

val (pair as (P,(argl:(string * sort) list,Q))) = 
("P",
  ([("X",set_sort),("Y",set_sort),("f",fun_sort (mk_set "X") (mk_set "Y"))], 
    mk_pred "Inj" [mk_var("f",fun_sort (mk_set "X") (mk_set "Y"))])); 

val f = mk_forall "B" set_sort 
(mk_forall "f" (fun_sort (mk_set "A") (mk_set "B"))  
 (mk_fvar "P" [mk_set "A",mk_set "B",mk_func "f" (mk_set "A") (mk_set "B")]))


val ((n,s),b) = dest_forall0 f 

fVar_Inst_f0 [s] pair b

val ((n1,s1),b1) = dest_forall0 b

fVar_Inst_P [recover_s 1 s1,s] pair b1


val (bs, pair, f) = ([recover_s 1 s1,s], pair, b1)



(*val bs =
   [srt ("fun", [Var ("A", srt ("set", [])), Bound 1]), srt ("set", [])]:
   sort list
val f = Pred ("P", false, [Var ("A", srt ("set", [])), Bound 1, Bound 0]):
   form
val pair =
   ("P",
    ([("X", srt ("set", [])), ("Y", srt ("set", [])),
      ("f",
       srt ("fun", [Var ("X", srt ("set", [])), Var ("Y", srt ("set", []))]))],
     Pred
      ("Q", false,
       [Var
         ("f",
          srt
           ("fun", [Var ("A", srt ("set", [])), Var ("B", srt ("set", []))]))]))):
   string * ((string * sort) list * form)*)

val args0 = #2 o dest_fvar $ b1 
 
val (venv,Q) = val venv = (("X", srt ("set", [])), Var ("A", srt ("set", []))),
    (("Y", srt ("set", [])), Bound 1),
    (("f",
      srt ("fun", [Var ("X", srt ("set", [])), Var ("Y", srt ("set", []))])),
     Bound 0)]: ((string * sort) * term) list
> # val Q =
   Pred
    ("Q", false,
     [Var
       ("f",
        srt ("fun", [Var ("A", srt ("set", [])), Var ("B", srt ("set", []))]))]):

val (vd,f) = (venv, Q)

Binarymap.listItems venv 

pinst_t venv (Var ("f",
        srt ("fun", [Var ("A", srt ("set", [])), Var ("B", srt ("set", []))])))


val tl = #2 (dest_fvar Q)
  

val bs = [s1,s]; val f = b1;
val (P0,args0) = dest_fvar f;

lcs = A B f:A->B 

pmatch_tl bs lcs
          (List.map mk_var argl) args0
          emptyvd

val (bs,nss,l1,l2,env) = 
(bs,lcs,List.map mk_var argl,args0,emptyvd)

val (h1,t1) = (hd l1,tl l1)
val (h2,t2) = (hd l2,tl l2)

val vd0 = (pmatch_t bs nss h1 h2 env)
 pmatch_tl bs nss t1 t2 vd0


val (bs,nss,l1,l2,env) =  (bs, nss, t1, t2, vd0)

val (h1,t1) = (hd l1,tl l1)
val (h2,t2) = (hd l2,tl l2)

Binarymap.listItems (pmatch_t bs nss h1 h2 env)


val env11 = (pmatch_t bs nss h1 h2 env) 

val (bs,nss,l1,l2,env) =  (bs, nss, t1, t2, env11)

val (h1,t1) = (hd l1,tl l1)
val (h2,t2) = (hd l2,tl l2)



problematic input of pmatch_tl:

 val (bs,nss,l1,l2,env) =
   ([srt ("fun", [Var ("A", srt ("set", [])), Bound 0]), srt ("set", [])], ?
(*[("A", srt ("set", [])), ("B", srt ("set", [])),
    ("f",
     srt ("fun", [Var ("A", srt ("set", [])), Var ("B", srt ("set", []))]))]*)

,
    [Var
      ("f",
       srt ("fun", [Var ("X", srt ("set", [])), Var ("Y", srt ("set", []))]))],
    [Bound 0], ?

(* [(("X", srt ("set", [])), Var ("A", srt ("set", []))),
    (("Y", srt ("set", [])), Bound 1)]: ((string * sort) * term) list
> *)):
   sort list * (string * sort) set * term list * term list * vd

(pmatch_t bs nss h1 h2 env)


raises

Exception-
   TER
     ("match_sort.attempting matching two different sorts: set , fun",
      [srt ("set", []), srt ("fun", [Var ("A", srt ("set", [])), Bound 0])],
      []) raised


h1:f:X->Y h2: bound 0 

val (pat,ct) = (h1,h2)

pmatch_t bs nss pat ct (env:vd) raise same exn.

val (n1,s1) = dest_var pat 
val i = 0

 val s2 = el (i + 1) bs
            val s2from0 = recover_s i s2

val vd1 = pmatch_s bs nss s1 s2from0 (env:vd)  exn here


val (sp,cs) = (s1,s2from0)
val (sp,cs) = (s1,srt ("fun", [Var ("A", srt ("set", [])), Bound 1]))

val venv = pmatch_s bs nss sp cs env





val f1 = mk_fvar "P" [mk_set "A",mk_set "B",mk_func "f" (mk_set "A") (mk_set "B")]


fVar_Inst_P bs pair f1 

val q = "!"
mk_quant q n s (fVar_Inst_f0 (s :: bs) pair b)



 AX1 |> qspecl [‘A’,‘A’]
     |> concl
     |> fVar_Inst_f ("P",([("a",mem_sort (mk_set "A")),
                             ("b",mem_sort (mk_set "B"))],“~(a:mem(A) = a)”))

           “~(a:mem(A) = a)”

fVar_Inst_f ("P",
             ([("a",fun_sort (mk_set "X") (mk_set "Y"))],
               “Inj(a:X->Y)”))
            “P(X,f:X->Y)”

fVar_Inst_f ("P",
             ([("X",set_sort),("Y",set_sort),
               ("a",fun_sort (mk_set "X") (mk_set "Y"))],
               “Inj(a:X->Y)”))
            “!f.P(A,B,f:A->B)”



fVar_Inst_f ("P",
             ([("X",set_sort),("Y",set_sort),
               ("a",fun_sort (mk_set "X") (mk_set "Y"))],
               “Inj(a:X->Y)”))
            “!f.P(A,B,f:A->B) & Inj(h)”





val pair = ("P",
             ([("X",set_sort),("Y",set_sort),("a",fun_sort (mk_set "X") (mk_set "Y"))],
               “Inj(a:X->Y)”))

val (P,(argl,Q)) =  ("P",
             ([("X",set_sort),("Y",set_sort),("a",fun_sort (mk_set "X") (mk_set "Y"))],
               “Inj(a:X->Y)”))

val f =           “P(A,f:A->B)”

fun pinst_f vd f = 
    case f of 
        Quant(q,n,s,b) => 
        let val vd1 = shift_vd 1 vd
            val b1 = pinst_f vd1 b
            val s1 = inst_sort vd1 s
        in Quant(q,n,s1,b1)
        end 
      | Pred(p,b,tl) => Pred(p,b,List.map (inst_term vd) tl)
      | Conn(co,fl) => Conn(co,List.map (pinst_f vd) fl)

val vl = List.map dest_var $ (#2 o dest_fvar) “P(X,p:X->N,R:X~>X,z:N->X)” 



(pair as (P,(argl:(string * sort) list,Q)))

fun fVar_Inst_P bs (pair as (P,(argl:(string * sort) list,Q))) f =
    let val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q) argl
    in
    case f of
        Pred(P0,false,args0) =>
        if P0 = P
        then let val venv = pmatch_tl bs lcs
                                     (List.map mk_var argl) args0
                                     emptyvd
             in pinst_f venv Q
             end 
             handle e => raise wrap_err "fVar_Inst_P" e
        else raise ERR ("fVar_Inst_P.different formula variable",[],[],[f])
      | _ => raise ERR ("fVar_Inst_P.not a formula variable",[],[],[f])
    end



fun fVar_Inst_P bs (pair as (P,(argl:(string * sort) list,Q))) f =
    let val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q) argl
    in
    case view_form f of
        vPred(P0,false,args0) =>
        if P0 = P
        then let val venv = pmatch_tl bs lcs
                                     (List.map mk_var argl) args0
                                     emptyvd
             in pinst_f venv Q
             end 
             handle e => raise wrap_err "fVar_Inst_P" e
        else raise ERR ("fVar_Inst_P.different formula variable",[],[],[f])
      | _ => raise ERR ("fVar_Inst_P.not a formula variable",[],[],[f])
    end

(*fVar_Inst_P 

("P",(vl,“Upows(n,p:X->N,R:X~>X,z:N->X)”)) f
*)

fun fVar_Inst_f0 bs (pair as (P,(argl:(string * sort) list,Q))) f = 
    let val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q) argl
    in
    case f of
        Pred(P0,false,args0) => fVar_Inst_P bs pair f
      | Conn(co,[f1,f2]) => 
        (let val f1' = fVar_Inst_f0 bs pair f1
         in Conn(co,[f1',fVar_Inst_f0 bs pair f2])
            handle _ => Conn(co,[f1',f2])
         end 
         handle _ => Conn(co,[f1,fVar_Inst_f0 bs pair f2]))
      | Conn("~",[f1]) => 
        Conn("~",[fVar_Inst_f0 bs pair f1])
      | Pred(_,true,_) => raise ERR ("fVar_Inst_f0.Pred cannot be fVar insted",[],[],[f])
      | Quant(q,n,s,b) => Quant(q,n,s,fVar_Inst_f0 (s :: bs) pair b)
    end






fun fVar_Inst_f (pair as (P,(argl:(string * sort) list,Q))) f = 
fVar_Inst_f0 [] pair f


exception UNCHANGED
 fun total f x = SOME (f x) handle e => NONE

fun MAP f l = 
   let
     (* map2 is the version where something has changed *)
     fun map2 A [] = List.rev A
       | map2 A (h::t) = map2 ((f h handle e => h) :: A) t
     (* map1 is the version to call where nothing has changed yet *)
     fun map1 n [] = raise UNCHANGED
       | map1 n (h::t) = 
           case total f h of
             SOME fh => map2 (fh::(rev $ List.take(l,n))) t
           | NONE => map1 (n + 1) t
   in
     map1 0 l
   end



fun fVar_Inst_th (pair as (P,(argl:(string * sort) list,Q1))) th = 
    let val (ct,asl,w) = dest_thm th
        val lcs = List.foldr
                      (fn (ns,nss) => HOLset.delete(nss,ns)
                                      handle _ => nss) 
                      (fvf Q1) argl
        val ct' = HOLset.union(ct,lcs)
        val aslw' = MAP (fVar_Inst_f pair) (w :: asl)
    in mk_thm (ct',tl aslw',hd aslw')
    end



val AX1 = store_ax("AX1",
“!A B:set.?!R:A~>B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(A,B,a,b)”);


AX1 |> fVar_sInst_th “P(A,B,a:mem(A),b:mem(B))”
            “?R1.Holds(R1:A~>B,a:mem(A),b:mem(B))” 

(* # Exception- TER ("term is bounded", [], []) raised*)


val bs = []:sort list;

val vX = ("X",set_sort);
val vY = ("Y",set_sort);
val vx = ("x",mem_sort (mk_set "X"));
val vy = ("y",mem_sort (mk_set "Y"));
val vR = ("R",rel_sort (mk_set "X") (mk_set "Y"))

(*?R:X~>Y.Q(R,x,y) *)

val fQ = mk_exists "R" (rel_sort (mk_set "X") (mk_set "Y"))
 $ mk_fvar "Q" [mk_var vR, mk_var vx,mk_var vy]

val (pair as (P,(argl:(string * sort) list,Q))) = 
("P",
             ([vX,vY,vx,vy],
 fQ)); (*also test with Q (a, b), with a b constants*)

val _ = new_pred "Holds" [("R",rel_sort (mk_set "A") (mk_set "B")),
                         ("a",mem_sort (mk_set "A")),
                         ("b",mem_sort (mk_set "B"))]

val rR = ("R",rel_sort (mk_set "A") (mk_set "B"));
val sA = ("A",set_sort);
val sB = ("B",set_sort);
val ma = ("a",mem_sort (mk_var sA)) ;
val mb = ("b",mem_sort (mk_var sB)) ;
val Holds = mk_pred "Holds" [mk_var rR,mk_var ma,mk_var mb]
val P1 = mk_fvar "P" [mk_var sA,mk_var sB,mk_var ma,mk_var mb];
val dimpf = mk_dimp Holds P1 
val f0 = mk_forall "a" (mem_sort (mk_var sA))
        $ mk_forall "b" (mem_sort (mk_var sB)) $ dimpf
val f = mk_forall "A" set_sort
         $ mk_forall "B" set_sort 
            $ mk_exists "R" (rel_sort (mk_set "A") (mk_set "B")) f0


val AX1 = mk_thm (essps ,[], f)



fVar_Inst_th pair AX1
HOLset.listItems (cont (fVar_Inst_th pair AX1))
