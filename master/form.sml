structure form :> form = 
struct
open term 

datatype form =
Pred of string * term list
| fVar of string * (string * sort) list * term list
| Conn of string * form list
| Quant of string * string * sort * form



exception ERR of string * sort list * term list * form list

fun simple_fail s = ERR (s,[],[],[]) 

fun wrap_err s exn = 
    case exn of ERR (s0,sl,tl,fl) => ERR (s^s0,sl,tl,fl)
              | TER (s0,sl,tl) => ERR (s^s0,sl,tl,[])
              | _ => raise simple_fail s 


fun subst_bound t = 
    let fun subst i (Pred(a,ts)) = 
            Pred(a, List.map (replacet (i, t)) ts) 
          | subst i (fVar(P,vl,tl)) = 
            fVar(P,vl, List.map (replacet (i, t)) tl)
          | subst i (Conn(b,As)) = Conn(b, List.map (subst i) As) 
          | subst i (Quant(q,n,s,b)) =
            Quant(q, n, replaces (i,t) s, subst (i+1) b)
    in subst 0 end


fun substf (V,t2) f = 
    case f of 
        Pred(P,tl) => Pred(P,List.map (substt (V,t2)) tl)
      | fVar(P,vl,tl) => fVar(P,vl,
List.map (substt (V,t2)) tl)
      | Conn(co,fl) => Conn(co,List.map (substf (V,t2)) fl)
      | Quant(q,n,s,b) => Quant(q,n,substs (V,t2) s,substf (V,t2) b)


fun abstract t = 
    let fun abs i (Pred(a,ts)) = Pred(a, List.map (substt (t,mk_bound i)) ts) 
          | abs i (fVar(P,vl,tl)) = 
if List.exists (fn (n,s) => HOLset.member(fvs s,t) ) vl then 
raise ERR ("abstract.attempting abstract the sort list of an fVar",[],[],[])
else fVar(P,vl,
 List.map (substt (t,mk_bound i)) tl)
          | abs i (Conn(b,As)) = Conn(b, List.map (abs i) As) 
          | abs i (Quant(q,b,s,A)) = 
            Quant(q, b, substs (t, mk_bound (i)) s, abs (i+1) A)
    in abs 0 end;

(*
absvl 0 ("A",mk_sort "set" [])
[
("B",mk_sort "set" []),
("f",mk_sort "fun" [mk_var ("A",mk_sort "set" []),
mk_var ("B",mk_sort "set" [])]) ]

 vl2sl 
[("C",mk_sort "set" []),
("D",mk_sort "set" []),
("E",mk_sort "set" []),
("g",mk_sort "fun" [mk_var ("C",mk_sort "set" []),
mk_var ("D",mk_sort "set" [])]),
("h",mk_sort "fun" [mk_var ("C",mk_sort "set" []),
mk_var ("E",mk_sort "set" [])]) ]

*)


fun fvf f = 
    case f of 
        Pred(P,tl) => fvtl tl
      | fVar(P,vl,tl) => HOLset.union(fvsl (vl2sl vl),fvtl tl)
      | Conn(co,fl) => fvfl fl
      | Quant(q,n,s,b) => HOLset.union (fvs s,fvf b)
and fvfl G = 
    case G of [] => essps
            | h :: t => HOLset.union (fvf h,fvfl t)

(*predicate functions*)

fun is_imp f = 
    case f of
        Conn("==>",[f1,f2]) => true
      | _ => false

fun is_dimp f = 
    case f of
        Conn("<=>",[f1,f2]) => true
      | _ => false

fun is_conj f = 
    case f of
        Conn("&",[f1,f2]) => true
      | _ => false

fun is_disj f = 
    case f of
        Conn("|",[f1,f2]) => true
      | _ => false

fun is_neg f = 
    case f of
        Conn("~",[f0]) => true
      | _ => false

fun is_eq f = 
    case f of Pred("=",[t1,t2]) => true
            | _ => false

fun is_forall f = 
    case f of 
        Quant("!",_,_,_) => true
      | _ => false


fun is_exists f = 
    case f of 
        Quant("?",_,_,_) => true
      | _ => false

fun is_uex f = 
    case f of 
        Quant("?!",_,_,_) => true
      | _ => false


fun is_quant f = 
    case f of 
        Quant _ => true
      | _ => false

(*
fun is_var f = 
    case f of
        Pred(_,false,_) => true
      | _ => false
*)

(*
fun boundst t = 
    case view_term t of
        vVar(n,s) => boundss s
      | vB i => HOLset.add(HOLset.empty Int.compare,i)
      | vFun(f,s,tl) => HOLset.union(boundss s,bigunion Int.compare (List.map boundst tl))
and boundss s = 
    case dest_sort s of
        (_, tl) => bigunion Int.compare (List.map boundst tl)
*)


val TRUE = Pred("T",[])

val FALSE = Pred("F",[])

fun mk_conn co fl = Conn(co,fl)

fun mk_neg f = Conn("~",[f])

fun mk_conj f1 f2 = Conn("&",[f1,f2])

fun mk_disj f1 f2 = Conn("|",[f1,f2])

fun mk_imp f1 f2 = Conn("==>",[f1,f2])

fun mk_dimp f1 f2 = Conn("<=>",[f1,f2])

fun mk_forall n s b = Quant("!",n,s,abstract (n,s) b)

fun mk_exists n s b = Quant("?",n,s,abstract (n,s) b)

fun mk_uex n s b = Quant("?!",n,s,abstract (n,s) b)

fun mk_quant q n s b = Quant(q,n,s,abstract (n,s) b)

fun mk_P0 p tl = Pred(p,tl)

fun mk_fvar f vl tl = fVar(f,vl,tl)

(*destructor functions*)

fun dest_eq f = 
    case f of
        Pred("=",[t1,t2]) => (t1,t2)
      | _ => raise ERR ("not an equality: ",[],[],[f])

fun dest_imp f = 
    case f of 
        Conn("==>",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a implication: ",[],[],[f])

fun dest_neg f = 
    case f of
        Conn("~",[f0]) => f0
      | _ => raise ERR ("not a negation: ",[],[],[f])


fun dest_conj f = 
    case f of
        Conn("&",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a conjunction: ",[],[],[f])

fun dest_disj f = 
    case f of
        Conn("|",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a disjunction: ",[],[],[f])
 

fun dest_dimp f = 
    case f of 
        Conn("<=>",[L,R]) => (L,R)
      | _ => raise ERR ("not a double implication: ",[],[],[f])


fun dest_pred f = 
    case f of 
        Pred(p,l) => (p,l)
      | _ => raise ERR ("not a predicate: ",[],[],[f])

fun dest_exists f = 
    case f of 
        Quant("?",n,s,b) => 
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not an existantial: ",[],[],[f])


fun dest_f (Quant(q,n,s,b)) = 
let fun dest (f,i) =
    case f of
        Pred(P,tl) => 
        Pred(P,List.map (fn t => dest_t (n,s) (t,i)) tl)
|  fVar(P,sl,tl) => 
   fVar(P,sl,List.map (fn t => dest_t (n,s) (t,i)) tl)
      | Conn("~",[f0]) => 
        Conn("~",[dest (f0,i)])
      | Conn(co,[f1,f2]) => 
        Conn(co,[dest (f1,i),dest (f2,i)])
      | Quant(q0,n0,s0,b0) => Quant(q0,n0,s0,dest (subst_bound (mk_var(n,s)) b0,i+1))
      | _ => raise ERR ("dest.ill-formed formula",[],[],[])
in ((n,s),dest(b,0))
   handle CLASH =>
          let val (n1,s1) = 
                  dest_var (pvariantt (fvf b) (mk_var (n,s)))
          in dest_f (Quant(q,n1,s1,b))
          end
end
  | dest_f _ = raise ERR ("dest_f.not a quantification",[],[],[])


fun dest_uex f = 
    case f of 
        Quant("?!",n,s,b) =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',subst_bound (mk_var ns') b)
        end
      | _ => raise ERR ("not a unique existantial",[],[],[f])

fun dest_fvar f =
    case f of
        fVar(p,vl,args)  => (p,vl,args)
      | _ => raise ERR ("not a formula variable",[],[],[f])

(*fun rev_vl2sl [] = []
  | rev_vl2sl (h :: t) = 

eq_absvl [("A",mk_sort "set" []),
("B",mk_sort "set" []),
("f",mk_sort "fun" [mk_var ("A",mk_sort "set" []),
mk_var ("B",mk_sort "set" [])]) ] 
[("C",mk_sort "set" []),
("D",mk_sort "set" []),
("g",mk_sort "fun" [mk_var ("C",mk_sort "set" []),
mk_var ("D",mk_sort "set" [])]) ]
*)



fun eq_absvl [] [] = true 
 |  eq_absvl (v1 :: vl1) (v2 :: vl2) = 
    #2 v1 = #2 v2 andalso
eq_absvl vl1 (List.map (fn (n,s) => (n,substs (v2,mk_var v1) s)) vl2)
 | eq_absvl _ _ = false


fun eq_form fp = PolyML.pointerEq (fst fp,snd fp) orelse
    case fp of 
        (Pred(P1,tl1),Pred(P2,tl2)) => 
        P1 = P2 andalso (*List.all (fn (t1,t2) => t1 = t2) (zip tl1 tl2)*) tl1 = tl2
      | (fVar(P1,vl1,tl1),fVar(P2,vl2,tl2)) =>
        P1 = P2 andalso eq_absvl vl1 vl2 andalso tl1 = tl2
      | (Conn(co1,fl1),Conn(co2,fl2)) => co1 = co2 andalso 
                                         ListPair.all eq_form (fl1,fl2)
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        q1 = q2 andalso s1 = s2 andalso eq_form (b1,b2)
      | _ => false

fun eq_forml (l1:form list) (l2:form list) = 
    case (l1,l2) of 
        ([],[]) => true
      | (h1 :: t1, h2 :: t2) => eq_form(h1,h2) andalso eq_forml t1 t2
      | _  => false

fun fmem f fl = List.exists (curry eq_form f) fl

fun ril i l = 
    case l of [] => []
            | h :: t => 
              if eq_form(h,i) then t else h :: (ril i t)

(*compare functions which help produces HOLsets.*)

type fvd = (string,form)Binarymap.dict
type menv = vd * fvd

(*matching environment: records where are term variables and formula variables matched to*)

fun vd_of ((vd,fvd):menv) = vd

fun fvd_of ((vd,fvd):menv) = fvd

fun mk_menv tenv fenv :menv = (tenv,fenv)

val emptyfvd:fvd = Binarymap.mkDict String.compare

val mempty : menv = (emptyvd,emptyfvd)

fun fv2f fm f (fvd:fvd):fvd = Binarymap.insert(fvd,fm,f)

fun fv2f' fm f menv0: menv = mk_menv (vd_of menv0) (fv2f fm f (fvd_of menv0))
 
fun lookup_f (fvd:fvd) fm = Binarymap.peek (fvd,fm)

fun lookup_f' (menv:menv) fm = Binarymap.peek (fvd_of menv,fm)

fun mk_fenv l :fvd= 
    case l of 
        [] => emptyfvd
      | (n:string,f:form) :: l0 => Binarymap.insert(mk_fenv l0,n,f)

fun mk_inst tl fl = mk_menv (mk_tenv tl) (mk_fenv fl)

fun pmenv (env:menv) = (pvd (vd_of env),Binarymap.listItems (fvd_of env))

fun match_tl' nss l1 l2 env0 = 
    let val (vd0,fvd0) = (vd_of env0,fvd_of env0)
        val vd = match_tl nss l1 l2 vd0 
    in mk_menv vd fvd0
    end


fun match_sort' nss s1 s2 env0 = 
    let val (vd0,fvd0) = (vd_of env0,fvd_of env0)
        val vd = match_sort nss s1 s2 vd0 
    in mk_menv vd fvd0
    end



fun match_form nss ps pat cf env:menv = 
    case (pat,cf) of
        (Pred(P1,l1),Pred(P2,l2)) => 
        if P1 <> P2 then 
            raise ERR ("different predicates: ",[],[],[pat,cf])
        else match_tl' nss l1 l2 env
      | (fVar(P1,vl1,h1 :: tl1),fVar(P2,vl2,h2 :: tl2)) =>
        if P1 = P2 andalso eq_absvl vl1 vl2 then
           match_tl' nss (h1 :: tl1) (h2 :: tl2) env 
        else  
            raise ERR ("different formula variables: ",[],[],[pat,cf])
      | (Conn(co1,l1),Conn(co2,l2)) => 
        if co1 <> co2 then 
            raise ERR ("different connectives: ",[],[],[pat,cf])
        else match_fl nss ps l1 l2 env
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        if q1 <> q2 then 
            raise ERR ("different quantifiers: ",[],[],[pat,cf])
        else match_form nss ps b1 b2 (match_sort' nss s1 s2 env)
      | (fVar (fm,[],[]),_) => 
        if HOLset.member(ps,fm) then 
            if eq_form(pat,cf) then env
            else raise ERR ("match_form.current fvar is local constant",[],[],[pat])
        else
            (case (lookup_f' env fm) of
                 SOME f => if eq_form(f,cf) then env else
                           raise ERR ("double bind of formula variables",[],[],[pat,f,cf])
               | _ => fv2f' fm cf env)
      | _ => raise ERR ("different formula constructors",[],[],[pat,cf])
and match_fl nss ps l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl nss ps t1 t2 (match_form nss ps h1 h2 env)
      | _ => raise simple_fail "incorrect length of list"

(*
fun fVars f = 
    case f of
        Pred _ = HOLset.empty String.compare
      | fVar(P,vl,args) => HOLset.add(HOLset.empty String.compare,())
      | Conn("~",[f0]) => fVars f0
      | Conn(_,[f1,f2]) => HOLset.union(fVars f1,fVars f2)
      | Quant(_,_,_,b) => fVars b
      | Pred(_,true,_) => HOLset.empty String.compare
      |_ => raise ERR ("fVars.ill-formed formula",[],[],[f])

fun fVarsl fl = bigunion String.compare (List.map fVars fl)
*)

fun strip_forall f = 
    case f of 
        Quant("!",n,s,b) => 
        let 
            val (b1,l) = 
                strip_forall 
                    (subst_bound (pvariantt (fvf f) (mk_var(n,s))) b) in
            (b1,dest_var (pvariantt (fvf f) (mk_var(n,s))) :: l) end
      | _ => (f,[])


fun strip_forall0 f = 
    case f of 
        Quant("!",n,s,b) => 
        let 
            val (b1,l) = strip_forall0 b in
            (b1,dest_var (pvariantt (fvf f) (mk_var(n,s))) :: l) end
      | _ => (f,[])

fun strip_exists f = 
    case f of 
        Quant("?",n,s,b) => 
        let 
            val (b1,l) = 
                strip_exists 
                    (subst_bound (pvariantt (fvf f) (mk_var(n,s))) b) in
            (b1,dest_var (pvariantt (fvf f) (mk_var(n,s))) :: l) end
      | _ => (f,[])

fun strip_uex f = 
    case f of 
        Quant("?!",n,s,b) => 
        let 
            val (b1,l) = 
                strip_uex
                    (subst_bound (pvariantt (fvf f) (mk_var(n,s))) b) in
            (b1,dest_var (pvariantt (fvf f) (mk_var(n,s))) :: l) end
      | _ => (f,[])

fun strip_quants f = 
    case f of 
        Quant(q,_,_,_) => if q = "!" then strip_forall f 
                          else if q = "?" then strip_exists f 
                          else if q = "?!" then strip_uex f 
                          else raise ERR ("strip_quants.not a quantified formula",[],[],[f])
      | _ => raise ERR ("strip_quants.not a quantified formula",[],[],[f])


fun strip_all_quants0 f = 
    case f of 
        Quant(q,n,s,b) => let val (l0,f0) = strip_all_quants0 b
                          in ((n,s) :: l0,f0)
                          end
      | _ => ([],f)


fun inst_term' env t = inst_term (vd_of env) t

fun inst_sort' env s = inst_sort (vd_of env) s

fun name_clash n env = 
    let
        val new_terms = List.map snd (pvd (vd_of env))
        val new_names = mapfilter (fst o dest_var) new_terms
    in 
        List.exists (fn n0 => n0 = n) new_names
    end

fun inst_form env f = 
    case f of
        Pred(P,tl) => Pred(P,List.map (inst_term' env) tl)
| fVar(P,vl,tl) => 
if vl = [] andalso tl = [] then
 (case lookup_f' env P of
             SOME f' =>(* inst_form env*) f'
           | NONE => fVar(P,[],[]))
  else
fVar (P,List.map (fn (n,s) => (n,inst_sort' env s)) vl 
(*
List.map (dest_var o (inst_term' env) o mk_var) vl*),
List.map (inst_term' env) tl)
      | Conn(co,fl) => Conn(co,List.map (inst_form env) fl)
      | Quant(q,n,s,b) => Quant(q,n,inst_sort' env s,inst_form env b)
     
    


fun psymsf f = 
    case f of 
        Pred(p,_) => HOLset.add(HOLset.empty String.compare,p)
      | fVar _ => HOLset.empty String.compare
      | Conn("~",[A]) => psymsf A
      | Conn(_,[A,B]) => HOLset.union(psymsf A,psymsf B)
      | Quant(_,_,_,b) => psymsf b
      | _ => raise ERR ("psymsf.ill-formed formula: ",[],[],[f])

fun fsymsf f = 
    case f of 
        Pred(_,l) => 
        List.foldr 
            (fn (t,fs) => HOLset.union (fsymst t,fs))
            (HOLset.empty String.compare)
            l
      | fVar _ => HOLset.empty String.compare
      | Conn("~",[A]) => fsymsf A
      | Conn(_,[A,B]) => HOLset.union(fsymsf A,fsymsf B)
      | Quant(_,_,_,b) => fsymsf b
      | _ => raise ERR ("fsyms.ill-formed formula",[],[],[f])





fun ok_dpdc (env:menv) ((n:string,s),t) = 
    if sort_of t = inst_sort' env s then true else false
    

fun is_wfmenv menv = 
    let val pairs = pvd (vd_of menv)
    in List.all (ok_dpdc menv) pairs
    end

fun mk_pred0 p tl = Pred (p,tl)

fun mk_pred p tl = 
    case lookup_pred (!psyms) p of 
        NONE => raise ERR ("mk_pred.psym not found",[],tl,[]) 
      | SOME l => 
        let val _ = match_tl essps (List.map mk_var l) tl emptyvd
                    handle _ => raise ERR ("mk_pred.wrong input of predicate:" ^ p,List.map sort_of tl,tl,[])
        in Pred(p,tl)
        end



fun mk_eq t1 t2 =
    case (sort_of t1,sort_of t2) of 
        (s1,s2) =>
        if s1 = s2 then 
            if has_eq (sort_name s1) then mk_pred0 "=" [t1,t2]
            else
                raise ERR ("mk_eq.the sort: " ^ (sort_name s1) ^ 
                           " does not have equality, attempting to make equality on",[s1,s2],[t1,t2],[])
        else raise ERR ("mk_eq.sorts are not equal",[s1,s2],[t1,t2],[])


datatype form_view =
    vConn of string * form list
  | vQ of string * string * sort * form
  | vPred of string * term list
  | vfVar of
    string * (string * sort) list * term list




local 
fun vsubst_bound ns =  
    let fun vsubst i (Pred(a,ts)) = 
            Pred(a, List.map (vreplacet (i, ns)) ts) 
          | vsubst i (fVar(a,vl,tl)) = 
            fVar(a,vl,List.map (vreplacet (i, ns)) tl) 
          | vsubst i (Conn(b,As)) = Conn(b, List.map (vsubst i) As) 
          | vsubst i (Quant(q,n,s,b)) =
            Quant(q, n, vreplaces (i,ns) s, vsubst (i+1) b)
    in vsubst 0 end
in
fun dest_forall f = 
    (case f of 
        Quant("!",n,s,b) =>
        (((n,s),vsubst_bound (n,s) b)
        handle CLASH  =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',vsubst_bound ns' b)
        end)
      | _ => raise ERR ("not a universal",[],[],[f]))
fun dest_exists f = 
    (case f of 
        Quant("?",n,s,b) =>
        (((n,s),vsubst_bound (n,s) b)
        handle CLASH  =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',vsubst_bound ns' b)
        end)
      | _ => raise ERR ("not a existantial",[],[],[f]))
fun dest_uex f = 
    (case f of 
        Quant("?!",n,s,b) =>
        (((n,s),vsubst_bound (n,s) b)
        handle CLASH  =>
        let val ns' = dest_var (pvariantt (fvf f) (mk_var(n,s)))
        in (ns',vsubst_bound ns' b)
        end)
      | _ => raise ERR ("not a uex",[],[],[f]))
end




fun view_form f =
    case f of
        Conn sfs => vConn sfs
      | Quant("!",n,s,b) => 
        let val (v as (n1,s1),b1) = dest_forall f
        in vQ("!",n1,s1,b1)
        end
      | Quant("?",n,s,b) => 
        let val (v as (n1,s1),b1) = dest_exists f
        in vQ("?",n1,s1,b1)
        end
      | Quant("?!",n,s,b) => 
        let val (v as (n1,s1),b1) = dest_uex f
        in vQ("?!",n1,s1,b1)
        end
      | Pred pi => vPred pi
      | fVar fv => vfVar fv
| _ => raise ERR ("view_form.ill-formed formula",[],[],[])


fun dest_quant0 f = 
    case f of Quant Qi => Qi
        | _ => raise ERR ("dest_quant0.input is not quantified: ",[],[],[f])

fun dest_forall0 f =
    case dest_quant0 f of 
        ("!",n,s,f) => ((n,s),f)
      | _ => raise ERR ("dest_forall0.not a forall",[],[],[f])


fun dest_exists0 f =
    case dest_quant0 f of 
        ("?",n,s,f) => ((n,s),f)
      | _ => raise ERR ("dest_exists0.not a exists",[],[],[f])

fun dest_uex0 f =
    case dest_quant0 f of 
        ("?!",n,s,f) => ((n,s),f)
      | _ => raise ERR ("dest_uex0.not a unique exists",[],[],[f])


val _ = new_pred "T" [];
val _ = new_pred "F" [];





fun rename_bound n1 f = 
    case f of 
        Quant(q,n,s,b) => Quant(q,n1,s,b)
      | _ => raise ERR ("rename_bound.not a quantified formula",[],[],[f])




fun shift_bmap i bmap = List.map (tshift i) bmap
    


fun fprpl i bmap f = 
    case f of 
        Pred(P,tl) => 
        Pred(P,List.map (tprpl i bmap) tl)
      | fVar(P,vl,tl) => 
        fVar(P,vl,(List.map (tprpl i bmap) tl))
      | Conn(co,fl) => 
        Conn(co,List.map (fprpl i bmap) fl)
      | Quant(q,n,s,b) =>
        Quant(q,n,sprpl i bmap s,
              fprpl (i+1) (shift_bmap 1 bmap) b)

(*
fprpl 0 [Fun ("N",srt("set",[]),[])]
(Quant("!","b",srt ("set",[]),Quant("!","a",srt ("set",[]),Pred("p",[Bound 1]))))

fprpl 2 [Fun ("N",srt("set",[]),[])] 
[tprpl 2 ([Fun ("N",srt("set",[]),[])]) (Bound 1)
])
*)


(*
fun fVar_prpl i
        (fd:(string * sort list,form)Binarymap.dict)
        fm = 
    case fm of 
        fVar(P,vl,tl) =>
        let val sl = vl2sl vl 
        in (case Binarymap.peek(fd,(P,sl)) of 
               SOME f0 => 
               fprpl i (List.rev tl) f0
             | _ => fm)
        end
      | Pred _ => fm
      | Conn(co,fl) =>
        Conn(co,List.map (fVar_prpl i fd) fl)
      | Quant(q,n,s,b) =>
        Quant(q,n,s,fVar_prpl (i+1) fd b)
*)


fun fVar_prpl
        (fd:(string * sort list,form)Binarymap.dict)
        fm = 
    case fm of 
        fVar(P,vl,tl) =>
        let val sl = vl2sl vl 
        in (case Binarymap.peek(fd,(P,sl)) of 
               SOME f0 => 
               fprpl 0 (List.rev tl) f0
             | _ => fm)
        end
      | Pred _ => fm
      | Conn(co,fl) =>
        Conn(co,List.map (fVar_prpl fd) fl)
      | Quant(q,n,s,b) =>
        Quant(q,n,s,fVar_prpl fd b)


fun no_fVar fm = 
    case fm of 
        Pred _ => true
      | fVar _ => false
      | Conn(co,fl) => List.all no_fVar fl
      | Quant(q,n,s,b) => no_fVar b


val empty_fVar_set = 
HOLset.empty
(pair_compare String.compare (list_compare sort_compare)) 

fun bigunion_of ord f l = 
case l of 
    [] => HOLset.empty ord
  | h :: t => HOLset.union(f h,bigunion_of ord f t)



fun fVars fm = 
    case fm of
        Pred _ => empty_fVar_set
      | fVar(P,vl,tl) => HOLset.add(empty_fVar_set,(P,vl2sl vl))
      | Quant(q,n,s,b) => fVars b
      | Conn(co,[f]) => fVars f
      | Conn(co,[f1,f2]) => HOLset.union(fVars f1,fVars f2)
| _ => raise ERR ("fVars.ill-formed formula",[],[],[fm]) 

val fVarsl = 
bigunion_of (pair_compare String.compare (list_compare sort_compare)) fVars


fun fabs v i (Pred(p,tl)) =
  Pred (p ,List.map (tabs v i) tl) 
| fabs v i (fVar(p,vl,tl)) =
  fVar (p,vl,List.map (tabs v i) tl) 
| fabs v i (Conn(co,fl)) =
  Conn(co,List.map (fabs v i) fl) 
| fabs v i (Quant(q,n,s,b)) =
  Quant(q,n,sabs v i s,fabs v (i + 1) b)
      
fun fabsl0 vl i f = 
    case vl of [] => f
             | h :: t => fabsl0 t (i+1) (fabs h i f) 

fun fabsl vl i f = fabsl0 (List.rev vl) i f 


fun delete_psym p = 
let val (d1,_) = Binarymap.remove (!psyms,p) 
in psyms := d1
end


fun mk_fd input = List.foldr 
(fn ((P:string,vs,f),fd) => 
    let val sl = vl2sl vs 
        val b = fabsl vs 0 f
    in Binarymap.insert(fd,(P,sl),b)
    end) (Binarymap.mkDict(pair_compare String.compare
(list_compare sort_compare))) input 

end
