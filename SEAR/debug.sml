
datatype sort = srt of string * term list 
and term =
    Var of string * sort
    | Bound of int
    | Fun of string * sort * term list;

exception TER of string * sort list * term list

exception CLASH

fun mk_sort str tl = srt (str,tl)


val sorts0:(string, (string * sort) list) Binarymap.dict =
    Binarymap.mkDict String.compare 

val SortDB = ref sorts0

fun new_sort sn depends = 
    SortDB := Binarymap.insert(!SortDB,sn,depends)

fun on_ground st = 
    case Binarymap.peek(!SortDB,st) of 
        SOME tl0 => if tl0 = [] then true else false
      | NONE => raise TER ("no sort with name: " ^ st,[],[])

fun listof_sorts (srts: (string, (string * sort) list) Binarymap.dict) = Binarymap.listItems srts

fun ground_sorts srts = 
    List.filter on_ground $ List.map fst (listof_sorts srts)

val sort_infixes0: (string,string)Binarymap.dict = 
    Binarymap.mkDict String.compare

val SortInx = ref sort_infixes0

fun new_sort_infix st symbol = 
    SortInx := Binarymap.insert(!SortInx,symbol,st)

fun sortname_of_infix syb =
    case Binarymap.peek(!SortInx,syb) of 
        SOME sn => sn
      | _ => raise TER ("sortname_of_infix.no sort with infix symbol: " ^ syb,[],[])


datatype term_view =
    vVar of string * sort
  | vB of int 
  | vFun of string * sort * term list

datatype sort_view = 
         vSrt of string * term list

fun view_term t = 
    case t of
        Var v => vVar v
      | Bound i => raise TER ("term is bounded",[],[]) (*vB i*) (*raise ERR instead, user cannot see it!*)
      | Fun sst => vFun sst

fun view_sort (srt p) = vSrt p
fun dest_sort (srt p) = p



fun wrap_ter s sl tl e = case e of TER (s0,sl0,tl0) => TER (s ^ s0,sl @ sl0,tl @ tl0)
                           | _ => e

fun sort_of t = 
    case t of Var (_,s) => s
            | Fun (_,s,_) => s 
            | Bound i => srt ("Bd",[])

fun is_var t = 
    case t of Var _ => true | _ => false

fun is_fun t = 
    case t of Fun _ => true | _ => false

fun is_bound t = 
    case t of Bound _ => true | _ => false

fun sort_name st = fst $ dest_sort st

fun depends_on st = snd $ dest_sort st

fun of_sort str t = 
    if sort_name (sort_of t) = str then true else false

fun dest_var t = 
    case t of Var(n,s) => (n,s)
            | _ => raise TER ("not a variable: ",[],[t])

fun dest_fun t = 
    case  t of 
        Fun(n,s,l) => (n,s,l)
      | _ => raise TER ("not a function: ",[],[t])

fun mk_var (name,st) = Var(name,st)

fun mk_fun0 f s l = Fun(f,s,l)

fun mk_bound i = Bound i

fun mk_const0 n s = mk_fun0 n s []


fun srt2ns st = 
    let val tl = 
            case Binarymap.peek(!SortDB,st) of 
                SOME tl0 => tl0
              | NONE => raise TER ("no sort with name: "^ st,[],[])
    in (st ^ Int.toString 0,mk_sort st $ List.map mk_var tl)
    end


fun replacet (i,new) t = 
    if t=Bound i then new else 
    case t 
     of Fun(f,s,tl) => 
        Fun(f,replaces (i,new) s, List.map (replacet(i,new)) tl) 
      | Var(n,s) => Var(n,replaces (i,new) s)
      | _ => t
(*      | _ => t *)
and replaces (i,new) s = 
    case s of 
        srt (name,tl) => srt (name, List.map (replacet (i,new)) tl)

fun vreplacet (i,(n,s)) t = 
    case t of 
        Var(n0,s0) => if n0 = n then raise CLASH else 
                       Var(n0,vreplaces (i,(n,s)) s0)
      | Fun(f,s0,tl0) => 
        Fun(f,vreplaces(i,(n,s)) s0,
            List.map (vreplacet(i,(n,s))) tl0)
      | Bound j => if i = j then mk_var(n,s) else t
and vreplaces (i,ns) s = 
    case s of 
        srt (name,tl) => 
        srt (name,List.map (vreplacet (i,ns)) tl)

fun eq_term (t1,t2) = 
    case (t1,t2) of 
        (Var(n1,s1),Var(n2,s2)) => 
        n1 = n2 andalso eq_sort(s1,s2)
      | (Fun(f1,s1,l1),Fun(f2,s2,l2)) =>
        f1 = f2 andalso eq_sort(s1,s2) andalso
        List.all eq_term (zip l1 l2)
      | (Bound i1,Bound i2) => i1 = i2
      | _ => false
and eq_sort (s1,s2) = 
    case (s1,s2) of 
        (srt (sn1,tl1),srt (sn2,tl2)) => 
        if sn1 = sn2 andalso
           List.all eq_term (zip tl1 tl2) then true 
        else false




fun substt (V as (m,s:sort),t2) t = 
   (* case view_term t of
        vVar(n,s') => 
        if m = n andalso s = s' then t2 
        else mk_var (n,substs (V,t2) s')
      | vFun(f,s',tl) => mk_fun0 f (substs (V,t2) s') (List.map (substt (V,t2)) tl)
      | _ => t*)
    case t of
        Var(n,s') => 
        if m = n andalso s = s' then t2 
        else mk_var (n,substs (V,t2) s')
      | Fun(f,s',tl) => mk_fun0 f (substs (V,t2) s') (List.map (substt (V,t2)) tl)
      | _ => t
and substs (V,t2) s = 
    case view_sort s of 
        vSrt (sn,tl) =>
        mk_sort sn (List.map (substt (V,t2)) tl)

fun pair_compare ac bc ((a1,b1),(a2,b2)) = 
    case (ac (a1,a2)) of 
        EQUAL => bc (b1,b2)
      | x => x


fun inv_image_compare f c (x,y) = 
    c (f x, f y)

fun list_compare c (l1,l2) = 
    case (l1,l2) of
        ([],[]) => EQUAL
      | (h1 :: t1, h2 :: t2) => pair_compare c (list_compare c)
                                             ((h1,t1),(h2,t2))
      | ([],_) => LESS
      | (_,[]) => GREATER


fun sort_cpr (s1,s2) = 
    if PolyML.pointerEq(s1,s2) then EQUAL else 
    case (dest_sort s1,dest_sort s2) of 
        ((sn1,tl1),(sn2,tl2)) =>
        (case String.compare (sn1,sn2) of 
             EQUAL => tml_cmp (tl1,tl2) 
           | x => x)
and term_cpr (t1,t2) = 
    if PolyML.pointerEq(t1,t2) then EQUAL else
    case (t1,t2) of 
        (Var (ns1 as (n1,s1)),Var (ns2 as (n2,s2))) =>  
        (case String.compare(n1,n2) of 
            EQUAL => sort_cpr (s1,s2)
          | x => x)
     | (Var _ , _) => LESS
     | (_,Var _) => GREATER
     | (Bound i1, Bound i2) => Int.compare (i1,i2)
     | (Bound _ , _) => LESS
     | (_, Bound _) => GREATER
     | (Fun(fsl1 as (f1,s1,l1)), Fun (fsl2 as (f2,s2,l2))) => 
       (case String.compare(f1,f2) of 
           EQUAL => 
           (case sort_cpr(s1,s2) of 
                EQUAL => tml_cmp (l1,l2)
              | x => x)
         | x => x)
and tml_cmp([],[]) = EQUAL
  | tml_cmp (_, []) = GREATER
  | tml_cmp ([], _) = LESS
  | tml_cmp (t1::tl1, t2::tl2) =
     case term_cpr(t1,t2) of
       EQUAL => tml_cmp(tl1,tl2)
     | x => x



val term_compare = term_cpr;
val sort_compare = sort_cpr;
fun var_ord (ns1 as (n1,s1),ns2 as (n2,s2)) =
    if PolyML.pointerEq(ns1,ns2) then EQUAL else
    case String.compare(n1,n2) of 
        EQUAL => sort_compare (s1,s2)
      | x => x

(*empty string-sort-pair set*)
val essps = HOLset.empty var_ord

type vd = ((string * sort),term)Binarymap.dict

fun pvd vd = Binarymap.listItems vd

val emptyvd:vd = Binarymap.mkDict var_ord

fun mk_tenv l = 
    case l of 
        [] => emptyvd
      | ((n,s),t) :: l0 => Binarymap.insert(mk_tenv l0,(n,s),t)

fun v2t (V:string * sort) (t:term) (vd:vd):vd = Binarymap.insert(vd,V,t)

fun lookup_t (vd:vd) V = Binarymap.peek (vd,V)

fun has_bound_t t = 
    (*case view_term t of 
        vVar (n,s) => has_bound_s s
      | vB _ => true
      | vFun (f,s,tl) => 
        List.exists has_bound_t tl orelse 
        has_bound_s s*)
    case t of 
        Var (n,s) => has_bound_s s
      | Bound _ => true
      | Fun (f,s,tl) => 
        List.exists has_bound_t tl orelse 
        has_bound_s s
and has_bound_s s = 
    case dest_sort s of
        (_,tl) => List.exists has_bound_t tl

        
fun match_term nss pat ct (env:vd) = 
    case (pat,ct) of 
        (Fun(f1,s1,l1),Fun(f2,s2,l2)) => 
        if f1 <> f2 then 
            raise TER("match_term.different function names: " ^ f1 ^ " , " ^ f2,[],[pat,ct])
        else (match_sort nss s1 s2 (match_tl nss l1 l2 env)  
             handle e => raise wrap_ter "match_term." [s1,s2] [pat,ct] e)
      | (Var(n1,s1),_) => 
        (*make sure that _ ct cannot include a bound variable*)
        if has_bound_t ct then 
            raise TER ("match_term.attempting matching to a term with bounded variable",[],[]) 
        else  
        if HOLset.member(nss,(n1,s1)) then
            if pat = ct then env 
            else raise TER ("match_term.current term is local constant: ",[],[pat,ct])
        else 
            (case (lookup_t env (n1,s1)) of
                 SOME t => if t = ct then env else
                           raise TER ("match_term.double bind: ",[],[pat,t,ct])
               | _ => 
                 v2t (n1,s1) ct (match_sort nss s1 (sort_of ct) env)
                 handle e => raise wrap_ter "match_term." [] [pat,ct] e)
      | (Bound i1,Bound i2) => 
        if i1 <> i2 then 
            raise TER ("match_term.bound variables have different levels: ",[],[pat,ct])
        else env
      | _ => raise Fail "match_term.unexpected term constructor"
and match_sort nss sp cs env = 
    case (dest_sort sp,dest_sort cs) of 
        ((sn1,tl1),(sn2,tl2)) =>
        if sn1 = sn2 then
            match_tl nss tl1 tl2 env
        else raise TER ("match_sort.attempting matching two different sorts: "^ sn1 ^ " , " ^ sn2,[sp,cs],[])
and match_tl nss l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_term nss h1 h2 (match_tl nss t1 t2 env)
      | _ => raise TER ("match_sort.incorrect length of list",[],[])



fun inst_term (env:vd) t = 
    (*case view_term t of 
        vVar(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => mk_var (n,inst_sort env s))
      | vFun(f,s,tl) => mk_fun0 f (inst_sort env s) (List.map (inst_term env) tl)
      | _ => t *)
    case t of 
        Var(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => mk_var (n,inst_sort env s))
      | Fun(f,s,tl) => mk_fun0 f (inst_sort env s) (List.map (inst_term env) tl)
      | _ => t
and inst_sort env s = 
    case (dest_sort s) of
        (sn,tl) => 
        mk_sort sn (List.map (inst_term env) tl)


fun pvariantt vd t = 
    case t of 
        Var(n,s) => 
        if mem n (List.map fst (HOLset.listItems vd))
        then pvariantt vd (Var(n ^ "'",s))
        else Var (n, s)
      | Fun(f,s,l) => Fun(f,s,List.map (pvariantt vd) l)
      | _ => t

fun bigunion ord setl = 
    case setl of [] => HOLset.empty ord
               | h :: t => HOLset.union(h,bigunion ord t)

fun var_bigunion setl =
    case setl of
        [] => essps
      | h :: t => HOLset.union(h,var_bigunion t)

fun fsymss s = 
    case dest_sort s of
        (_, tl) =>
        bigunion String.compare (List.map fsymst tl)
and fsymst t = 
    case t of
        Var(n,s) => fsymss s
      | Fun(_,s,l) => 
        let val argfs = List.foldr 
                            (fn (t,fs) => HOLset.union (fsymst t,fs))
                            (HOLset.empty String.compare)
                            l
        in HOLset.union(argfs,fsymss s)
        end
      | _ => HOLset.empty String.compare


fun fvt t = 
    case t of 
        Var(n,s) => HOLset.add (fvs s,(n,s)) 
      | Bound i => essps
      | Fun(f,s,tl) => 
        (case tl of 
             [] => essps
           | h :: t => HOLset.union 
                           (HOLset.union ((fvt h),(fvs s)), 
                            fvtl t))
and fvs s = 
    case dest_sort s of 
        (sn,tl) => fvtl tl
and fvtl tl = var_bigunion (List.map fvt tl)


fun fvta a t = 
    case t of 
        Var(p as (n,s)) => fvsa (HOLset.add(a,p)) s
      | Bound _ => a 
      | Fun(f,s,tl) => fvtla (fvsa a s) tl
and fvtla a [] = a
  | fvtla a (t :: ts) = fvtla (fvta a t) ts
and fvsa a (srt(sname,ts)) = 
    fvtla a ts

fun FVT a t =
  case t of
    Var (p as (_, s)) => FVS (p::a) s
  | Bound _ => a
  | Fun (_, s, tl) => FVTL (FVS a s) tl
and FVTL a [] = a
  | FVTL a (t::ts) = FVTL (FVT a t) ts
and FVS a (srt (_, ts)) = FVTL a ts

val fvt = fvta essps

val fvtl = fvtla essps

val fvs = fvsa essps


fun fxty i = 
    case i of 
       "<=>" => 100
      | "==>" => 200
      | "|" => 300
      | "&" => 400
      | "=" => 450
      | "==" => 450
      | "o" => 455
      | "@" => 455
      | ":" => 460 (*900*)
      | "->" => 470 (*900*)
      | "=>" => 470 (*900*)
      | "~>" => 470 
      | "+" => 500
      | "*" => 600
      | "^" => 700
      | "~" => 900
      | _ => ~1

val eqsorts0: string list = [] 

val EqSorts = ref eqsorts0

fun has_eq sn = mem sn (!EqSorts)


type fsymd = (string, sort * ((string * sort) list)) Binarymap.dict

type psymd = (string, (string * sort) list) Binarymap.dict

fun lookup_pred (pd:psymd) p = Binarymap.peek (pd,p)

fun lookup_fun (fd:fsymd) f = Binarymap.peek (fd,f)




val psyms0:psymd = Binarymap.mkDict String.compare

val fsyms0:fsymd = Binarymap.mkDict String.compare

val fsyms = ref fsyms0
val psyms = ref psyms0


fun mk_fun f tl = 
    case lookup_fun (!fsyms) f of 
        NONE => raise TER ("mk_fun.function: " ^ f ^ " not found",[],tl)
      | SOME(s,l) => 
        let val vd = (match_tl essps (List.map mk_var l) tl emptyvd)
            val s' = inst_sort vd s
        in mk_fun0 f s' tl
        end

fun is_fun sr = 
    case (Binarymap.peek (!fsyms,sr)) of 
        SOME _ => true
      | _ => false

fun is_pred sr =
    case (Binarymap.peek (!psyms,sr)) of
        SOME _ => true
      | _ => false

fun is_const sr = 
    case (Binarymap.peek (!fsyms,sr)) of 
        SOME (_,l) => if length l = 0 then true else false
      | _ => false


fun new_pred p tl = psyms := Binarymap.insert (!psyms,p,tl)

fun new_fun f (s,tl) = fsyms := Binarymap.insert (!fsyms,f,(s,tl))


fun ill_formed_fv (n,s) = 
    case dest_sort s of (_,tl) => 
                        List.exists is_bound tl

fun strtml_cmp ((s1, tl1), (s2, tl2)) =
    case String.compare(s1,s2) of
    	 EQUAL => tml_cmp (tl1,tl2)
	 | x => x 
val abbrdict0: 
 (string * (term list), string * (term list)) Binarymap.dict = Binarymap.mkDict strtml_cmp

val abbrdict = ref abbrdict0

val unabbrdict0: (string * (term list), string * (term list)) Binarymap.dict = Binarymap.mkDict strtml_cmp

val unabbrdict = ref unabbrdict0

fun new_abbr (f,tl) (abf,tl') =
    let 
        val _ = abbrdict :=
                Binarymap.insert(!abbrdict,(f,tl),(abf,tl'))
        val _ = unabbrdict := 
                Binarymap.insert(!unabbrdict,(abf,tl'),(f,tl))
in () end



fun dest_t (n,s) (t,i) = 
    case t of 
        Bound j => if i = j then mk_var(n,s) else t
      | Var(m,st) => if n = m then raise CLASH 
                     else Var(m,dest_s (n,s) (st,i))
      | Fun(f,st,tl) => Fun(f,dest_s (n,s) (st,i),
                            List.map (fn t => dest_t (n,s) (t,i)) tl)
and dest_s (n,s) (st,i) = 
    case st of
        srt(sname,tl) => 
        srt(sname,List.map (fn t => dest_t (n,s) (t,i)) tl)

(*add_to_bvs increment_bvs*)
fun recover_s i (srt (sname,tl)) = 
    srt (sname,List.map (recover_t i) tl)
and recover_t i t = 
    case t of 
        Var(n,s) => Var(n,recover_s i s)
      | Fun(f,s,l) => Fun(f,recover_s i s, List.map (recover_t i) l)
      | Bound j => Bound (i + j)




fun shift_vd_eval i vd ns = 
    case Binarymap.peek(vd,ns) of 
        SOME t => recover_t i t
      | _ => raise TER ("shift_vd_eval.no value stored for that key",[],[])

fun shift_vd i vd = 
    Binarymap.foldl 
        (fn (ns,t,d) => Binarymap.insert(d,ns,recover_t i t)) vd vd (*first vd here should be emptyvd*)







fun pmatch_t bs nss pat ct (env:vd) = 
    case (pat,ct) of 
        (Fun(f1,s1,l1),Fun(f2,s2,l2)) => 
        if f1 <> f2 then 
            raise TER("match_term.different function names: "^ f1 ^ " , " ^ f2,[],[pat,ct])
        else (pmatch_s bs nss s1 s2 (pmatch_tl bs nss l1 l2 env)  
             handle e => raise wrap_ter "pmatch_term." [s1,s2] [pat,ct] e)
      | (Var(n1,s1),Bound i) =>
        let val s2 = el (i + 1) bs
            (*val s2from0 = recover_s i s2*)
            val vd1 = pmatch_s bs nss s1 s2 (* s2from0 *) (env:vd) 
        in v2t (*v2t should called insert*) (n1,s1) ct vd1
        end
      | (Var(n1,s1),_) => 
        if HOLset.member(nss,(n1,s1)) then
            if pat = ct then env 
            else raise TER ("match_term.current term is local constant: ",[],[pat,ct])
        else 
            (case (lookup_t env (n1,s1)) of
                 SOME t => if t = ct then env else
                           raise TER ("pmatch_t.double bind: ",[],[pat,t,ct])
               | _ => 
                 v2t (n1,s1) ct (pmatch_s bs nss s1 (sort_of ct) env)
                 handle e => raise wrap_ter "pmatch_t." [] [pat,ct] e)
      | (Bound i1,Bound i2) => 

        (*pat cannot be bound variable, so get rid of this case or exn*)
        if i1 <> i2 then 
            raise TER ("pmatch_t.bound variables have different levels: ",[],[pat,ct])
        else env
      | _ => raise Fail "pmatch_t.unexpected term constructor"
and pmatch_s bs nss sp cs env = 
    case (dest_sort sp,dest_sort cs) of 
        ((sn1,tl1),(sn2,tl2)) =>
        if sn1 = sn2 then
            pmatch_tl bs nss tl1 tl2 env
        else raise TER ("match_sort.attempting matching two different sorts: "^ sn1 ^ " , " ^ sn2,[sp,cs],[])
and pmatch_tl bs nss l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        pmatch_tl bs nss t1 t2 (pmatch_t bs nss h1 h2 env)
      | _ => raise TER ("match_sort.incorrect length of list",[],[])



fun pinst_t (env:vd) t = 
    case  t of 
        Var(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => Var(n,pinst_s env s))
      | Fun(f,s,tl) => 
        Fun(f,pinst_s env s,List.map (pinst_t env) tl)
      | _ => t
and pinst_s env s = 
    case (dest_sort s) of
        (sn,tl) => 
        srt(sn,List.map (pinst_t env) tl)




local
fun delete'(set,mem) = HOLset.delete(set,mem) handle _ => set
in
fun filter_cont ct = 
    HOLset.foldr 
        (fn (ns,set) => 
            case HOLset.find 
                     (fn (vn,vs) => HOLset.member(fvs vs,ns)) set of 
                SOME _ => delete'(set,ns)
              | NONE => set) ct ct
end


datatype form =
Pred of string * bool * term list
| Conn of string * form list
| Quant of string * string * sort * form



exception ERR of string * sort list * term list * form list

fun simple_fail s = ERR (s,[],[],[]) 

fun wrap_err s exn = 
    case exn of ERR (s0,sl,tl,fl) => ERR (s^s0,sl,tl,fl)
              | TER (s0,sl,tl) => ERR (s^s0,sl,tl,[])
              | _ => raise simple_fail s 


fun subst_bound t = 
    let fun subst i (Pred(a,b,ts)) = 
            Pred(a, b,List.map (replacet (i, t)) ts) 
          | subst i (Conn(b,As)) = Conn(b, List.map (subst i) As) 
          | subst i (Quant(q,n,s,b)) =
            Quant(q, n, replaces (i,t) s, subst (i+1) b)
    in subst 0 end


fun substf (V,t2) f = 
    case f of 
        Pred(P,b,tl) => Pred(P,b,List.map (substt (V,t2)) tl)
      | Conn(co,fl) => Conn(co,List.map (substf (V,t2)) fl)
      | Quant(q,n,s,b) => Quant(q,n,substs (V,t2) s,substf (V,t2) b)


fun abstract t = 
    let fun abs i (Pred(a,b,ts)) = Pred(a,b, List.map (substt (t,mk_bound i)) ts) 
          | abs i (Conn(b,As)) = Conn(b, List.map (abs i) As) 
          | abs i (Quant(q,b,s,A)) = 
            Quant(q, b, substs (t, mk_bound (i)) s, abs (i+1) A)
    in abs 0 end;


fun fvf f = 
    case f of 
        Pred(P,b,tl) => fvtl tl
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
    case f of Pred("=",true,[t1,t2]) => true
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

fun is_var f = 
    case f of
        Pred(_,false,_) => true
      | _ => false

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


val TRUE = Pred("T",true,[])

val FALSE = Pred("F",true,[])

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

fun mk_P0 p tl = Pred(p,true,tl)

fun mk_fvar f tl = Pred(f,false,tl)

(*destructor functions*)

fun dest_eq f = 
    case f of
        Pred("=",true,[t1,t2]) => (t1,t2)
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
        Pred(p,true,l) => (p,l)
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
        Pred(P,bl,tl) => 
        Pred(P,bl,List.map (fn t => dest_t (n,s) (t,i)) tl)
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
        Pred(p,false,args)  => (p,args)
      | _ => raise ERR ("not a formula variable",[],[],[f])

fun eq_form fp = PolyML.pointerEq (fst fp,snd fp) orelse
    case fp of 
        (Pred(P1,b1,tl1),Pred(P2,b2,tl2)) => 
        P1 = P2 andalso b1 = b2 andalso (*List.all (fn (t1,t2) => t1 = t2) (zip tl1 tl2)*) tl1 = tl2
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
        (Pred(P1,true,l1),Pred(P2,true,l2)) => 
        if P1 <> P2 then 
            raise ERR ("different predicates: ",[],[],[pat,cf])
        else match_tl' nss l1 l2 env
      | (Conn(co1,l1),Conn(co2,l2)) => 
        if co1 <> co2 then 
            raise ERR ("different connectives: ",[],[],[pat,cf])
        else match_fl nss ps l1 l2 env
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        if q1 <> q2 then 
            raise ERR ("different quantifiers: ",[],[],[pat,cf])
        else match_form nss ps b1 b2 (match_sort' nss s1 s2 env)
      | (Pred (fm,false,[]),_) => 
        if HOLset.member(ps,fm) then 
            if eq_form(pat,cf) then env
            else raise ERR ("match_form.current fvar is local constant",[],[],[pat])
        else
            (case (lookup_f' env fm) of
                 SOME f => if eq_form(f,cf) then env else
                           raise ERR ("double bind of formula variables",[],[],[pat,f,cf])
               | _ => fv2f' fm cf env)
      | (Pred(fm1,false,args1),cf) =>
        (case cf of 
            Pred(fm',false,args') =>
            if fm' = fm1 then match_tl' nss args1 args' env
            else raise ERR ("match_form.attempting match fvar with arguments to concrete formula, which is a formula variable",[],[],[pat])
          | _ => raise ERR ("match_form.attempting match fvar with arguments to concrete formula",[],[],[pat]))
      | _ => raise ERR ("different formula constructors",[],[],[pat,cf])
and match_fl nss ps l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl nss ps t1 t2 (match_form nss ps h1 h2 env)
      | _ => raise simple_fail "incorrect length of list"


fun fVars f = 
    case f of
        Pred(P,false,args) => HOLset.add(HOLset.empty String.compare,P)
      | Conn("~",[f0]) => fVars f0
      | Conn(_,[f1,f2]) => HOLset.union(fVars f1,fVars f2)
      | Quant(_,_,_,b) => fVars b
      | Pred(_,true,_) => HOLset.empty String.compare
      |_ => raise ERR ("fVars.ill-formed formula",[],[],[f])

fun fVarsl fl = bigunion String.compare (List.map fVars fl)

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
        Pred(P,true,tl) => Pred(P,true,List.map (inst_term' env) tl)
      | Conn(co,fl) => Conn(co,List.map (inst_form env) fl)
      | Quant(q,n,s,b) => Quant(q,n,inst_sort' env s,inst_form env b)
      | Pred(f,false,tl) => 
        (case lookup_f' env f of
             SOME f' =>(* inst_form env*) f'
           | NONE => Pred(f,false,List.map (inst_term' env) tl))

    


fun psymsf f = 
    case f of 
        Pred(p,true,_) => HOLset.add(HOLset.empty String.compare,p)
      | Conn("~",[A]) => psymsf A
      | Conn(_,[A,B]) => HOLset.union(psymsf A,psymsf B)
      | Quant(_,_,_,b) => psymsf b
      | _ => raise ERR ("psymsf.ill-formed formula: ",[],[],[f])

fun fsymsf f = 
    case f of 
        Pred(_,_,l) => 
        List.foldr 
            (fn (t,fs) => HOLset.union (fsymst t,fs))
            (HOLset.empty String.compare)
            l
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

fun mk_pred0 p tl = Pred (p,true,tl)

fun mk_pred p tl = 
    case lookup_pred (!psyms) p of 
        NONE => raise ERR ("mk_pred.psym not found",[],tl,[]) 
      | SOME l => 
        let val _ = match_tl essps (List.map mk_var l) tl emptyvd
                    handle _ => raise ERR ("mk_pred.wrong input of predicate:" ^ p,List.map sort_of tl,tl,[])
        in Pred(p,true,tl)
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
  | vPred of string * bool * term list




local 
fun vsubst_bound ns =  
    let fun vsubst i (Pred(a,b,ts)) = 
            Pred(a, b,List.map (vreplacet (i, ns)) ts) 
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



fun pinst_f vd f (*extra parameter counting how many quantifiers*)= 
    case f of 
        Quant(q,n,s,b) => 
        let val vd1 = shift_vd 1 vd
            val b1 = pinst_f vd1 b
            val s1 = inst_sort vd1 s
        in Quant(q,n,s1,b1)
        end 
      | Pred(p,b,tl) => Pred(p,b,List.map (pinst_t vd) tl)
      | Conn(co,fl) => Conn(co,List.map (pinst_f vd) fl)
      

(*local constants: vars in Q that is not in argl*)
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
             handle e => raise wrap_err "fVar_Inst_P." e
        else raise ERR ("fVar_Inst_P.different formula variable",[],[],[f])
      | _ => raise ERR ("fVar_Inst_P.not a formula variable",[],[],[f])
    end



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
      | Pred(_,true,_) =>(* Should be just be f  *)raise ERR ("fVar_Inst_f0.Pred cannot be fVar insted",[],[],[f])
      | Quant(q,n,s,b) => 
(*Quant(q,n,s,fVar_Inst_f0 ((recover_s 1 s) :: bs) pair b)(*should also add 1 on previous sorts, shift bs by +1*)*)
Quant(q,n,s,fVar_Inst_f0 (List.map (recover_s 1) (s :: bs)) pair b)
    end

(*calculate lcs here instead of in f0, and pass it as a parameter into fvar_inst_f0*)
fun fVar_Inst_f (pair as (P,(argl:(string * sort) list,Q))) f = 
fVar_Inst_f0 [] pair f



val _ = new_sort "set" [];
val _ = new_sort "mem" [("A",mk_sort "set" [])];
val _ = new_sort "rel" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "rel" "~>"

val set_sort = mk_sort "set" []
fun mem_sort A = mk_sort "mem" [A]
fun rel_sort A B = mk_sort "rel" [A,B]
fun mk_set A = mk_var(A,set_sort)
fun mk_rel R A B = mk_var(R,rel_sort A B)
fun mk_mem a A = mk_var(a,mem_sort A)

val _ = EqSorts := "rel" :: (!EqSorts)
val _ = EqSorts := "mem" :: (!EqSorts)


val _ = new_sort "fun" [("A",mk_sort "set" []),("B",mk_sort "set" [])]
val _ = new_sort_infix "fun" "->"

fun fun_sort A B = mk_sort "fun" [A,B]
fun mk_func f A B = mk_var(f,fun_sort A B)
val _ = EqSorts := "fun" :: (!EqSorts)


datatype thm = thm of ((string * sort) set * form list * form) 
datatype thm_view = vThm of ((string * sort) set * form list * form) 

fun view_thm (thm(G,A,C)) = vThm (G,A,C)

fun dest_thm (thm(G,A,C)) = (G,A,C)

fun mk_thm (G,A,C) = thm(G,A,C)

fun mk_fth f = thm(fvf f,[],f)

fun ant (thm(_,A,_)) = A

fun concl (thm(_,_,C)) = C 

fun cont (thm(G,_,_)) = G

fun eq_thm th1 th2 = 
    HOLset.equal(cont th1,cont th2) andalso
    eq_forml (ant th1) (ant th2) andalso
    eq_form (concl th1, concl th2)

(**********************************************************************

A, Γ |- C
-------------------- inst_thm env
A', Γ' |- C'

A',C' is obtained by pluging in variables recorded in env
Γ' is obtained by collecting all variables in substituted Γ.

**********************************************************************)



fun inst_thm env th = 
    if is_wfmenv env then
        let
            val G0 = HOLset.listItems (cont th)
            val G = var_bigunion (List.map (fvt o (inst_term (vd_of env)) o mk_var) G0)
            val A = List.map (inst_form env) (ant th)
            val C = inst_form env (concl th)
           (* val _ = HOLset.isSubset(HOLset.union(fvfl A,fvf C),G) orelse raise simple_fail "extra variable caused by inst_thm"*)
            val G1 = HOLset.union(G,fvfl (C :: A))
        in
            thm(G1,A,C)
        end
    else raise simple_fail "bad environment"

fun asml_U (asml:(form list) list) = 
    case asml of 
        [] => []
      | h :: t => op_union (curry eq_form) h (asml_U t)

fun contl_U contl = 
    case contl of 
        [] => HOLset.empty (pair_compare String.compare sort_compare)
      | h :: t => HOLset.union(h,contl_U t)

(*primitive inference rules*)

fun assume f = thm (fvf f,[f],f)

fun conjI (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    thm (contl_U [G1,G2],asml_U [A1,A2],mk_conj C1 C2)
   
fun conjE1 (thm(G,A,C)) = 
    let 
        val (C1,_) = dest_conj C
    in 
        thm (G,A,C1)
    end

fun conjE2 (thm(G,A,C)) = 
    let 
        val (_,C2) = dest_conj C
    in 
        thm (G,A,C2)
    end

fun disjI1 f (thm (G,A,C)) = thm (contl_U[G,fvf f],A,mk_disj C f)

fun disjI2 f (thm (G,A,C)) = thm (contl_U[G,fvf f],A,mk_disj f C)

(**********************************************************************

A |- t1 \/ t2 ,   A1,t1 |- t ,   A2,t2|- t
-------------------------------------------------- disjE
A u A1 u A2 |- t

**********************************************************************)

fun disjE th1 th2 th3 = 
    let val (A,B) = dest_disj(concl th1)
        val _ = eq_form(concl th2, concl th3)
                orelse raise ERR ("disjE.conclsions of th#2, th#3 not equal",[],[],[concl th2,concl th3])
        val _ = fmem A (ant th2) orelse
                raise ERR ("disjE.first disjunct not in the formula list: ",
                           [],[],[A])
        val _ = fmem B (ant th3) orelse
                raise ERR ("disjE.second disjunct not in the formula list: ",
                           [],[],[B])
    in
        thm(contl_U [cont th1,cont th2, cont th3],asml_U [ant th1,ril A (ant th2),ril B (ant th3)],
            concl th3)
    end


fun thml_eq_pairs (th:thm,(ll,rl,asml)) = 
    if is_eq (concl th) then  
        let 
            val (l,r) = dest_eq (concl th)
            val asm = ant th
        in 
            (l::ll,r::rl,asml_U [asm,asml])
        end
    else 
        raise ERR ("thml_eq_pairs.input thm is not an equality: ",
                   [],[],[concl th])

fun EQ_fsym f thml = 
    case lookup_fun (!fsyms) f of 
        NONE => raise simple_fail ("EQ_fsym.function: " ^ f ^ " is not found")
      | SOME(s,l) => 
        let 
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in
            thm (contl_U (List.map cont thml),asml,
                 mk_eq (mk_fun f ll) (mk_fun f rl))
        end



                
fun EQ_psym p thml = 
    case lookup_pred (!psyms) p of 
        NONE => if p = "=" then 
                    let 
                        val sl = List.map (fst o dest_eq o concl) thml
                        val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
                        fun mkeq l = case l of [t1,t2] => mk_eq t1 t2
                                             | _ =>  raise ERR ("EQ_psym.mkeq.not a 2-item list",[],l,[])
                    in 
                        thm (contl_U (List.map cont thml),asml,
                             mk_dimp (mkeq ll) (mkeq rl))
                    end
                else raise simple_fail ("EQ_psym.predicate: " ^ p ^ " is not found")
      | SOME l => 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in 
            thm (contl_U (List.map cont thml),asml,
                 mk_dimp (mk_pred p ll) (mk_pred p rl))
        end



              
fun EQ_psym p thml = 
    if p = "=" then 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
            fun mkeq l = case l of [t1,t2] => mk_eq t1 t2
                                 | _ =>  raise ERR ("EQ_psym.mkeq.not a 2-item list",[],l,[])
        in 
            thm (contl_U (List.map cont thml),asml,
                 mk_dimp (mkeq ll) (mkeq rl))
        end
    else 
        let val sl = List.map (fst o dest_eq o concl) thml
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in case lookup_pred (!psyms) p of 
               SOME _ => 
               thm (contl_U (List.map cont thml),asml,
                    mk_dimp (mk_pred p ll) (mk_pred p rl))
             | _ => thm (contl_U (List.map cont thml),asml,
                    mk_dimp (mk_fvar p ll) (mk_fvar p rl))
        end





fun tautI f = thm(fvf f,[],mk_disj f (mk_neg f))

(*TODO find all drule that use it and take tautI out!!!!!!!\
 add an axiom instead.
*)

fun negI f (thm (G,A,C)) = 
    let 
        val _ = eq_form(C,FALSE) orelse 
                raise ERR ("negI.concl of thm is not FALSE",
                          [],[],[C])
        val _ = fmem f A orelse
                raise ERR ("negI.formula to be negated not in the asl",
                           [],[],[f])
    in
        thm (G,ril f A, mk_neg f)
    end

fun negE (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let 
        val _ = eq_form(C2,mk_neg C1) orelse 
                raise ERR ("negE.not a pair of contradiction",
                           [],[],[C1,C2])
    in
        thm (contl_U [G1,G2],asml_U [A1,A2],FALSE)
    end

fun falseE fl f = 
    let val _ = fmem FALSE fl orelse 
                raise simple_fail "falseE.FALSE is not in the asl"
    in
        thm(fvfl (f::fl),fl,f)
    end

        
fun trueI A = thm (fvfl A,A,TRUE)

fun dimpI (thm (G1,A1,I1)) (thm (G2,A2,I2)) =
    let 
        val (f1,f2) = dest_imp I1
        val (f3,f4) = dest_imp I2
        val _ = eq_form(f1,f4) andalso eq_form(f2,f3) orelse
                raise ERR ("dimpI.no match",
                           [],[],[I1,I2])
    in
        thm (contl_U[G1,G2],asml_U[A1,A2],mk_dimp f1 f2)
    end

fun dimpE (thm(G,A,C)) = 
    let
        val (f1,f2) = dest_dimp C
    in
        thm(G,A,mk_conj (mk_imp f1 f2) (mk_imp f2 f1))
    end

fun depends_on (n,s) t = HOLset.member(fvt t,(n,s))

fun allI (ns as (a,s)) (thm(G,A,C)) = 
    let 
        val G0 = HOLset.delete(G,ns) 
                 handle _ => G
        val D0 = HOLset.listItems $ HOLset.difference(fvs s,G0) (*HOLset.numItems gives size of set, can merge in the variable into G0 and remove this check*)
        val _ = List.length D0 = 0 orelse
                raise ERR ("sort of the variable to be abstract has extra variable(s)",[],List.map mk_var D0,[])  
        val _ = case HOLset.find
                         (fn (n0,s0) => depends_on ns (mk_var (n0,s0))) G0 of 
                    NONE => ()
                  | SOME _ => 
                    raise simple_fail
                          "variable to be abstract occurs in context" 
        val _ = not (HOLset.member(fvfl A,ns)) orelse 
                raise simple_fail "variable to be abstract occurs in assumption" 
    in thm(G0,A,mk_forall a s C)
    end


(**********************************************************************

A,Γ |- !x:s. ϕ(x),  |=_s t: s
---------------------------------------- allE, requires sort of t is s
A,Γ u (Var(t)) |- ϕ(t)


rastt "Pr(f:X->A,g:X->B)" 

 "*" 

|=_s A:ob  |=_s B:ob
-----
|=_s A * B: ob

a1: S1....an:Sn /\ A1 /\ ... /\ Am ==> !x. x:s ==> phi(x)
------------------------ 
a1: S1....an:Sn /\ A1 /\ ... /\ Am ==> ... & t:s ==> phi(t)

f:A->B f:C->D

ar




**********************************************************************)

fun allE t (thm(G,A,C)) = 
    let 
        val (ns as (n,s),b) = dest_forall C
        val _ = sort_of t = s orelse 
                raise ERR ("allE.sorts inconsistent",
                           [s,sort_of t],[mk_var(n,s),t],[])
    in
        thm(contl_U [G,fvt t],A,substf (ns,t) b)
    end

(**********************************************************************

A,Γ |- f[t/Var(a,s)]
------------------------------ existsI, require sort_of t = s, Var(t) ⊆ Γ
A,Γ |- ?a: s. f

Note: by induction, already have Var(s), Var(t) is subset of G? No, say 
when we want ?a:ob. TRUE from empty cont and assum list.

**********************************************************************)

fun existsI (a,s) t f (thm(G,A,C)) = 
    let 
        val _ = HOLset.isSubset(fvt t,G)
        val _ = sort_of t = s orelse 
                raise simple_fail"term and variable to be abstract of different sorts"
        val _ = eq_form (C, substf ((a,s),t) f) orelse
                raise ERR ("existsI.formula has the wrong form, should be something else: ",
                           [],[],[C,substf ((a,s),t) f])
    in
        thm(G,A,mk_exists a s (abstract (a,s) f))
    end


(**********************************************************************

X, Γ1 |- ?x. ϕ(x)        Y, ϕ(a),Γ2 ∪ {a:s0} |- B
-------------------------------------------------- existsE, requires a not in Y and not in B
X,Y, Γ1 ∪ Γ2 |- B

**********************************************************************)

local
    fun delete'(s,e) = HOLset.delete(s,e) handle _ => s 
in
fun existsE (a,s0) (thm(G1,A1,C1)) (thm(G2,A2,C2)) =
    let 
        val ((n,s),b) = dest_exists C1
        val _ = fmem (substf ((n,s),mk_var(a,s0)) b) A2
        val _ = s = s0 orelse 
                raise ERR ("the given variable has unexpected sort, should have another sort",[s,s0],[],[])
        val _ = (HOLset.member
                     (HOLset.union
                          (fvfl (ril (substf ((n,s),mk_var(a,s0)) b) A2),
                           fvf C2),(a,s0)) = false) orelse
                raise simple_fail "the given variable occurs unexpectedly"
    in
        thm(contl_U[G1,delete'(G2,(a,s0))],
            asml_U[A1,(ril (substf ((n,s),mk_var(a,s0)) b) A2)],C2)
    end
end

(**********************************************************************

input (?!a. ϕ(a))

phi a

fvf phi,[] |- (?!a. ϕ(a)) <=> ?a. ϕ(a) & !a'. ϕ(a') ==> a' = a

**********************************************************************)


fun uex_def f = 
    case view_form f of
        vQ("?!",n,s,b) => 
        let val n' = fst o dest_var o (pvariantt (fvf b)) $ mk_var(n^"'",s)
                                                          (*n ^ "'"*)
            val phia' = substf((n,s),mk_var(n',s)) b
            val impf = mk_imp phia' (mk_eq (mk_var(n',s)) (mk_var(n,s)))
            val allimpf = mk_forall n' s impf
            val rhs = mk_exists n s (mk_conj b allimpf)
        in
            mk_thm(fvf f,[],mk_dimp f rhs)
        end
      | _ => raise ERR ("uex_def.input is not a unique existence",[],[],[f])



fun refl t = thm (fvt t,[],mk_eq t t) 

fun sym th = 
    if is_eq (concl th) then 
        let 
            val (l,r) = dest_eq (concl th)
        in thm(cont th,ant th,mk_eq r l)
        end
    else raise ERR ("sym.not an equality: ",[],[],[concl th])

fun trans th1 th2 = 
    let 
        val _ = is_eq (concl th1) orelse 
                raise ERR ("trans.first thm not an equality: ",[],[],[concl th1])
        val _ = is_eq (concl th2) orelse
                raise ERR ("trans.second thm not an equality: ",[],[],[concl th2])
        val (t1,t2) = dest_eq (concl th1)
        val (t3,t4) = dest_eq (concl th2)
        val _ = t2 = t3 orelse
                raise ERR ("trans.equalities do not match",[],[],[concl th1,concl th2])
    in 
        thm(contl_U[cont th1,cont th2],
            asml_U[ant th1,ant th2],mk_eq t1 t4)
    end


(**********************************************************************

A, f1, Γ |- f2
-------------------- disch f1
A, Γ u Var(f1) |- f1 ==> f2

Note: do not require f1 in assumption, if not, add its variables into the context.

**********************************************************************)

fun disch f1 (thm(G,A,f2)) =
        thm (HOLset.union(G,fvf f1),ril f1 A,mk_imp f1 f2)

(**********************************************************************

A1, Γ1 |- A ==> B           A2, Γ2|- A
---------------------------------------- mp
A1 u A2, Γ1 u Γ2 |- B

**********************************************************************)


fun mp (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let
        val (A,B) = dest_imp C1
        val _ = eq_form(C2,A) orelse 
                raise ERR ("mp.no match",[],[],[C1,C2])
    in
        thm (contl_U [G1,G2],asml_U[A1,A2],B) 
    end


(**********************************************************************

A, Γ |- B
-------------------- add_cont Γ'
A, Γ u Γ' |- B

**********************************************************************)

fun add_cont nss th = thm(HOLset.union(cont th,nss),ant th,concl th)

fun check_wffv fvs = 
    case fvs of 
        [] => true
      | h :: t => if ill_formed_fv h then
                      raise ERR ("ill-formed free variable",[snd h],[mk_var h],[])
                  else check_wffv t

fun wffv_ok f = check_wffv (HOLset.listItems (fvf f))

fun new_ax f = 
    let
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end



fun mk_foralls nsl f = 
    case nsl of 
        [] => f
      | (h as (n,s)) :: t =>
        mk_forall n s (mk_foralls t f)





fun new_ax f = 
    let
        val _ = HOLset.equal(fvf f,essps) orelse
                raise simple_fail"formula has free variables"
    in
        mk_thm(essps,[],f)
    end







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


val _ = new_pred "Holds" [("R",rel_sort (mk_set "A") (mk_set "B")),
                         ("a",mem_sort (mk_set "A")),
                         ("b",mem_sort (mk_set "B"))]


(*
val AX1 = store_ax("AX1",
“!A B:set.?!R:A~>B.!a:mem(A) b:mem(B).Holds(R,a,b)<=> P(A,B,a,b)”);

fVar_Inst_f ("P",([sA,sB,ma,mb], Qf)) f

“!A B.?!R:A~>B.!a:mem(A) b:mem(B). P(A,B,a,b)” 
|> fVar_Inst_f0 [] ("P",([("A",set_sort),("B",set_sort),
("a",mem_sort (mk_set "A")),("b",mem_sort (mk_set "B"))],
            “?R1.Holds(R1:A~>B,a:mem(A),b:mem(B))” ))
*)




val vX = ("X",set_sort);
val vY = ("Y",set_sort);
val vx = ("x",mem_sort (mk_set "X"));
val vy = ("y",mem_sort (mk_set "Y"));
val vR = ("R",rel_sort (mk_set "X") (mk_set "Y"))

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
            $ mk_uex "R" (rel_sort (mk_set "A") (mk_set "B")) f0

val rR1 = ("R1",rel_sort (mk_set "A") (mk_set "B"))

val Qf = mk_exists "R1" (rel_sort (mk_set "A") (mk_set "B"))
 $ mk_pred "Holds" [mk_var rR1, mk_var ma,mk_var mb]


val f' = mk_forall "A" set_sort
         $ mk_forall "B" set_sort 
            $ mk_forall "a" (mem_sort (mk_var sA))
               $ mk_forall "b" (mem_sort (mk_var sB)) P1



val f'' = mk_forall "B" set_sort 
            $ mk_forall "a" (mem_sort (mk_var sA))
               $ mk_forall "b" (mem_sort (mk_var sB)) P1


val AX1 = mk_thm (essps ,[], f)

fVar_Inst_f ("P",([sA,sB,ma,mb], Qf)) f

fVar_Inst_f ("P",([sA,sB,ma,mb], Qf)) f'

fVar_Inst_f0 [] ("P",([sA,sB,ma,mb], Qf)) f' (* = *)

val n = "A"; val s = set_sort;
val b = Quant
      ("!", "B", srt ("set", []),
       Quant
        ("!", "a", srt ("mem", [Bound 1]),
         Quant
          ("!", "b", srt ("mem", [Bound 1]),
           Pred ("P", false, [Bound 3, Bound 2, Bound 1, Bound 0]))))

val bs = [];
fVar_Inst_f0 ((recover_s 1 s) :: bs)
("P",([sA,sB,ma,mb], Qf)) b (*prblmtc*)


val bs = [set_sort] 

val s = set_sort 

val b' = Quant
      ("!", "a", srt ("mem", [Bound 1]),
       Quant
        ("!", "b", srt ("mem", [Bound 1]),
         Pred ("P", false, [Bound 3, Bound 2, Bound 1, Bound 0])))

fVar_Inst_f0 ((recover_s 1 s) :: bs)
("P",([sA,sB,ma,mb], Qf)) b' (*prblmtc*)



val bs = [set_sort,set_sort] 

val s = srt ("mem", [Bound 1])

val b'' = 
       Quant
        ("!", "b", srt ("mem", [Bound 1]),
         Pred ("P", false, [Bound 3, Bound 2, Bound 1, Bound 0]))

fVar_Inst_f0 ((recover_s 1 s) :: bs)
("P",([sA,sB,ma,mb], Qf)) b'' (*prblmtc*)



val bs = [srt ("mem", [Bound 2]),set_sort,set_sort] 

val s = srt ("mem", [Bound 1])

val b''' = 
       
         Pred ("P", false, [Bound 3, Bound 2, Bound 1, Bound 0])

fVar_Inst_f0  [srt ("mem", [Bound 2]),srt ("mem", [Bound 3]),set_sort,set_sort] 
("P",([sA,sB,ma,mb], Qf)) b''' (*prblmtc*)

()



fVar_Inst_P ((recover_s 1 s) :: bs)
("P",([sA,sB,ma,mb], Qf)) b''' (*prblmtc*)


val bs = 

HOLset.listItems (cont (fVar_Inst_th ("P",([sA,sB,ma,mb], Qf)) AX1))



(*attempt of finding MWE*)

val f = mk_forall "A" set_sort (mk_fvar "P" [mk_set "A"]);
val Q = mk_exists "B" set_sort (mk_fvar "Q" [mk_set "A",mk_set "B"]); 

fVar_Inst_f ("P",([("A",set_sort)], Q)) f

(******************************************************************************************)
 
fun define_psym (pname,vl) f = 
    let 
        val _ = case lookup_pred (!psyms) pname of
                    NONE => ()
                  | _ => raise simple_fail 
                               ("predicate with name: "^ pname ^ " already exists")
        val _ = new_pred pname vl
        val pfm = mk_pred pname (List.map mk_var vl)
        val fm = mk_dimp pfm f
        val _ = HOLset.isSubset(fvf f,fvf pfm) orelse 
                raise simple_fail "define_psym.input contains extra variable(s)"
        val ct = fvf fm
    in mk_thm (ct,[],fm)
    end


fun mk_foralls vl f = 
    case vl of [] => f 
             | h :: t => uncurry mk_forall h (mk_foralls t f)



fun mk_tinst l = mk_inst l [] 

fun addprims l = 
            case l of [] => l
                    | (n,s) :: t =>
                      let val new = (n^"'",s)
                      in
                          new :: 
                          (List.map 
                               (dest_var o 
                                (substt ((n,s),mk_var new)) o mk_var) (addprims t))
                      end

fun mk_existss nsl f = 
    case nsl of 
        [] => f
      | (h as (n,s)) :: t =>
        mk_exists n s (mk_existss t f)

fun dest_n_exists n f = 
    if n = 0 then ([],f) else 
    let val (l,b) = dest_n_exists (n-1) f
        val (ns,b1) = dest_exists b
    in (l @ [ns],b1)
    end

fun mk_REFL_condf (arg1:(string * sort) list,
                  arg2:(string * sort) list,eqr) = 
    let
        val argtrefl = List.map mk_var arg1
        val reflbody = 
            inst_form (mk_tinst (zip arg2 argtrefl)) eqr
        val reflcl = mk_foralls arg1 reflbody
    in reflcl
    end


fun mk_SYM_condf (arg1:(string * sort) list,
                  arg2:(string * sort) list,eqr) = 
    let
        val (symt1,symt2) = (List.map mk_var arg1,
                             List.map mk_var arg2)
       val symconc = 
            inst_form
            (mk_tinst((zip arg1 symt2) @ (zip arg2 symt1)))
            eqr
        val symbody = 
            mk_imp eqr symconc
        val symcl = mk_foralls (arg1 @ arg2) symbody    
    in symcl
    end
 
fun mk_TRANS_condf (arg1:(string * sort) list,
                    arg2:(string * sort) list,eqr) = 
    let
        val arg3 = addprims arg2
        val (transt1,transt2,transt3) =
            (List.map mk_var arg1,
             List.map mk_var arg2,
             List.map mk_var arg3)
        val transant2 = 
            inst_form
            (mk_tinst((zip arg1 transt2) @ (zip arg2 transt3)))
            eqr
        val transconc = 
            inst_form
            (mk_tinst((zip arg1 transt1) @ (zip arg2 transt3)))
            eqr
        val transbody = mk_imp (mk_conj eqr transant2)
                               transconc
        val transcl = mk_foralls (arg1 @ arg2 @ arg3)
                                 transbody
    in transcl
    end 
 
fun mk_ER_condf argseqr = 
    let val reflcl = mk_REFL_condf argseqr
        val symcl = mk_SYM_condf argseqr
        val transcl = mk_TRANS_condf argseqr
        val eqvcls = mk_conj reflcl (mk_conj symcl transcl)
    in eqvcls
    end 

(*val argseqr = arg12eqr 
  val reflth = coPr_REFL
  val symth = coPr_SYM
  val transth = coPr_TRANS
*)
fun check_REFL argseqr reflth =
    let val reflcl = mk_REFL_condf argseqr 
        val _ = eq_form (reflcl,concl reflth)
    in ()
    end


fun check_SYM argseqr symth =
    let val symcl = mk_SYM_condf argseqr 
        val _ = eq_form (symcl,concl symth)
    in ()
    end


fun check_TRANS argseqr transth =
    let val transcl = mk_TRANS_condf argseqr 
        val _ = eq_form (transcl,concl transth)
    in ()
    end


fun check_ER argseqr eqvth uexth = 
    let val eqvcls = mk_ER_condf argseqr
        val _ = eq_form (eqvcls,concl eqvth) orelse
                raise simple_fail "newspec.eqvth concl"
        val _ = HOLset.isSubset(cont eqvth,cont uexth) orelse
                raise simple_fail "newspec.eqvth cont"
        val _ = List.all 
                    (fn asm => 
                        List.exists
                            (fn a => eq_form(a,asm)) (ant uexth))
                    (ant eqvth) orelse
                raise simple_fail "newspec.eqvth ant"
(*all the condition that requires to prove the equivalence relation is contained in the existential-up-to-unique theorem*)  
    in ()
    end        

(*take: 1.the body of formula we want to create function symbols for
        2.the equivalence relation and its two arguments.
  produce: the existence of the terms in the body of the formula up to the 
  relation*)

fun mk_uexf (arg:(string * sort) list,Q) 
            (arg1:(string * sort) list,
             arg2:(string * sort) list,eqr) = 
    let
        val maint = List.map mk_var arg
        val mainprimv = addprims arg
        val mainprimt = List.map mk_var mainprimv
        val mainprim = inst_form
            (mk_tinst (zip arg mainprimt)) Q
        val relf = 
            inst_form
            (mk_tinst((zip arg1 maint) @ (zip arg2 mainprimt)))
            eqr
        val cj2ofit = mk_foralls mainprimv 
                      (mk_imp mainprim relf)
        val whole = mk_existss arg (mk_conj Q cj2ofit)
    in
        whole
    end

fun check_uexth argQ arg12eqr uexth = 
    let 
        val whole = mk_uexf argQ arg12eqr
        val _ = eq_form(whole,concl uexth) orelse
                raise simple_fail "newspec.uexth concl"
    in ()
    end

(*check the soundness theorem. to pass the check, require the term to exist once the variables in uexth exist, under no assumption and of correct form.*)

fun check_eth arg eth uexth = 
    let val _ = HOLset.isSubset(cont eth,cont uexth) orelse
                raise simple_fail "newspec.eth has extra variables"
        val _ = eq_forml (ant eth) [] orelse
                raise simple_fail "newspec.eth has assumptions"
        val _ = eq_form(concl eth, mk_existss arg TRUE)
                orelse 
                raise simple_fail "newspec.ill-formed eth"
    in ()
    end

(*check the information contained in inputs is enough*)
fun check_inputs vl vs0 = 
    let 
        val inputvars0 = filter_cont vs0
        val inputvars = List.foldr (fn (s,e) => HOLset.add(e,s)) 
                           essps vl
        val _ = HOLset.isSubset(inputvars0,inputvars) orelse 
                raise simple_fail "there are necessary input variables missing"
    in ()
    end


fun check_no_fVars f = HOLset.equal(fVars f,HOLset.empty String.compare) orelse 
raise ERR ("check_no_fVars. the input has formula variables",[],[],[f])

fun mk_newfsym fnames vl uexth = 
    let val (newspvs,b) = dest_n_exists (length fnames) (concl uexth)
        val (main,impf) = dest_conj b 
        val _ = check_no_fVars main 
        val recoverex = mk_existss newspvs main
        val sts = List.map snd newspvs
        val (ct,asm) = (cont uexth,ant uexth)
        fun itmk fnl sts vl f = 
            case fnl of 
                [] => (fnl,f)
              | h :: t =>
                let val _ = case lookup_fun (!fsyms) (hd fnl) of 
                    NONE => () 
                  | _ => raise simple_fail ("function symbol with name: " ^ (hd fnl) ^ " already exists")
                    val _ = new_fun (hd fnl) (hd sts,vl)
                    val ft = mk_fun (hd fnl) (List.map mk_var vl)
                    val (ns,b) = dest_exists f
                    val f0 = substf (ns,ft) b
                    val sts' = List.map (substs (ns,ft)) sts
                in itmk (tl fnl) (tl sts') vl f0
                end 
(*
        fun itmk fnl sts vl f = (*List.foldl  *)
            case fnl of 
                [] => (fnl,f)
              | h :: t =>
                let val _ = new_fun (hd fnl) (hd sts,vl)
                    val ft = mk_fun (hd fnl) (List.map mk_var vl)
                    val (ns,b) = dest_exists f
                    val f0 = substf (ns,ft) b
                in itmk (tl fnl) (tl sts) vl f0
                end *)
        val (_,conc) = itmk fnames sts vl recoverex
    in
        mk_thm(ct,asm,conc)
    end

fun new_spec argQ arg12eqr
             fnames vl eth eqvth uexth = 
    let val _ = check_ER arg12eqr eqvth uexth 
        val _ = check_uexth argQ arg12eqr uexth
        val arg = #1 argQ
        val _ = check_eth arg eth uexth
        val vs0 = cont uexth
        val _ = check_inputs vl vs0
    in mk_newfsym fnames vl uexth
    end


val funeqeqvth = proved_th $
e0
(rpt strip_tac >> arw[])
(form_goal “∀A B. (!i:A->B. i = i) &
 (!i:A->B i':A->B. i = i' ==> i' = i) &
 (!i:A->B i':A->B i'':A->B. 
   i = i' & i' = i'' ==> i = i'')”)


val releqeqvth = proved_th $
e0
(rpt strip_tac >> arw[])
(form_goal “∀A B. (!i:A~>B. i = i) &
 (!i:A~>B i':A~>B. i = i' ==> i' = i) &
 (!i:A~>B i':A~>B i'':A~>B. 
   i = i' & i' = i'' ==> i = i'')”)


val memeqeqvth = proved_th $
e0
(rpt strip_tac >> arw[])
(form_goal “∀A. (!i:mem(A). i = i) &
 (!i:mem(A) i':mem(A). i = i' ==> i' = i) &
 (!i:mem(A) i':mem(A) i'':mem(A). 
   i = i' & i' = i'' ==> i = i'')”)



fun uex_spec fname vl eth uexth0 = 
    let 
        val ((_,st),_) = dest_uex (concl uexth0)
        val stn = st |> dest_sort |> #1
        val dependson = st |> dest_sort |> #2 
        val eqvth = if stn = "mem" then memeqeqvth |> specl dependson else 
                    if stn = "fun" then funeqeqvth |> specl dependson else
                    if stn = "rel" then releqeqvth |> specl dependson else
                    raise simple_fail "uex_spec.ill-formed sort"
        val uexth = uex_expand' uexth0
        val (arg,Q) = dest_uex (concl uexth0)
        val argQ = ([arg],Q)
        val arg' = dest_var (pvariantt (fvf Q) (mk_var arg)) 
        val equality = mk_eq (mk_var arg) (mk_var arg') 
        val arg12eqr = ([arg],[arg'],equality) 
    in new_spec argQ arg12eqr [fname] vl eth eqvth uexth
    end

fun quex_spec fname qvl eth uexth0 = 
    let val tl = List.map (qparse_term_with_cont (cont uexth0)) qvl 
        val vl = List.map dest_var tl
    in uex_spec fname vl eth uexth0
    end

fun simple_uex_spec fname vl uexth0 = 
    let val uexth = uex_expand' uexth0
        val eth0 = ex_P_ex (concl uexth)
        val eth = mp eth0 uexth
    in uex_spec fname vl eth uexth0 
    end


fun qsimple_uex_spec fname qvl uexth0 = 
    let val tl = List.map (qparse_term_with_cont (cont uexth0)) qvl 
        val vl = List.map dest_var tl
    in simple_uex_spec fname vl uexth0
    end


val define_fsym_lemma_mem = proved_th $
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘newfsym0’ >> rw[])
(form_goal “!A newfsym0:mem(A). 
 ?!newfsym. newfsym = newfsym0”)


val define_fsym_lemma_fun = proved_th $
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘newfsym0’ >> rw[])
(form_goal “!A B newfsym0:A->B. 
 ?!newfsym. newfsym = newfsym0”)


val define_fsym_lemma_rel = proved_th $
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘newfsym0’ >> rw[])
(form_goal “!A B newfsym0:A~>B. 
 ?!newfsym. newfsym = newfsym0”)






fun define_fsym (fname,vl) t = 
    let val st = sort_of t
        (*val _ = new_fun fname (st, vl) *)
        (*val ft = mk_fun fname (List.map mk_var vl)*)
        (*check vl is subset of vars in t*)
        val inputvset = List.foldr
                            (fn(a,s) => HOLset.union(s,fvt (mk_var a))) essps vl
        val _ = HOLset.isSubset(fvt t,inputvset) orelse 
                raise simple_fail "define_fsym.input contains extra variable(s)"
        val stn = st |> dest_sort |> #1
        val th = if stn = "mem" then define_fsym_lemma_mem |> sspecl [t] else 
                 if stn = "fun" then define_fsym_lemma_fun |> sspecl [t] else
                 if stn = "rel" then define_fsym_lemma_rel |> sspecl [t] else
                    raise simple_fail "uex_spec.ill-formed sort"
    in simple_uex_spec fname vl th
    end


fun qdefine_fsym (fname,ql) qt = let val tl = List.map
    (qparse_term_with_cont essps) ql val ct0 = fvtl tl val t =
    qparse_term_with_cont ct0 qt val vl = List.map dest_var tl in
    define_fsym (fname,vl) t end
