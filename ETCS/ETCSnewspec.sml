
val areqeqvth = proved_th $
e0
(rpt strip_tac >> arw[])
(form_goal “∀A B. (!i:A->B. i = i) &
 (!i:A->B i':A->B. i = i' ==> i' = i) &
 (!i:A->B i':A->B i'':A->B. 
   i = i' & i' = i'' ==> i = i'')”)




fun uex_spec fname vl eth uexth0 = 
    let 
        val ((_,st),_) = dest_uex (concl uexth0)
        val stn = st |> dest_sort |> #1
        val dependson = st |> dest_sort |> #2 
        val eqvth = if stn = "ar" then areqeqvth |> specl dependson else
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


val define_fsym_lemma = proved_th $
e0
(rpt strip_tac >> uex_tac >>
 qexists_tac ‘newfsym0’ >> rw[])
(form_goal “!A B newfsym0:A->B. 
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
        val th = sspecl [t] define_fsym_lemma
    in simple_uex_spec fname vl th
    end


fun qdefine_fsym (fname,ql) qt = let val tl = List.map
    (qparse_term_with_cont essps) ql val ct0 = fvtl tl val t =
    qparse_term_with_cont ct0 qt val vl = List.map dest_var tl in
    define_fsym (fname,vl) t end

(*
val (fname,ql) = ("FALSE",[]); 
val qt = ‘i1(1,1)’
*)
