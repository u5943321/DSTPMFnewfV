fun aimp_rule th =
    let
      val (l, r) = dest_imp (concl th)
      val (c1, c2) = dest_conj l
      val cth = conjI (assume c1) (assume c2)
    in
      disch c1 (disch c2 (mp th cth))
    end




fun norm th =
    if is_forall (concl th) then norm (spec_all th)
    else
      case total dest_imp (concl th) of
          NONE => th
        | SOME (l,r) =>
          if is_conj l then norm (aimp_rule th)
          else norm (undisch th)

fun overlaps fvset (tfvs,_) =
      not (HOLset.isEmpty (HOLset.intersection(fvset, tfvs)))

fun union ((fvset1, tlist1), (fvset2, tlist2)) =
      (HOLset.union(fvset1, fvset2), tlist1 @ tlist2)

fun recurse gfvs acc tlist =
      case tlist of
          [] => acc
        | t::ts =>
          let
            val tfvs = HOLset.difference(fvf t, gfvs)
          in
            case List.partition (overlaps tfvs) acc of
                ([], _) => recurse gfvs ((tfvs,[t])::acc) ts
              | (ovlaps, rest) =>
                recurse gfvs (List.foldl union (tfvs, [t]) ovlaps :: rest) ts
          end

fun group_hyps gfvs tlist = recurse gfvs [] tlist

fun foldthis ((n,s),(t,th)) =
      let val ext = mk_exists n s t
      in
        (ext, existsE (n,s) (assume ext) th)
      end






val conjuncts =
   let
      fun aux acc th =
         aux (aux acc (conjE2 th)) (conjE1 th)
         handle _ => th :: acc
   in
      aux []
   end

(*to get consistent order, foldl, or rev and take hd and tl, then foldr
current gives 
 ["P(a)","P(b)","P(c)"] |-> P(c) & (P(b) & P(a))
*)
fun list_mk_conj fl = List.foldl (uncurry mk_conj) (List.hd fl) (List.tl fl)



fun conjl ts th = let
  val c = list_mk_conj ts
  val cths = conjuncts (assume c)
in
  (List.foldl (fn (c,th) => prove_hyp c th) th cths, c)
end



fun form_list_diff l1 l2 = 
    case l1 of 
        [] => []
      | h :: t => if fmem h l2 then form_list_diff t l2 else h :: form_list_diff t l2



open SymGraph


fun edges_from_fvs1 (n:string,s:sort) l = 
    case l of [] => []
            | h :: t => 
              if depends_t (n,s) (mk_var h) then 
                  ((n,s),h) :: edges_from_fvs1 (n,s) t
              else edges_from_fvs1 (n,s) t

fun edges_from_fvs0 nss = 
    let val l = HOLset.listItems nss
    in List.foldr 
           (fn (ns,l0) => (edges_from_fvs1 ns l) @ l0) [] l 
    end



fun edges_from_fvs nss = 
    List.filter (fn ((n1,s1),(n2,s2)) => n1 <> n2 orelse not $ (*eq_sort(s1,s2)*) s1 = s2) (edges_from_fvs0 nss)


fun order_of_fvs f = 
    let val nss = fvf f
        val g0 = HOLset.foldr (fn ((n,s),g) => new_node (n,s) g) empty nss
        val g = List.foldr (fn (((n1,_),(n2,_)),g) => 
                               add_edge (n1,n2) g) g0 (edges_from_fvs nss)
    in topological_order g
    end

fun order_of nss = 
    let 
        val g0 = HOLset.foldr (fn ((n,s),g) => new_node (n,s) g) empty nss
        val g = List.foldr (fn (((n1,_),(n2,_)),g) => 
                               add_edge (n1,n2) g) g0 (edges_from_fvs nss)
    in topological_order g
    end

fun abstl l th = 
    case l of 
        [] => th
      | (n,s) :: t => allI (n,s) (abstl t th)

fun find_var l n = 
    case l of 
        [] => raise simple_fail"variable name not found"
      | h :: t => 
        if fst h = n then h 
        else find_var t n

fun genl vsl th = 
    let
        val ovs = order_of ((foldr (uncurry (C (curry HOLset.add)))) essps vsl)
        val vl = List.map (find_var vsl) ovs
    in 
        abstl vl th
    end

fun choosel' vs t th = 
    let val ovs = order_of ((foldr (uncurry (C (curry HOLset.add)))) essps vs)
        val vl = List.map (find_var vs) ovs
    in List.foldr foldthis (t,th) vl
    end



fun recurse' acc groups th =
      case groups of
          [] => (acc, th)
        | (fvset, ts) :: rest =>
          let
            val (th1,c) = conjl ts th
            val (ext, th2) = choosel' (HOLset.listItems fvset) c th1
          in
            recurse' (ext::acc) rest th2
          end

fun reconstitute' groups th = recurse' [] groups th


(*
fun ir_canon th =
  let
    val th1 = norm (gen_all th)
    val origl = ant th
    val gfvs = fvfl (concl th1 :: origl) 
    val newhyps = form_list_diff (ant th1)  origl
    val grouped = group_hyps gfvs newhyps
    val (cs, th2) = reconstitute' grouped th1
  in
    case cs of
        [] => gen_all th2
      | _ =>
        let
          val (th3,c) = conjl cs th2
        in
          disch c th3 |> gen_all
        end
  end
*)



fun ir_canon th =
  let
    val th1 = norm (gen_all th)
    val origl = ant th
    val gfvs = fvfl (concl th1 :: origl) 
    val newhyps = form_list_diff (ant th1)  origl
    val grouped = group_hyps gfvs newhyps
    val (cs, th2) = reconstitute' grouped th1
  in
    case cs of
        [] => gen_all th2
      | _ =>
        let
          val (th3,c) = conjl (rev cs) th2
        in
          disch c th3 |> gen_all
        end
  end


val irule = match_mp_tac o ir_canon


(*
fun foldthis1 ((n,s),(t,th)) =
      let val ext = mk_exists n s t
      in
        (ext, existsE (n,s) (assume ext) th)
        handle _ => (t,th)
      end


fun choosel1 vs t th = 
    let val ovs = order_of ((foldr (uncurry (C (curry HOLset.add)))) essps vs)
        val vl = List.map (find_var vs) ovs
    in List.foldr foldthis1 (t,th) vl
    end

fun recurse1 acc groups th =
      case groups of
          [] => (acc, th)
        | (fvset, ts) :: rest =>
          let
            val (th1,c) = conjl ts th
            val (ext, th2) = choosel1 (HOLset.listItems fvset) c th1
          in
            recurse1 (ext::acc) rest th2
          end

fun reconstitute1 groups th = recurse1 [] groups th
*)



fun abstl1 l th = 
    case l of 
        [] => th
      | (n,s) :: t => allI (n,s) (abstl1 t th) handle _ => (abstl1 t th)


fun gen_all1 th = 
    let 
        val vs = HOLset.difference
                     (fvf (concl th), fvfl (ant th))
        val vsl = HOLset.listItems vs
        val ovs = order_of vs
        val vl = List.map (find_var vsl) ovs
    in 
        abstl1 vl th
    end

fun forbid_vars f = 
    case view_form f of
        vPred _ => essps
      | vConn (co,fl) => 
        List.foldr (fn (f,s) => HOLset.union(forbid_vars f,s)) essps fl
      | vQ(_,_,_,b) => forbid_vars b
      | vfVar(_,nsl,_) => var_bigunion (List.map (fvs o #2) nsl)

fun forbid_varsl fl = var_bigunion (List.map forbid_vars fl)

fun ir_canon1 th =
  let
    val th1 = norm (gen_all1 th)
    val origl = ant th
    val forbidvars = forbid_varsl (concl th :: ant th)
    val gfvs = HOLset.difference(fvfl (concl th1 :: origl),forbid_varsl ( (concl th :: ant th)))
    val newhyps = form_list_diff (ant th1)  origl
    val grouped = group_hyps gfvs newhyps
    val grouped1 = List.map (fn (s,fl) => (HOLset.difference(s,forbidvars),fl))
                            grouped
    val (cs, th2) = reconstitute' grouped1 th1
  in
    case cs of
        [] => gen_all1 th2
      | _ =>
        let
          val (th3,c) = conjl (rev cs) th2
        in
          disch c th3 |> gen_all1
        end
  end


val irule1 = match_mp_tac o ir_canon1

