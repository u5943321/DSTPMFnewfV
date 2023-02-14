
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
