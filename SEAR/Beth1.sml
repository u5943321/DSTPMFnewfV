val AX5_fib = prove_store("AX5_fib",
e0
strip_assume_tac AX5 >>
x_choose_then "Y1" strip_assume_tac
 (Thm_2_4 |> qtinst_thm [(‘A’,‘Y’)]
 |> qfVar_prpl_th1 ("P",[‘y:mem(Y)’],
                    ‘?b. Holds(M:B~>Y,b,y)’)) >>
qexistsl_tac [‘B’,‘p’,‘Y1’] >>



 rpt strip_tac 
(form_goal
 “?B p:B->A Y f:Y->B.  
 (!S i:S->Y b. 
  isset(i,FIB(f,b)) ⇒
  P[a:mem(A),X](App(p,b),S)) & 
 !a:mem(A) X. P[a:mem(A),X](a,X) ==> ?b. App(p,b) = a”));



Theorem AX5_fib
(AX5 |> qtinst_thm [(‘A’,‘N’)] 
 |> qfVar_prpl_th1 ("P",[‘n:mem(N)’,‘X’],‘?p:X->N R:X~>X z:N ->X. Upows(n,p,R,z)’))
