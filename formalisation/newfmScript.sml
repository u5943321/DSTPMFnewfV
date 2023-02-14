open HolKernel Parse boolLib bossLib;

val _ = new_theory "newfm";

        
        
     

Theorem cont_is_cont:
∀pf. Pf Σ axs pf ⇒ ∀th. MEM th pf ⇒ is_cont (cont th)
Proof
cheat
QED
 


(*
Theorem insth_cont:
  cont (insth σf σv (Γ,A,f)) =
*)

Theorem NOTIN_genavds:
(n,s) ∉ genavds (G,A,f) ⇔
(∀n0 s0. (n0,s0) ∈ G ⇒ (n,s) ∉ sfv s0) ∧
(∀a. a ∈ A ⇒ (n,s) ∉ ffv a) ∧
(∀P sl s0. (P,sl) ∈ fVars f ∧ MEM s0 sl ⇒ (n,s) ∉ sfv s0)
Proof
cheat
QED
        


  


        (*
Theorem cth_eqiDrv:
is_cth th ⇒ ()      have to be after the main thm  
*)

(*restrict to no fVar fms, PfDrv iff Pf0Drv*)

(*
Definition vinst_fVar_def:
vinst_fVar vσ (P,sl) = (P,MAP (sinst vσ) sl)
End

*)

(*        
Definition vinstfVmap_def:
vinstfVmap vσ fσ =
FUN_FMAP (λ(P,sl). if sl ∈ IMAGE vinst_fVar (FDOM fσ) then
   vinst vσ (fσ ' sl) else ARB)
(IMAGE vinst_fVar (FDOM fσ))
End

Theorem vinst_fVinst:
vinst vσ fVinst fσ f =
fVinst 
*)

        
  
     
Theorem ffv_instf:
∀f.
 ffv f ⊆ FDOM σv ⇒
 ffv (instf σf σv f) ∪ vinst_cont σv (fVslv f) =
 vinst_cont σv (ffv f) ∪
 ofFMAP ffv σf (IMAGE (vinst_fVar σv) (fVars f))
Proof 
 Induct_on ‘f’ >>
 gs[ffv_thm,instf_def,fVinst_def,fVars_def,
 ofFMAP_EMPTY,vinst_cont_EMPTY]
 >- (rw[vinst_cont_def,MEM_MAP,PULL_EXISTS] >>
    rw[ofFMAP_def,PULL_EXISTS] >>
    cheat (*tfv_sinst*))
 >- (rw[] >> gs[]   >>
    rw[vinst_cont_def,ofFMAP_def,Uof_UNION] >>
    gs[SUBSET_DEF,EXTENSION] >>
    rw[ofFMAP_def] >>  metis_tac[])
 >- (rw[] >> gs[] >> rw[vinst_cont_def]  >> (*tfv_sinst*)
    cheat) >>
 rw[] (* 2 *)
 >-
*)




Theorem fVars_finst:
∀f. fVars (finst vσ f) = IMAGE (vinst_fVar vσ) (fVars f)
Proof
Induct_on ‘f’ >> gs[vinst_fVar_def,finst_def,fVars_def]
QED
        
 
 
(*     
Definition fVinsts_def:
  fVar_thprpl σf (ct,asm,f) =
  (ct ∪ ofFMAP ffv σf (Uof fVars ({f} ∪ asm)), 
  IMAGE (fVar_prpl σf) asm,fVar_prpl σf f)
End        
*)

val _ = export_theory();

