open HolKernel Parse boolLib bossLib;

val _ = new_theory "Prf";



Inductive Prf0:
[~AX:]
(∀ax. ax ∈ axs ⇒
      Prf0 Σ axs [(ffv ax,ax)]) ∧
[~FalseE1:]
  (∀Γ A pf f.
      Prf0 Σ axs pf ∧
      MEM (Γ,IMP (Neg f) False) pf ⇒
      Prf0 Σ axs (pf ++ [(Γ,f)])) ∧
[~FalseE2:]
  (∀Γ A pf f.
    Prf0 Σ axs pf ∧
    MEM (Γ,IMP f0 False) pf ⇒
    Prf0 Σ axs (pf ++ [(Γ ∪ ffv f,IMP f0 f)])) ∧
[~assume:]
  (∀c:form. Prf0 Σ axs [(ffv c,{c},c)]) ∧
[~mp:]
  (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
     Prf0 Σ axs pf1 ∧ Prf0 Σ axs pf2 ∧
     MEM (Γ1,A1,IMP f1 f2) pf1 ∧
     MEM (Γ2,A2,f1) pf2 ⇒
     Prf0 Σ axs (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2, A1 ∪ A2,f2)])) ∧
[~disch:]
  (∀Γ A pf f a.
     Prf0 Σ axs pf ∧ MEM (Γ,A,f) pf ⇒
     Prf0 Σ axs (pf ++ [(Γ ∪ ffv a,A DELETE a,IMP a f)])) ∧
[~ALLI:]
  (∀Γ A pf f x s.
     Prf0 Σ axs pf ∧ 
     MEM (Γ,A,f) pf ∧
     (sfv s) ⊆ Γ ∧
     (∀n0 s0. (n0,s0) ∈ Γ ⇒ (x,s) ∉ sfv s0) ∧
     (∀a. a ∈ A ⇒ (x,s) ∉ ffv a) ⇒
     Prf0 Σ axs (pf ++ [(Γ DELETE (x,s),A,FALL x s f)])) ∧
[~ALLE:]
  (∀Γ A pf n s f t.
     Prf0 Σ axs pf ∧
     MEM (Γ,A,FALL n s f) pf ∧
     sort_of t = s ⇒
     Prf0 Σ axs (pf ++ [(Γ ∪ tfv t,A,finst (TO_FMAP [((n,s),t)]) f)])) ∧
[~refl:]
  (∀t. 
     Prf0 Σ axs [(tfv t,{},EQ t t)]) ∧
[~sym:]
  (∀Γ A pf t1 t2.
     Prf0 Σ axs pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
     Prf0 Σ axs (pf ++ [(Γ,A,EQ t2 t1)])) ∧
[~trans:]
  (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
     Prf0 Σ axs pf1 ∧ Prf0 Σ axs pf2 ∧
     MEM (Γ1,A1,EQ t1 t2) pf1 ∧ MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
     Prf0 Σ axs (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)]))
End


val _ = export_theory();

