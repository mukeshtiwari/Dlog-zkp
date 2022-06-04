Require Import Coq.Classes.Morphisms
  Coq.micromega.Lia Sigma.Algebra.Hierarchy
  Sigma.Algebra.Monoid Sigma.Algebra.Group
  Sigma.Algebra.Ring.
Require Coq.setoid_ring.Integral_domain
  Coq.setoid_ring.Ncring Coq.setoid_ring.Cring.

(* https://github.com/coq/coq/blob/master/theories/setoid_ring/Integral_domain.v *)
Section IntegralDomain.

  Context 
    {T eq zero one opp add sub mul}
    {Hi:@integral_domain T eq zero one opp add sub mul}.

  Lemma nonzero_product_iff_nonzero_factors :
      forall x y : T, 
      ~eq (mul x y) zero <-> ~eq x zero /\ ~eq y zero.
  Proof.
    setoid_rewrite ring_zero_product_iff_zero_factor.
    intuition.
  Qed.

  
  (* This is from the Coq library *)
  Global Instance Intdom :
    @Integral_domain.Integral_domain 
      T zero one add mul sub opp eq _ _ _. 
  Proof.
    split. 
    apply zero_product_zero_factor.
    apply one_neq_zero.
  Defined.

End IntegralDomain.












