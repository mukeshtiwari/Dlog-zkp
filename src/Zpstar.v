Require Import Coq.PArith.PArith 
  Coq.ZArith.ZArith Lia
  Coq.ZArith.Znumtheory
  Eqdep_dec Arith
  Sigma.Functions 
  Zpow_facts.

Module Zp.

  Open Scope N_scope.
  (* multiplicative Group *)
  Section ZpstarGroup. 
    Context 
      {p : N}
      {Hp : prime (Z.of_N p)}.

    
    Record Zpstar := 
      mk_zpstar {v : N; Hv : (0 < v < p)%N}.


    Lemma dec_lt_general : 
      forall x y (Hx Hy: (x < y)%N),  Hx = Hy.
    Proof.
      intros; apply Eqdep_dec.eq_proofs_unicity;
      intros u v; destruct u; destruct v; auto;
      try (right; intro Hpp; inversion Hpp).
    Qed.


    Lemma dec_proof : 
      forall x (Hx Hy : (0 < x < p)%N), Hx = Hy.
    Proof.
      intros ? [Hxl Hxr] [Hyl Hyr];
      f_equal; apply dec_lt_general.
    Qed.


    Lemma dec_p : forall x y : Zpstar, {x = y} + {x <> y}.
    Proof.
      intros [x Hx] [y Hy].
      destruct (N.eq_dec x y) as [Hl | Hr].
      left. subst. f_equal. apply dec_proof.
      right. intro H; inversion H; 
      contradiction.
    Qed.



    (* Neutral Element *)
    Definition one : Zpstar.
      refine (mk_zpstar 1 _).
      pose proof (prime_ge_2 _ Hp).
      abstract nia.
    Defined.

    
    Lemma multiplication_bound : 
      forall au av : N, 
      0 < au < p ->
      0 < av < p ->
      0 < N.modulo (au * av) p < p.
    Proof.
    Admitted.


    
    (* multiplication *)
    Definition mul_zpstar (u v : Zpstar) : Zpstar.
      refine(
        match u, v with 
        | mk_zpstar au Hu, mk_zpstar av Hv => 
          mk_zpstar 
            (N.modulo (au * av) p) 
            (multiplication_bound _ _ Hu Hv)
        end).
    Defined.
  
    Lemma power_bound : 
      forall a : N, 
      0 < a < p -> 
      0 < Npow_mod a (p - 1) p < p.
    Proof.
      (* Npow_mod a (p - 1) p = 1 *)
      intros a Ha. 

    Admitted.
  

    Definition inv_zpstar (u : Zpstar) : Zpstar.
      refine(
        match u with 
        | mk_zpstar au Hu => 
          mk_zpstar (Npow_mod au (p - 1) p) (power_bound au Hu)
        end).
    Defined.
    
    (* Now I need to establish that it's a group *)

    


  End ZpstarGroup.

  (* Prime Field *)
  Section ZpField.

  End ZpField.


  Section VectorSpace.


  End VectorSpace.


End Zp. 
      
  