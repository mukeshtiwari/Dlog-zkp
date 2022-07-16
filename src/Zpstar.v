Require Import Coq.PArith.PArith 
  Coq.ZArith.ZArith Lia
  Coq.ZArith.Znumtheory
  Eqdep_dec Arith
  Sigma.Functions 
  Zpow_facts Sigma.Algebra.Hierarchy
  Sigma.Fermat.

Module Zpstar.

  
  (* multiplicative Group *)
  Section ZpstarGroup. 
    Context 
      {p : Z}
      {Hp : prime p}.

    
    Fact Hp_2_p : 2 <= p.
    Proof.
      pose proof (prime_ge_2 p Hp) as Ht.
      nia.
    Qed.

    Fact H_0_p : 0 < p.
    Proof.
      pose proof (prime_ge_2 p Hp).
      nia.
    Qed.
    
    Fact Hp_1_p : 1 < p.
    Proof.
      pose proof (prime_ge_2 p Hp).
      nia.
    Qed.

    
    Record Zpstar := 
      mk_zpstar {v : Z; Hv : 0 < v < p}.


    Lemma dec_lt_general : 
      forall x y (Hx Hy: (x < y)),  Hx = Hy.
    Proof.
      intros; apply Eqdep_dec.eq_proofs_unicity;
      intros u v; destruct u; destruct v; auto;
      try (right; intro Hpp; inversion Hpp).
    Qed.


    Lemma uniqueness_zpstar_proof : 
      forall x (Hx Hy : (0 < x < p)), Hx = Hy.
    Proof.
      intros ? [Hxl Hxr] [Hyl Hyr];
      f_equal; apply dec_lt_general.
    Qed.


    Lemma dec_zpstar : forall x y : Zpstar, {x = y} + {x <> y}.
    Proof.
      intros [x Hx] [y Hy].
      destruct (Z.eq_dec x y) as [Hl | Hr].
      left. subst. f_equal. 
      apply uniqueness_zpstar_proof.
      right. intro H; inversion H; 
      contradiction.
    Qed.


    Lemma construct_zpstar : 
      forall x y 
      (Hx : 0 < x < p) 
      (Hy : 0 < y < p), 
      x = y -> 
      mk_zpstar x Hx = mk_zpstar y Hy.
    Proof.
      intros; subst; f_equal.
      apply uniqueness_zpstar_proof.
    Qed. 



    (* Neutral Element *)
    Definition one : Zpstar.
      refine (mk_zpstar 1 _).
      pose proof (prime_ge_2 _ Hp).
      abstract nia.
    Defined.



    Lemma mod_not_eq_zero : 
      forall m, 
      m mod p <> 0 <-> 
      exists k w, m = k * p + w /\ 1 <= w < p.
    Proof.
      intros ?; split; intros Hm.
      exists (Z.div m p), (Zmod m p). 
      split.
      rewrite mod_eq_custom. nia.
      apply H_0_p. 
      remember (m mod p) as mp.
      assert (Hpt : 0 <= mp < p)
        by (rewrite Heqmp; 
        apply Z.mod_pos_bound; apply H_0_p). 
      nia.
      destruct Hm as [k [w [Hk Hw]]].
      rewrite Hk, Z.add_comm, Z.mod_add.
      rewrite mod_eq_custom.
      assert (Hwp: w / p = 0). 
      apply Zdiv_small; nia.
      intro. rewrite Hwp in H. nia.
      apply H_0_p. pose Hp_2_p. nia.
    Qed.

   
    Lemma mod_not_zero : 
      forall w₁ w₂,  
      1 <= w₁ < p ->  
      1 <= w₂ < p -> 
      (w₁ * w₂) mod p <> 0.
    Proof.
      intros ? ? Hw₁ Hw₂.
      assert (Hwm: 1 <= w₁ * w₂ < p * p) by nia.
      pose proof Hp_2_p.
      pose proof (rel_prime_le_prime w₁ p Hp Hw₁) as Hwp1.
      pose proof (rel_prime_le_prime w₂ p Hp Hw₂) as Hwp2.
      apply rel_prime_sym in Hwp1; 
      apply rel_prime_sym in Hwp2.
      pose proof (rel_prime_mult _ _ _ Hwp1 Hwp2) as Hwpp.
      apply rel_prime_sym in Hwpp.
      apply Zrel_prime_neq_mod_0. 
      nia. exact Hwpp.
    Qed. 


    Lemma mod_single_not_zero : 
      forall w : Z,
      1 <= w < p ->
      w mod p <> 0.
    Proof.
      intros ? Hw.
      pose proof (rel_prime_le_prime w p Hp Hw) as Hwp.
      apply Zrel_prime_neq_mod_0.
      nia.
      exact Hwp.
    Qed.
       



    


    Lemma mod_not_zero_general: 
      forall vm vn, 
      vm mod p <> 0 -> 
      vn mod p <> 0 -> 
      ((vm * vn) mod p) mod p <> 0.
    Proof.
      intros ? ? Hvm Hvn. 
      apply mod_not_eq_zero in Hvm.
      apply mod_not_eq_zero in Hvn.
      apply mod_not_eq_zero.
      destruct Hvm as [k1 [w1 [Hk1 Hw1]]].
      destruct Hvn as [k2 [w2 [Hk2 Hw2]]].
      assert (Hvmn : (vn * vm) mod p = (w1 * w2) mod p).
      rewrite Hk1, Hk2. 
      rewrite Zmult_mod, Z.add_comm, 
      Z.mod_add, Z.add_comm, Z.mod_add.
      rewrite <-Zmult_mod, Z.mul_comm; 
      reflexivity.
      pose proof Hp_2_p. abstract nia.
      pose proof Hp_2_p. abstract nia.
      exists 0, ((w1 * w2) mod p).
      split. simpl. rewrite Z.mul_comm, Hvmn; 
      reflexivity.
      assert (Hwt: 0 <= (w1 * w2) mod p < p) by 
        apply (Z.mod_pos_bound (w1 * w2) p H_0_p).
      assert ((w1 * w2) mod p <> 0).
      pose proof (mod_not_zero w1 w2 Hw1 Hw2).
      exact H. abstract nia.
    Qed.

    (* moved the proof as a lemma to avoid blowing of proof terms *)
    Lemma znot_zero_mul_proof: 
      forall vx vy, 
      1 <= vx < p -> 
      1 <= vy < p -> 
      1 <= (vx * vy) mod p < p.
    Proof.
      intros ? ? Hvx Hvy.
      assert (Hwt: 0 <= (vx * vy) mod p < p) by 
      apply (Z.mod_pos_bound (vx * vy) p H_0_p).
      assert ((vx * vy) mod p <> 0).
      pose proof (@mod_not_zero vx vy Hvx Hvy).
      exact H.
      nia.
    Qed.

    Lemma multiplication_bound : 
     forall vx vy, 
      0 < vx < p -> 
      0 < vy < p -> 
      0 < (vx * vy) mod p < p.
    Proof.
      intros ? ? Ha Hb.
      assert (Hc : 1 <= vx < p) by
      nia.
      assert (Hd : 1 <= vy < p) by 
      nia.
      pose proof (znot_zero_mul_proof _ _ Hc Hd) as He.
      nia. 
    Qed.



    
    (* multiplication *)
    Definition mul_zpstar (u v : Zpstar) : Zpstar.
      refine(
        match u, v with 
        | mk_zpstar au Hu, mk_zpstar av Hv => 
          mk_zpstar 
            (Z.modulo (au * av) p) 
            (multiplication_bound _ _ Hu Hv)
        end).
    Defined.
  
   
    Lemma fermat_theorem : forall au, 
      0 < au < p ->
      Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 1)) (Z.to_N p)) = 1.
    Proof.
      intros ? Hau.
      rewrite zmod_nmod, 
      !Z2N.id.
      rewrite fermat_little_ZZ;
      try nia; try assumption.
      all:try nia.
      rewrite !Z2N.id.
      exact Hp.
      nia.
    Qed.

    

    Lemma mod_bound : forall au, 
      0 < au < p ->
      0 < Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 2)) (Z.to_N p)) < p.
    Proof.
      intros ? Ha.
      rewrite zmod_nmod, 
      !Z2N.id,
      Zpow_mod_correct.
      split.
      admit.


      apply Z.mod_pos_bound;
      try assumption; try nia.
      all: try nia.
      rewrite Z2N.id.
      exact Hp.
      nia. 
    Admitted.

     


    (* u ^ (p - 2) is inverse of u *)
    Definition inv_zpstar (u : Zpstar) : Zpstar.
      refine(
        match u with 
        | mk_zpstar au Hu => mk_zpstar 
            (Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 2)) (Z.to_N p)))
            (mod_bound _ Hu) 
        end).
    Defined.
    
    (* Now I need to establish that it's a group *)

    (* Zpstar is a commutative Group *)
    Global Instance zpstar_comm : @commutative_group 
      Zpstar (@eq Zpstar) mul_zpstar one inv_zpstar.
    Proof.
    Admitted.


  End ZpstarGroup.
End Zpstar.

Module Zp.

  (* Prime Field *)
  Section ZpField.

    Context 
      {p : Z}
      {Hp : prime p}.


      
    Record Zp := 
      mk_zp {v : Z; Hv : Z.modulo v p = v}.

    
    Definition zp_zero : Zp. 
      refine (mk_zp 0 (Z.mod_0_l _ _)).
      pose proof prime_ge_2 _ Hp as Ht.
      abstract nia.
    Defined.



    Definition zp_one : Zp. 
      refine(mk_zp 1 (Z.mod_1_l _ _ )).
      pose proof prime_ge_2 _ Hp as Ht.
      abstract nia.
    Defined.


    Definition zp_add (x y : Zp) : Zp.
      refine (match x, y with
        | mk_zp ax _, mk_zp ay _ => mk_zp (Z.modulo (ax + ay) p) _ 
      end).

    Admitted.


    Definition zp_sub (x y : Zp) : Zp.
      refine (match x, y with
      | mk_zp ax _, mk_zp ay _ => mk_zp (N.modulo (ax - ay) p) _ 
      end).
    Admitted.




  End ZpField.

End Zp. 
(* 
  Section VectorSpace.


  End VectorSpace.


End Zp. *)
      
  