Require Import Coq.PArith.PArith 
  Coq.ZArith.ZArith Lia
  Coq.ZArith.Znumtheory
  Eqdep_dec Arith
  Sigma.Functions 
  Zpow_facts Sigma.Algebra.Hierarchy
  Sigma.Fermat
  Sigma.Util Coq.Classes.Morphisms.

Module Zpstar.

  
  (* multiplicative Group *)
  Section ZpstarGroup. 
    Context 
      {p : Z}
      {Hp : prime p}.

    
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

    
    (* multiplication *)
    Definition mul_zpstar (u v : Zpstar) : Zpstar.
      refine(
        match u, v with 
        | mk_zpstar au Hu, mk_zpstar av Hv => 
          mk_zpstar 
            (Z.modulo (au * av) p) 
            (@multiplication_bound p Hp _ _ Hu Hv)
        end).
    Defined.
  
   
    Lemma fermat_theorem : 
      forall au, 
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
      !Z2N.id.
      apply fermat_bound.
      exact Hp.
      all:try nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.
    
     


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

    Lemma zpstar_mul_associative : 
      forall x y z : Zpstar, 
      mul_zpstar x (mul_zpstar y z) =  
      mul_zpstar (mul_zpstar x y) z.
    Proof.
      pose proof @H_0_p p Hp.
      intros ? ? ?; 
      destruct x as [x Hx]; 
      destruct y as [y Hy]; 
      destruct z as [z Hz]; 
      simpl in * |- *.
      eapply construct_zpstar.
      rewrite Z.mul_mod_idemp_l.
      rewrite Z.mul_mod_idemp_r.
      rewrite Z.mul_assoc. 
      reflexivity.
      all:nia.
    Qed.

    Lemma one_is_left_identity : 
      forall x, mul_zpstar one x = x.
    Proof.
      intro x. 
      unfold mul_zpstar, one.
      destruct x as [x Hx]. 
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_1_l. 
      apply mod_not_zero_one. 
      exact Hx.
    Qed.

    Lemma one_is_right_identity : 
      forall x, mul_zpstar x one = x.
    Proof.
      intro x. 
      unfold mul_zpstar, one.
      destruct x as [x Hx]. 
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_1_r. 
      apply mod_not_zero_one. 
      exact Hx.
    Qed.

  
    Lemma zpstar_mul_commutative : 
      forall x y : Zpstar, 
      mul_zpstar x y =  mul_zpstar y x.
    Proof.
      destruct x as [x Hx]; 
      destruct y as [y Hy]; simpl.
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_comm.
      reflexivity.
    Qed.

    Global Instance zpstar_mul_proper: Proper (eq ==> eq ==> eq) mul_zpstar.
    Proof.
      intros x y Hxy z u Hzu.
      destruct x as [x Hx]; destruct y as [y Hy];
      destruct z as [z Hz]; destruct u as [u Hu]; simpl in * |- *.
      refine(construct_zpstar _ _ _ _ _).
      inversion Hxy; inversion Hzu; subst; reflexivity.
    Defined. 

    Lemma zpstar_left_inv :
      forall x, mul_zpstar (inv_zpstar x) x = one.
    Proof.
      intros ?.
      unfold mul_zpstar, inv_zpstar, one.
      destruct x as (v & Hv).
      apply construct_zpstar.
      rewrite Z.mul_comm.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia. 
      assert (Ht : v * v ^ (p - 2) = v ^ (p - 1)).
      rewrite Hpp. 
      rewrite Z.pow_add_r. 
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp. 
      exact Hv.
      nia. 
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.
    
    Lemma zpstar_right_inv :
      forall x, mul_zpstar x (inv_zpstar x) = one.
    Proof.
      intros ?.
      unfold mul_zpstar, inv_zpstar, one.
      destruct x as (v & Hv).
      apply construct_zpstar.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia. 
      assert (Ht : v * v ^ (p - 2) = v ^ (p - 1)).
      rewrite Hpp. 
      rewrite Z.pow_add_r. 
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp. 
      exact Hv.
      nia. 
      rewrite Z2N.id.
      exact Hp.
      nia. 
    Qed.


    (* Zpstar is a commutative Group *)
    Global Instance zpstar_comm : @commutative_group 
      Zpstar (@eq Zpstar) mul_zpstar one inv_zpstar.
    Proof.
      repeat econstructor.
      + unfold is_associative; 
        intros ? ? ?.
        apply zpstar_mul_associative.
      + intro x. apply one_is_left_identity.
      + intro x. apply one_is_right_identity.
      + apply zpstar_mul_proper.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y z Hxy Hyz. rewrite Hxy. exact Hyz.
      + intro x. apply zpstar_left_inv.
      + intro x. apply zpstar_right_inv.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y. apply zpstar_mul_commutative.
    Qed. 


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
      
  