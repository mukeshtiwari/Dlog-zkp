Require Import Coq.ZArith.ZArith
  Coq.NArith.BinNatDef
  Coq.micromega.Lia
  Coq.ZArith.ZArith Lia Psatz 
  Coq.Classes.Morphisms
  Coq.Arith.Even
  Sigma.Algebra.Hierarchy
  Sigma.Algebra.Group
  Coq.NArith.NArith.

  
  Section Functions.

    Context 
      {T : Type} 
      {op : T -> T -> T} {id : T} {inv : T -> T}
      {Hcgroup : @commutative_group T (@eq T) op id inv}.

    Local Infix "*" := op.

    (* This function computes e^n by repeated squaring. In addtion, 
      it return the nubmer of steps it has taken *)
    Fixpoint repeat_op_ntimes_rec (e : T) (n : positive) : T * positive :=
      match n with
      | xH => (e, xH)
      | xO p => 
        let (ret, w) := repeat_op_ntimes_rec e p 
        in (ret * ret, Pos.add 1 w) 
      | xI p => 
        let (ret, w) := repeat_op_ntimes_rec e p 
        in (e * (ret * ret), Pos.add 1 w) 
      end.

    (* Proof that the number of steps is bounded by a 
      polynomial. It can be even proven it's bounded 
        <= Log2 n but it will take some effort *)
    Lemma repeat_op_ntimes_rec_bound : 
      forall n e, (snd (repeat_op_ntimes_rec e n) <= n)%positive.
    Proof.
      induction n;
      intros ?.
      + cbn.
        pose proof (IHn e). 
        destruct (repeat_op_ntimes_rec e n) as [cnt w];
        cbn in * |- *.
        destruct w; try nia. 
      + cbn.
        pose proof (IHn e).
        destruct (repeat_op_ntimes_rec e n) as [cnt w];
        cbn in * |- *.
        destruct w; try nia.
      + cbn. nia.
    Qed.  


  

    Lemma op_pushes_out : forall n e,
      fst (repeat_op_ntimes_rec (e * e) n) = 
      fst (repeat_op_ntimes_rec e n) * fst (repeat_op_ntimes_rec e n).
    Proof.
      induction n.
      + intros ?. 
        specialize (IHn e).
        cbn.
        destruct (repeat_op_ntimes_rec (e * e) n) as [f s];
        cbn in * |- *.
        rewrite IHn.
        destruct (repeat_op_ntimes_rec e n) as [u v];
        cbn in * |- *.
        repeat rewrite <-associative.
        repeat rewrite group_cancel_left.
        assert (Ht : e * (u * (u * (u * u))) = u * (u * (e * (u * u)))).
          repeat rewrite associative.
          repeat rewrite group_cancel_right.
          rewrite <-associative, commutative.
          reflexivity.
        rewrite Ht. 
        reflexivity.
      + intros ?.
        specialize (IHn e).
        cbn.
        destruct (repeat_op_ntimes_rec (e * e) n) as [f s];
        cbn in * |- *.
        rewrite IHn.
        destruct (repeat_op_ntimes_rec e n) as [u v];
        cbn in * |- *. 
        reflexivity.
      + intros ?; 
        reflexivity. 
    Qed.  


    
    Definition repeat_op_ntimes_Z (e : T) (n : Z) := 
      match n with
      | Z0 => id
      | Zpos p => fst (repeat_op_ntimes_rec e p)
      | Zneg p => inv (fst (repeat_op_ntimes_rec e p))
      end.

    

    Definition repeat_op_ntimes_N (e : T) (n : N) :=
      match n with
      | N0 => id
      | Npos p => fst (repeat_op_ntimes_rec e p)
      end.


    Fixpoint repeat_op_ntimes_unary_nat (e : T) (n : nat) := 
      match n with
      | 0 => id
      | S n' => op e (repeat_op_ntimes_unary_nat e n')
      end.



    Lemma binnat_zero : forall (n : nat), 
      0%N = N.of_nat n :> N -> n = 0 :> nat.
    Proof.
      induction n; try lia.
    Qed.

    Lemma binnat_odd : forall (p : positive) (n : nat), 
      N.pos p~1 = N.of_nat n :> N -> 
      exists k, n = (2 * k + 1) /\ (N.pos p) = (N.of_nat k).
    Proof.
      intros p n Hp.
      destruct (Even.even_or_odd n) as [H | H].
      apply Even.even_equiv in H. destruct H as [k Hk].
      (* Even (impossible) Case *)
      rewrite Hk in Hp; lia.
      (* Odd (possible) case *)
      apply Even.odd_equiv in H. destruct H as [k Hk].
      rewrite Hk in Hp. exists k.
      split. exact Hk. lia.
    Qed.



    Lemma binnat_even : forall (p : positive) (n : nat), 
      N.pos p~0 = N.of_nat n :> N -> 
      exists k, n = (Nat.mul 2 k) /\ (N.pos p) = (N.of_nat k).
    Proof.
      intros p n Hp.
      destruct (Even.even_or_odd n) as [H | H].
      apply Even.even_equiv in H. destruct H as [k Hk].
      (* Even (possible) case*)
      rewrite Hk in Hp. exists k.
      split. exact Hk. lia.
      (* Odd (impossible) case *)
      apply Even.odd_equiv in H. 
      destruct H as [k Hk].
      rewrite Hk in Hp. lia.
    Qed. 


    Lemma push_out_e_unary_nat_gen : forall k1 k2 e, 
      repeat_op_ntimes_unary_nat e (k1 + k2) = 
      repeat_op_ntimes_unary_nat e k1 * repeat_op_ntimes_unary_nat e k2.
    Proof.
      induction k1.
      + intros ? ?; simpl. 
        rewrite left_identity; reflexivity.
      + intros ? ?; simpl. rewrite IHk1.
        rewrite <- associative.
        reflexivity.
    Qed. 



    Lemma connection_N_and_unary_nat : forall (n : nat) (m : N) e, 
      m = (N.of_nat n) ->
      repeat_op_ntimes_unary_nat e n = repeat_op_ntimes_N e m.
    Proof.
      destruct m.
      + intros ? He. rewrite binnat_zero with (n := n). 
        reflexivity. exact He.
      + simpl. generalize dependent n; generalize dependent p.
      induction p using positive_ind.
        * simpl. intros.
          destruct (binnat_odd p n H) as [k [Hkl Hkr]].
          pose proof (IHp k e Hkr) as Hp. rewrite Hkl.
          assert (Ht : @Logic.eq _ (2 * k + 1) (1 + 2 * k)) by lia.
          rewrite Ht; clear Ht.
          simpl.  assert (Ht : @Logic.eq _(k + 0) k) by lia.
          rewrite Ht; clear Ht.
          rewrite push_out_e_unary_nat_gen.
          rewrite Hp.
          destruct (repeat_op_ntimes_rec e p) as [u v];
          cbn in * |- *.
          reflexivity.
        * simpl. intros.
          destruct (binnat_even p n H) as [k [Hkl Hkr]].
          pose proof (IHp k e Hkr) as Hp. rewrite Hkl.
          assert (Ht : @Logic.eq _ (Nat.mul 2 k) (k + k)) by lia.
          rewrite Ht; clear Ht.
          rewrite push_out_e_unary_nat_gen.
          rewrite Hp. 
          destruct (repeat_op_ntimes_rec e p) as [u v];
          cbn in * |- *.
          reflexivity.
        * simpl. intros.
          assert (Ht : @Logic.eq _ n 1) by lia.
          rewrite Ht. simpl. rewrite right_identity. 
          reflexivity.
    Qed. 
    


End Functions.



