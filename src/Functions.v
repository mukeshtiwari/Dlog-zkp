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

    (* Big_o notations *)
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
        (* How to reason about inv's complexity? *)
      end.

    

    Definition repeat_op_ntimes_N (e : T) (n : N) :=
      match n with
      | N0 => (id, xH) 
      | Npos p => (repeat_op_ntimes_rec e p)
      end.

   
    (* *)
    Lemma complexity_repeat_op_ntimes_N :
      forall e n, 
      (N.pos (snd (repeat_op_ntimes_N e n)) <= 1 + n)%N.
    Proof.
      intros ? [|n];
      cbn.
      + nia.
      + pose proof repeat_op_ntimes_rec_bound n e as Hne. 
        destruct (repeat_op_ntimes_rec e n); cbn in *;
        destruct n;
        nia.
    Qed.
      
    

    

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



    Lemma connection_N_and_unary_nat : 
      forall (n : nat) (m : N) e, 
      m = (N.of_nat n) ->
      repeat_op_ntimes_unary_nat e n = fst (repeat_op_ntimes_N e m).
    Proof.
      destruct m.
      + intros ? He. rewrite binnat_zero with (n := n). 
        reflexivity. exact He.
      + simpl. 
        generalize dependent n; generalize dependent p.
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


Require Import Coq.NArith.NArith
  Znumtheory Lia
  Zdiv Zpow_facts.
From Coq Require Import Even.

Module Fn.
  


  Fixpoint repeat_op_ntimes_rec (e : N) (n : positive) (w : N) : N :=
    match n with
    | xH => N.modulo e w
    | xO p => let ret := repeat_op_ntimes_rec e p w in N.modulo (ret * ret) w
    | xI p => let ret := repeat_op_ntimes_rec e p w in N.modulo (e * (ret * ret)) w 
    end.

  Definition Npow_mod (e : N) (n w : N) :=
    match n with
    | N0 => Npos xH
    | Npos p => repeat_op_ntimes_rec e p w 
    end.


  (* slow function, will be used to prove that this slow function is 
    equivalent to Npow_mod, faster one. *)
  Fixpoint Npow_mod_unary (e : N) (n : nat) (w : N) : N :=
    match n with 
    | 0%nat => Npos xH
    | S n' => N.modulo (e * Npow_mod_unary e n' w) w
    end.


  (* acc is accumulator, for efficient reduction of terms *)
  Fixpoint repeat_op_ntimes_acc (e : N) (n : positive) (w acc : N) : N :=
    match n with
    | xH => N.modulo (e * acc) w
    | xO p => let ee := (N.modulo (e * e) w) in repeat_op_ntimes_acc ee p w acc 
    | xI p => let ee := (N.modulo (e * e) w) in 
              let ea := (N.modulo (e * acc) w) in 
              repeat_op_ntimes_acc ee p w ea  
    end.

  Lemma op_pushes_out : forall n e w, prime (Z.of_N w) -> 
    repeat_op_ntimes_rec ((e * e) mod w) n w = 
    N.modulo ((repeat_op_ntimes_rec e n w * repeat_op_ntimes_rec e n w)) w.
  Proof.
    induction n.
    - simpl; intros ? ? Hw.
      rewrite IHn.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      remember (repeat_op_ntimes_rec e n w * repeat_op_ntimes_rec e n w)%N as enw.
      rewrite <- N.mul_mod_idemp_r.
      repeat rewrite N.mul_mod_idemp_l.
      repeat rewrite N.mul_mod_idemp_r.
      assert (Ht : (e * enw * (e * enw) = 
        e * e * (enw * enw))%N). lia.
      rewrite Ht; clear Ht.
      repeat rewrite N.mul_assoc.
      rewrite N.mul_mod_idemp_r.
      reflexivity.
      all:(try lia; try assumption).
    - simpl; intros ? ? Hw.
      rewrite IHn.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      reflexivity. exact Hw.
    - simpl; intros ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite N.mod_mod.
      rewrite N.mul_mod_idemp_l.
      rewrite N.mul_mod_idemp_r.
      reflexivity.
      all:lia.
  Qed.


  Lemma positive_mul_group_acc_rec_connection : forall n e w acc, prime (Z.of_N w) ->
    repeat_op_ntimes_acc e n w acc = N.modulo (acc * repeat_op_ntimes_rec e n w) w.
  Proof.
    induction n.
    - simpl; intros ? ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      specialize (IHn (N.modulo (e * e) w) w (N.modulo (e * acc) w)).
      rewrite IHn.
      rewrite op_pushes_out.
      remember (repeat_op_ntimes_rec e n w * repeat_op_ntimes_rec e n w)%N as enw.
      rewrite N.mul_mod_idemp_l.
      repeat rewrite N.mul_mod_idemp_r.
      assert (Ht : ((acc * (e * enw) = e * acc * enw)%N)).
      lia.
      rewrite Ht; clear Ht.
      reflexivity.
      all:(try lia; try assumption).
    - simpl; intros ? ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite IHn. rewrite op_pushes_out.
      reflexivity.
      all:assumption.
    - simpl; intros ? ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite N.mul_mod_idemp_r.
      assert (Ht : (acc * e = e * acc)%N). lia.
      rewrite Ht; clear Ht.
      reflexivity.
      lia.
  Qed.

      
  Definition Npow_mod_constant_space (e : N) (n w : N) :=
    match n with
    | N0 => Npos xH
    | Npos p => repeat_op_ntimes_acc e p w 1 
    end.

  
  Lemma npow_mod_npow_constant_eqv : forall n e w, prime (Z.of_N w) ->
    Npow_mod e n w = Npow_mod_constant_space e n w.
  Proof.
    destruct n; simpl; intros ? ? Hw.
    - reflexivity.
    - pose proof positive_mul_group_acc_rec_connection p e w 1 Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite H. rewrite N.mul_1_l.
      destruct p.
      all:simpl; rewrite N.mod_mod; lia.
  Qed.


  Lemma Npow_mod_unary_bound : forall (n : nat) (e w : N), prime (Z.of_N w) -> 
    (Npow_mod_unary e n w < w)%N.
  Proof.
    induction n.
    - simpl; intros ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      lia.
    - simpl; intros ? ? Hw.
      apply N.mod_lt.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      lia.
  Qed.

  Lemma binnat_zero : forall (n : nat), 0%N = N.of_nat n -> n = 0%nat.
  Proof.
    induction n; try lia.
  Qed.

  Theorem Npow_mod_add_mul : forall n m e w, prime (Z.of_N w) ->
    Npow_mod_unary e (n + m) w = N.modulo (Npow_mod_unary e n w * 
    Npow_mod_unary e m w) w.
  Proof.
    induction n.
    - intros ? ? ? Hw.
      rewrite Nat.add_0_l. 
      assert (Ht : Npow_mod_unary e 0 w = Npos xH).
      simpl. reflexivity. 
      rewrite Ht.
      rewrite N.mul_1_l.
      induction m.
      + simpl. rewrite N.mod_1_l.
        reflexivity.
        pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
        lia.
      + simpl. rewrite N.mod_mod.
        reflexivity. 
        pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
        lia.
    - simpl; intros ? ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite IHn. 
      rewrite N.mul_mod_idemp_r.
      rewrite N.mul_mod_idemp_l.
      rewrite N.mul_assoc. reflexivity.
      lia. lia. assumption.
  Qed.



  Lemma binnat_odd : forall (p : positive) (n : nat), 
    N.pos (xI p) = N.of_nat n -> 
    exists k,  n = (2 * k + 1)%nat /\  (N.pos p) = (N.of_nat k).
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
    N.pos (xO p) = N.of_nat n :> N -> 
    exists k, n = (Nat.mul 2 k) /\  (N.pos p) = (N.of_nat k).
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

  (* slow is equivalent to fast *)
  Lemma npow_mod_exp_unary_binary_eqv : forall (n : N) e w, prime (Z.of_N w) ->
    Npow_mod_unary e (N.to_nat n) w = Npow_mod e n w.
  Proof.
    destruct n.
    - simpl; intros ? ? Hw.
      reflexivity.
    - simpl; revert p.
      induction p.
      + simpl; intros ? ? Hw.
        pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
        rewrite <-IHp.
        rewrite ZL6.
        rewrite Npow_mod_add_mul.
        rewrite N.mul_mod_idemp_r.
        reflexivity.
        lia. exact Hw.
        exact Hw.
      + simpl; intros ? ? Hw.
        rewrite <-IHp.
        rewrite Pos2Nat.inj_xO.
        assert (Ht : (2 * Pos.to_nat p = 
          Pos.to_nat p + Pos.to_nat p)%nat).
        lia. rewrite Ht.
        rewrite Npow_mod_add_mul.
        reflexivity.
        exact Hw.
        exact Hw.
      + simpl; intros ? ? Hw.
        rewrite N.mul_1_r.
        reflexivity.
  Qed.
        
     

  
  Lemma mod_reduce_pow : forall n e w, prime (Z.of_N w) -> repeat_op_ntimes_rec e n w = 
    repeat_op_ntimes_rec (N.modulo e w) n w.
  Proof.
    induction n.
    - simpl; intros ? ? Hp.
      rewrite IHn.
      remember (repeat_op_ntimes_rec (e mod w) n w *
      repeat_op_ntimes_rec (e mod w) n w)%N as t.
      rewrite N.mul_mod_idemp_l.
      reflexivity.
      pose proof (prime_ge_2 (Z.of_N w) Hp) as Ht.
      lia. exact Hp.
    - simpl; intros ? ? Hp.
      rewrite IHn.
      reflexivity.
      exact Hp.
    - simpl; intros ? ? Hp.
      rewrite N.mod_mod.
      reflexivity.
      pose proof (prime_ge_2 (Z.of_N w) Hp) as Ht.
      lia.
  Qed.


  Lemma Nmod_reduce_pow : forall n e w, prime (Z.of_N w) -> 
    Npow_mod e n w = Npow_mod (N.modulo e w) n w.
  Proof.
    destruct n.
    - simpl; intros ? ? Hp.
      reflexivity.
    - simpl; intros ? ? Hp.
      apply mod_reduce_pow.
      exact Hp.
  Qed.

  Lemma wp_mod_zero : forall (w k p : N), prime (Z.of_N p) -> (2 <= k)%N -> (2 <= p)%N ->
    (w mod p = 0)%N ->  (Npow_mod (w mod p) k p = 0)%N.
  Proof.
    intros ? ? ? Hp Hk Hpt Hwp.
    rewrite Hwp.
    unfold Npow_mod.
    destruct k. lia.
    clear Hk.
    induction p0.
    simpl. rewrite N.mod_0_l.
    reflexivity. lia.
    simpl. rewrite IHp0.
    rewrite N.mod_0_l. 
    reflexivity. lia.
    simpl. rewrite N.mod_0_l.
    reflexivity. lia.
  Qed.
    
  Lemma wp_mod_one : forall (w k p : N), prime (Z.of_N p) -> (2 <= k)%N -> (2 <= p)%N ->
    (w mod p = 1)%N ->  (Npow_mod (w mod p) k p = 1)%N.
  Proof.
    intros ? ? ? Hp Hk Hpt Hwp.
    rewrite Hwp.
    unfold Npow_mod.
    destruct k. lia.
    clear Hk.
    induction p0.
    simpl. rewrite IHp0.
    simpl. rewrite N.mod_1_l.
    reflexivity. lia.
    simpl. rewrite IHp0.
    rewrite N.mod_1_l. 
    reflexivity. lia.
    simpl. rewrite N.mod_1_l.
    reflexivity. lia.
  Qed.

  
    
  Lemma zmod_nmod : forall (b a w : N), prime (Z.of_N w) ->
    Z.of_N (Npow_mod a b w) = Zpow_mod (Z.of_N a) (Z.of_N b) (Z.of_N w).
  Proof.
    intros ? ? ? Hw.
    rewrite Zpow_mod_correct.
    destruct b; simpl.
    - symmetry.
      rewrite Z.mod_1_l.
      reflexivity. 
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Ht.
      lia.
    - revert p.
      induction p.
      + simpl. 
        assert (Ht : (p~1 = p + p + 1)%positive).
        lia. rewrite Ht.
        rewrite Zpower_pos_is_exp.
        rewrite Zpower_pos_is_exp.
        rewrite Zpower_pos_1_r.
        rewrite N2Z.inj_mod.
        rewrite N2Z.inj_mul.
        rewrite N2Z.inj_mul.
        rewrite IHp.
        remember (Z.pow_pos (Z.of_N a) p) as zps.
        remember (Z.of_N a) as za.
        remember (Z.of_N w) as zw. 
        assert (Hzp: zps * zps * za = za * (zps * zps)).
        lia. rewrite Hzp; clear Hzp; clear Ht.
        rewrite <-Zmult_mod_idemp_l.
        assert (Ht : (za * (zps * zps)) mod zw = (za mod zw * (zps * zps)) mod zw).
        rewrite <-Zmult_mod_idemp_l.
        reflexivity. rewrite Ht; clear Ht.
        assert (Ht : (za mod zw * (zps * zps)) mod zw = 
        (za mod zw * ((zps * zps) mod zw)) mod zw).
        rewrite <-Zmult_mod_idemp_r. reflexivity.
        rewrite Ht; clear Ht.
        assert (Ht : (zps * zps) mod zw = 
          (zps mod zw * (zps mod zw)) mod zw).
        rewrite <-Zmult_mod_idemp_l.
        rewrite <-Zmult_mod_idemp_r.
        reflexivity.
        rewrite Ht.
        rewrite Zmult_mod_idemp_r.
        reflexivity.
      + simpl.
        assert (Ht : (p~0 = p + p)%positive).
        lia. rewrite Ht.
        rewrite Zpower_pos_is_exp.
        rewrite N2Z.inj_mod.
        rewrite N2Z.inj_mul.
        rewrite IHp.
        remember (Z.pow_pos (Z.of_N a) p) as zps.
        remember (Z.of_N a) as za.
        remember (Z.of_N w) as zw.
        rewrite Zmult_mod_idemp_l.
        rewrite Zmult_mod_idemp_r.
        reflexivity.
      + simpl. rewrite Zpower_pos_1_r.
        rewrite N2Z.inj_mod.
        reflexivity.
    - pose proof (prime_ge_2 (Z.of_N w) Hw) as Ht.
      lia.
  Qed.

  Lemma npow_mod_nat : forall (n a p : nat), 
    prime (Z.of_nat p) ->
    Npow_mod_unary (N.of_nat a) n (N.of_nat p) =
    N.of_nat (Nat.modulo (Nat.pow a n) p).
  Proof.
    induction n.
    + intros * Hp.
      pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
      simpl. rewrite Nat.mod_1_l.
      lia. lia.
    + intros * Hp.
      simpl.
      pose proof (IHn a p Hp).
      rewrite H.
      rewrite <-Nat2N.inj_mul,
      <-Nat2N.inj_mod.
      f_equal.
      rewrite Nat.mul_mod_idemp_r.
      reflexivity.
      pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
      lia.
  Qed. 
      
  Lemma N_to_nat_exp : forall (n a p : N), 
    prime (Z.of_N p) ->
    N.modulo (N.pow a n) p = 
    N.of_nat (Nat.modulo (Nat.pow (N.to_nat a) 
      (N.to_nat n)) (N.to_nat p)).
  Proof.
    intros * Hp.
    rewrite <-N2Nat.inj_pow.
    rewrite <-N2Nat.inj_mod.
    lia.
  Qed.


Module Fn.  




