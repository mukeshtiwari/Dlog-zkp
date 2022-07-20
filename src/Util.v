Require Import Vector 
  Fin Coq.Bool.Bool.

Import VectorNotations.

Section Vect.


  Context 
    {R : Type}
    {Hdec : forall x y : R, {x = y} + {x <> y}}.

  Lemma vector_inv_0 (v : Vector.t R 0) :
    v = @Vector.nil R.
  Proof.
    refine (match v with
            | @Vector.nil _ => _
            end).
    reflexivity.
  Defined.


  Lemma vector_inv_S : 
      forall {n : nat} (v : Vector.t R (S n)), {h & {t | v = h :: t}}.
  Proof.
    intros n v.
    refine 
    (match v as v' in Vector.t _ (S n') return 
      forall (pf : n' = n),
        v = eq_rect n' (fun w => Vector.t R (S w))
              v' n pf -> {h : R & {t | v' = h :: t}}
    with
    | cons _ h _ t => fun pf Hv => _ 
    end eq_refl eq_refl).
    exists h, t.
    exact eq_refl.
  Defined.
  

  Lemma fin_inv_0 (i : Fin.t 0) : False.
  Proof. refine (match i with end). Defined.

  Lemma fin_inv_S (n : nat) (i : Fin.t (S n)) :
    (i = Fin.F1) + {i' | i = Fin.FS i'}.
  Proof.
    refine (match i with
            | Fin.F1 => _
            | Fin.FS _ => _
            end); eauto.
  Defined.


  Definition vector_to_finite_fun : 
    forall n, Vector.t R n -> (Fin.t n -> R).
  Proof.
    induction n.
    + intros v f.
      apply fin_inv_0 in f.
      refine (match f with end).
    + intros v f.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      destruct (fin_inv_S _ f) as [h | [t p]].
      exact vhd.
      exact (IHn vtl t).
  Defined.


  Definition finite_fun_to_vector : 
    forall n,  (Fin.t n -> R) -> Vector.t R n.
  Proof.
    induction n.
    + intros f.
      apply Vector.nil.
    + intros f.
      apply Vector.cons.
      apply f, Fin.F1.
      apply IHn;
      intro m.
      apply f, Fin.FS, m.
  Defined.


  Lemma finite_fun_to_vector_correctness 
    (m : nat) (f : Fin.t m -> R) (i : Fin.t m) :
    Vector.nth (finite_fun_to_vector _ f) i = f i.
  Proof.
    induction m.
    - inversion i.
    - pose proof fin_inv_S _ i as [-> | (i' & ->)].
      + reflexivity.
      + cbn. 
        now rewrite IHm.
  Defined.


  Lemma vector_to_finite_fun_correctness 
    (m : nat) (v : Vector.t R m) (i : Fin.t m) :
    Vector.nth v i = (vector_to_finite_fun _ v) i.
  Proof.
    induction m.
    - inversion i.
    - pose proof fin_inv_S _ i as [-> | (i' & ->)].
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      rewrite vp.
      reflexivity.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      rewrite vp;
      simpl; 
      now rewrite IHm.
  Defined.

  Lemma vector_finite_back_forth : 
    forall (n : nat) (v : Vector.t R n),
    v = finite_fun_to_vector _ (vector_to_finite_fun _ v).
  Proof.
    induction n.
    + intros v.
      pose proof (vector_inv_0 v) as Hv.
      subst; 
      reflexivity.
    + intros v.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      subst; simpl; f_equal.
      apply IHn.
  Defined.
        

  (* It combines two vectors pointwise using the function (f : R -> T -> U) *)
  Definition zip_with {P T U : Type} : 
    forall {n : nat}, (P -> T -> U) ->  
    Vector.t P n -> Vector.t T n -> Vector.t U n.
  Proof.
    refine(
      fix zip_with n f u {struct u} :=
      match u as u' in Vector.t _ n'  
        return
          forall (pf : n' = n), 
            u = eq_rect n' _ u' n pf -> 
            Vector.t T n' -> Vector.t U n'  
      with 
      | nil _ => 
          fun pf H v => @nil _ 
      | cons _ hu m tu => 
          fun pf H v => 
          match v as v' in Vector.t _ (S m')
            return 
              forall (pf : m' = m),
                v = eq_rect m' (fun w => Vector.t T (S w)) v' m pf ->
                Vector.t U (S m') 
          with 
          | nil _ => idProp
          | cons _ hv n tv => 
              fun pfv Hv => 
                cons _ 
                  (f hu hv) _ 
                  _ 
          end eq_refl eq_refl 
      end eq_refl eq_refl
    ).
    subst.
    exact (zip_with _ f tu tv).
  Defined.
  
  
  Definition eq_bool (x y : R) : bool :=
    match Hdec x y with 
    | left _ => true 
    | right _ => false
    end.

  
  Definition two_challenge_vectors_disjoint 
    {n : nat} (u v : Vector.t R n) :=
    Vector.fold_right (fun x y => x && y)
      (zip_with (fun x y => negb (eq_bool x y)) u v) true.
    
  Lemma dec_true : forall x y, 
    (if Hdec x y then true else false) = true <-> x = y.
  Proof.
    intros ? ?.
    destruct (Hdec x y); split; 
    intro H; auto.
    inversion H.
  Qed.

  Lemma dec_false : forall x y, 
    (if Hdec x y then true else false) = false <-> x <> y.
  Proof.
    intros ? ?.
    destruct (Hdec x y); split; 
    intro H; auto.
    inversion H.
    congruence.
  Qed.

  Lemma dec_eq_true : forall x, 
    (if Hdec x x then true else false) = true.
  Proof.
    intros ?.
    destruct (Hdec x x).
    reflexivity.
    congruence.
  Qed.


  (* Two vectors are pointwise not equal *)
  Lemma two_challenge_vectors_disjoint_true : 
    forall n (u v : Vector.t R (S n)), 
    two_challenge_vectors_disjoint u v = true ->
    forall m : Fin.t (S n), 
    Vector.nth u m <> Vector.nth v m. 
  Proof.
    induction n. 
    + unfold two_challenge_vectors_disjoint;
      intros ? ? Ha ?.
      destruct (vector_inv_S u) as (uh & ut & Hu).
      destruct (vector_inv_S v) as (vh & vt & Hv).
      pose proof (vector_inv_0 ut) as Hun.
      pose proof (vector_inv_0 vt) as Hvn.
      rewrite Hun in Hu.
      rewrite Hvn in Hv.
      rewrite Hu, Hv in Ha |- *.
      simpl in Ha |- *.
      rewrite andb_true_r in Ha.
      apply negb_true_iff in Ha.
      destruct (fin_inv_S _ m) as [Hb | (b & Hb)];
      subst; cbn.
      unfold eq_bool in Ha.
      rewrite dec_false in Ha.
      exact Ha.
      destruct (fin_inv_0 b).
    + unfold two_challenge_vectors_disjoint;
      intros ? ? Ha ?.
      destruct (vector_inv_S u) as (uh & ut & Hu).
      destruct (vector_inv_S v) as (vh & vt & Hv).
      rewrite Hu, Hv in Ha.
      simpl in Ha.
      apply andb_true_iff in Ha.
      destruct Ha as [Ha Hb].
      rewrite Hu, Hv;
      simpl.
      destruct (fin_inv_S _ m) as [Hc | (c & Hc)].
      subst; cbn.
      apply negb_true_iff in Ha.
      unfold eq_bool in Ha.
      apply dec_false in Ha.
      exact Ha.
      (* indcution case *)
      subst; cbn.
      apply IHn.
      exact Hb.
  Qed.



      
      
      


End Vect. 

Require Import Coq.PArith.PArith 
  Coq.ZArith.ZArith Lia
  Coq.ZArith.Znumtheory
  Arith 
  Zpow_facts.

Section Modutil.

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

  Lemma mod_eq_custom : 
    forall (a b : Z), 
    (0 < b)%Z -> 
    Z.modulo a b = (a - b * (a / b))%Z.
  Proof.
    intros a b Hb.
    rewrite Zmod_eq; nia.
  Qed. 


  Lemma mod_not_zero_one : 
    forall w,
    (0 < w < p)%Z -> Z.modulo w p = w.
  Proof.
    intros ? Hw.
    rewrite mod_eq_custom.
    assert (Hwp: (w/p = 0)%Z).
    apply Zdiv_small; nia.
    rewrite Hwp. nia. nia.
  Qed.


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

End Modutil. 
