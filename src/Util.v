Require Import Vector 
  Fin Coq.Bool.Bool Coq.Unicode.Utf8.

Import VectorNotations.

Section Dec.

  Context 
    {R : Type}
    {Hdec : forall x y : R, {x = y} + {x <> y}}.

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

   
  Definition eq_bool (x y : R) : bool :=
    match Hdec x y with 
    | left _ => true 
    | right _ => false
    end.


End Dec.


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
  
 
  Fixpoint repeat_ntimes (n : nat) (w : R) : Vector.t R n :=
    match n as n' return Vector.t R n' with
    | 0 => []
    | S n' => w :: repeat_ntimes n' w 
    end.

  
  (* Two challenge vectors are same pointwise *)
  Definition two_challenge_vectors_same_everyelem {n : nat} :
    Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∀ (f : Fin.t n),
    nth u f = nth v f.
  
  (* Two challenge vectors differs at atleast one point *)
  Definition two_challenge_vectors_disjoint_someelem {n : nat} :
     Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∃ (f : Fin.t n),
    nth u f <> nth v f.
    
  (* Two challenge vectors are different pointwise *)
  Definition two_challenge_vectors_different_everyelem {n : nat} :
    Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∀ (f : Fin.t n),
    nth u f <> nth v f.
  
  (* Two challenge vectors same at some point *)
  Definition two_challenge_vectors_same_someelem {n : nat} :
     Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∃ (f : Fin.t n),
    nth u f = nth v f.

  

  (* Write Ltac *)

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

  Lemma mod_more_gen_bound : 
    forall w,
    (0 <= w < p)%Z <-> Z.modulo w p = w.
  Proof.
    intros ?. split; intro Hw.
    +
    rewrite mod_eq_custom.
    assert (Hwp: (w/p = 0)%Z).
    apply Zdiv_small; nia.
    rewrite Hwp. nia. nia.
    + rewrite <-Hw.
      apply Z_mod_lt.
      pose proof (Hp_2_p).
      nia. 
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


  Lemma mod_exists: 
    forall m,
    exists k w, m = k * p + w /\ 0 <= w < p.
  Proof.
    intros ?.
    exists (Z.div m p), (Zmod m p). 
    split.
    rewrite mod_eq_custom. nia.
    apply H_0_p.
    apply Z.mod_pos_bound.
    apply H_0_p.
  Qed.


  Lemma mod_exists_pos : 
    forall m,
    0 <= m -> 
    exists k w, m = k * p + w /\ 0 <= w < p 
    /\ 0 <= k.
  Proof.
    intros ? Hm.
    exists (Z.div m p), (Zmod m p). 
    split.
    rewrite mod_eq_custom. nia.
    apply H_0_p.
    split.
    apply Z.mod_pos_bound.
    apply H_0_p.
    pose proof Hp_2_p as Hw.
    apply Z.div_pos;
    try nia.
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

  Lemma rewrite_gop {G : Type} (gop : G -> G -> G) : 
    forall a b c d : G, 
    a = b -> c = d -> gop a c = gop b d.
  Proof.
    intros * Hab Hcd;
    subst;
    reflexivity.
  Qed.

End Modutil. 


Section Vecinvert.

  Context 
    {R : Type}.


  Inductive vec_shape_O : Vector.t R 0 -> Type :=
  | vec_shape_O_intro : vec_shape_O [].

  Inductive vec_shape_S {n : nat} : Vector.t R (1 + n) -> Type :=
  | vec_shape_S_intro r v : vec_shape_S (r :: v).

  Definition vec_invert_t {n : nat} : Vector.t R n -> Type :=
    match n with 
    | O  => vec_shape_O 
    | S n => @vec_shape_S n
    end.
    
  Definition vec_invert 
    {n : nat}  (v : Vector.t R n) : vec_invert_t v  :=
    match v with 
    | [] => vec_shape_O_intro  
    | r :: v => vec_shape_S_intro r v
    end.

  
End Vecinvert.

Section Fininvert.


  Inductive fin_shape_0 : Fin.t 0 -> Type :=.

  Inductive fin_shape_S {n : nat} : Fin.t (S n) -> Type :=
  | fin_shape_S_fst : fin_shape_S F1 
  | fin_shape_S_nxt s : fin_shape_S (FS s).

  Definition fin_invert_t {n : nat} : Fin.t n -> Type :=
    match n with 
    | O => fin_shape_0
    | (S n') => fin_shape_S
    end.
  

  Definition fin_invert 
    {n : nat} (f : Fin.t n) : fin_invert_t f :=
    match f with 
    | F1 => fin_shape_S_fst 
    | FS s => fin_shape_S_nxt s 
    end.

  Definition fin_O_rect X (i : Fin.t 0) : X :=
    match fin_invert i with end.

  Variables (n : nat)
            (P : Fin.t (S n) → Type)
            (P_0 : P F1)
            (P_S : ∀i, P (FS i)).

  Definition fin_S_rect i : P i :=
    match fin_invert i with
      | fin_shape_S_fst => P_0
      | fin_shape_S_nxt i => P_S i
    end.

End Fininvert.




Section Hvect.

  (* Hetrogeneous Vector *)
  Inductive Hvect : ∀ {n : nat}, Vector.t Type n -> Type :=
  | Hnil : @Hvect 0 []
  | Hcon {A : Type} {n : nat} {v : Vector.t Type n} : 
      A -> @Hvect n v -> @Hvect (1 + n) (A :: v).

  
  (*
    Check [nat; nat; bool].
    Check [Vector.t nat 1; Vector.t nat 1; Vector.t bool 1].
    Check Hcon 1 (Hcon 2 (Hcon true Hnil)).
    Check Hcon [1] (Hcon [2] (Hcon [true] Hnil)).
  *)


  Inductive hvec_shape_0 : Hvect [] -> Type  :=
  | hvec_shape_0_intro : hvec_shape_0 Hnil.

  Inductive hvec_shape_S {n X V} : @Hvect (S n) (X :: V) -> Type  :=
  | hvec_shape_S_intro r v : hvec_shape_S (Hcon r v).

  Definition hvec_invert_t {n : nat} {v : Vector.t Type n} 
    : @Hvect n v -> Type :=
    match v with 
    | [] => hvec_shape_0
    | X :: V => hvec_shape_S 
    end.
  
  Definition hvec_invert {n v} (w : @Hvect n v) : hvec_invert_t w :=
    match w with 
    | Hnil => hvec_shape_0_intro 
    | Hcon r v => hvec_shape_S_intro r v 
    end.

  (*
    This function takes a (hetrogeneous)
    vector of n elements and returns 
    a (hetrogeneous) vector of n unit lenght 
    vector.   
  *)
  Definition sigma_proto :
    forall {n : nat} {r : Vector.t Type n},
    @Hvect n r -> @Hvect n
      (Vector.map (fun x => Vector.t x 1) r).
  Proof.
    induction n as [|n IHn];
    intros V W.
    +
     destruct (vec_invert V);
     cbn; exact W.
    +
      destruct (vec_invert V) as (hv & tv).
      destruct (hvec_invert W) as (hw & tw).
      cbn.
      refine (Hcon [hw] (IHn _ tw)).
  Defined.

  (* 
  Eval compute in sigma_protocol 
    (Hcon 1 (Hcon 2 (Hcon true Hnil))).
  *)
  (* same as sigma_proto function *)
  Theorem sigma_protocol :
    forall {n : nat} {r : Vector.t Type n},  
    @Hvect n r -> @Hvect n 
      (Vector.map (fun x => Vector.t x 1) r).
  Proof.
    intros ? ? X.
    induction X as [|A n v x w IHn]; cbn;
    [exact Hnil |
    refine (Hcon [x] IHn)].
  Defined.

  (* For example, three move can be 
    encoded as follows:*)
  Definition three_move_sigma 
    {A B C : Type} (com : A) 
    (cha : B) (res : C) : 
    @Hvect 3 [Vector.t A 1; Vector.t B 1; Vector.t C 1] :=
    sigma_proto (Hcon com (Hcon cha (Hcon res Hnil))).

  
End Hvect.


  
