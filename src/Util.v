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
  
  
  (* I need to think about it. *)
  Definition two_challenge_vectors_disjoint 
    {n : nat} (u v : Vector.t R n)  :=
    Vector.fold_right (fun x y => x && y)
      (zip_with (fun x y => 
        match Hdec x y with 
        | left _ => false
        | right _ => true
        end) u v) true.

    
  Lemma dec_false : forall x y, 
    (if Hdec x y then false else true) = false <-> x = y.
  Proof.
    intros ? ?.
    destruct (Hdec x y); split; 
    intro H; auto.
    inversion H.
    congruence.
  Qed.

  Lemma dec_true : forall x y, 
    (if Hdec x y then false else true) = true <-> x <> y.
  Proof.
    intros ? ?.
    destruct (Hdec x y); split; 
    intro H; auto.
    inversion H.
  Qed.

  Lemma dec_eq_true : forall x, 
    (if Hdec x x then false else true) = false.
  Proof.
    intros ?.
    destruct (Hdec x x).
    reflexivity.
    congruence.
  Qed.


  Lemma two_challenge_vectors_disjoint_true : 
    forall n (u v : Vector.t R (S n)), 
    two_challenge_vectors_disjoint u v = true ->
    hd u <> hd v /\ tl u <> tl v.
  Proof.
    induction n. 
    + unfold two_challenge_vectors_disjoint;
      intros ? ? Ha.
      destruct (vector_inv_S u) as (uh & ut & Hu).
      destruct (vector_inv_S v) as (vh & vt & Hv).
      pose proof (vector_inv_0 ut) as Hun.
      pose proof (vector_inv_0 vt) as Hvn.
      rewrite Hun in Hu.
      rewrite Hvn in Hv.
      rewrite Hu, Hv in Ha |- *.
      simpl in Ha |- *.
      rewrite andb_true_r in Ha.
      apply dec_true in Ha.
      split.
      exact Ha.
  Admitted.
  
      
      


End Vect. 