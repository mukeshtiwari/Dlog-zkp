Require Import ExtLib.Structures.Monad
  ExtLib.Structures.Functor
  ExtLib.Structures.Applicative
  ExtLib.Structures.MonadLaws
  ExtLib.Structures.FunctorLaws
  Coq.Unicode.Utf8 
  Coq.Logic.FunctionalExtensionality
  Coq.PArith.Pnat Coq.NArith.BinNatDef
  Coq.PArith.BinPos Lia Coq.Lists.List
  Coq.Classes.Morphisms 
  Coq.Classes.SetoidClass 
  Coq.Sorting.Permutation
  Coq.Relations.Relation_Definitions
  Coq.Logic.FunctionalExtensionality 
  Prob.

Import ListNotations.
Section Distr.



  (* Probability Distribution on a type A *)
  Definition dist (A : Type) :=  list (A * prob).
    
  (* Equality on probability distributions. Two probability 
    distributions are equal when they are same list but 
    in different order.
  *)
  Definition dist_equiv {A : Type} : relation (dist A) := 
    fun xs ys => 
    (∀ x, In x xs <-> In x ys) ∧ 
    (List.length xs = List.length ys).

   
  Local Infix "=r=" := dist_equiv 
    (at level 70, no associativity).


  (* dist_equiv is Equivalence relation *)  
  Global Instance dist_refl {A : Type} : 
    Reflexive (@dist_equiv A).
  Proof.
    unfold dist_equiv, Reflexive.
    firstorder.
  Qed.

  Global Instance dist_sym {A : Type} : 
    Symmetric (@dist_equiv A).
  Proof.
    unfold dist_equiv, Symmetric.
    intros * [Hx Hy].
    split; 
    [firstorder |
    nia].
  Qed.

  Global Instance dist_trans {A : Type} : 
    Transitive (@dist_equiv A).
  Proof.
    unfold dist_equiv, Transitive;
    try firstorder; try nia.
  Qed.

  Global Instance dist_Equiv {A : Type} : 
    Equivalence (@dist_equiv A).
  Proof.
    constructor; 
    [apply dist_refl | 
     apply dist_sym | 
     apply dist_trans].
  Qed.
  
  (* end of equivalence relation *) 
  

  (* Needed for rewriting *)
  Global Instance cons_proper {A : Type} (d : A * prob) 
    : Proper (dist_equiv ==> dist_equiv) (cons d).
  Proof.
    intros x y Hxy.
    unfold dist_equiv in Hxy.
    destruct Hxy as [Hl Hr].
    unfold dist_equiv.
    split; 
    try firstorder.
    simpl.
    f_equal; 
    assumption.
  Qed.
  
  
  Global Instance app_proper {A : Type} (ys : dist A) : 
    Proper (dist_equiv ==> dist_equiv) (fun xs => xs ++ ys).
  Proof.
    intros x y Hxy. 
    unfold dist_equiv in * |- *.
    split.
    + 
      intros xt; 
      split; 
      intros H.
      apply in_app_iff in H; 
      apply in_app_iff.
      destruct H as [Hl | Hr].
      destruct Hxy as [Hxy Hrr].
      specialize (proj1 (Hxy xt) Hl); 
      intros Hx.
      left; exact Hx. 
      right; exact Hr.
      apply in_app_iff in H; 
      apply in_app_iff.
      destruct H as [Hl | Hr].
      destruct Hxy as [Hxy Hrr].
      specialize (proj2 (Hxy xt) Hl); 
      intros Hx.
      left; exact Hx. 
      right; exact Hr.
    + 
      destruct Hxy as [_ Hxy].
      repeat (rewrite app_length).
      nia.
  Qed.


  Global Instance app_end_proper {A : Type} (ys : dist A) : 
    Proper (dist_equiv ==> dist_equiv) (fun xs => ys ++ xs).
  Proof.
    intros x y Hxy. 
    unfold dist_equiv in * |- *.
    destruct Hxy as [Hxy Hrr].
    split.
    + 
    intros xt; split; 
    intros H.
    apply in_app_iff in H; 
    apply in_app_iff.
    destruct H as [Hl | Hr].
    left. exact Hl.
    specialize (proj1 (Hxy xt) Hr); 
    intros Hx.
    right; exact Hx.
    apply in_app_iff in H; 
    apply in_app_iff.
    destruct H as [Hl | Hr].
    left; exact Hl.
    specialize (proj2 (Hxy xt) Hr); 
    intros Hx.
    right; exact Hx.
  + repeat (rewrite app_length).
    nia.
  Qed.



  Lemma dist_equiv_inv_perm {A : Type} : 
    forall (xs ys : dist A) a, xs =r= ys -> 
    cons a xs =r= ys ++ [a].
  Proof.
    unfold dist_equiv.
    intros ? ? ? [Hl Hr]; split. 
    split; intros Hb.
    destruct Hb as [Hbl | Hbr].
    apply in_app_iff. 
    right; firstorder.
    apply Hl in Hbr. 
    apply in_app_iff;
    firstorder.
    apply in_app_iff in Hb;
    firstorder.
    repeat (rewrite app_length);
    simpl.
    nia.
  Qed.


  Lemma dist_equiv_first_last {A : Type} : 
    forall (xs : dist A) a, cons a xs =r= xs ++ [a].
  Proof.
    intros ? ?.
    assert (Ht: xs =r= xs). 
    reflexivity.
    exact (dist_equiv_inv_perm xs xs a Ht).
  Qed.


  Lemma dist_equiv_inv_comm {A : Type} : 
    forall (xs ys : dist A), xs ++ ys =r= ys ++ xs.
  Proof.
    unfold dist_equiv.
    intros ? ?. split.
    intros ?.
    split; intro Hl.
    apply List.in_app_iff.
    apply List.in_app_iff in Hl.
    firstorder.
    apply List.in_app_iff.
    apply List.in_app_iff in Hl.
    firstorder.
    repeat (rewrite app_length);
    simpl.
    nia.
  Qed.


  (* Probability Monad *)
  Definition Ret {A : Type} (x : A) : dist A := [(x, one)].

  Fixpoint Bind {A B : Type} (xs : dist A)  
    (f : A -> dist B) : dist B := 
    match xs with 
    | [] => [] 
    | (ax, px) :: tx => 
      (List.map 
        (fun '(ut, pt) => (ut, mul_prob px pt)) (f ax)) ++ 
      Bind tx f
    end.

  Global Instance distmonad : Monad dist. 
  Proof.
    constructor.
    + exact @Ret.
    + exact @Bind.
  Defined.


  Lemma bind_ret_left : forall (A B : Type) 
    (a : A) (f : A -> dist B), Bind (Ret a) f = f a.
  Proof.
    intros ? ? ? f.
    unfold Bind, Ret.
    rewrite app_nil_r.
    induction (f a) as [ |(bx, px) ts IHn]. 
    + simpl; reflexivity. 
    + simpl; repeat f_equal. 
      destruct px; 
      repeat f_equal; 
      try lia.
      apply IHn.
  Qed.

  Lemma bind_ret_right : forall (A B : Type) 
    (a : dist A), Bind a Ret = a.
  Proof.
    intros ? ? a.
    unfold Bind, Ret, mul_prob.
    induction a as [| (bx, px) ts IHn]. 
    + simpl; reflexivity.
    + simpl; repeat f_equal. 
      destruct px; 
      repeat f_equal; 
      try lia.
      apply IHn.
  Qed.


  Lemma bind_map : ∀ (A B C : Type) 
    (ax : A)  (f : A -> dist B) 
    (g : B -> dist C)
    (ts : dist A) (px : prob), 
    Bind (map (λ '(ut, pt), 
      (ut, mul_prob px pt)) (f ax) ++ Bind ts f) g =
    map (λ '(ut, pt), (ut, mul_prob px pt)) 
      (Bind (f ax) g) ++ Bind (Bind ts f) g.
  Proof.
    intros ? ? ? ? ?.
    induction (f ax) as [| (axx, pxx) tss IHn].
    + simpl; 
      intros ? ? p; 
      reflexivity.
    + intros ? ? ?. 
      simpl. 
      rewrite IHn.
      rewrite app_assoc. 
      eapply app_inv_tail_iff.
      rewrite map_app, map_map.
      apply app_inv_tail_iff,
      map_ext. 
      intros [ut pt].
      rewrite mul_prob_assoc.
      reflexivity.
  Qed.



  Lemma bind_assoc : ∀ (A B C : Type) 
    (am : dist A) (f : A -> dist B) (g : B -> dist C), 
    Bind (Bind am f) g = Bind am (fun a => Bind (f a) g).
  Proof.
    intros ? ? ?. 
    induction am as [| (ax, px) ts IHn].
    + simpl. 
      reflexivity.
    + intros ? ?. 
      simpl. 
      rewrite <-IHn.
      rewrite bind_map; 
      reflexivity.
  Qed.



  Global Instance distmonad_law : MonadLaws distmonad.
  Proof.
    constructor; intros.
    + apply bind_ret_left.
    + apply bind_ret_right; 
      exact A.
    + apply bind_assoc.
  Defined.


  




