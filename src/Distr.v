Require Import 
  ExtLib.Structures.Monad
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
  Sigma.Prob.

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


  (* Uniform distribution u*)
  Definition uniform_with_replacement {A : Type} : 
    forall (l : list A), l <> [] -> dist A.
  Proof.
    intros ? H.
    remember (Pos.of_nat (List.length l)) as len.
    exact (List.map (fun x =>  (x, mk_prob 1 len)) l).
  Defined.


  (* function that adds all the probabilities  *)
  Definition sum_of_uniform_with_replacement {A : Type} : 
    dist A -> prob.
  Proof.
    intros d.
    exact (List.fold_right 
      (fun '(_, y) acc => add_prob acc y)
      zero d).
  Defined.


  Definition prob_equiv : relation prob := 
    fun p q => prob_eq p q = true.
  
  Local Infix "=p=" := prob_equiv 
    (at level 70, no associativity).
  
    

  Global Instance prob_R : Reflexive (prob_equiv).
  Proof.
    intro x. 
    apply prob_eq_refl.
  Qed.

  Global Instance prob_S : Symmetric (prob_equiv).
  Proof.
    intros [ax px] [ay py] Hxy; subst.
    unfold prob_equiv, prob_eq in * |- *.
    apply PeanoNat.Nat.eqb_eq in Hxy.
    apply PeanoNat.Nat.eqb_eq. nia.
  Qed.

  Global Instance prob_T : Transitive (prob_equiv).
  Proof.
    intros [ax px] [bx qx] [cx rx] Hx Hy.
    unfold prob_equiv, prob_eq in * |- *.
    apply PeanoNat.Nat.eqb_eq in Hx, Hy.
    apply PeanoNat.Nat.eqb_eq. nia.
  Qed.

  
  Global Instance prob_Equiv : Equivalence (prob_equiv).
  Proof.
    constructor; [apply prob_R | apply prob_S | apply prob_T].
  Qed.


  Global Instance add_proper : 
    Proper (prob_equiv ==> prob_equiv ==> prob_equiv) (@add_prob).
  Proof.
    intros [ax px] [bx qx] Hxy [ux uy] [vx vy] Huv.
    unfold add_prob, prob_equiv, prob_eq in * |- *.
    apply PeanoNat.Nat.eqb_eq in Hxy, Huv.
    apply PeanoNat.Nat.eqb_eq.
    repeat rewrite Pos2Nat.inj_mul, 
      PeanoNat.Nat.mul_assoc.
    repeat rewrite PeanoNat.Nat.mul_add_distr_r.
    assert (Ht₁: ax * Pos.to_nat uy * Pos.to_nat qx * Pos.to_nat vy = 
      ax * Pos.to_nat qx * Pos.to_nat uy * Pos.to_nat vy) by nia.
    rewrite Ht₁, Hxy; 
    clear Ht₁.
    assert (Ht₁: ux * Pos.to_nat px * Pos.to_nat qx * Pos.to_nat vy = 
      ux * Pos.to_nat vy * Pos.to_nat px * Pos.to_nat qx) by nia.
    rewrite Ht₁, Huv;
    clear Ht₁. 
    nia.
  Qed.


  Global Instance mul_proper : 
    Proper (prob_equiv ==> prob_equiv ==> prob_equiv) (@mul_prob).
  Proof.
    intros [ax px] [bx qx] Hxy [ux uy] [vx vy] Huv.
    unfold mul_prob, prob_equiv, prob_eq in * |- *.
    apply PeanoNat.Nat.eqb_eq in Hxy, Huv.
    apply PeanoNat.Nat.eqb_eq.
    repeat rewrite Pos2Nat.inj_mul, 
      PeanoNat.Nat.mul_assoc.
    nia.
  Qed.


  Definition prop_Eqdec : forall p q : prob, {p =p= q} + {~(p =p= q)}.
  Proof.
    intros [px qx] [py qy]; 
    unfold add_prob, prob_equiv, prob_eq in * |- *.
    destruct (Nat.eqb (px * Pos.to_nat qy) (py * Pos.to_nat qx)).
    + left; reflexivity.
    + right; intro H; inversion H.
  Defined.


  Lemma one_prob : forall a b, mk_prob a b =p= one <-> a = Pos.to_nat b.
  Proof.
    intros ? ?; simpl; split; intro H.
    unfold one in H.
    unfold prob_equiv, prob_eq in  H.
    apply PeanoNat.Nat.eqb_eq in H. nia.
    unfold one.
    unfold prob_equiv, prob_eq.
    apply PeanoNat.Nat.eqb_eq. 
    nia.
  Qed.

  Lemma eq_prob : forall p, p =p= one <-> num p = Pos.to_nat (denum p).
  Proof.
    intros [ap bp]; simpl; split; intro H.
    apply one_prob in H. nia.
    apply one_prob. nia.
  Qed.


  Lemma fold_right_map_add : forall (A : Type) (l : list A) (k : nat),
    fold_right (λ '(_, y) (acc : prob), add_prob acc y) zero
    (map (λ x : A, (x, {| num := 1; denum := Pos.of_nat k |})) l) =p=
    mk_prob (List.length l) (Pos.of_nat k).
  Proof.
    intros ?. 
    induction l.
    + intros ?; reflexivity.
    + intros ?.  
      rewrite map_cons.
      simpl; specialize (IHl k).
      rewrite add_prob_comm.
      remember (fold_right (λ '(_, y) (acc : prob), add_prob acc y) zero
        (map (λ x : A, (x, {| num := 1; denum := Pos.of_nat k |})) l)) as Hf.
      destruct Hf. simpl.
      apply PeanoNat.Nat.eqb_eq.
      apply PeanoNat.Nat.eqb_eq in IHl.
      rewrite IHl. nia.
  Qed.


  Lemma uniform_with_replacement_adds_to_one {A : Type} : 
    forall (l : list A) (d : dist A) (H₁ : l <> []) 
    (H₂ : d = uniform_with_replacement l H₁), 
    sum_of_uniform_with_replacement d =p= one.
  Proof.
    unfold uniform_with_replacement, 
    sum_of_uniform_with_replacement.
    intros ? ? Hl Hd. 
    subst.
    rewrite fold_right_map_add.
    unfold prob_equiv, one,
    prob_eq.
    apply PeanoNat.Nat.eqb_eq.
    rewrite Nat2Pos.id; try nia. 
    assert (Hw: exists w, length l = S w).
    destruct l. 
    unfold not in Hl; 
    specialize (Hl eq_refl); 
    inversion Hl.
    eexists; simpl;
    eauto.
    destruct Hw as [w Hw]. 
    rewrite Hw.
    nia.
  Qed.
    



  Lemma prob_list : ∀ (A : Type) 
    (xf : A) (pf : prob) (plv : positive) (la : list A), 
    In (xf, pf) (map 
      (λ x : A, (x, {| num := 1; denum := plv |})) la) <->
    In xf la ∧ pf = mk_prob 1 plv.
  Proof.
    intros ? ? ? ? ?.
    revert xf pf plv.
    induction la.
    + intros ? ? ?; 
      split; intro Hin.
      inversion Hin.
      inversion Hin; 
      inversion H.
    + intros ? ? ?; 
      split; 
      intro Hin.
      rewrite map_cons in Hin.
      destruct Hin eqn:Hf.
      inversion e. 
      firstorder.
      pose proof (proj1 (IHla xf pf plv) i) as Hind.
      firstorder.
      rewrite map_cons. simpl.
      destruct Hin as [[Hla | Hlb] Hr].
      ++ left; subst; reflexivity.
      ++ right; apply IHla; firstorder.
  Qed.



  Lemma perm_membership : ∀ (A : Type) 
    (la lb : list A), Permutation la lb -> 
    (∀ x, In x la <-> In x lb) /\ 
    (List.length la = List.length lb).
  Proof.
    intros ? ? ?; split.
    intros x. 
    split; intros Hin.
    apply Permutation_in with (l := la);
    assumption.
    apply Permutation_in with (l := lb).
    apply Permutation_sym; assumption. 
    assumption.
    apply Permutation_length;
    assumption.
  Qed.


  Lemma inject_in_list : ∀ (A : Type) 
    (l : list A) (x : A) (pf : prob), 
    In (x, pf) (map (λ y : A, (y, pf)) l) <-> In x l.
  Proof.
    intros ?.
    induction l.
    + intros ? ?; 
      split; 
      intro Hin.
      inversion Hin.
      inversion Hin.
    + intros ? ?; 
      split; 
      intro Hin.
      rewrite map_cons in Hin.
      simpl. simpl in Hin.
      destruct Hin as [Hl | Hr].
      ++ left; inversion Hl; subst;
         reflexivity.
      ++ right; apply IHl with pf;
         exact Hr.
      ++ rewrite map_cons.
         simpl in Hin.
         simpl. destruct Hin.
         -
         left; subst;
         reflexivity.
         -
         right; apply IHl;
         exact H.
  Qed.


  Lemma list_uniform_dist : ∀ (A : Type) 
    (la lb : list A)  (H₁ : la <> []) (H₂ : lb <> []), 
    List.length la = List.length lb -> 
    (∀ x : A, In x la ↔ In x lb) <-> 
    uniform_with_replacement la H₁ =r=  
    uniform_with_replacement lb H₂.
  Proof.
    intros ? ? ? ? ? Hl; 
    split; intro Hin.
    unfold uniform_with_replacement, dist_equiv.
    split.
    intros [xa pa]; 
    split; intro Hf.
    apply prob_list. 
    apply prob_list in Hf.
    rewrite <-Hl; firstorder.
    apply prob_list. 
    apply prob_list in Hf.
    rewrite Hl. 
    firstorder.
    repeat rewrite map_length;
    assumption.
    unfold uniform_with_replacement, 
    dist_equiv in Hin.
    intros ?; split; intros Hf.
    remember (length lb) as lv.
    assert (Hlv : 0 < lv).
      destruct lb. 
      simpl in Heqlv.
      congruence. 
      simpl in Heqlv.
      nia.
    remember (Pos.of_nat lv) as plv.
    rewrite Hl in Hin.
    rewrite <- Heqplv in Hin.
    remember (mk_prob 1 plv) as pf.
    apply inject_in_list with pf.
    apply Hin, inject_in_list.
    assumption.
    remember (length lb) as lv.
    assert (Hlv : 0 < lv).
      destruct lb. simpl in Heqlv.
      congruence. simpl in Heqlv.
      nia.
    remember (Pos.of_nat lv) as plv.
    rewrite Hl in Hin.
    rewrite <- Heqplv in Hin.
    remember (mk_prob 1 plv) as pf.
    apply inject_in_list with pf.
    apply Hin. apply inject_in_list.
    assumption.
  Qed.


  (* If two lists are permutation of each other, 
    they induce the same distribution *)
  Lemma uniform_dist_inv_permutation : ∀ (A : Type) 
    (la lb : list A) (H₁ : la <> []) (H₂ : lb <> []), 
    Permutation la lb -> 
    uniform_with_replacement la H₁ =r= 
    uniform_with_replacement lb H₂.
  Proof.
    intros * Hp.
    eapply list_uniform_dist.
    apply Permutation_length; 
    assumption.
    pose proof perm_membership _ la lb 
      Hp as [Ha _].
    exact Ha.
  Qed.


  Global Instance proper_fn {A : Type} : 
    Proper (eq ==> @dist_equiv A) (fun x => Ret x).
  Proof.
    intros x y Hxy.
    rewrite Hxy.
    reflexivity.
  Qed.



  Global Instance subrel_eq_respect {A B : Type} 
    (Ra : relation A) 
    (Rb : relation B) 
    (sa : subrelation Ra eq) 
    (sb : subrelation eq Rb) : 
    subrelation eq (respectful Ra Rb).
  Proof. 
    intros f g Hfg.
    Print subrelation. 
    subst. 
    intros a a' Raa'. 
    apply sb.
    f_equal. 
    apply (sa _ _ Raa'). 
  Qed.
  
  Global Instance pointwise_eq_ext {A B : Type} 
    (Rb : relation B) 
    (sb : subrelation Rb eq) : 
    subrelation (pointwise_relation A Rb) eq.
  Proof.
    intros f g Hfg.
    unfold pointwise_relation in Hfg.
    apply functional_extensionality.
    intros. apply sb, Hfg.
  Qed.


  (* joining two probability distribution *)
  Fixpoint join_with {A B C : Type} (f : A -> B -> C) 
    (xs : dist A) (ys : dist B) : dist C :=
    match xs with 
    | [] => [] 
    | (ax, px) :: tx =>  
      List.map (fun '(ut, pt) => (f ax ut, mul_prob px pt)) ys 
      ++ join_with f tx ys
    end.


  Fixpoint fmap {A B : Type} (f : A -> B) (xs : dist A) : dist B :=
    match xs with 
    | [] => []
    | (ax, px) :: tx => (f ax, px) :: fmap f tx 
    end.


  Lemma fmap_identity : ∀ (T : Type) (x : dist T), fmap id x = x.
  Proof.
    intro T. 
    induction x; 
    simpl; 
    try reflexivity.
    destruct a. 
    rewrite IHx. 
    reflexivity.
  Qed.


  Lemma fmap_compose : ∀ (T U V : Type) 
    (f : T → U) (g : U → V) (x : dist T),
    fmap (PreFun.compose g f) x = fmap g (fmap f x).
  Proof.
    intros ? ? ? ? ?. 
    induction x; 
    simpl; try reflexivity.
    destruct a; simpl. 
    rewrite IHx; 
    reflexivity.
  Qed.


  Global Instance dist_functor : Functor dist.
  Proof.
    constructor. 
    intros ? ? f Ha. 
    exact (@fmap A B f Ha).
  Defined.


  Global Instance dist_functor_law : 
    FunctorLaws dist_functor.
  Proof.
    constructor.
    + apply fmap_identity.
    + apply fmap_compose.
  Defined. 

End Distr.


Section Event.

  Context 
    {A : Type}
    (Hdec: forall x y : A, {x = y} + {x <> y}).


  (* event as a boolean function (computable) *)
  Definition event := A -> bool.


  (* complement of an evant *)
  Definition comp_event (e : event) := 
    fun x => negb (e x).

  (* list of event in the probability distribution *)
  Definition list_of_events (e : event) (xs : dist A) : dist A  := 
    List.filter (fun '(x, y) => e x) xs. 

  (* sum of the probabilities in the distribution *)
  Definition prob_of_an_event (e : event ) (xs : dist A) : prob := 
    List.fold_right (fun '(tx, bx) ax => add_prob ax bx) 
    zero (list_of_events e xs).
  
  
  Definition union_of_events (e₁ e₂ : event) (xs : dist A) : dist A :=
    List.filter (fun '(x, y) => orb (e₁ x) (e₂ x)) xs.

  Definition intersection_of_events (e₁ e₂ : event) 
    (xs : dist A) : dist A := 
    List.filter (fun '(x, y) => andb (e₁ x) (e₂ x)) xs.
  
  (* Non dependent function that sums all the probabilites  *)
  Fixpoint rec_sum_prob (l : dist A) : prob :=
    match l with 
    | [] => zero
    | (_, h) :: t => add_prob h (rec_sum_prob t)
    end. 


  Local Infix "=r=" := dist_equiv 
  (at level 70, no associativity).


  (* A ∪ B =r= A + B - A ∩ B *)
  Theorem union_intersection_proof : 
    forall (xs : dist A) (e1 e2 : event), 
    (union_of_events e1 e2 xs ++ intersection_of_events e1 e2 xs) =r= 
    (list_of_events e1 xs ++ list_of_events e2 xs).
  Proof.
    intros ?.
    unfold union_of_events, 
    intersection_of_events,
    list_of_events.
    induction xs.
    + simpl; 
      intros ? ?;
      reflexivity.
    + simpl; intros ? ?. 
      destruct a as [ap bp].
      destruct (e1 ap) eqn:He1; 
      destruct (e2 ap) eqn:He2; 
      simpl.
      apply cons_proper.
      rewrite dist_equiv_inv_comm.
      assert (Hf: filter (λ '(x, _), e1 x) xs ++ (ap, bp) :: filter (λ '(x, _), e2 x) xs  =r= 
        (ap, bp) :: filter (λ '(x, _), e2 x) xs ++ filter (λ '(x, _), e1 x) xs).
      rewrite dist_equiv_inv_comm. 
      reflexivity.
      rewrite Hf; simpl. 
      apply cons_proper.
      rewrite dist_equiv_inv_comm. 
      clear Hf.
      assert (Hf: filter (λ '(x, _), e2 x) xs ++ filter (λ '(x, _), e1 x) xs =r=
        filter (λ '(x, _), e1 x) xs ++ filter (λ '(x, _), e2 x) xs).
      rewrite dist_equiv_inv_comm; reflexivity.
      rewrite Hf, IHxs; reflexivity.
      apply cons_proper, IHxs; reflexivity.
      assert (Hf: filter (λ '(x, _), e1 x) xs ++ (ap, bp) :: filter (λ '(x, _), e2 x) xs =r= 
        (ap, bp) :: filter (λ '(x, _), e2 x) xs ++ filter (λ '(x, _), e1 x) xs).
      rewrite dist_equiv_inv_comm; reflexivity.
      rewrite Hf.
      apply cons_proper.
      clear Hf.
      assert (Hf : filter (λ '(x, _), e2 x) xs ++ filter (λ '(x, _), e1 x) xs =r= 
        filter (λ '(x, _), e1 x) xs ++ filter (λ '(x, _), e2 x) xs).
      rewrite dist_equiv_inv_comm.
      reflexivity.
      rewrite Hf, IHxs; reflexivity.
      apply IHxs.
  Qed.


  (* Event and its complement preservs the universe (modulo =r=)*)
  Lemma universe_event_comp_event : 
    forall (l : dist A) (f : event),
    List.filter (fun '(x, _) => f x) l ++ 
    List.filter (fun '(x, _) => comp_event f x) l =r= l.
  Proof.
    intros ?; 
    unfold comp_event.
    induction l.
    + simpl; intros ?; 
      reflexivity.
    + destruct a as (a & ap); 
      simpl; intros ?.
      refine (match (f a) as a' return f a = a' -> _ with 
        | true => fun Ht => _  
        | false => fun Hf => _ 
      end eq_refl).
      rewrite Ht; simpl;
      rewrite IHl; reflexivity.
      rewrite Hf; simpl.
      rewrite dist_equiv_inv_comm.
      simpl. 
      apply cons_proper.
      rewrite dist_equiv_inv_comm.
      rewrite IHl; reflexivity.
  Qed.

  Local Infix "=p=" := prob_equiv 
    (at level 70, no associativity).

 


  Lemma sum_prob_event_comp_event : 
    forall (l : dist A) (f : event),
    rec_sum_prob l =p= 
    add_prob (prob_of_an_event f l) (prob_of_an_event (comp_event f) l).
  Proof.
    intros ?. 
    unfold prob_of_an_event, comp_event.
    induction l; 
    intros ?; 
    simpl in * |- *.
    + subst; simpl; reflexivity.
    + destruct a as (ap & bp).
      destruct (f ap) eqn:Hf.
      simpl. 
      assert (Hft: add_prob
        (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (list_of_events f l)) bp =
        add_prob bp
        (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (list_of_events f l))). 
      rewrite add_prob_comm;
      reflexivity.
      rewrite Hft; 
      clear Hft.
      rewrite add_prob_assoc.
      apply add_proper.
      reflexivity. 
      apply IHl.
      simpl.
      assert (Hft: (add_prob
        (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (list_of_events (λ x : A, negb (f x)) l)) bp) = 
        (add_prob bp
        (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (list_of_events (λ x : A, negb (f x)) l)))). 
      rewrite add_prob_comm.
      reflexivity.
      rewrite Hft; clear Hft.
      assert (Hft:
      add_prob
      (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (list_of_events f l))
      (add_prob bp
        (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (list_of_events (λ x : A, negb (f x)) l))) = 
      add_prob 
      (add_prob bp
        (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (list_of_events (λ x : A, negb (f x)) l)))
        (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (list_of_events f l))).
      rewrite add_prob_comm; 
      reflexivity.
      rewrite Hft; clear Hft.
      rewrite add_prob_assoc.
      apply add_proper.
      reflexivity. 
      rewrite add_prob_comm.  
      apply IHl.
  Qed.

  Lemma rec_sum_prob_eq_sum_of_uniform_with_replacement : 
    forall l, 
    rec_sum_prob l =p= 
    sum_of_uniform_with_replacement l.
  Proof.
    induction l as [|(ax, ay) l IHl]. 
    + simpl; reflexivity.
    + simpl. rewrite IHl.
      rewrite add_prob_comm.
      reflexivity.
  Qed.

  Lemma sum_of_uniform_prob_event_comp_event : 
    forall (l : dist A) (f : event),
    sum_of_uniform_with_replacement l =p= 
    add_prob (prob_of_an_event f l) (prob_of_an_event (comp_event f) l).
  Proof.
    intros *.
    rewrite <-rec_sum_prob_eq_sum_of_uniform_with_replacement.
    apply sum_prob_event_comp_event.
  Qed.
  
  

  Local Infix "<p=" := (leq) (at level 70).

  Lemma fold_right_filter_map_add_zero : forall (e : event) l k, 
    fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
    (filter (λ '(x, _), e x) 
      (map (λ x : A, (x, {| num := 1; denum := Pos.of_nat k |})) l)) <p= 
      mk_prob (List.length l) (Pos.of_nat k) = true.
  Proof.
    intros ? ?.
    induction l.
    + simpl; reflexivity.
    + intros ?. 
      rewrite map_cons.
      destruct (e a) eqn:H.
      simpl. 
      rewrite H; simpl.
      rewrite add_prob_comm.
      destruct (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (filter (λ '(x, _), e x)
        (map (λ x : A, (x, {| num := 1; denum := Pos.of_nat k |})) l))) eqn:Hf.
      simpl in * |- *.
      apply PeanoNat.Nat.leb_le.
      specialize (IHl k). 
      rewrite Hf in IHl. 
      simpl in IHl.
      apply PeanoNat.Nat.leb_le in IHl. 
      nia.
      (* false case *)
      simpl. 
      rewrite H.
      destruct (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
        (filter (λ '(x, _), e x)
        (map (λ x : A, (x, {| num := 1; denum := Pos.of_nat k |})) l))) eqn:Hf.
      simpl in * |- *.
      specialize (IHl k).
      rewrite Hf in IHl. 
      simpl in IHl.
      apply PeanoNat.Nat.leb_le in IHl. 
      apply PeanoNat.Nat.leb_le. 
      nia.
  Qed.


  (* Probability of an event is bounded between 0 and 1 (included) *)
  Lemma event_uniform_prob : forall (e : event) (l : list A) 
    (H : l <> []) (xs : dist A) pevent, 
    xs = uniform_with_replacement l H -> 
    pevent = prob_of_an_event e xs -> 
    zero <p= pevent = true ∧ pevent <p= one = true.
  Proof.
    unfold uniform_with_replacement, 
    prob_of_an_event, 
    list_of_events.
    intros ? ? ? ? ? Hxs Hpevent.
    rewrite Hpevent, Hxs. 
    split.
    pose proof (fold_right_filter_map_add_zero e l (length l)) as Hf.
    destruct (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
      (filter (λ '(x, _), e x)
      (map (λ x : A, (x, {| num := 1; denum := Pos.of_nat (length l) |})) l))) eqn:Hff.
    simpl in * |- *; reflexivity.
    pose proof (fold_right_filter_map_add_zero e l (length l)) as Hf.
    destruct (fold_right (λ '(_, bx) (ax : prob), add_prob ax bx) zero
      (filter (λ '(x, _), e x)
      (map (λ x : A, (x, {| num := 1; denum := Pos.of_nat (length l) |})) l))) eqn:Hff.
    simpl in * |- *. 
    apply PeanoNat.Nat.leb_le. 
    apply PeanoNat.Nat.leb_le in Hf.
    nia.
  Qed.

  (* choice p a b := selects a with probablity p and 
     b with probability 1 - p *)
  Definition choice (p : prob) (a b : A) : dist A :=
    [(a, p); (b, mk_prob (Pos.to_nat (denum p) - num p) (denum p))].


  Lemma choice_correct : ∀ (p : prob) (a b : A), 
    zero <p= p = true -> 
    p <p= one = true -> 
    rec_sum_prob (choice p a b) =p= one.
  Proof.
    intros ? ? ? Hzero Hone.
    unfold choice. 
    destruct p as (ap & bp). 
    simpl.
    apply one_prob. 
    assert (Ht : Pos.to_nat (bp * 1) = Pos.to_nat bp) by nia.
    rewrite Ht; clear Ht.
    assert (Ht : (Pos.to_nat bp - ap) * Pos.to_nat 1 + 0 = 
      (Pos.to_nat bp - ap)).
    nia.
    rewrite Ht; clear Ht.
    rewrite PeanoNat.Nat.mul_sub_distr_r.
    assert (Ht : Pos.to_nat (bp * (bp * 1)) = Pos.to_nat (bp * bp)).
    nia. 
    rewrite Ht; clear Ht.
    rewrite Minus.le_plus_minus_r. 
    nia.
    apply leq_prob in Hone.
    simpl in Hone. nia.
  Qed.




End Event.

Section Example.

    Export MonadNotation.
    Open Scope monad_scope.

    Fact Hneq : [1; 2; 3; 4] <> [].
    Proof.
        intro H; inversion H.
    Defined. 

    Eval compute in uniform_with_replacement [1; 2; 3; 4] Hneq.
    (*
      [(1, {| num := 1; denum := 4 |}); (2, {| num := 1; denum := 4 |});
       (3, {| num := 1; denum := 4 |}); (4, {| num := 1; denum := 4 |})]
     : dist nat
    *)
    
    (*
    Definition prob1 (l : list nat) (H : l <> []):=
      Bind (uniform_with_replacement l H) (fun x => 
        Bind (uniform_with_replacement l H) (fun y => 
          Ret (x * y, x, y))). 
    *)
    Definition prob1 (l : list nat) (H : l <> []) :=
      x <- uniform_with_replacement l H ;;
      y <- uniform_with_replacement l H ;; 
      ret  (x * y, x, y).

    (*
    Definition prob2 (l : list nat) (H : l <> []) :=
      Bind (uniform_with_replacement l H) (fun y => 
        Bind (uniform_with_replacement l H) (fun x => 
          Ret (y * x, y, x))).
    *)

    Definition prob2 (l : list nat) (H : l <> []) :=
      y <- uniform_with_replacement l H ;;
      x <- uniform_with_replacement l H ;; 
      ret  (y * x, y, x).
  
    Eval compute in prob1 [1; 2; 3; 4] Hneq.
    (*
      [(1, 1, 1, {| num := 1; denum := 16 |});
       (2, 1, 2, {| num := 1; denum := 16 |});
       (3, 1, 3, {| num := 1; denum := 16 |});
       (4, 1, 4, {| num := 1; denum := 16 |});
       (2, 2, 1, {| num := 1; denum := 16 |});
       (4, 2, 2, {| num := 1; denum := 16 |});
       (6, 2, 3, {| num := 1; denum := 16 |});
       (8, 2, 4, {| num := 1; denum := 16 |});
       (3, 3, 1, {| num := 1; denum := 16 |});
       (6, 3, 2, {| num := 1; denum := 16 |});
       (9, 3, 3, {| num := 1; denum := 16 |});
       (12, 3, 4, {| num := 1; denum := 16 |});
       (4, 4, 1, {| num := 1; denum := 16 |});
       (8, 4, 2, {| num := 1; denum := 16 |});
       (12, 4, 3, {| num := 1; denum := 16 |});
       (16, 4, 4, {| num := 1; denum := 16 |})]
     : dist (nat * nat * nat)
    *)

    Eval compute in prob2 [1; 2; 3; 4] Hneq.
    (*
       [(1, 1, 1, {| num := 1; denum := 16 |});
       (2, 1, 2, {| num := 1; denum := 16 |});
       (3, 1, 3, {| num := 1; denum := 16 |});
       (4, 1, 4, {| num := 1; denum := 16 |});
       (2, 2, 1, {| num := 1; denum := 16 |});
       (4, 2, 2, {| num := 1; denum := 16 |});
       (6, 2, 3, {| num := 1; denum := 16 |});
       (8, 2, 4, {| num := 1; denum := 16 |});
       (3, 3, 1, {| num := 1; denum := 16 |});
       (6, 3, 2, {| num := 1; denum := 16 |});
       (9, 3, 3, {| num := 1; denum := 16 |});
       (12, 3, 4, {| num := 1; denum := 16 |});
       (4, 4, 1, {| num := 1; denum := 16 |});
       (8, 4, 2, {| num := 1; denum := 16 |});
       (12, 4, 3, {| num := 1; denum := 16 |});
       (16, 4, 4, {| num := 1; denum := 16 |})]
     : dist (nat * nat * nat)
    *)

    Local Infix "=r=" := dist_equiv 
    (at level 70, no associativity).

    (* Two probability distributions are same *)
    Lemma similar_distribution : forall (l : list nat) (H : l <> []),  
      @prob1 l H =r= @prob2 l H.
    Proof.
      intros *.
      unfold prob1, prob2. 
      simpl. 
      reflexivity.
    Qed.

End Example.

(* Not need for my crypto project but it's fun to 
  formalise *)
Section Uniform_Without_Replacement.

  (* uniform without replacement *)
  Theorem uniform_without_replacement {A : Type} : 
    forall (l : list A), l <> [] -> dist A.
  Proof.
   induction l.
   + intro Hf; unfold not in Hf; 
     specialize (Hf eq_refl); inversion Hf.
   + intro Hal. destruct l as [| hd tl].
    ++ (* one element case *) exact [(a, mk_prob 1 1)].
    ++ (* inductive case *)
       assert (Hne: hd :: tl <> []). 
       intro Hf; inversion Hf.
       remember (Pos.of_nat (List.length (a :: hd :: tl))) as hdl.
       exact ((a, mk_prob 1 hdl) :: (IHl Hne)).
  Defined.


  Theorem list_not_empty : forall (A : Type) 
    (l tl: list A) (h : A), l = h :: tl -> l <> [].
  Proof.
    intros ? ? ? ? ? H; 
    subst; 
    inversion H.
  Qed.

  (* The probability of the first element is same in both cases *)
  Theorem uniform_prop : forall (A : Type) 
    (l tl: list A) (h : A) (H : l = h :: tl), 
    List.hd_error (uniform_with_replacement l (list_not_empty A l tl h H)) =
    List.hd_error (uniform_without_replacement l (list_not_empty A l tl h H)).
  Proof.
    intros ? ? ? ? ?; 
    subst; simpl.
    destruct tl; simpl. 
    all: reflexivity.
  Qed.


  (* We can simulate without replacement with replacement by 
    computing the distribution and deleting the elements *)
  Theorem multi_uniform_with_replacement {A : Type} : 
    forall (l : list A), l <> [] -> dist A.
  Proof.
    induction l.
    + intro H; 
      unfold not in H; 
      specialize (H eq_refl); 
      inversion H.
    + destruct l.
      ++ intro H. 
         exact (uniform_with_replacement [a] H).
      ++ (* induction case *)
         assert (Ht : a0 :: l <> []). 
         intro H; 
         inversion H.
         intro H. 
         exact ((List.hd (a, mk_prob 0 xH) 
          (uniform_with_replacement (a :: a0 :: l) H)) :: (IHl Ht)).
  Defined.

  Lemma connection_mult_uniform_with_replacement_uniform_without_replacement :
    forall (A : Type)  (l : list A) (H : l <> []),
    multi_uniform_with_replacement l H = uniform_without_replacement l H.
  Proof.
    intros ?. 
    induction l.
    + intro H. 
      unfold not in H. 
      refine (match H with
        | _ => _ 
      end ); specialize (f eq_refl); 
      inversion f.
    + intro H; 
      unfold not in H.
      destruct l.
      ++ simpl. 
         unfold uniform_with_replacement. 
         simpl; reflexivity.
      ++ assert (Ht : a0 :: l <> []). 
         intro Hw; inversion Hw.
         specialize (IHl Ht). 
        simpl. f_equal.
  Qed.

End Uniform_Without_Replacement.



  




    







  

  






