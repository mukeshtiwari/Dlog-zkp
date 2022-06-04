Require Import Setoid
    Sigma.Algebra.Hierarchy
    Sigma.Algebra.Group Sigma.Algebra.Monoid
    Sigma.Algebra.Field Sigma.Algebra.Integral_domain
    Sigma.Algebra.Ring Sigma.Algebra.Vector_space
    Lia Vector Coq.Unicode.Utf8 Fin.


Section Elgamal.

  (* Underlying Field of Vector Space *)
  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}.

  (* Vector Element *)
  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Hvec: @vector_space F (@eq F) zero one add mul sub 
      div opp inv G (@eq G) gid ginv gop gpow}.

  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.

  Context 
    (x : F) (* private key *)
    (g h : G) (* group generator and public key *)
    (Hk : h = g^x).

  Definition enc (m : F) (r : F) : G * G := 
    (g^r, gop (g^m) (h^r)).

  Definition dec (c : G * G) := 
    match c with
    |(c₁, c₂) => gop c₂ (ginv (c₁^x))
    end.

  
    (* encryption and decryption lemma.
      Note that we are getting g^m back, not m, 
      so we need to run a proof search to recover 
      m from g^m 
    *)
  Lemma dec_is_left_inv_of_enc : 
    forall (c d : G) (r m : F), 
    (c, d) = enc m r -> g^m = dec (c, d).
  Proof. 
    unfold enc, dec; 
    intros ? ? ? ? H;
    inversion H; clear H. 
    rewrite Hk.
    rewrite <- !(@vector_space_smul_associative_fmul F (@eq F) 
      zero one add mul sub div 
      opp inv G (@eq G) gid ginv gop gpow Hvec).
    setoid_rewrite <- (@monoid_is_associative G (@eq G) gop gid).
    rewrite <- commutative.
    rewrite (@commutative_ring_is_commutative F (@eq F) 
      zero one opp add sub mul).
    rewrite (@group_is_right_inverse G (@eq G) gop gid ginv).
    rewrite left_identity. 
    exact eq_refl.
    typeclasses eauto.
    typeclasses eauto.
    typeclasses eauto.
  Qed.
  
  
  (* Re Encryption of cipher text *)
  Definition re_enc (c : G * G) (r : F) : G * G := 
    match c with
    |(c₁, c₂) => (gop c₁ (g^r), gop c₂ (h^r))
    end.

  
  (* re_encryption decrypts to the same value *)
  Lemma dec_re_enc_left_inv : 
    forall c d e f r₁ r₂ m, 
    (c, d) = enc m r₁ -> 
    (e, f) = re_enc (c, d) r₂ -> 
    g^m = dec (e, f).
  Proof. 
    unfold re_enc, enc, dec.
    intros ? ? ? ? ? ? ? H₁ H₂. 
    inversion H₁; clear H₁. 
    inversion H₂; clear H₂.
    rewrite Hk in * |- *.
    subst.
    remember (gop (g ^ r₁) (g ^ r₂) ^ x) as t.
    rewrite <- smul_distributive_fadd in Heqt.
    rewrite <- (@vector_space_smul_associative_fmul 
      F (@eq F) zero one add mul sub div 
      opp inv G (@eq G) gid ginv gop gpow) in Heqt.
    rewrite (@commutative_ring_is_commutative 
      F (@eq F) zero one opp add sub mul) in Heqt.
    rewrite (@ring_is_left_distributive 
      F (@eq F) zero one opp add sub mul) in Heqt.   
    repeat rewrite smul_pow_up.
    assert (Ht : (gop (gop (g ^ m) (g ^ (x * r₁))) (g ^ (x * r₂)) = 
          (gop (g ^ m) (gop (g ^ (x * r₁)) (g ^ (x * r₂)))))).
    rewrite <- (@monoid_is_associative G (@eq G) gop gid). 
    reflexivity. 
    typeclasses eauto.
    rewrite Ht; clear Ht. 
    rewrite <- smul_distributive_fadd.
    rewrite <- (@monoid_is_associative G (@eq G) gop gid).
    rewrite Heqt. 
    rewrite (@group_is_right_inverse G (@eq G) gop gid ginv).
    rewrite monoid_is_right_identity. 
    reflexivity.
    typeclasses eauto.
    typeclasses eauto.
    typeclasses eauto.
    typeclasses eauto.
    typeclasses eauto.
  Qed.
  
  
  (* mulitply two cipher text *)
  Definition mul_cipher (c₁ c₂ : G * G) : G * G :=
    match c₁, c₂ with
    |(c₁, d₁), (c₂, d₂) => (gop c₁ c₂, gop d₁ d₂)
    end.

  (* 
  Not working! 
  Add Field cField : field_theory_for_stdlib_tactic.
  *)

  Lemma additive_homomorphic_property : 
    forall c d e f r₁ r₂ m₁ m₂, 
    (c, d) = enc m₁ r₁ -> 
    (e, f) = enc m₂ r₂ -> 
    g^(m₁ + m₂) = dec (mul_cipher (c, d) (e, f)).
  Proof.
    unfold re_enc, enc, dec, mul_cipher.
    intros ? ? ? ? ? ? ? ? H1 H2.
    inversion H1; clear H1; 
    inversion H2; clear H2.
    rewrite Hk in * |- *.
    subst.
    remember (gop (g ^ r₁) (g ^ r₂) ^ x) as t.
    rewrite <- smul_distributive_fadd in Heqt.
    rewrite <- (@vector_space_smul_associative_fmul 
      F (@eq F) zero one add mul sub div 
      opp inv G (@eq G) gid ginv gop gpow) in Heqt.
    rewrite (@commutative_ring_is_commutative 
      F (@eq F) zero one opp add sub mul) in Heqt.
    rewrite (@ring_is_left_distributive 
      F (@eq F) zero one opp add sub mul) in Heqt.
    rewrite Heqt.
    rewrite connection_between_vopp_and_fopp.
    repeat rewrite smul_pow_up.
    repeat rewrite <- smul_distributive_fadd.
    assert (Htt: x * r₁ + m₂ = m₂ + x * r₁).
      rewrite commutative; reflexivity.
    rewrite associative. 
    assert (Htv: m₁ + x * r₁ + m₂ = m₁ + (x * r₁ + m₂)).
      rewrite associative; reflexivity.
    rewrite Htv, Htt, associative.
    clear Htt; clear Htv; clear Heqt.
    assert(Htt: m₁ + m₂ + x * r₁ + x * r₂ + opp (x * r₁ + x * r₂) = 
      m₁ + m₂ + (x * r₁ + x * r₂ + opp (x * r₁ + x * r₂))).
      repeat rewrite associative; reflexivity.
    rewrite Htt, field_zero_iff_right, right_identity;
    reflexivity.
    typeclasses eauto.
    typeclasses eauto.
    typeclasses eauto.
  Qed.

  


  

  

End Elgamal.  


