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
  
  

End Elgamal.  


