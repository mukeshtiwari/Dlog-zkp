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

  Section EncDec.   
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

  End EncDec.

  (* Not needed for now *)
  Section Ballot.


    (* It combines two vectors pointwise using the function (f : R -> T -> U) *)
    Definition zip_with {R T U : Type} : 
      forall {n : nat}, (R -> T -> U) ->  
      Vector.t R n -> Vector.t T n -> Vector.t U n.
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
    
    


    Definition encrypted_ballot {n : nat} 
      (ms rs : Vector.t F n) : Vector.t (G * G) n :=
      zip_with (fun m r => enc m r) ms rs.

    Definition decrypted_ballot {n : nat} 
      (cs : Vector.t (G * G) n) : Vector.t G n :=
      map (fun c => dec c) cs.

    Definition re_encryption_ballot {n : nat} 
      (cs : Vector.t (G * G) n) (rs : Vector.t F n) : 
      Vector.t (G * G) n :=
      zip_with (fun c r => re_enc c r) cs rs.

    Definition mul_encrypted_ballots {n : nat} 
      (us vs : Vector.t (G * G) n) : Vector.t (G * G) n := 
      zip_with (fun c₁ c₂ => mul_cipher c₁ c₂) us vs.

    Definition raise_message_gen {n : nat} 
      (ms : Vector.t F n) : Vector.t G n := 
      map (fun m => g^m) ms.

    Lemma vector_inv_0 {R : Type} (v : Vector.t R 0) :
      v = @Vector.nil R.
    Proof.
      refine (match v with
              | @Vector.nil _ => _
              end).
      reflexivity.
    Defined.
  
    Lemma vector_inv_S {R : Type} (n : nat) (v : Vector.t R (S n)) :
      {x & {v' | v = @Vector.cons _ x _ v'}}.
    Proof.
      refine (match v with
              | @Vector.cons _ x _ v' =>  _
              end);
      eauto.
    Defined.
    
    
    (* When we decrypt an encrypted ballot, we get group element, g^m, and 
      one way to recover this m is to write a formally verified discrete logarithm 
      algorithm, or write an OCaml code *)
    Lemma ballot_encryption_decryption_raise_message: 
      forall (n : nat) (ms rs : Vector.t F n) (cs :  Vector.t (G * G) n), 
      cs = encrypted_ballot ms rs -> 
      raise_message_gen ms = decrypted_ballot cs.
    Proof.
      induction n.
      + intros ? ? cs ->. 
        refine (match ms, rs with 
          | nil _, nil _ => _ 
          end).
        reflexivity.
      + intros ? ? cs ->.
        pose proof (vector_inv_S _ ms) as (hms & tms & Hms).
        pose proof (vector_inv_S _ rs) as (hrs & trs & Hrs).
        rewrite Hms, Hrs; simpl. 
        f_equal.
        rewrite Hk. 
        repeat rewrite smul_pow_up, 
        smul_pow_mul, <-associative, right_inverse, 
        right_identity; reflexivity.
        apply IHn with  (rs := tl rs).
        unfold encrypted_ballot.
        rewrite Hrs; simpl.
        reflexivity.
    Qed.


    Lemma ballot_re_encryption_decryption_raise_message : 
      forall (n : nat) (ms rs₁ rs₂: Vector.t F n) cs₁ cs₂, 
      cs₁ = encrypted_ballot ms rs₁ -> 
      cs₂ = re_encryption_ballot cs₁ rs₂ -> 
      raise_message_gen ms = decrypted_ballot cs₂.
    Proof.
      induction n.
      + intros ? ? ? ? ? Hcs₁ ->. 
        rewrite Hcs₁; clear Hcs₁; 
        clear cs₁.
        refine (match ms, rs₁, rs₂ with 
          | nil _, nil _, nil _ => _ 
          end).
        reflexivity.
      + intros ? ? ? ? ? Hcs₁ ->. 
        rewrite Hcs₁; clear Hcs₁; clear cs₁.
        pose proof (vector_inv_S _ ms) as (hms & tms & Hms).
        pose proof (vector_inv_S _ rs₁) as (hrs₁ & trs₁ & Hrs₁).
        pose proof (vector_inv_S _ rs₂) as (hrs₂ & trs₂ & Hrs₂).
        rewrite Hms, Hrs₁, Hrs₂; simpl.
        f_equal.
        rewrite Hk. 
        repeat rewrite smul_pow_up,
        smul_pow_mul.
        assert (Ht : 
          (gop (gop (g ^ hms) (g ^ (x * hrs₁))) 
              (g ^ (x * hrs₂))) = 
          (gop (g ^ hms) 
               (gop (g ^ (x * hrs₁)) 
                    (g ^ (x * hrs₂))))).
        rewrite <- (@monoid_is_associative G (@eq G) gop gid). 
        reflexivity. 
        typeclasses eauto.
        assert (Htv : hrs₂ * x = x * hrs₂). 
        rewrite commutative;
        reflexivity. 
        rewrite <-Htv in Ht.  
        rewrite Ht. 
        clear Ht.
        rewrite <- smul_distributive_fadd.
        rewrite <- (@monoid_is_associative G (@eq G) gop gid).
        assert (Htt: gop (g ^ hrs₁) (g ^ hrs₂) ^ x = 
          gop (g ^ (hrs₁ * x)) (g ^ (hrs₂ * x))).
        rewrite <- smul_distributive_fadd.
        rewrite <- (@vector_space_smul_associative_fmul 
            F (@eq F) zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow).
        rewrite (@commutative_ring_is_commutative F (@eq F) zero one opp add sub mul).
        rewrite (@ring_is_left_distributive F (@eq F) zero one opp add sub mul).
        rewrite (@vector_space_smul_distributive_fadd 
          F (@eq F) zero one add mul sub div 
          opp inv G (@eq G) gid ginv gop gpow).
        assert (Hwt₁: x * hrs₁ = hrs₁ * x). 
        rewrite commutative; reflexivity.
        rewrite Hwt₁.
        assert (Hwt₂: x * hrs₂ = hrs₂ * x). 
        rewrite commutative; reflexivity.
        rewrite Hwt₂. 
        reflexivity.
        typeclasses eauto.
        typeclasses eauto.
        typeclasses eauto.
        typeclasses eauto.
        rewrite Htt.
        rewrite <- (@vector_space_smul_distributive_fadd 
          F (@eq F) zero one add mul sub div 
          opp inv G (@eq G) gid ginv gop gpow).
        assert (Hwt₁: x * hrs₁ = hrs₁ * x). 
        rewrite commutative; reflexivity.
        rewrite <-Hwt₁.
        assert (Hwt₂: x * hrs₂ = hrs₂ * x). 
        rewrite commutative; reflexivity.
        rewrite <-Hwt₂. 
        rewrite right_inverse, right_identity;
        reflexivity. 
        typeclasses eauto. 
        typeclasses eauto.
        exact (IHn tms trs₁ trs₂ 
          (encrypted_ballot tms trs₁) 
          (re_encryption_ballot 
            (encrypted_ballot tms trs₁) trs₂)
          eq_refl eq_refl).
    Qed.
    
    
  End Ballot.
        

End Elgamal.



