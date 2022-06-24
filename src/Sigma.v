Require Import Setoid
  Sigma.Algebra.Hierarchy
  Sigma.Algebra.Group Sigma.Algebra.Monoid
  Sigma.Algebra.Field Sigma.Algebra.Integral_domain
  Sigma.Algebra.Ring Sigma.Algebra.Vector_space
  Lia Vector Coq.Unicode.Utf8 Sigma.Prob
  Sigma.Distr Psatz
  ExtLib.Structures.Monad
  Coq.Bool.Bool.
      
Import 
  MonadNotation 
  VectorNotations.

Local Open Scope monad_scope.

Module Zkp.

  (* Discrete Logarithm Zero Knowlege Proof *) 
  Section DL. 
    (* Underlying Field of Vector Space *)
    Context 
      {F : Type}
      {zero one : F} 
      {add mul sub div : F -> F -> F}
      {opp inv : F -> F}
      {Fdec: forall x y : F, {x = y} + {x <> y}}. 
      (* decidable equality on Field *)

    (* Vector Element *)
    Context 
      {G : Type} 
      {gid : G} 
      {ginv : G -> G}
      {gop : G -> G -> G} 
      {gpow : G -> F -> G}
      {Hvec: @vector_space F (@eq F) zero one add mul sub 
        div opp inv G (@eq G) gid ginv gop gpow}
      {Gdec : forall x y : G, {x = y} + {x <> y}}. 
      (* decidable equality on G *)
    
    Lemma gdec_true : forall x y, 
      (if Gdec x y then true else false) = true <-> x = y.
    Proof.
      intros ? ?.
      destruct (Gdec x y); split; 
      intro H; auto.
      inversion H.
    Qed.

    Lemma gdec_false : forall x y, 
      (if Gdec x y then true else false) = false <-> x <> y.
    Proof.
      intros ? ?.
      destruct (Gdec x y); split; 
      intro H; auto.
      inversion H. 
      congruence.
    Qed.

    Lemma gdec_eq_true : forall x, 
      (if Gdec x x then true else false) = true.
    Proof.
      intros ?.
      destruct (Gdec x x).
      reflexivity.
      congruence.
    Qed.

    

    Local Infix "^" := gpow.
    Local Infix "*" := mul.
    Local Infix "/" := div.
    Local Infix "+" := add.
    Local Infix "-" := sub.



    (* sigma protocol for proof of knowledge of discrete logarithm *)
    (* A prover is convincing a verified that she know the discrete log, 
      log_{g} h = x. We will turn this into NIZK by Fiat-Shamir transform 
      (careful )*)
   
    Record sigma_proto {n m r : nat}:= 
      mk_sigma 
      {
        announcement : Vector.t G n; 
        challenge : Vector.t F m; 
        response : Vector.t F r
      }.
      (* 
      I am not adding any axioms because it will 
      depend on how we componse the protocols. 
      *)

    Notation "( a ; c ; r )" := 
      (@mk_sigma _ _ _ a c r).

    
  
    Section Basic_sigma.

      (* 
        x is a secret that a prover tries to convince a verifier, 
        g and h are public value, in a group, and the relation 
        is discrete log ∃ x : F, g ^ x = h. 
      *)
      Section Def.
      
        (* x is a secret *)
        Context (x : F) (g h : G). 
        (* h = g^x *)
      

        (* Real transcript, using the witness x *)
        Definition schnorr_protocol (r : F) (c : F) : sigma_proto := 
          ([g^r]; [c]; [r + c * x]).

        (* Fake transcript without the witness x, simulator with 
          random r and c *)
        Definition schnorr_simulator (r c : F) : sigma_proto := 
          ([gop (g^r) (h^(opp c))]; [c]; [r]).

        (* 
          (a, c, r)
          g^res = ann * h ^ cha
        *)
        Definition accepting_conversation (v : @sigma_proto 1 1 1) : bool :=
          match v with
          | (a; c; r) =>  
            match Gdec (g^(hd r)) (gop (hd a) (h^(hd c))) with 
            | left _ => true
            | right _ => false 
            end
          end.

      End Def.

      Section Proofs.

        Context (x : F) (g h : G) (key_rel : h = g^x).

        (* Sigma protocol is correct.
          For some randomness r (a = g^r) and challenge c, 
          (schnorr_protocol x g r c) returns 
          an accepting conversation (a₁; c₁; r₁) 
        *)
        Lemma schnorr_correctness : forall r c,
           accepting_conversation g h (schnorr_protocol x g r c) = true.
        Proof.
          unfold schnorr_protocol, 
          accepting_conversation;
          simpl.
          intros ? ?.
          rewrite key_rel.
          assert (Hg : (g ^ x) ^ c = (g ^ (x * c))).
          rewrite smul_pow_up. 
          reflexivity.
          rewrite Hg; clear Hg.
          assert (Hxc : x * c = c * x).
          rewrite commutative; reflexivity.
          rewrite Hxc; clear Hxc.
          rewrite <- (@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow).
          subst.
          destruct (Gdec (g ^ (r + c * x)) (g ^ (r + c * x))) eqn:Hg.
          + reflexivity.
          + congruence.
          + typeclasses eauto.
        Qed.


        (* it's same as above but more clear. *)
        Lemma schnorr_correctness_berry : forall r c a₁ c₁ r₁, 
           (a₁; c₁; r₁) = (schnorr_protocol x g r c) ->
           accepting_conversation g h (a₁; c₁; r₁) = true.
        Proof.
          intros * Ha.
          rewrite Ha.
          eapply schnorr_correctness.
        Qed.


        (* simulator produces an accepting conversation 
           without using the secret x *)
        Lemma simulator_correctness : 
           ∀ r c, accepting_conversation g h 
            (schnorr_simulator g h r c) = true.
        Proof.
          unfold accepting_conversation, 
            schnorr_simulator; 
          intros ? ?; simpl.
          rewrite gdec_true.
          rewrite <-associative.
          rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow).
          rewrite field_zero_iff_left,
          vector_space_field_zero,
          monoid_is_right_identity.
          reflexivity.
          typeclasses eauto.
         Qed.
        
        
        Lemma simulator_correctness_berry : 
          forall r c a₁ c₁ r₁,
          (a₁; c₁; r₁) = (schnorr_simulator g h r c) ->
          accepting_conversation g h (a₁; c₁; r₁) = true.
        Proof.
          intros * Ha.
          rewrite Ha.
          apply simulator_correctness.
        Qed.


        (* special soundness: if the prover replies two challenge with 
          same randomness, then exatractor can extract a/the? witness *)
        Lemma special_soundness : 
          forall r c c', c <> c' ->  
          accepting_conversation g h (schnorr_protocol x g r c) = true -> 
          accepting_conversation g h (schnorr_protocol x g r c') = true ->
          ∃ y : F, g^y = h.
        Proof.
          unfold accepting_conversation,
          schnorr_protocol; simpl.
          intros * Ha Hb Hc.
          remember (r + c * x) as res₁.
          remember (r + c' * x) as res₂.
          exists ((res₁ + opp res₂) * inv (c + opp c')).
          subst.
          rewrite gdec_true in Hb, Hc.
          assert (Ht : opp (r + c' * x) = 
            opp (c' * x) + opp r).
          rewrite group_inv_flip;
          reflexivity.
          rewrite Ht; clear Ht.
          assert (Ht : (r + c * x + (opp (c' * x) + opp r)) = 
          ((opp (c' * x) + opp r) + r + c * x)).
          rewrite commutative, associative.
          reflexivity.
          rewrite Ht; clear Ht.
          assert (Ht : opp (c' * x) + opp r + r = 
          opp (c' * x)).
          rewrite <-associative.
          rewrite field_zero_iff_left.
          rewrite monoid_is_right_identity.
          reflexivity.
          rewrite Ht.


          
          (* I need to simplify it*)


        Admitted.


        Lemma special_soundness_berry : 
          forall r c c', c <> c' -> 
          forall a₁ c₁ r₁ a₂ c₂ r₂, 
          (a₁; c₁; r₁) = (schnorr_protocol x g r c)  -> (* first conversation *)
          accepting_conversation g h (a₁; c₁; r₁) = true ->  
          (a₂; c₂; r₂) = (schnorr_protocol x g r c') -> (* second conversation *)
          accepting_conversation g h (a₂; c₂; r₂) = true -> 
          ∃ y : F, g^y = h.
        Proof.
          intros * Hdisj * Ha Hb Hc Hd.
          rewrite Ha in Hb.
          rewrite Hc in Hd.
          eapply special_soundness.
          + exact Hdisj.
          + exact Hb.
          + exact Hd.
        Qed.   

      
        


        (* https://www.win.tue.nl/~berry/2WC13/LectureNotes.pdf 
          We fix the challenge and show that both,  protocol 
          using witness x as input and simulated --not using x--, 
          have the same distributions.
        
          To prove the indistinguishability between a real transcript 
          and a simulated transcript, we construct two distributions,
          one using the witness (real transcript) and other without
          using the witness (fake/simulator transcript). 
          We demonstrate that  
          the probability of the real transcript is same as 
          the fake transcript. One thing that is implicit 
          in these two distributions is both, real transcript 
          and fake transcript, pass the verification test, 
          i.e. returns true to a verifier. 
          We use this implicit knowledge and
          construct two distributions as a pair in 
          which the first pair is a sigma triple and second pair
          is the probability of the triple, ((a, c, r), prob), 
          in the given distribution. 
          
          In the proof, we apply (map) 
          accepting_conversation to crunch the first pair, 
          (a, c, r), and produce boolean a value (true), 
          and then we show that these two distribution are 
          identical 
        *)

        (* involves secret x*)    
        Definition schnorr_distribution 
          {lf : list F} {Hlfn : lf <> List.nil} (c : F) := 
          r <- (uniform_with_replacement lf Hlfn) ;;
          Ret (schnorr_protocol x g r c).
        
        
        (* without secret *)
        Definition simulator_distribution 
          {lf : list F} {Hlfn : lf <> List.nil} (c : F) :=
          r <- (uniform_with_replacement lf Hlfn) ;;
          Ret (schnorr_simulator g h r c).


        
        Lemma generic_distribution : 
          forall l c, 
          List.map (λ '(a, p), (accepting_conversation g h a, p))
          (Bind l
             (λ r : F, Ret (schnorr_protocol x g r c))) =
          List.map (λ '(a, p), (accepting_conversation g h a, p))
          (Bind l
             (λ r : F, Ret (schnorr_simulator g h r c))).
        Proof.
          induction l. 
          + simpl; intros ?.
            reflexivity.
          + simpl; intros ?.
            destruct a as (a, b);
            simpl.
            f_equal.
            rewrite key_rel.
            assert (Hg : (g ^ x) ^ c = (g ^ (x * c))).
            rewrite smul_pow_up. 
            reflexivity.
            rewrite Hg; 
            clear Hg.
            assert (Hg : (g ^ x) ^ opp c = (g ^ (x * opp c))).
            rewrite smul_pow_up. 
            reflexivity.
            rewrite Hg; 
            clear Hg.
            assert (Ht : 
              (gop (gop (g ^ a) (g ^ (x * opp c))) (g ^ (x * c)) = 
            (gop (g ^ a) (gop (g ^ (x * opp c)) (g ^ (x * c)))))).
            rewrite <- (@monoid_is_associative G (@eq G) gop gid).
            reflexivity. 
            typeclasses eauto.
            rewrite Ht; clear Ht. 
            assert (Ht : (gop (g ^ a) (g ^ (x * c))) = 
              g^(a + x * c)).
            rewrite (@vector_space_smul_distributive_fadd 
              F (@eq F) zero one add mul sub div 
              opp inv G (@eq G) gid ginv gop gpow).
            reflexivity.
            typeclasses eauto.
            rewrite Ht; 
            clear Ht.
            rewrite <-(@vector_space_smul_distributive_fadd 
              F (@eq F) zero one add mul sub div 
              opp inv G (@eq G) gid ginv gop gpow).
            assert (Ht : (x * opp c + x * c) = 
              x * (opp c + c)).
            (* why rewrite not working? *)
            pose proof ring_is_left_distributive.
            unfold is_left_distributive in H.
            specialize (H x (opp c) c).
            symmetry.
            exact H.
            rewrite Ht; clear Ht.
            assert (Ht : (opp c) + c = c + opp c).
            rewrite (@commutative_group_is_commutative F 
            (@eq F) add zero opp).
            reflexivity.
            typeclasses eauto.
            rewrite Ht; 
            clear Ht.
            assert (Ht : (c + opp c) = zero).
            rewrite field_zero_iff_right.
            reflexivity.
            rewrite Ht; clear Ht.
            assert (Ht : x * zero = zero).
            rewrite ring_mul_0_r;
            reflexivity.
            rewrite Ht; 
            clear Ht.
            assert (Ht : (g ^ zero) = gid).
            rewrite vector_space_field_zero.
            reflexivity.
            rewrite Ht; 
            clear Ht.
            assert (Ht : (gop (g ^ a) gid) = g^a).
            rewrite monoid_is_right_identity.
            reflexivity.
            rewrite Ht;
            clear Ht.
            assert (Ht : c * x = x * c).
            rewrite (@commutative_ring_is_commutative F (@eq F) zero 
              one opp add sub mul).
            reflexivity.
            typeclasses eauto.
            rewrite Ht; 
            clear Ht.
            rewrite (@commutative_group_is_commutative F 
            (@eq F) add zero opp).
            rewrite !gdec_eq_true.
            reflexivity.
            typeclasses eauto.
            typeclasses eauto.
            apply IHl.
        Qed.
           



        (* in fact, it's identical *)
        Lemma special_honest_verifier_zkp : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F), 
            List.map (fun '(a, p) => 
              (accepting_conversation g h a, p))
              (@schnorr_distribution lf Hlfn c) = 
            List.map (fun '(a, p) => 
              (accepting_conversation g h a, p))
              (@simulator_distribution lf Hlfn c).
        Proof.
          intros ? ? ?.
          unfold schnorr_distribution, 
          simulator_distribution.
          cbn.
          apply generic_distribution.
        Qed.
        
        


       

        
        (*
          Now we prove that two distributions, real one --constructed by 
          using the witness x-- and fake one --constructed without x--,
          are similar, modulo prob_equiv. 
          How to bring =r= notation from Prob? 
        *)
          
        

      End Proofs.

    (* call the sha 256 hash function 
      here to turn the interactive version into non-interactive,
      strong Fiat Shamir transformation
      https://eprint.iacr.org/2016/771.pdf.
      Definition nizp_schnorr (r : F) :=
        let c := sha256_string statement-with-other-values in  
        schnorr_protocol r c.
    *)

    End Basic_sigma.

    (* 
    Parallel Composition
    AND composition
    EQ Composition
    OR Composition  
    *)


    Section And_Sigma.
