Require Import Setoid
  Sigma.Algebra.Hierarchy
  Sigma.Algebra.Group Sigma.Algebra.Monoid
  Sigma.Algebra.Field Sigma.Algebra.Integral_domain
  Sigma.Algebra.Ring Sigma.Algebra.Vector_space
  Lia Vector Coq.Unicode.Utf8 Sigma.Prob
  Sigma.Distr Psatz
  ExtLib.Structures.Monad.
      
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

    

    Local Infix "^" := gpow.
    Local Infix "*" := mul.
    Local Infix "/" := div.
    Local Infix "+" := add.
    Local Infix "-" := sub.



    (* sigma protocol for proof of knowledge of discrete logarithm *)
    (* A prover is convincing a verified that she know the discrete log, 
      log_{g} h = x. We will turn this into NIZK by Fiat-Shamir transform 
      (careful )*)
    (* It generic! In case of basic sigma, *)
    Record sigma_proto {n m r : nat}:= 
      mk_sigma 
      {
        commitment : Vector.t G n; 
        challenge : Vector.t F m; 
        response : Vector.t F r
      }.
    (* I am not adding any axioms because it will 
      depend on how we componse the protocols. *)

    
  
    Section Basic_sigma.

      (* 
        x is a secret that a prover tries to convince a verifier, 
        g and h are public value, in a group, and the relation 
        is discrete log ∃ x : F, g ^ x = h. 
      *)
      Section Def.
      
        Context (x : F) (g h : G). 
        (* h = g^x *)


        (* Real transcript, using the witness x *)
        Definition schnorr_protocol (r : F) (c : F) : sigma_proto := 
          mk_sigma _ _ _ [g^r] [c] [r + c * x].

        (* Fake transcript without the witness x, simulator with 
          random z and c *)
        Definition schnorr_simulator (z c : F) : sigma_proto := 
          mk_sigma _ _ _ [gop (g^z) (h^(opp c))] [c] [z].

        (* 
          (com, cha, res)
          g^res = com * h ^ cha
          Turn this into decidable Proposition! 
        *)
        Definition schnorr_protocol_correct (v : @sigma_proto 1 1 1) : bool :=
          match v with
          | mk_sigma _ _ _ com chal res =>  
            match Gdec (g^(hd res)) (gop (hd com) (h^(hd chal))) with 
            | left _ => true
            | right _ => false 
            end
          end.

      End Def.

      Section Proofs.

        Context (x : F) (g h : G) (key_rel : h = g^x).

        (* Sigma protocol is correct *)
        Lemma schnorr_correctness: forall r c, 
          schnorr_protocol_correct g h (schnorr_protocol x g r c) = true.
        Proof.
          unfold schnorr_protocol, 
            schnorr_protocol_correct;
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


        (* special soundness: if the prover replies two challenge with 
          same randomness, then exatractor can extract a witness,
          or the witness? *)
        Lemma special_soundness : 
          forall r c c', c <> c' ->  
          schnorr_protocol_correct g h (schnorr_protocol x g r c) = true -> 
          schnorr_protocol_correct g h (schnorr_protocol x g r c') = true ->
          ∃ y : F, g^y = h.
        Proof.
          unfold schnorr_protocol_correct,
          schnorr_protocol; simpl.
          intros * Ha Hb Hc.
          remember (r + c * x) as res₁.
          remember (r + c' * x) as res₂.
          exists ((res₁ - res₂)/(c - c')).
          subst.
          rewrite gdec_true in Hb, Hc.
          (* I need to simplify it*)


        Admitted.

      
        Lemma simulator_correctness : 
          ∀ z c, schnorr_protocol_correct g h 
            (schnorr_simulator g h z c) = true.
        Proof.
          unfold schnorr_protocol_correct, 
            schnorr_simulator; intros ? ?; simpl.
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


        (* https://www.win.tue.nl/~berry/2WC13/LectureNotes.pdf 
          We fix the challenge and show that both,  protocol 
          using witness x as input and simulated --not using x--, have the same 
          distributions.
        
          To prove the indistinguishability between a real transcript 
          and a simulated transcript, we construct two distributions,
          one using the witness (real transcript) and other without
          using the witness (fake/simulator transcript). 
          We demonstrate that  
          the probability of the real transcript is same as 
          the fake transcript. One thing that is implicit 
          in these two distributions is both, real transcript 
          and fake transcript, pass the verification test, 
          i.e. returns true to a verifier. We use this implicit knowledge and
          construct two distributions as a pair in 
          which the first pair is a sigma triple and second pair
          is the probability of the triple, ((com, chal, res), prob), 
          in the given distribution. Thereafter we apply the 
          sigma_compute to crunch the first pair, 
          (com, chal, res), and produce boolean a value (true), 
          and then we show that these two distribution are similar. 
        *)
        
        
        (* involves secret x*)
        Definition schnorr_protocol_distribution 
          {lf : list F} {Hlfn : lf <> List.nil} (c : F) := 
          r <- (uniform_with_replacement lf Hlfn) ;;
          Ret (schnorr_protocol_correct g h (schnorr_protocol x g r c)).
        

        (* without secret *)
        Definition simulator_distribution 
          {lf : list F} {Hlfn : lf <> List.nil} (c : F) :=
          z <- (uniform_with_replacement lf Hlfn) ;;
          Ret (schnorr_protocol_correct g h (schnorr_simulator g h z c)).
        
        (*
          Now we prove that two distributions, real one --constructed by 
          using the witness x-- and fake one --constructed without x--,
          are similar, modulo prob_equiv. 
          How to bring =r= notation from Prob? Also, 
          the monadic notations?
        *)

        Lemma special_honest_verifier_zkp : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F), 
          Distr.dist_equiv 
            (@schnorr_protocol_distribution lf Hlfn c) 
            (@simulator_distribution lf Hlfn c).
        Proof.
          intros ? ? ?.
          unfold schnorr_protocol_distribution, 
          simulator_distribution.
          setoid_rewrite schnorr_correctness;
          setoid_rewrite simulator_correctness.
          reflexivity.
        Qed.
      
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
