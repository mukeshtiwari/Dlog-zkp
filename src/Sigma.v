Require Import Setoid
  Sigma.Algebra.Hierarchy
  Sigma.Algebra.Group Sigma.Algebra.Monoid
  Sigma.Algebra.Field Sigma.Algebra.Integral_domain
  Sigma.Algebra.Ring Sigma.Algebra.Vector_space
  Lia Vector Coq.Unicode.Utf8 Sigma.Prob
  Sigma.Distr Psatz
  ExtLib.Structures.Monad
  Coq.Bool.Bool
  Coq.PArith.Pnat 
  Coq.NArith.BinNatDef
  Coq.PArith.BinPos
  Sigma.Distr 
  Sigma.Util.

      
Import MonadNotation 
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
     

    Local Infix "^" := gpow.
    Local Infix "*" := mul.
    Local Infix "/" := div.
    Local Infix "+" := add.
    Local Infix "-" := sub.


    Section SigmaDefinition.
      (* sigma protocol for proof of knowledge of discrete logarithm *)
      (* A prover is convincing a verifier that she know the discrete log, 
        log_{g} h = x. We will turn this into NIZK by Fiat-Shamir transform 
        (careful )*)
    
      Record sigma_proto {n m r : nat} := 
        mk_sigma 
        {
          announcement : Vector.t G n; (* prover announcement*)
          challenge : Vector.t F m; (* verifier randomness *)
          response : Vector.t F r (* prover response *)
        }.
    


     

    End SigmaDefinition.

    Local Notation "( a ; c ; r )" := 
      (@mk_sigma _ _ _ a c r).

    
  
    Section Basic_sigma.

      (* 
        x is a secret that a prover tries to convince a verifier, 
        g and h are public value, in a group, and the relation 
        is discrete log ∃ x : F, g ^ x = h. 
      *)
      Section Def.
      
        (* x is a secret *)
        (* g and h are public values *)
        (* Relation: R := h = g^x *)
        (* A prover convinces a verified that they know 
          x such that h := g^x *)
      

        (* Real transcript, using randomness u and (secret) witness x *)
        Definition schnorr_protocol (x : F) (g : G) (u c : F) : @sigma_proto 1 1 1 :=  
          ([g^u]; [c]; [u + c * x]).

        (* Fake transcript (without the witness x) *)
        Definition schnorr_simulator (g h : G) (u c : F) : @sigma_proto 1 1 1 := 
          ([gop (g^u) (h^(opp c))]; [c]; [u]).

        (* 
          This function checks if a conversation (a; c; r) 
          is accepting or not. It checks if g^r = a * h^c
        *)
        Definition accepting_conversation 
          (g h : G)
          (v : @sigma_proto 1 1 1) : bool :=
          match v with
          | (a; c; r) =>  
            match Gdec (g^(hd r)) (gop (hd a) (h^(hd c))) with 
            | left _ => true
            | right _ => false 
            end
          end.


        (* Distribution that involves the secret x *)
        Definition schnorr_distribution  (lf : list F) 
          (Hlfn : lf <> List.nil) (x : F) (g : G) (c : F) : dist sigma_proto :=
          u <- (uniform_with_replacement lf Hlfn) ;;
          Ret (schnorr_protocol x g u c).
        
        
        (* without secret x *)
        Definition simulator_distribution 
          (lf : list F) (Hlfn : lf <> List.nil) (g h : G) (c : F) :=
          u <- (uniform_with_replacement lf Hlfn) ;;
          Ret (schnorr_simulator g h u c).
  
      
      End Def.

      Section Proofs.

        
        (* available in global context *)
        Context 
          (x : F) (* secret witness *) 
          (g h : G) (* public values *)
          (R : h = g^x). (* relation that prover trying to 
            establish, or convince a verifier*)

        (* Sigma protocol is correct.
          For some randomness r (a = g^r) and challenge c, 
          (schnorr_protocol x g r c) returns 
          an accepting conversation.
        *)
        Lemma schnorr_completeness :
          forall r c,
           accepting_conversation g h (schnorr_protocol x g r c) = true.
        Proof.
          unfold schnorr_protocol, 
          accepting_conversation;
          simpl.
          intros ? ?.
          rewrite R.
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


        (* it's same as above but more clear. 
           It explicitly binds the accepting 
           conversation to variables (a₁; c₁; r₁).
        *)
        Lemma schnorr_completeness_berry : forall r c a₁ c₁ r₁, 
           (a₁; c₁; r₁) = (schnorr_protocol x g r c) ->
           accepting_conversation g h (a₁; c₁; r₁) = true.
        Proof.
          intros * Ha.
          rewrite Ha.
          eapply schnorr_completeness.
        Qed.


        (* simulator produces an accepting conversation,
           without using the secret x *)
        Lemma simulator_completeness : forall r c, 
          accepting_conversation g h 
            (schnorr_simulator g h r c) = true.
        Proof using -(x R).
          clear x R. (* Without the secret x *)
          unfold accepting_conversation, 
            schnorr_simulator; 
          intros ? ?; simpl.
          rewrite (@dec_true _ Gdec).
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
        
        (* it's same as above but more clear. 
           It explicitly binds the accepting 
           conversation of simulator 
           to variables (a₁; c₁; r₁).
        *)
        Lemma simulator_completeness_berry : 
          forall r c a₁ c₁ r₁,
          (a₁; c₁; r₁) = (schnorr_simulator g h r c) ->
          accepting_conversation g h (a₁; c₁; r₁) = true.
        Proof using -(x R).
          clear x R.
          intros * Ha.
          rewrite Ha.
          apply simulator_completeness.
        Qed.



        (* special soundness: if the prover replies two challenge with 
          same randomness r, i.e., same announcement, 
          then exatractor can extract a witness 
        *)
      
        Lemma special_soundness_berry : 
          forall a c₁ r₁ c₂ r₂, 
          c₁ <> c₂ -> 
          accepting_conversation g h ([a]; [c₁]; [r₁]) = true -> (* and it's accepting *) 
          accepting_conversation g h ([a]; [c₂]; [r₂]) = true -> (* and it's accepting *)
          ∃ y : F, g^y = h. (* then we can find a witness y such that g^y = h *)
        Proof using -(x R).
          clear x R. (* remove the assumption, otherwise it's trivial :) *)
          intros ? ? ? ? ? Ha Hb Hc.
          apply (@dec_true _ Gdec) in Hb, Hc. 
          simpl in Hb, Hc.
          (* produce a witness *)
          exists ((r₁ - r₂) * inv (c₁ - c₂)).
          eapply f_equal with (f := ginv) in Hc.
          rewrite connection_between_vopp_and_fopp in Hc.
          rewrite group_inv_flip  in Hc.
          rewrite commutative in Hc.
          pose proof (@rewrite_gop G gop _ _ _ _ Hb Hc) as Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd 
            F (@eq F) zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          assert (Hwt : gop a (h ^ c₁) = gop (h ^ c₁) a).
          rewrite commutative; reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
          in Hcom.
          assert (Hwt : (gop a (gop (ginv a) (ginv (h ^ c₂)))) = 
          (ginv (h ^ c₂))).
          rewrite associative.
          rewrite group_is_right_inverse,
          monoid_is_left_idenity;
          reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          rewrite connection_between_vopp_and_fopp in Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd 
            F (@eq F) zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          apply f_equal with (f := fun x => x^(inv (c₁ + opp c₂)))
          in Hcom.
          rewrite !smul_pow_up in Hcom.
          assert (Hw : (c₁ + opp c₂) * inv (c₁ + opp c₂) = 
          (inv (c₁ + opp c₂) * (c₁ + opp c₂))).
          rewrite commutative; reflexivity.
          rewrite Hw in Hcom; clear Hw.
          rewrite field_is_left_multiplicative_inverse in Hcom.
          pose proof vector_space_field_one as Hone.
          unfold is_field_one in Hone.
          specialize (Hone h).
          rewrite Hone in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          exact Hcom.
          intros Hf.
          pose proof ring_neq_sub_neq_zero c₁ c₂ Ha as Hw.
          apply Hw.
          rewrite ring_sub_definition.
          exact Hf.
          all:typeclasses eauto.
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
        
        *)

        (* involves secret x*)    
        (* Under the hood, it is modelled as a list and 
            looks like:
            [((a; c; r), prob); ((a; c; r), prob) ......]
        *)
      
        
        Local Notation "p / q" := (mk_prob p (Pos.of_nat q)).


        Lemma probability_schnorr_distribution_generic_probability : 
          forall l trans prob c n,
          (forall trx prx, List.In (trx, prx) l -> 
            prx = 1 / n) ->  
          List.In (trans, prob)
            (Bind l
              (λ u : F, Ret (schnorr_protocol x g u c))) ->
          prob = 1 / n.
        Proof.
          induction l as [|(a, p) l IHl].
          + intros * Ha Hin.
            simpl in Hin.
            inversion Hin.
          + intros * Ha Hin.
            pose proof (Ha a p (or_introl eq_refl)).
            destruct Hin as [Hwa | Hwb].
            inversion Hwa; subst; 
            clear Hwa.
            unfold mul_prob, 
            Prob.one; simpl.
            f_equal.
            nia.
            simpl in Hwb.
            eapply IHl.
            intros ? ? Hinn.
            exact (Ha trx prx (or_intror Hinn)).
            exact Hwb.
        Qed.



        Lemma probability_schnorr_distribution_generic_transcript : 
          forall l trans prob c,
          List.In (trans, prob)
            (Bind l
              (λ u : F, Ret (schnorr_protocol x g u c))) ->
          accepting_conversation g h trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          + intros * Ha.
            simpl in Ha;
            inversion Ha.
          + intros * Ha.
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              simpl in Ha;
              destruct Ha as [Ha | Ha];
              inversion Ha; subst.
              unfold schnorr_protocol, 
              accepting_conversation;
              cbn.
              (* algebraic manipulation *)
              assert (Hb : (g ^ x) ^ c = (g ^ (x * c))).
              rewrite smul_pow_up. 
              reflexivity.
              rewrite Hb; 
              clear Hb.
              assert (Hb : (gop (g ^ a) (g ^ (x * c))) = 
              g^(a + x * c)).
              rewrite (@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              reflexivity.
              typeclasses eauto.
              rewrite Hb; 
              clear Hb.
              assert (Hg : c * x = x * c).
              rewrite (@commutative_ring_is_commutative F (@eq F) zero 
                one opp add sub mul).
              reflexivity.
              typeclasses eauto.
              rewrite Hg; 
              clear Hg.
              now rewrite !dec_eq_true.
            ++
             
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha; subst;
                unfold accepting_conversation, 
                schnorr_protocol; cbn.
                assert (Hb : (g ^ x) ^ c = (g ^ (x * c))).
                rewrite smul_pow_up. 
                reflexivity.
                rewrite Hb; 
                clear Hb.
                assert (Hb : (gop (g ^ a) (g ^ (x * c))) = 
                g^(a + x * c)).
                rewrite (@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow).
                reflexivity.
                typeclasses eauto.
                rewrite Hb; 
                clear Hb.
                assert (Hg : c * x = x * c).
                rewrite (@commutative_ring_is_commutative F (@eq F) zero 
                  one opp add sub mul).
                reflexivity.
                typeclasses eauto.
                rewrite Hg; 
                clear Hg.
                now rewrite !dec_eq_true.
              +++
                (* inductive case *)
                eapply IHl; exact Ha.
        Qed.
          
          
        


        (* Every elements in @schnorr_distribution 
          has probability 1/ (List.length lf) where 
          lf the list of scalor (Field) elements from which the 
          random r is drawn and every corresponding 
          conversation is accepting
        *)

        Lemma probability_schnorr_distribution : 
          forall (lf : list F) 
          (Hlfn : lf <> List.nil) (c : F) a₁ c₁ r₁ prob n,
          n = List.length lf -> 
          List.In ((a₁; c₁; r₁), prob) 
            (@schnorr_distribution lf Hlfn x g c) ->
          prob = 1 / n ∧
          accepting_conversation g h (a₁; c₁; r₁) = true.
        Proof.
          intros * Hn Hl.
          split.
          +
            assert (Hlt : List.length (uniform_with_replacement lf Hlfn) =
              List.length lf).
            unfold uniform_with_replacement.
            rewrite List.map_length;
            reflexivity.
            pose proof probability_schnorr_distribution_generic_probability
            (uniform_with_replacement lf Hlfn)
            (a₁; c₁; r₁) prob c n as Ht.
            rewrite Hn.
            rewrite Hn in Ht.
            specialize (Ht 
              (uniform_probability lf Hlfn) Hl).
            exact Ht.
          +
            unfold schnorr_distribution in Hl;
            cbn in Hl.
            eapply probability_schnorr_distribution_generic_transcript.
            exact Hl.
        Qed.
            
      

          
        Lemma probability_simulator_distribution_generic_probability : 
          forall l trans prob c n,
          (forall trx prx, List.In (trx, prx) l -> 
            prx = 1 / n) ->  
          List.In (trans, prob)
            (Bind l
              (λ u : F, Ret (schnorr_simulator g h u c))) ->
          prob = 1 / n.
        Proof.
          induction l as [|(a, p) l IHl].
          + intros * Ha Hin.
            simpl in Hin.
            inversion Hin.
          + intros * Ha Hin.
            pose proof (Ha a p (or_introl eq_refl)).
            destruct Hin as [Hwa | Hwb].
            inversion Hwa; subst; 
            clear Hwa.
            unfold mul_prob, 
            Prob.one; simpl.
            f_equal.
            nia.
            simpl in Hwb.
            eapply IHl.
            intros ? ? Hinn.
            exact (Ha trx prx (or_intror Hinn)).
            exact Hwb.
        Qed.

        Lemma probability_simulator_distribution_generic_transcript : 
          forall l trans prob c, 
          List.In (trans, prob)
            (Bind l
              (λ u : F, Ret (schnorr_simulator g h u c))) ->
          accepting_conversation g h trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          + intros * Ha.
            simpl in Ha;
            inversion Ha.
          + intros * Ha.
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              simpl in Ha;
              destruct Ha as [Ha | Ha];
              inversion Ha; subst.
              unfold schnorr_simulator, 
              accepting_conversation;
              cbn.
              (* algebraic manipulation. There should 
              a way to automate these proofs! *)
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
              rewrite <-(@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              assert (Ht : (x * opp c + x * c) = 
                x * (opp c + c)).
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
              now rewrite !dec_eq_true.
              eauto.
            ++
             
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha; subst;
                unfold accepting_conversation, 
                schnorr_simulator; cbn.
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
              rewrite <-(@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              assert (Ht : (x * opp c + x * c) = 
                x * (opp c + c)).
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
                now rewrite !dec_eq_true.
                eauto.
              +++
                (* inductive case *)
                eapply IHl; exact Ha.
        Qed.
        


        (* Every elements in @simulator_distribution 
          has probability 1/ (List.length lf) where 
          lf the list of Field element from which the 
          random r is drawn and it's an accepting 
          conversation *)
        Lemma probability_simulator_distribution : 
          forall (lf : list F) 
          (Hlfn : lf <> List.nil) (c : F) a₁ c₁ r₁ prob n, 
          n = List.length lf -> 
          List.In ((a₁; c₁; r₁), prob) 
            (@simulator_distribution lf Hlfn g h c) ->
          prob = 1 / n ∧  (* probability is 1/n *)
          accepting_conversation g h (a₁; c₁; r₁) = true.
        Proof.
          intros * Hn Hl.
          split.
          +
            assert (Hlt : List.length (uniform_with_replacement lf Hlfn) =
              List.length lf).
            unfold uniform_with_replacement.
            rewrite List.map_length;
            reflexivity.
            pose proof probability_simulator_distribution_generic_probability
            (uniform_with_replacement lf Hlfn)
            (a₁; c₁; r₁) prob c n as Ht.
            rewrite Hn.
            rewrite Hn in Ht.
            specialize (Ht 
              (uniform_probability lf Hlfn) Hl).
            exact Ht.
          +
            unfold simulator_distribution in Hl.
            eapply probability_simulator_distribution_generic_transcript;
            exact Hl.
        Qed.
       
      
        (* Do I still need this? *)
        Lemma generic_distribution : 
          forall l c, 
          List.map (λ '(a, p), (accepting_conversation g h a, p))
            (Bind l (λ u : F, Ret (schnorr_protocol x g u c))) =
          List.map (λ '(a, p), (accepting_conversation g h a, p))
            (Bind l (λ u : F, Ret (schnorr_simulator g h u c))).
        Proof.
          induction l. 
          + simpl; intros ?.
            reflexivity.
          + simpl; intros ?.
            destruct a as (a, b);
            simpl.
            f_equal.
            rewrite R.
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
            rewrite !dec_eq_true.
            reflexivity.
            typeclasses eauto.
            typeclasses eauto.
            apply IHl.
        Qed.
            



        (* it's identical *)
        (* We map 
          accepting_conversation to crunch the first pair, 
          (a, c, r), and produce boolean a value (true), 
          and then we show that these two distribution are 
          identical 
        *)
        Lemma special_honest_verifier_zkp : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F), 
            List.map (fun '(a, p) => 
              (accepting_conversation g h a, p))
              (@schnorr_distribution lf Hlfn x g c) = 
            List.map (fun '(a, p) => 
              (accepting_conversation g h a, p))
              (@simulator_distribution lf Hlfn g h c).
        Proof.
          intros ? ? ?.
          unfold schnorr_distribution, 
          simulator_distribution.
          cbn.
          apply generic_distribution.
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
    Running two instances of a nontrivial Σ-protocol for relation 
    R in parallel results in a Σ-protocol for R with a larger 
    challenge space.

    In this section, we generalise it and compose n nontrivial Σ-protocol
    for a relation R.
    *)

   
    
    Section Parallel.

      Section Def.

        Definition compose_two_parallel_sigma_protocols {n m r u v w : nat} 
          (s₁ : @sigma_proto n m r) (s₂ : @sigma_proto u v w) :
          @sigma_proto (n + u) (m + v) (r + w) :=
        match s₁, s₂ with 
        |(mk_sigma _ _ _ a₁ c₁ r₁), (mk_sigma _ _ _ a₂ c₂ r₂) =>
          mk_sigma _ _ _ (a₁ ++ a₂) (c₁ ++ c₂) (r₁ ++ r₂)
        end.


        (*
          Construct parallel Sigma protocol for a 
          the relation R : h = g^x
        *)
        Definition construct_parallel_conversations_schnorr :
          forall {n : nat}, 
          F -> G ->  Vector.t F n -> Vector.t F n -> @sigma_proto n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun x g us cs => _
          | S n' => fun x g us cs  => _
          end).
          + refine (mk_sigma _ _ _ [] [] []).
          + 
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S cs) as (csh & cstl & _).
            exact (@compose_two_parallel_sigma_protocols _ _ _ _ _ _ 
              (schnorr_protocol x g ush csh)
              (Fn _ x g ustl cstl)).
        Defined.


        (* Does not involve the secret x *)
        Definition construct_parallel_conversations_simulator :
          forall {n : nat}, 
          G ->  G -> Vector.t F n -> Vector.t F n -> @sigma_proto n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun g h us cs => _
          | S n' => fun g h us cs  => _
          end).
          + refine (mk_sigma _ _ _ [] [] []).
          + 
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S cs) as (csh & cstl & _).
            exact (@compose_two_parallel_sigma_protocols _ _ _ _ _ _ 
              (schnorr_simulator g h ush csh)
              (Fn _ g h ustl cstl)).
        Defined.



      
        Definition generalised_parallel_accepting_conversations : 
          forall {n : nat} (g h : G),
          @sigma_proto n n n -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun _ _ p => true
            | S n' => fun g h p => 
              match p with 
              | (a; c ; r) => _ 
              end 
            end).
          destruct (vector_inv_S a) as (ah & atl & _).
          destruct (vector_inv_S c) as (ch & ctl & _).
          destruct (vector_inv_S r) as (rh & rtl & _).
          exact ((@accepting_conversation g h ([ah]; [ch]; [rh])) &&
            (Fn _ g h (atl; ctl; rtl))).
        Defined.


        
        Definition generalised_parallel_schnorr_distribution  
          {n : nat} (lf : list F) 
          (Hlfn : lf <> List.nil) (x : F) (g : G) 
          (cs : Vector.t F n) : dist (@sigma_proto n n n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_parallel_conversations_schnorr x g us cs).
        
        
        
        (* without secret *)
        Definition generalised_parallel_simulator_distribution 
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) (g h : G) 
          (cs : Vector.t F n) : dist (@sigma_proto n n n) := 
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_parallel_conversations_simulator g h us cs).
  

      End Def.


      Section Proofs. 

        Context
          (x : F) (* secret witness *)
          (g h : G) (* public values *) 
          (R : h = g ^ x). (* relation that 
          prover trying to establish, or convince a verifier*)

       
        (* 
          when generalised_accepting_conversations return true 
          then every individual sigma protocol is an 
          accepting conversations.
        *)
        Lemma generalised_parallel_accepting_conversations_correctness_forward : 
          forall (n : nat) (s : @sigma_proto n n n),
          @generalised_parallel_accepting_conversations n g h s = true ->
          ∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation g h 
              (mk_sigma 1 1 1
                [(nth a f)] [(nth c f)] [(nth r f)]) = true
          end.
        Proof using -(x R).
          clear x R. (* This is not needed in this proof 
          and therefore I remove it to make this lemma 
          more generic *)
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +  
            intros ? Ha f.
            refine (match f with end).
          +
            intros ? Ha f.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(a; c; r) => fun Hc => _  
            end eq_refl).
            rewrite Hc in Ha.
            destruct (vector_inv_S a) as (ha & ta & Hd).
            destruct (vector_inv_S c) as (hc & tc & He).
            destruct (vector_inv_S r) as (hr & tr & Hf).
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            subst; simpl.
            eapply andb_true_iff in Ha. 
            destruct Ha as (Ha & _).
            rewrite Ha; reflexivity.
            subst ; simpl.
            eapply andb_true_iff in Ha.
            destruct Ha as (_ & Ha).
            exact (IHn _ Ha hf).
        Qed.
     
          
        (* When we have accepting conversations, then 
        generalised_accepting accepts it.
        *)
        Lemma generalised_parallel_accepting_conversations_correctness_backward : 
          forall (n : nat) (s : @sigma_proto n n n), 
          (forall (f : Fin.t n),
            match s with 
            | (a; c; r) => 
              @accepting_conversation g h 
                (mk_sigma 1 1 1
                  [(nth a f)] [(nth c f)] [(nth r f)]) = true 
            end) -> 
          @generalised_parallel_accepting_conversations n g h s = true.
        Proof using -(x R).
          clear x R.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +
            intros ? Ha.
            reflexivity.
          +
            intros ? Ha.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(a; c; r) => fun Hb => _  
            end eq_refl).
            destruct (vector_inv_S a) as (ha & ta & Hc).
            destruct (vector_inv_S c) as (hc & tc & Hd).
            destruct (vector_inv_S r) as (hr & tr & He);
            subst.
            eapply andb_true_iff; split;
            [exact (Ha Fin.F1) |
            eapply IHn; 
            intros fz;
            exact (Ha (Fin.FS fz))].
        Qed.


        Lemma generalised_parallel_accepting_conversations_correctness : 
          forall (n : nat) (s : @sigma_proto n n n), 
          (forall (f : Fin.t n),
            match s with 
            | (a; c; r) => 
              @accepting_conversation g h 
                (mk_sigma 1 1 1
                  [(nth a f)] [(nth c f)] [(nth r f)]) = true 
            end) <-> 
          @generalised_parallel_accepting_conversations n g h s = true.
        Proof using -(x R).
          clear x R.
          split;
          [apply generalised_parallel_accepting_conversations_correctness_backward |
          apply generalised_parallel_accepting_conversations_correctness_forward].
        Qed.


        (* completeness *)
        Lemma construct_parallel_conversations_schnorr_completeness : 
          forall (n : nat) (us cs : Vector.t F n),
          @generalised_parallel_accepting_conversations n g h
            (@construct_parallel_conversations_schnorr n x g us cs) = true.
        Proof.
          induction n as [|n IHn];
          [intros ? ?;
          reflexivity | intros ? ? ].
          destruct (vector_inv_S us) as (hus & tus & Ha).
          destruct (vector_inv_S cs) as (hcs & tcs & Hb).
          rewrite Ha, Hb.
          specialize (IHn tus tcs).
          pose proof 
          generalised_parallel_accepting_conversations_correctness_forward
          _ _ IHn as Hc.
          eapply 
          generalised_parallel_accepting_conversations_correctness_backward.
          intros ?; cbn.
          remember (construct_parallel_conversations_schnorr x g tus tcs) as s.
          refine
          (match s as s'
          return s = s' -> _ with 
          |(a; c; r) => fun Hb => _  
          end eq_refl).
          destruct (fin_inv_S _ f) as [hd | (hd & Hf)].
          +
            rewrite hd; cbn.
            (* by schnorr completeness *)
            now eapply schnorr_completeness.
          +
            rewrite Hf; cbn.
            specialize (Hc hd);
            rewrite Hb in Hc;
            exact Hc.
        Qed.
        

        Lemma construct_parallel_conversations_simulator_completeness : 
          forall (n : nat) (us cs : Vector.t F n),
          @generalised_parallel_accepting_conversations n g h
            (@construct_parallel_conversations_simulator n g h us cs) = true.
        Proof using -(x R).
          clear x R. (* clear the relation *)
          induction n as [|n IHn];
          [intros ? ?;
          reflexivity | intros ? ? ].
          destruct (vector_inv_S us) as (hus & tus & Ha).
          destruct (vector_inv_S cs) as (hcs & tcs & Hb).
          rewrite Ha, Hb.
          specialize (IHn tus tcs).
          pose proof 
          generalised_parallel_accepting_conversations_correctness_forward
          _ _ IHn as Hc.
          eapply 
          generalised_parallel_accepting_conversations_correctness_backward.
          intros ?; cbn.
          remember (construct_parallel_conversations_simulator g h tus tcs) as s.
          refine
          (match s as s'
          return s = s' -> _ with 
          |(a; c; r) => fun Hb => _  
          end eq_refl).
          destruct (fin_inv_S _ f) as [hd | (hd & Hf)].
          +
            rewrite hd; cbn.
            (* by simulator completeness *)
            now eapply simulator_completeness.
          +
            rewrite Hf; cbn.
            specialize (Hc hd);
            rewrite Hb in Hc;
            exact Hc.
        Qed.


           
        (* soundness *)
        Lemma generalise_parallel_sigma_soundenss : 
          ∀ (n : nat) 
          (s₁ s₂ : @sigma_proto ((S n)) ((S n)) ((S n))),
          (match s₁, s₂ with 
          | (a₁ ; c₁; _), (a₂ ; c₂; _) => 
          two_challenge_vectors_same_everyelem a₁ a₂ ->
          two_challenge_vectors_disjoint_someelem c₁ c₂ ->
          (* accepting conversatation*)
          generalised_parallel_accepting_conversations g h s₁ = true -> 
          (* accepting conversatation*)
          generalised_parallel_accepting_conversations g h s₂ = true ->
          ∃ y : F, g^y = h
          end).
        Proof using -(x R).
          clear x R. (* otherwise, it's trivial :) *)
          induction n as [|n IHn].
          +
            intros ? ?.
            refine 
            (match s₁ as s'
            return s₁ = s' -> _ with 
            |(a₁; c₁; r₁) => fun Ha => _  
            end eq_refl).
            refine 
            (match s₂ as s'
            return s₂ = s' -> _ with 
            |(a₂; c₂; r₂) => fun Hb => _  
            end eq_refl).
            intros Hc Hd He Hf.
            unfold two_challenge_vectors_same_everyelem in Hc.
            destruct Hd as [f Hd].
            destruct (vector_inv_S a₁) as (ha₁ & ta₁ & Hg).
            destruct (vector_inv_S c₁) as (hc₁ & tc₁ & Hh).
            destruct (vector_inv_S r₁) as (hr₁ & tr₁ & Hi).
            rewrite Hg, Hh, Hi in He;
            cbn in He.
            destruct (vector_inv_S a₂) as (ha₂ & ta₂ & Hj).
            destruct (vector_inv_S c₂) as (hc₂ & tc₂ & Hk).
            destruct (vector_inv_S r₂) as (hr₂ & tr₂ & Hl).
            rewrite Hj, Hk, Hl in Hf;
            cbn in Hf.
            (* using the special soundness 
              of Schonorr protocol as 
              base case 
            *)
            apply special_soundness_berry with 
            (a := ha₁) (c₁ := hc₁) (r₁ := hr₁)
            (c₂ := hc₂) (r₂ := hr₂).
            
            rewrite Hh, Hk in Hd.
            destruct (fin_inv_S _ f) as [hf | (hf & Hm)];
            [rewrite hf in Hd;
            cbn in Hd; exact Hd |
            inversion hf].
            apply andb_true_iff in He;
            cbn; exact (proj1 He).
            apply andb_true_iff in Hf;
            cbn.
            rewrite Hg, Hj in Hc.
            specialize (Hc f).
            destruct (fin_inv_S _ f) as [hf | (hf & Hm)].
            rewrite hf in Hc;
            cbn in Hc; rewrite Hc.
            exact (proj1 Hf).
            inversion hf.
          +
            intros ? ?.
            refine 
            (match s₁ as s'
            return s₁ = s' -> _ with 
            |(a₁; c₁; r₁) => fun Ha => _  
            end eq_refl).
            refine 
            (match s₂ as s'
            return s₂ = s' -> _ with 
            |(a₂; c₂; r₂) => fun Hb => _  
            end eq_refl).
            intros Hc Hd He Hf.
            (* interesting way to control the 
            normalisation! *)
            remember (S n) as sn.
            destruct (vector_inv_S a₁) as (ha₁ & ta₁ & Hg).
            destruct (vector_inv_S c₁) as (hc₁ & tc₁ & Hh).
            destruct (vector_inv_S r₁) as (hr₁ & tr₁ & Hi).
            destruct (vector_inv_S a₂) as (ha₂ & ta₂ & Hj).
            destruct (vector_inv_S c₂) as (hc₂ & tc₂ & Hk).
            destruct (vector_inv_S r₂) as (hr₂ & tr₂ & Hl).
            rewrite Hg, Hj in Hc.
            rewrite Hh, Hk in Hd.
            rewrite Hg, Hh, Hi in He.
            rewrite Hj, Hk, Hl in Hf.
            cbn in He, Hf.
            apply andb_true_iff in He, Hf.
            destruct He as [Hel Her].
            destruct Hf as [Hfl Hfr].
            destruct Hd as [f Hm].
            destruct (fin_inv_S _ f) as [hf | (hf & Hn)].
            rewrite hf in Hm;
            cbn in Hm.
            (* 
              using the special soundness 
              of Schonorr protocol as 
              base case 
            *)
            apply special_soundness_berry with 
            (a := ha₁) (c₁ := hc₁) (r₁ := hr₁)
            (c₂ := hc₂) (r₂ := hr₂).
            exact Hm.
            exact Hel.
            cbn.
            pose proof (Hc f) as Hn;
            rewrite hf in Hn;
            cbn in Hn;
            rewrite Hn;
            exact Hfl.
            (* 
              induction case
            *)
            specialize (IHn (ta₁; tc₁; tr₁)
            (ta₂; tc₂; tr₂));
            cbn in IHn.
            assert (Ho : two_challenge_vectors_same_everyelem ta₁ ta₂).
            intro Ho;
            pose proof (Hc (Fin.FS Ho)) as Hp;
            cbn in Hp;
            exact Hp.
            assert (Hp : two_challenge_vectors_disjoint_someelem tc₁ tc₂).
            exists hf;
            rewrite Hn in Hm;
            cbn in Hm; exact Hm.
            eapply IHn; 
            try assumption.
        Qed.
            

        (* zero-knowledge-proof *)
        

        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
        *)
        Lemma special_honest_verifier_schnorr_dist {n : nat}: 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (cs : Vector.t F n) a b, 
          List.In (a, b) 
            (generalised_parallel_schnorr_distribution lf Hlfn x g cs) ->
            (* it's an accepting conversation and probability is *)
          generalised_parallel_accepting_conversations g h a = true ∧ 
          b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
        Proof.
        Admitted.

        Lemma special_honest_verifier_simulator_dist {n : nat}: 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (cs : Vector.t F n) a b, 
          List.In (a, b) 
            (generalised_parallel_simulator_distribution lf Hlfn g h cs) ->
            (* first component is true and probability is *)
          generalised_parallel_accepting_conversations g h a = true ∧ 
          b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
        Proof.
        Admitted.
        

      End Proofs.


    
    End Parallel.

    Section And.

      Section Def.

        Definition compose_two_and_sigma_protocols {n : nat} 
          (s₁ : @sigma_proto 1 1 1) (s₂ : @sigma_proto n 1 n) :
          @sigma_proto (1 + n) 1 (1 + n) :=
        match s₁, s₂ with 
        |(mk_sigma _ _ _ a₁ c₁ r₁), (mk_sigma _ _ _ a₂ _ r₂) =>
          mk_sigma _ _ _ (a₁ ++ a₂) c₁ (r₁ ++ r₂)
        end.
         
       (*
          ∃ x₁ x₂ x₃ : g₁ = h₁^x₁ ∧ g₂ = h₂^x₂ ∧ g₃ = h₃^x₃ ...
          
          xs : List F (* list of secres*)
          gh and hs : List G (* list of public values *)
          c : single challenge 
        *)

       
        Definition construct_and_conversations_schnorr :
          forall {n : nat}, 
          Vector.t F n -> Vector.t G n -> 
          Vector.t F n -> F -> @sigma_proto n 1 n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun xs gs us c => _
          | S n' => fun xs gs us c  => _
          end).
          + 
            (* Base case *)
            refine (mk_sigma _ _ _ [] [c] []).
          +
            destruct (vector_inv_S xs) as (xsh & xstl & _).
            destruct (vector_inv_S gs) as (gsh & gstl & _).
            destruct (vector_inv_S us) as (ush & ustl & _).
            exact (@compose_two_and_sigma_protocols _
              (schnorr_protocol xsh gsh ush c)
              (Fn _ xstl gstl ustl c)).
        Defined.


        (* Does not involve the secret x *)
        Definition construct_and_conversations_simulator :
          forall {n : nat}, 
          Vector.t G n ->  Vector.t G n -> Vector.t F n -> 
          F -> @sigma_proto n 1 n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun gs hs us c => _
          | S n' => fun gs hs us c  => _
          end).
          + 
            refine (mk_sigma _ _ _ [] [c] []).
          + 
            destruct (vector_inv_S gs) as (gsh & gstl & _).
            destruct (vector_inv_S hs) as (hsh & hstl & _).
            destruct (vector_inv_S us) as (ush & ustl & _).
            exact (@compose_two_and_sigma_protocols _ 
              (schnorr_simulator gsh hsh ush c)
              (Fn _ gstl hstl ustl c)).
        Defined.

        
        Definition generalised_and_accepting_conversations : 
          forall {n : nat}
          (g h : Vector.t G n),
          @sigma_proto n 1 n -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun _ _ p => true
            | S n' => fun g h p => 
              match p with 
              | (a; c ; r) => _ 
              end 
            end).
          destruct (vector_inv_S a) as (ah & atl & _).
          destruct (vector_inv_S c) as (ch & ctl & _).
          destruct (vector_inv_S r) as (rh & rtl & _).
          destruct (vector_inv_S g) as (gh & gtl & _).
          destruct (vector_inv_S h) as (hh & htl & _).
          exact ((@accepting_conversation gh hh ([ah]; [ch]; [rh])) &&
            (Fn _ gtl htl (atl; c; rtl))).
        Defined.

         
        (* Check the definition *)
        Definition generalised_and_schnorr_distribution  
          {n : nat} (lf : list F) 
          (Hlfn : lf <> List.nil) (xs : Vector.t F n) 
          (gs : Vector.t G n) 
          (c : F) : dist (@sigma_proto n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_schnorr xs gs us c).
        
        
        
        (* without secret *)
        Definition generalised_and_simulator_distribution 
          {n : nat} (lf : list F) 
          (Hlfn : lf <> List.nil) (gs hs : Vector.t G n) 
          (c : F) : dist (@sigma_proto n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_simulator gs hs us c).


      End Def.

      Section Proofs.

        (*
          ∃ x₁ : g₁ = h₁^x ..... 
        *)
        Context
          {n : nat}
          (xs : Vector.t F n)
          (gs hs : Vector.t G n)
          (H : forall (f : Fin.t n), 
            (Vector.nth gs f)^(Vector.nth xs f) = Vector.nth hs f).

        (* Completeness, Special Soundess (proof of knowledge) and 
          zero-knowledge *)
        

        


      End Proofs.
          

    End And.

    Section EQ.

      (* Common witness w for 2 or more relations 
        ∃ w : F, R₁ x w ∧ R₂ x w 
      *)
      Section Def.

        (* 
          x : common witness for all relations
          gs and hs : public inputs 
          c : single challenge
        *)

        (* we construct n copies of the witness x and 
          call And composition 
        *)
        Definition construct_eq_conversations_schnorr :
          forall {n : nat}, 
          F -> Vector.t G n -> Vector.t F n -> 
          F -> @sigma_proto n 1 n.
        Proof.
          intros ? x gs us c.
          exact (construct_and_conversations_schnorr
            (repeat_ntimes n x) gs us c).
        Defined.
      


        (* Does not involve the secret x *)
        Definition construct_eq_conversations_simulator :
          forall {n : nat}, 
          Vector.t G n ->  Vector.t G n -> Vector.t F n -> 
          F -> @sigma_proto n 1 n.
        Proof.
          intros ? gs hs us c.
          exact (construct_and_conversations_simulator 
            gs hs us c).
        Defined.
       

        
        Definition generalised_eq_accepting_conversations : 
          forall {n : nat}
          (g h : Vector.t G n),
          @sigma_proto n 1 n -> bool.
        Proof.
          intros * g h Ha.
          exact (generalised_and_accepting_conversations g h Ha).
        Defined.
        


         (* Check the definition *)
         Definition generalised_eq_schnorr_distribution  
          {n : nat} (lf : list F) 
          (Hlfn : lf <> List.nil) (x : F) 
          (gs : Vector.t G n) (c : F) : dist (@sigma_proto n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_eq_conversations_schnorr x gs us c).
        
       
       
       (* without secret *)
        Definition generalised_eq_simulator_distribution 
          {n : nat} (lf : list F) 
          (Hlfn : lf <> List.nil) (gs hs : Vector.t G n) 
          (c : F) : dist (@sigma_proto n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_eq_conversations_simulator gs hs us c).



      End Def.


      Section Proofs.

         Context
          {n : nat}
          (x : F)
          (gs hs : Vector.t G n)
          (H : forall (f : Fin.t n), 
            (Vector.nth gs f)^x = Vector.nth hs f).



      End Proofs.

    End EQ.


    Section Or.

      (* 
          What if I want to prove k-out-n Or proof? 
          https://www.win.tue.nl/~berry/papers/crypto94.pdf
      *)
      (* Generalised Or composition? 
      
        ∃ x : g₁^w = h₁ ∨ g₂^w = h₂ ∨ g₃^w = h₃ ... 

        One witness out of n statements
      
      *)
      Section Def.

        Definition compose_two_or_sigma_protocols {n m r u v w : nat} 
          (s₁ : @sigma_proto n m r) (s₂ : @sigma_proto u v w) :
          @sigma_proto (n + u) (m + v) (r + w) :=
        match s₁, s₂ with 
        |(mk_sigma _ _ _ a₁ c₁ r₁), (mk_sigma _ _ _ a₂ c₂ r₂) =>
          mk_sigma _ _ _ (a₁ ++ a₂) (c₁ ++ c₂) (r₁ ++ r₂)
        end.


        (* Prover knows the ith relation *)
        (* The way out is that the verifier may let the prover “cheat” a 
          little bit by allowing the prover to use the simulator of the 
          Σ-protocol for the relation Ri for which the prover does not 
          know witness wi (i = 1 or i = 2). The verifier will do so by 
          providing a single challenge c which the prover is allowed to 
          split into two challenges c1, c2 provided c1, c2 satisfy a 
          linear constraint in terms of c. For example, the constraint 
          may be c = c1 ⊕ c2 if the challenges happen to be bit strings. 
          Essentially, the prover gets one degree of freedom to cheat. 
        *)
        (* 
          prover knowns ith relation 
          x is the secret 
          rs is randomly generated scalors 
          us = usl ++ [u_i] ++ usr
          rs = rsl ++ [_] ++ rsr 
          Prover recomputes: 
          r_i := c - Σ rsl + rsr 

          Uses simulator on (usl ++ usr) (rsl ++ rsr)
          Uses Schnorr protocol u_i r_i 
          Package them together.

          Verifier check the if all the individual 
          sigma protocols are valid and 
          challenges sum up to c.
        *)

        (* Does not involve the secret x *)
        (* gs hs us rs *)
        Definition construct_or_conversations_simulator :
          forall {n : nat}, 
          Vector.t G n ->  Vector.t G n -> Vector.t F n -> 
          Vector.t F n -> @sigma_proto n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun gs hs us rs => _
          | S n' => fun gs hs us rs  => _
          end).
          + refine (mk_sigma _ _ _ [] [] []).
          + 
            destruct (vector_inv_S gs) as (gsh & gstl & _).
            destruct (vector_inv_S hs) as (hsh & hstl & _).
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S rs) as (rsh & rstl & _).
            exact (compose_two_or_sigma_protocols 
              (schnorr_simulator gsh hsh ush rsh)
              (Fn _ gstl hstl ustl rstl)).
        Defined.

        (* 
          intros m n x gs hs us rs c. 
          x is secret  
          gs and hs are public group elements 
          and prover knows the (m + 1)th relation.
          us and cs --verifier let prover cheat -- are randomness 
          c is challenge
        *)  
        Definition construct_or_conversations_schnorr :
          forall {m n : nat}, 
          F -> Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F (m + (1 + n)) -> Vector.t F (m + (1 + n)) -> 
          F -> @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros ? ? x gs hs us cs c.
          destruct (splitat m gs) as (gsl & gsrt).
          destruct (vector_inv_S gsrt) as (g & gsr & _).
          destruct (splitat m hs) as (hsl & hsrt).
          (* discard h because it is not needed in schnorr protocol *)
          destruct (vector_inv_S hsrt) as (_ & hsr & _).
          (* us := usl ++ [r_i] ++ usr *)
          destruct (splitat m us) as (usl & rurt).
          destruct (vector_inv_S rurt) as (u_i & usr & _).
          (* rs := rsl ++ [_] ++ rsr *)
          destruct (splitat m cs) as (csl & csrt).
          (* discard r_i *)
          destruct (vector_inv_S csrt) as (__ & csr & _).
          (* compute r_i  *)
          remember (c - (Vector.fold_right add (csl ++ csr) zero)) 
          as r_i.
          (* we will return rsl ++ [r_i] ++ rsr in c field *)
          (* run simulator on gsl hsl usl rsl *)
          remember (construct_or_conversations_simulator 
            gsl hsl usl csl) as Ha.
          (* run protocol for known relation *)
          remember (schnorr_protocol x g u_i r_i) as Hb.
          (* run simulator on gsr hsr usr rsr *)
          remember (construct_or_conversations_simulator 
            gsr hsr usr csr) as Hc.
          (* now combine all and put the 
            c at front of challenges *)
          refine 
            match Ha, Hb, Hc with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂), (a₃; c₃; r₃) => 
              ((a₁ ++ (a₂ ++ a₃)); c :: c₁ ++ (c₂ ++ c₃); (r₁ ++ (r₂ ++ r₃)))
            end.
        Defined.



        Local Definition generalised_or_accepting_conversations_t : 
          forall {n : nat}, 
          Vector.t G n -> Vector.t G n ->
          @sigma_proto n n n -> bool.
        Proof.
          refine
            (fix Fn n := 
            match n with 
            | 0 => fun gs hs Ha => true
            | S n' => fun gs hs Ha => 
              match Ha with 
              | (a₁; c₁; r₁) => _ 
              end 
            end).
          destruct (vector_inv_S gs) as (g & gsr & _).
          destruct (vector_inv_S hs) as (h & hsr & _).
          destruct (vector_inv_S a₁) as (a & asr & _).
          destruct (vector_inv_S c₁) as (c & csr & _).
          destruct (vector_inv_S r₁) as (r & rsr & _).
          exact ((accepting_conversation g h ([a]; [c]; [r])) &&
            (Fn _ gsr hsr (asr; csr; rsr))).
        Defined.
          
    
        (* verify or sigma protocol *)
        Definition generalised_or_accepting_conversations : 
          forall {m n : nat}, 
          Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)) ->
          bool.
        Proof.
          intros ? ? gs hs Ha.
          (* prover knows for (m+1)th relation *)
          refine 
            match Ha with 
            |(a; ct; r) => _ 
            end.
          (* Verifier first checks if challenge c is equal 
            to the rest of challenges *)
          destruct (vector_inv_S ct) as (c & cs & _).
          refine
            match Fdec c (Vector.fold_right add cs zero) with 
            | left _ => 
                (* now check sigma *)
                generalised_or_accepting_conversations_t gs hs (a; cs; r)
            | right _ => false (* if it's false, there is 
              no point for checking further *)
            end.
        Defined.


        (* distribution *)
         
          
          


        
          




      End Def.


      Section Proofs.


        (* properties about accepting funciton *)
        (* 
          when generalised_or_accepting_conversations return true 
          then every individual sigma protocol is an 
          accepting conversations and 
          hd c = sum of rest of c 
        *)
        Lemma generalised_or_accepting_conversations_correctness_forward : 
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_or_accepting_conversations gs hs s = true ->
          ∀ (f : Fin.t (m + (1 + n))), 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true
          end.
        Proof.
        Admitted.


        Lemma generalised_or_accepting_conversations_correctness_backward : 
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          (∀ (f : Fin.t (m + (1 + n))), 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true
          end) -> 
          generalised_or_accepting_conversations gs hs s = true.
        Proof.
        Admitted.


        Lemma generalised_or_accepting_conversations_correctness: 
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          (∀ (f : Fin.t (m + (1 + n))), 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true
          end) <-> 
          generalised_or_accepting_conversations gs hs s = true.
        Proof.
          intros *; 
          split; intro Ha.
          +
            eapply generalised_or_accepting_conversations_correctness_backward; 
            try assumption.
          +
            eapply generalised_or_accepting_conversations_correctness_forward;
            try assumption.
        Qed.
        (* end of properties *)

        (* Let's prove completeness *)
        (* gs := gsl ++ [g] ++ gsr *)
        (* hs := hsl ++ [h] ++ hsr *)

        
        Context
          {m n : nat}
          (gsl : Vector.t G m) 
          (gsr : Vector.t G n)
          (x : F) (* secret witness *)
          (g h : G) (* public values *)
          (hsl : Vector.t G m) 
          (hsr : Vector.t G n) 
          (R : h = g ^ x).  (* Prover knows (m + 1)th relation *)

        
        (* completeness *)
        Lemma construct_or_conversations_schnorr_completeness : 
          ∀ (us cs : Vector.t F (m + (1 + n))) (c : F),
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
            (construct_or_conversations_schnorr x
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
              us cs c) = true.
        Proof.
          intros *.
          unfold generalised_or_accepting_conversations,
          construct_or_conversations_schnorr.
          repeat rewrite VectorSpec.splitat_append.
          destruct (vector_inv_S ([g] ++ gsr)) as (ga & gt & Ha).
          destruct (vector_inv_S ([h] ++ hsr)) as (ha & ht & Hb).
          destruct (splitat m us) as (usa & usb) eqn:Hc.
          destruct (vector_inv_S usb) as (usba & usbb & Hd).
          destruct (splitat m cs) as (csa & csb) eqn:He.
          destruct (vector_inv_S csb) as (csba & csbb & Hf).
          remember (construct_or_conversations_simulator gsl hsl usa csa)
          as sa.
          refine
          (match sa as s'
          return sa = s' -> _ with 
          |(a₁; c₁; r₁) => fun Hg => _  
          end eq_refl).
          unfold schnorr_protocol.
          remember (construct_or_conversations_simulator gt ht usbb csbb)
          as sb. 
          refine
          (match sb as s'
          return sb = s' -> _ with 
          |(a₂; c₂; r₂) => fun Hi => _  
          end eq_refl); cbn.
          (* 
          fold_right add (csa ++ csbb) zero = c₁ + c₂
          *)
          destruct (Fdec c
          (fold_right add
             (c₁ ++ c - fold_right add (csa ++ csbb) zero :: c₂) zero)) 
          as [Hj | Hj].
          subst.
          cbn in Ha, Hb.
          inversion Ha; subst.
          inversion Hb; subst.
          eapply Eqdep.EqdepTheory.inj_pair2 in H1, H2.
          subst.
        Admitted. 
         
          


          
          







      End Proofs.


    End Or.


    Section NEQ.

      (* generalised NEQ *)
      Section Def.

      End Def.


      Section Proofs.


      End Proofs.

    End NEQ.


    

  End DL.

    (* 
    Parallel Composition
    AND composition
    EQ Composition
    OR Composition  
    Section And_Sigma.
    *)
End Zkp.


  
