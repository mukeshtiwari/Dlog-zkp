Require Import Setoid
  Coq.setoid_ring.Field
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

#[local] Open Scope monad_scope.

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
      {Gdec : forall x y : G, {x = y} + {x <> y}}. 
      (* decidable equality on G *)
     

    #[local] Infix "^" := gpow.
    #[local] Infix "*" := mul.
    #[local] Infix "/" := div.
    #[local] Infix "+" := add.
    #[local] Infix "-" := sub.


    Section SigmaDefinition.
      (* sigma protocol for proof of knowledge of discrete logarithm *)
      (* A prover is convincing a verifier that she know the discrete log, 
        log_{g} h = x. We will turn this into NIZK by Fiat-Shamir transform 
        (careful )*)
    
      Record sigma_proto {n m r : nat} : Type := 
        mk_sigma 
        {
          announcement : Vector.t G n; (* prover announcement*)
          challenge : Vector.t F m; (* verifier randomness *)
          response : Vector.t F r (* prover response *)
        }.

       
    

    End SigmaDefinition.

    #[local] Notation "( a ; c ; r )" := 
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
          (g h : G) (v : @sigma_proto 1 1 1) : bool :=
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
          (* draw u from a random distribution *)
          u <- (uniform_with_replacement lf Hlfn) ;;
          Ret (schnorr_protocol x g u c).
        
        
        (* without secret x *)
        Definition simulator_distribution (lf : list F) 
          (Hlfn : lf <> List.nil) (g h : G) (c : F) : dist sigma_proto :=
          (* draw u from a random distribution *)
          u <- (uniform_with_replacement lf Hlfn) ;;
          Ret (schnorr_simulator g h u c).
  
      End Def.

      Section Proofs.

        (* properties about  accepting_conversation  *)
        Lemma accepting_conversation_correct : 
            forall (g h a : G) (c r : F), 
            accepting_conversation g h ([a]; [c]; [r]) = true <->
            (g^r) = (gop a (h^c)). (* g^r := a ∙ h^c *)
        Proof.
          intros *; 
          split; intros Ha.
          all:
            (apply (@dec_true _ Gdec) in Ha; 
            exact Ha).
        Qed.

        (* end of properties *)

        (* Vector Space *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        
        (* available in global context *)
        Context 
          (x : F) (* secret witness *) 
          (g h : G) (* public values *)
          (R : h = g^x). (* relation that prover trying to 
            establish, or convince a verifier*)

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).
          
        (* Sigma protocol is correct.
          For some randomness r (a = g^r) and challenge c, 
          (schnorr_protocol x g r c) returns 
          an accepting conversation.
        *)
        Lemma schnorr_completeness :
          forall (r c : F),
           accepting_conversation g h 
            (schnorr_protocol x g r c) = true.
        Proof.
          unfold schnorr_protocol, 
          accepting_conversation; cbn.
          intros *; rewrite R.
          assert (Hg : (g ^ x) ^ c = (g ^ (x * c))).
          rewrite smul_pow_up. 
          reflexivity.
          rewrite Hg; clear Hg.
          assert (Hxc : x * c = c * x) by field.
          rewrite Hxc; clear Hxc.
          rewrite <- (@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow);
          subst; [rewrite dec_true; exact eq_refl 
          | assumption].
        Qed.


        (* it's same as above but more clear. 
           It explicitly binds the accepting 
           conversation to variables (a₁; c₁; r₁).
        *)
        Lemma schnorr_completeness_berry : 
          forall (r c : F) (a₁ : t G 1) (c₁ r₁ : t F 1),
          (a₁; c₁; r₁) = (schnorr_protocol x g r c) ->
          accepting_conversation g h (a₁; c₁; r₁) = true.
        Proof.
          intros * Ha; rewrite Ha;
          eapply schnorr_completeness.
        Qed.


        (* simulator produces an accepting conversation,
           without using the secret x *)
        Lemma simulator_completeness : 
          forall (r c : F), 
          accepting_conversation g h (schnorr_simulator g h r c) = true.
        Proof using -(x R).
          clear x R. (* Just for sanity. *)
          unfold accepting_conversation, 
            schnorr_simulator; 
          intros *; simpl.
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
          forall (r c : F) (a₁ : t G 1) (c₁ r₁ : t F 1),
          (a₁; c₁; r₁) = (schnorr_simulator g h r c) ->
          accepting_conversation g h (a₁; c₁; r₁) = true.
        Proof using -(x R).
          clear x R.
          intros * Ha;
          rewrite Ha;
          apply simulator_completeness.
        Qed.



        (* special soundness: if the prover replies two challenge with 
          same randomness r, i.e., same announcement, 
          then exatractor can extract a witness 
        *)
      
        Lemma special_soundness_berry_gen : 
          forall (a : G) (c₁ r₁ c₂ r₂ : F),
          c₁ <> c₂ -> 
          accepting_conversation g h ([a]; [c₁]; [r₁]) = true -> (* and it's accepting *) 
          accepting_conversation g h ([a]; [c₂]; [r₂]) = true -> (* and it's accepting *)
          ∃ y : F, g^y = h ∧ y =  ((r₁ - r₂) * inv (c₁ - c₂)).
          (* The explicit value of y is require in EQ proof *)
          (* then we can find a witness y such that g^y = h *)
        Proof using -(x R).
          clear x R. (* remove the assumption, otherwise it's trivial :) *)
          intros * Ha Hb Hc.
          apply (@dec_true _ Gdec) in Hb, Hc. 
          cbn in Hb, Hc.
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
          exact (conj Hcom eq_refl).
          intros Hf.
          pose proof ring_neq_sub_neq_zero c₁ c₂ Ha as Hw.
          apply Hw.
          rewrite ring_sub_definition.
          exact Hf.
          all:typeclasses eauto.
        Qed.


        Lemma special_soundness_berry: 
          forall (a : G) (c₁ r₁ c₂ r₂ : F),
          c₁ <> c₂ -> 
          accepting_conversation g h ([a]; [c₁]; [r₁]) = true -> (* and it's accepting *) 
          accepting_conversation g h ([a]; [c₂]; [r₂]) = true -> (* and it's accepting *)
          ∃ y : F, g^y = h.
          (* then we can find a witness y such that g^y = h *)
        Proof using -(x R).
          intros * Ha Hb Hc.
          pose proof special_soundness_berry_gen 
          a c₁ r₁ c₂ r₂ Ha Hb Hc as Hd.
          destruct Hd as (y & Hd & He).
          exists y; exact Hd.
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
        (* Under the hood, it is modelled as a list and looks like:
            [((a; c; r), prob); ((a; c; r), prob) ......]
        *)
      
        
        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (* every triple in schnorr distribution has 
          probability 1/n *)
        Lemma schnorr_distribution_probability_generic : 
          forall (l : dist F) (trans : sigma_proto) 
          (prob : Prob.prob) (c : F) (n : nat),
          (forall trx prx, List.In (trx, prx) l -> prx = 1 / n) ->  
          List.In (trans, prob) (Bind l (λ u : F, Ret (schnorr_protocol x g u c))) ->
          prob = 1 / n.
        Proof.
          induction l as [|(a, p) l IHl].
          + intros * Ha Hin.
            cbn in Hin.
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


        (* every triple in schnorr distribution is 
          an accepting conversation *)
        Lemma schnorr_distribution_transcript_generic : 
          forall(l : dist F) (trans : sigma_proto) 
          (prob : Prob.prob) (c : F),
          List.In (trans, prob) (Bind l (λ u : F, Ret (schnorr_protocol x g u c))) ->
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
              inversion Ha.
              eapply schnorr_completeness.
            ++
             
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply  schnorr_completeness.
              +++
                (* inductive case *)
                eapply IHl; exact Ha.
        Qed.
          
          
        

        (* special honest verifier zero-knowledge-proof *)
        (* Every elements in @schnorr_distribution 
          has probability 1/ (List.length lf) where 
          lf the list of scalor (Field) elements from which the 
          random r is drawn and every corresponding 
          conversation is accepting
        *)

        Lemma schnorr_distribution_probability : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) (a₁ : t G 1) (c₁ r₁ : t F 1) 
          (prob : Prob.prob) (n : nat),
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
            pose proof schnorr_distribution_probability_generic
            (uniform_with_replacement lf Hlfn)
            (a₁; c₁; r₁) prob c n as Ht.
            rewrite Hn in Ht |- *.
            exact (Ht (uniform_probability lf Hlfn) Hl).
          +
            unfold schnorr_distribution in Hl;
            cbn in Hl.
            eapply schnorr_distribution_transcript_generic;
            exact Hl.
        Qed.
            
      

          
        Lemma simulator_distribution_probability_generic : 
          forall (l : dist F) (trans : sigma_proto) 
          (prob : Prob.prob) (c : F) (n : nat),
          (forall trx prx, List.In (trx, prx) l -> prx = 1 / n) ->  
          List.In (trans, prob) (Bind l (λ u : F, Ret (schnorr_simulator g h u c))) ->
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


        Lemma simulator_distribution_transcript_generic : 
          forall (l : dist F) (trans : sigma_proto) 
          (prob : Prob.prob) (c : F),
          List.In (trans, prob) (Bind l (λ u : F, Ret (schnorr_simulator g h u c))) ->
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
              inversion Ha.
              eapply simulator_completeness.
            ++
             
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply simulator_completeness.
              +++
                (* inductive case *)
                eapply IHl; exact Ha.
        Qed.
        

        (* special honest verifier zero-knowledge-proof *)
        (* Every elements in @simulator_distribution 
          has probability 1/ (List.length lf) where 
          lf the list of Field element from which the 
          random r is drawn and it's an accepting 
          conversation *)
        Lemma probability_simulator_distribution : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) (a₁ : t G 1) (c₁ r₁ : t F 1) 
          (prob : Prob.prob) (n : nat),
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
            pose proof simulator_distribution_probability_generic
            (uniform_with_replacement lf Hlfn)
            (a₁; c₁; r₁) prob c n as Ht.
            rewrite Hn.
            rewrite Hn in Ht.
            specialize (Ht 
              (uniform_probability lf Hlfn) Hl).
            exact Ht.
          +
            unfold simulator_distribution in Hl.
            eapply simulator_distribution_transcript_generic;
            exact Hl.
        Qed.
          


        (* it's identical (information theoretic zero-knowledge proof) *)
        (* Under the hood, it is modelled as a list and looks like:
            [((a; c; r), prob); ((a; c; r), prob) ......].
          We map accepting_conversation to crunch the first pair, 
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
          eapply map_ext_eq.
          + unfold schnorr_distribution, simulator_distribution;
            cbn. admit. 
          +
            intros (aa, cc, rr) y Ha. 
            eapply and_comm.
            eapply schnorr_distribution_probability.
            auto. exact Ha.
          + 
            intros (aa, cc, rr) y Ha. 
            eapply and_comm.
            eapply probability_simulator_distribution.
            reflexivity. 
            exact Ha. 
        Admitted.
        
      

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
        |(a₁; c₁; r₁), (a₂; c₂; r₂) =>
          (a₁ ++ a₂; c₁ ++ c₂; r₁ ++ r₂)
        end.


        (*
          Construct parallel Sigma protocol for a 
          the relation R : h = g^x
        *)
        (* input: x g us cs *)
        (* secret x, generator g, commitments us, challenges cs *)
        Definition construct_parallel_conversations_schnorr :
          forall {n : nat}, 
          F -> G ->  Vector.t F n -> Vector.t F n ->
          @sigma_proto n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun x g us cs => _
          | S n' => fun x g us cs  => _
          end).
          + 
            (* base case. *)
            refine ([]; []; []).
          + 
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S cs) as (csh & cstl & _).
            exact (@compose_two_parallel_sigma_protocols _ _ _ _ _ _ 
              (schnorr_protocol x g ush csh)
              (Fn _ x g ustl cstl)).
        Defined.


        (* Does not involve the secret x *)
        (* input: g h us cs *)
        (* group generator g and h, commitments us, challenges cs *)
        Definition construct_parallel_conversations_simulator :
          forall {n : nat}, 
          G ->  G -> Vector.t F n -> Vector.t F n -> @sigma_proto n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun g h us cs => _
          | S n' => fun g h us cs  => _
          end).
          + refine ([]; []; []).
          + 
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S cs) as (csh & cstl & _).
            exact (@compose_two_parallel_sigma_protocols _ _ _ _ _ _ 
              (schnorr_simulator g h ush csh)
              (Fn _ g h ustl cstl)).
        Defined.



        (* Function that takes group generators g, h, and 
        sigma protocol and returns a boolean value *)
        Definition generalised_parallel_accepting_conversations : 
          forall {n : nat}, 
          G -> G -> @sigma_proto n n n -> bool.
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


        (* Parallel Schnorr distribution (involves secret x)*)
        Definition generalised_parallel_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (x : F) (g : G) (cs : Vector.t F n) : dist (@sigma_proto n n n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_parallel_conversations_schnorr x g us cs).
        
        
        
        (* Parallel Simulator distribution (without secret x) *)
        Definition generalised_parallel_simulator_distribution 
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (g h : G) (cs : Vector.t F n) : dist (@sigma_proto n n n) := 
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_parallel_conversations_simulator g h us cs).
  

      End Def.


      Section Proofs. 

        
       
        (* 
          when generalised_accepting_conversations return true 
          then every individual sigma protocol is an 
          accepting conversations.
        *)
        Lemma generalised_parallel_accepting_conversations_correctness_forward : 
          forall (n : nat) g h (s : @sigma_proto n n n),
          @generalised_parallel_accepting_conversations n g h s = true ->
          ∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation g h 
              ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true
          end.
        Proof.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +  
            intros * Ha f.
            refine (match f with end).
          +
            intros * Ha f.
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
            exact (IHn _ _ _ Ha hf).
        Qed.
     
          
        (* When we have accepting conversations, then 
        generalised_accepting accepts it.
        *)
        Lemma generalised_parallel_accepting_conversations_correctness_backward : 
          forall (n : nat) g h (s : @sigma_proto n n n), 
          (forall (f : Fin.t n),
            match s with 
            | (a; c; r) => 
              @accepting_conversation g h 
                ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true 
            end) -> 
          @generalised_parallel_accepting_conversations n g h s = true.
        Proof.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +
            intros * Ha.
            reflexivity.
          +
            intros * Ha.
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
          forall (n : nat) g h (s : @sigma_proto n n n), 
          (forall (f : Fin.t n),
            match s with 
            | (a; c; r) => 
              @accepting_conversation g h 
                ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true 
            end) <-> 
          @generalised_parallel_accepting_conversations n g h s = true.
        Proof.
          split;
          [apply generalised_parallel_accepting_conversations_correctness_backward |
          apply generalised_parallel_accepting_conversations_correctness_forward].
        Qed.


        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow} (* vector space *)
          (x : F) (* secret witness *)
          (g h : G) (* public values *) 
          (R : h = g ^ x). (* relation that 
          prover trying to establish, or convince a verifier*)



        (* completeness *)
        Lemma construct_parallel_conversations_schnorr_completeness : 
          forall (n : nat) (us cs : Vector.t F n),
          generalised_parallel_accepting_conversations g h
            (construct_parallel_conversations_schnorr x g us cs) = true.
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
          _ _ _ _ IHn as Hc.
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
        

        (* simulator completeness *)
        Lemma construct_parallel_conversations_simulator_completeness : 
          forall (n : nat) (us cs : Vector.t F n),
          generalised_parallel_accepting_conversations g h
            (construct_parallel_conversations_simulator g h us cs) = true.
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
          _ _ _ _ IHn as Hc.
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

        

        (* special soundness helper *)
        Lemma generalise_parallel_sigma_soundness_supplement : 
          ∀ (n : nat) 
          (s₁ s₂ : @sigma_proto (S n) (S n) (S n)),
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
            eapply special_soundness_berry with
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


        (* special soundness *)
        Lemma generalise_parallel_sigma_soundness : 
          ∀ (n : nat) (a : Vector.t G (1 + n)) 
          (c₁ r₁ c₂ r₂ : Vector.t F (1 + n)),
          c₁ <> c₂ -> 
          (* accepting conversatation*)
          generalised_parallel_accepting_conversations g h (a; c₁; r₁) = true -> 
          (* accepting conversatation*)
          generalised_parallel_accepting_conversations g h (a; c₂; r₂) = true ->
          ∃ y : F, g^y = h.
        Proof using -(x R).
          clear x R.
          intros * Ha Hb Hc.
          exact (generalise_parallel_sigma_soundness_supplement n
            (a; c₁; r₁) (a; c₂; r₂) 
            (vector_same_implies_same_everyelem _ a a eq_refl)
            (@vector_not_equal_implies_disjoint_someelem _ Fdec _ c₁ c₂ Ha) 
            Hb Hc).
        Qed.
        
            
        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (* Honest Verifier zero-knowledge-proof *)
        Lemma generalised_parallel_schnorr_distribution_transcript_generic {n : nat} : 
          forall (l : dist (Vector.t F n)) 
          (trans : sigma_proto) (pr : prob) (cs : Vector.t F n),
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_schnorr x g us cs))) → 
          generalised_parallel_accepting_conversations g h trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_parallel_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_parallel_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.
            


        Lemma generalised_parallel_schnorr_distribution_probability_generic {n : nat} : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) 
          (pr : prob) (cs : Vector.t F n) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_schnorr x g us cs))) → 
          pr = 1 / m.
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

        
        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        Lemma generalised_parallel_special_honest_verifier_schnorr_dist {n : nat}: 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (cs : Vector.t F n) a b, 
          List.In (a, b) 
            (generalised_parallel_schnorr_distribution lf Hlfn x g cs) ->
            (* it's an accepting conversation and probability is *)
          generalised_parallel_accepting_conversations g h a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) n).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_parallel_schnorr_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_parallel_schnorr_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.
        

        (* fact about simultor *)
        Lemma generalised_parallel_simulator_distribution_transcript_generic {n : nat} : 
          forall (l : dist (Vector.t F n)) 
          (trans : sigma_proto) (pr : prob) (cs : Vector.t F n),
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_simulator g h us cs))) → 
          generalised_parallel_accepting_conversations g h trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_parallel_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_parallel_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.
            


        Lemma generalised_parallel_simulator_distribution_probability_generic {n : nat} : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) 
          (pr : prob) (cs : Vector.t F n) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_simulator g h us cs))) → 
          pr = 1 / m.
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



        (* *)
        Lemma generalised_parallel_special_honest_verifier_simulator_dist {n : nat}: 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (cs : Vector.t F n) (a : sigma_proto) (b : prob),
          List.In (a, b) 
            (generalised_parallel_simulator_distribution lf Hlfn g h cs) ->
            (* first component is true and probability is *)
          generalised_parallel_accepting_conversations g h a = true ∧ 
          b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_parallel_simulator_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_parallel_simulator_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.


        (* distributions is identical (information theoretic soundenss because 
        the most powerful computer can't also distinguish between the two) *)
        Lemma generalised_parallel_special_honest_verifier_zkp : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (n : nat) 
          (cs : Vector.t F n),
          List.map (fun '(a, p) => 
            (generalised_parallel_accepting_conversations g h a, p))
            (@generalised_parallel_schnorr_distribution n lf Hlfn x g cs) = 
          List.map (fun '(a, p) => 
            (generalised_parallel_accepting_conversations g h a, p))
            (@generalised_parallel_simulator_distribution n lf Hlfn g h cs).
        Proof.
          intros ? ? ? ?.
          eapply map_ext_eq.
          + unfold generalised_parallel_schnorr_distribution, 
            generalised_parallel_simulator_distribution; cbn. admit.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_parallel_special_honest_verifier_schnorr_dist.
            exact Ha.
          + 
            intros (aa, cc, rr) y Ha. 
            eapply generalised_parallel_special_honest_verifier_simulator_dist.
            exact Ha.
        Admitted.

        
        

      End Proofs.
    
    End Parallel.

    Section And.

      Section Def.

        Definition compose_two_and_sigma_protocols {n : nat} 
          (s₁ : @sigma_proto 1 1 1) (s₂ : @sigma_proto n 1 n) :
          @sigma_proto (1 + n) 1 (1 + n) :=
        match s₁, s₂ with 
        |(a₁; c₁; r₁), (a₂; _; r₂) =>
          (a₁ ++ a₂; c₁; r₁ ++ r₂)
        end.
         
       (*
          ∃ x₁ x₂ x₃ : g₁ = h₁^x₁ ∧ g₂ = h₂^x₂ ∧ g₃ = h₃^x₃ ...
          
          xs : List F (* list of secres*)
          gh and hs : List G (* list of public values *)
          c : single challenge 
        *)

       (* input: xs gs us c *)
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
        (*input: gs hs us c *)
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
          forall {n : nat}, 
          Vector.t G n -> Vector.t G n ->
          @sigma_proto n 1 n -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun _ _ p => true
            | S n' => fun gs hs p => 
              match p with 
              | (a; c ; r) => _ 
              end 
            end).
          destruct (vector_inv_S a) as (ah & atl & _).
          destruct (vector_inv_S c) as (ch & ctl & _).
          destruct (vector_inv_S r) as (rh & rtl & _).
          destruct (vector_inv_S gs) as (g & gtl & _).
          destruct (vector_inv_S hs) as (h & htl & _).
          exact ((@accepting_conversation g h ([ah]; [ch]; [rh])) &&
            (Fn _ gtl htl (atl; c; rtl))).
        Defined.

         
        (* Check the definition *)
        Definition generalised_and_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (xs : Vector.t F n) (gs : Vector.t G n) 
          (c : F) : dist (@sigma_proto n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_schnorr xs gs us c).
        
        
        
        (* without secret *)
        Definition generalised_and_simulator_distribution 
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G n) 
          (c : F) : dist (@sigma_proto n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_simulator gs hs us c).


      End Def.

      Section Proofs.

        (* properties about the generalised_and_accepting_conversations function *)

        Lemma generalised_and_accepting_conversations_correctness_forward : 
          forall (n : nat) (gs hs : Vector.t G n) (s : @sigma_proto n 1 n),
          generalised_and_accepting_conversations gs hs s = true ->
          (∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation (nth gs f) (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = true
          end).
        Proof.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +  
            intros * Ha f.
            refine (match f with end).
          +
            intros * Ha f.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(a; c; r) => fun Hc => _  
            end eq_refl).
            rewrite Hc in Ha.
            destruct (vector_inv_S a) as (ha & ta & Hd).
            destruct (vector_inv_S c) as (hc & tc & He).
            destruct (vector_inv_S r) as (hr & tr & Hf).
            destruct (vector_inv_S gs) as (gsa & gstl & Hi).
            destruct (vector_inv_S hs) as (hsa & hstl & Hj).
            eapply andb_true_iff in Ha.
            destruct Ha as [Hal Har].
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            ++
              subst; cbn;
              exact Hal.
            ++
              rewrite Hi, Hf, Hd, Hj, He, 
              Hg; cbn.
              specialize (IHn _ _ _ Har hf);
              cbn in IHn.
              rewrite He in IHn;
              cbn in IHn; exact IHn.
        Qed.

        

        Lemma generalised_and_accepting_conversations_correctness_backward : 
          forall (n : nat) (gs hs : Vector.t G n) (s : @sigma_proto n 1 n),
          (∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation (nth gs f) (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = true
          end) ->
          generalised_and_accepting_conversations gs hs s = true.         
        Proof.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +
            intros * Ha.
            reflexivity.
          +
            intros * Ha.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(a; c; r) => fun Hb => _  
            end eq_refl).
            destruct (vector_inv_S a) as (ha & ta & Hc).
            destruct (vector_inv_S c) as (hc & tc & Hd).
            destruct (vector_inv_S r) as (hr & tr & He).
            destruct (vector_inv_S gs) as (gsa & gstl & Hi).
            destruct (vector_inv_S hs) as (hsa & hstl & Hj).
            eapply andb_true_iff; split.
            ++
              subst.
              exact (Ha Fin.F1).
            ++
              eapply IHn;
              intro fz.
              pose proof (Ha (Fin.FS fz)) as Hk.
              subst; cbn in Hk |- *.
              exact Hk.
        Qed.

          


        Lemma generalised_and_accepting_conversations_correctness : 
          forall (n : nat) (gs hs : Vector.t G n) (s : @sigma_proto n 1 n),
          (∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation (nth gs f) (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = true
          end) <->
          generalised_and_accepting_conversations gs hs s = true.         
        Proof.
          intros *; 
          split.
          +
            eapply generalised_and_accepting_conversations_correctness_backward;
            try assumption.
          +
            eapply generalised_and_accepting_conversations_correctness_forward;
            try assumption.
        Qed.

        (* end of properites *)

        (* Proof that we are using the same challenge for all 
          relations *)
        Lemma construct_and_conversations_schnorr_challenge : 
          ∀ (n : nat) (xs : t F n) (gs : t G n) (us : t F n) 
          (c : F) (aw : t G n) (cw : t F 1) (rw : t F n),
          (aw; cw; rw) = construct_and_conversations_schnorr xs gs us c ->
          cw = [c].
        Proof.
          destruct n as [|n].
          +
            cbn;
            intros * ? ? ? ? ? ? ? Ha.
            inversion Ha; subst;
            reflexivity.
          +
            cbn;
            intros ? ? ? ? ? ? ? H.
            destruct (vector_inv_S xs) as (xsa & xstl & Ha).
            destruct (vector_inv_S gs) as (gsa & gstl & Hb).
            destruct (vector_inv_S us) as (usa & ustl & Hc).
            remember (construct_and_conversations_schnorr xstl gstl ustl c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            rewrite Hd in H;
            inversion H; 
            reflexivity.
        Qed.

        Lemma construct_and_conversations_simulator_challenge : 
          ∀ (n : nat) (gs hs : t G n) (us : t F n) 
          (c : F) (aw : t G n) (cw : t F 1) (rw : t F n),
          (aw; cw; rw) = construct_and_conversations_simulator gs hs us c ->
          cw = [c].
        Proof.
          destruct n as [|n].
          +
            cbn;
            intros * ? ? ? ? ? ? ? Ha.
            inversion Ha; subst;
            reflexivity.
          +
            cbn;
            intros ? ? ? ? ? ? ? H.
            destruct (vector_inv_S gs) as (gsa & gstl & Hb).
            destruct (vector_inv_S hs) as (hsa & hstl & Hc).
            destruct (vector_inv_S us) as (usa & ustl & Hd).
            remember (construct_and_conversations_simulator gstl hstl ustl c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            rewrite Hd in H;
            inversion H; 
            reflexivity.
        Qed.
        (* end of same challenge *)

        (*
          ∃ x₁ x₂ x₃ : F : h₁ = g₁^x₁ ∧ h₂ = g₂^x₂ ∧ h₃ = g₃^x₃ ..... 
        *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}
          {n : nat}
          (xs : Vector.t F n)
          (gs hs : Vector.t G n)
          (R : forall (f : Fin.t n), 
            (Vector.nth gs f)^(Vector.nth xs f) = Vector.nth hs f).

        
        (* completeness *)
        Lemma construct_and_conversations_schnorr_completeness : 
          forall (us : Vector.t F n) (c : F),
          generalised_and_accepting_conversations gs hs
            (construct_and_conversations_schnorr xs gs us c) = true.
        Proof.
          induction n as [|n' IHn].
          +
            intros *.
            cbn; reflexivity.
          +
            intros *.
            cbn.
            destruct (vector_inv_S xs) as (xsa & xstl & Ha).
            destruct (vector_inv_S gs) as (gsa & gstl & Hb).
            destruct (vector_inv_S us) as (usa & ustl & Hc).
            remember (construct_and_conversations_schnorr xstl gstl ustl c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            destruct (vector_inv_S hs) as (hsa & hstl & He).
            eapply andb_true_iff.
            split.
            ++
              eapply schnorr_completeness.
              (* I need hsa = gsa^x *)
              subst.
              specialize (R Fin.F1); 
              cbn in R; subst; reflexivity.
            ++
              specialize (IHn xstl gstl hstl).
              assert (Hg : (∀ f : Fin.t n', gstl[@f] ^ xstl[@f] = hstl[@f])).
              intros f; subst.
              exact (R (Fin.FS f)).
              specialize (IHn Hg ustl c).
              rewrite <-Heqs, Hd in IHn.
              rewrite Hd in Heqs.
              eapply construct_and_conversations_schnorr_challenge in Heqs.
              rewrite <-Heqs.
              exact IHn. 
        Qed.


        
        Lemma construct_and_conversations_simulator_completeness : 
          forall (us : Vector.t F n) (c : F),
          generalised_and_accepting_conversations gs hs
            (construct_and_conversations_simulator gs hs us c) = true.
        Proof using -(xs R).
          clear xs R. 
          induction n as [|n' IHn].
          +
            intros *;
            cbn; reflexivity.
          +
            intros *;
            cbn.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            destruct (vector_inv_S us) as (usa & ustl & Hc).
            remember (construct_and_conversations_simulator gstl hstl ustl c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            eapply andb_true_iff.
            split.
            ++
              subst.
              now eapply simulator_completeness.
            ++
              specialize (IHn gstl hstl ustl c).
              rewrite <-Heqs, Hd in IHn.
              rewrite Hd in Heqs.
              eapply construct_and_conversations_simulator_challenge in Heqs.
              rewrite <-Heqs.
              exact IHn.
        Qed. 


        (* special soundeness (proof of knowledge) *)
        Lemma generalise_and_sigma_soundness :
          forall (a : Vector.t G n) (c₁ : Vector.t F 1) 
          (r₁ : Vector.t F n) (c₂ : Vector.t F 1) (r₂ : Vector.t F n),
          generalised_and_accepting_conversations gs hs (a; c₁; r₁) = true ->
          generalised_and_accepting_conversations gs hs (a; c₂; r₂) = true ->
          c₁ <> c₂ ->
          (* we can extract a vector of witnesses such that 
            all the individual relations hold gi^xi = hi *)
          (∃ ys : Vector.t F n, ∀ (f : Fin.t n), 
            (nth gs f)^(nth ys f) = (nth hs f)).
        Proof using -(xs R).
          clear xs R. (* otherwise trival *)
          induction n as [|n' IHn].
          +
            intros * Ha Hb Hc.
            exists [];
            intros f; inversion f.
          +
            intros * Ha Hb Hc.
            destruct (vector_inv_S a) as (ah & atl & Hd).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & He).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hf).
            destruct (vector_inv_S c₂) as (ch₂ & ctl₂ & Hg).
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hi).
            destruct (vector_inv_S gs) as (gsh & gstl & Hj).
            destruct (vector_inv_S hs) as (hsh & hstl & Hk).
            specialize (IHn gstl hstl atl c₁ rtl₁ c₂ rtl₂).
            rewrite Hd, Hf, He, Hj, Hk in Ha; 
            cbn in Ha.
            rewrite Hd, Hg, Hi, Hj, Hk in Hb; 
            cbn in Hb.
            eapply andb_true_iff in Ha, Hb.
            destruct Ha as [Hal Har];
            destruct Hb as [Hbl Hbr].
            rewrite <-He in Har;
            rewrite <-Hg in Hbr.
            specialize (IHn Har Hbr Hc).
            destruct IHn as (ys & IHn).
            exists (((rh₁ - rh₂) * inv (ch₁ - ch₂)) :: ys).
            intro f.
            destruct (fin_inv_S _ f) as [hf | (hf & Hl)].
            ++
              subst; cbn.
              rewrite dec_true in Hal, Hbl.
              eapply f_equal with (f := ginv) in Hbl.
              rewrite connection_between_vopp_and_fopp in Hbl.
              rewrite group_inv_flip in Hbl.
              rewrite commutative in Hbl.
              pose proof (@rewrite_gop G gop _ _ _ _ Hal Hbl) as Hcom.
              rewrite <-(@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow) in Hcom.
              rewrite <-ring_sub_definition in Hcom.
              assert (Hwt : gop ah (hsh ^ ch₁) = gop (hsh ^ ch₁) ah).
              rewrite commutative; reflexivity.
              rewrite Hwt in Hcom; clear Hwt.
              setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
              in Hcom.
              assert (Hwt : (gop ah (gop (ginv ah) (ginv (hsh ^ ch₂)))) = 
              (ginv (hsh ^ ch₂))).
              rewrite associative.
              rewrite group_is_right_inverse,
              monoid_is_left_idenity;
              reflexivity.
              rewrite Hwt in Hcom; clear Hwt.
              rewrite connection_between_vopp_and_fopp in Hcom.
              rewrite <-(@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow) in Hcom.
              apply f_equal with (f := fun x => x^(inv (ch₁ + opp ch₂)))
              in Hcom.
              rewrite !smul_pow_up in Hcom.
              assert (Hw : (ch₁ + opp ch₂) * inv (ch₁ + opp ch₂) = 
              (inv (ch₁ + opp ch₂) * (ch₁ + opp ch₂))).
              rewrite commutative; reflexivity.
              rewrite Hw in Hcom; clear Hw.
              rewrite field_is_left_multiplicative_inverse in Hcom.
              pose proof vector_space_field_one as Hone.
              unfold is_field_one in Hone.
              specialize (Hone hsh).
              rewrite Hone in Hcom.
              rewrite <-ring_sub_definition in Hcom.
              exact Hcom.
              intros Hf.
              assert (Ht : ch₁ <> ch₂).
              intro Hg; eapply Hc;
              subst. f_equal.
              rewrite (vector_inv_0 ctl₁);
              rewrite (vector_inv_0 ctl₂);
              reflexivity.
              pose proof ring_neq_sub_neq_zero ch₁ ch₂ Ht as Hw.
              apply Hw.
              rewrite ring_sub_definition.
              exact Hf.
              all:typeclasses eauto.
            ++
              specialize (IHn hf).
              rewrite Hj, Hk, Hl; cbn.
              exact IHn.
        Qed.
        (* what an awesome proof *)




        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).
        (* zero-knowledge-proof *)
        
        
        Lemma generalised_and_schnorr_distribution_transcript_generic : 
          forall (l : dist (Vector.t F n)) 
          (trans : sigma_proto) (pr : prob) (c : F ),
          List.In (trans, pr) (Bind l (λ us : t F n, 
            Ret (construct_and_conversations_schnorr xs gs us c))) → 
          generalised_and_accepting_conversations gs hs trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_and_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_and_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.
            


        Lemma generalised_and_schnorr_distribution_probability_generic : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) 
          (pr : prob) (c : F) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr) (Bind l (λ us : t F n, 
            Ret (construct_and_conversations_schnorr xs gs us c))) → 
          pr = 1 / m.
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

        
        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        Lemma generalised_and_special_honest_verifier_schnorr_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F) (a : sigma_proto) (b : prob), 
          List.In (a, b)  (generalised_and_schnorr_distribution lf Hlfn xs gs c) ->
          (* it's an accepting conversation and probability is *)
          generalised_and_accepting_conversations gs hs a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) n).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_and_schnorr_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_and_schnorr_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.
        

        (* fact about simultor *)
        Lemma generalised_and_simulator_distribution_transcript_generic : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr) (Bind l (λ us : t F n, 
            Ret (construct_and_conversations_simulator gs hs us c))) → 
          generalised_and_accepting_conversations gs hs trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_and_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_and_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.
            


        Lemma generalised_and_simulator_distribution_probability_generic : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) 
          (pr : prob) (c : F) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_and_conversations_simulator gs hs us c))) → 
          pr = 1 / m.
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



        (* special honest verifier zero-knowledge *)
        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
        *)
        Lemma generalised_and_special_honest_verifier_simulator_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F)  (a : sigma_proto) (b : prob),
          List.In (a, b) (generalised_and_simulator_distribution lf Hlfn gs hs c) ->
          (* first component is true and probability is 1 / |lf|^n *)
          generalised_and_accepting_conversations gs hs a = true ∧ 
          b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_and_simulator_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_and_simulator_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.
        
        

      End Proofs.
          

    End And.

    Section EQ.

      (* Common witness w for 2 or more relations 
        ∃ w : F, R₁ x w ∧ R₂ x w 
      *)
      Section Def.

        Definition compose_two_eq_sigma_protocols {n : nat} 
          (s₁ : @sigma_proto 1 1 1) (s₂ : @sigma_proto n 1 1) :
          @sigma_proto (1 + n) 1 1 :=
        match s₁, s₂ with 
        |(a₁; c₁; r₁), (a₂; _; _) =>
          (a₁ ++ a₂; c₁; r₁)
        end.



        (* 
          x : common witness for all relations
          gs and hs : public inputs 
          c : single challenge
        *)
        Definition construct_eq_conversations_schnorr :
          forall {n : nat}, 
          F -> Vector.t G (1 + n) -> F  -> 
          F -> @sigma_proto (1 + n) 1 1. (* @sigma_proto n 1 1 *)
        Proof.
          refine(
            fix Fn n :=
            match n with 
            | 0 => fun x gs u c => _ 
            | S n' => fun x gs u c => _
            end).
          +
            (* base case *)
            destruct (vector_inv_S gs) as (g & _ & _).
            exact (schnorr_protocol x g u c).
          +
            (* inductive case *)
            destruct (vector_inv_S gs) as (g & gtl & _).
            exact (compose_two_eq_sigma_protocols 
            (schnorr_protocol x g u c)
            (Fn _ x gtl u c)).
        Defined.
            
       


        (* Does not involve the secret x *)
        (* input gs hs u c *)
        Definition construct_eq_conversations_simulator :
          forall {n : nat}, 
          Vector.t G (1 + n) ->  Vector.t G (1 + n) -> 
          F -> F -> @sigma_proto (1 + n) 1 1.
        Proof.
          refine(
            fix Fn n :=
            match n with 
            | 0 => fun gs hs u c => _ 
            | S n' => fun gs hs u c => _
            end).
          +
            (* base case *)
            destruct (vector_inv_S gs) as (g & _ & _).
            destruct (vector_inv_S hs) as (h & _ & _).
            exact (schnorr_simulator g h u c).
          +
            (* inductive case *)
            destruct (vector_inv_S gs) as (g & gtl & _).
            destruct (vector_inv_S hs) as (h & htl & _).
            exact (compose_two_eq_sigma_protocols 
            (schnorr_simulator g h u c)
            (Fn _ gtl htl u c)).
          Defined.



          Definition generalised_eq_accepting_conversations : 
            forall {n : nat},
            Vector.t G (1 + n) -> Vector.t G (1 + n) ->
            @sigma_proto (1 + n) 1 1 -> bool.
          Proof.
            refine(
              fix Fn n :=
              match n with 
              | 0 => fun gs hs Ha => _ 
              | S n' => fun gs hs Ha => _
              end).
            +
              (* base case *)
              destruct (vector_inv_S gs) as (g & _ & _).
              destruct (vector_inv_S hs) as (h & _ & _).
              exact (accepting_conversation g h Ha).
            +
              destruct (vector_inv_S gs) as (g & gtl & _).
              destruct (vector_inv_S hs) as (h & htl & _).
              refine 
                match Ha with 
                |(a; c; r) => _ 
                end.
              destruct (vector_inv_S a) as (ah & atl & _).
              exact ((accepting_conversation g h ([ah]; c; r)) && 
                (Fn _ gtl htl (atl; c; r))).
          Defined.
              
         


          (* Check the definition *)
          Definition generalised_eq_schnorr_distribution  
            {n : nat} (lf : list F)  (Hlfn : lf <> List.nil) (x : F) 
            (gs : Vector.t G (1 + n)) (c : F) : dist (@sigma_proto (1 + n) 1 1) :=
            (* draw u randomly *)
            u <- (uniform_with_replacement lf Hlfn) ;;
            Ret (construct_eq_conversations_schnorr x gs u c).
          
        
        
          (* without secret *)
          Definition generalised_eq_simulator_distribution 
            {n : nat} (lf : list F) 
            (Hlfn : lf <> List.nil) (gs hs : Vector.t G (1 + n)) 
            (c : F) : dist (@sigma_proto (1 + n) 1 1) :=
            (* draw u random  *)
            u <- uniform_with_replacement lf Hlfn ;;
            Ret (construct_eq_conversations_simulator gs hs u c).

        

      End Def.


      Section Proofs.

        (* properties about generalised_eq_accepting_conversations *)

        Lemma generalised_eq_accepting_conversations_correctness_forward : 
          forall (n : nat) (gs hs : Vector.t G (1 + n)) 
          (s : @sigma_proto (1 + n) 1 1),
          generalised_eq_accepting_conversations gs hs s = true ->
          (∀ f : Fin.t (1 + n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation (nth gs f) (nth hs f)
              ([(nth a f)]; c; r) = true
          end).
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha ?.
            cbn in f.
            refine
              (match s as s' return s = s' -> _ 
              with 
              |(a; c; r) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & Hc).
            destruct (vector_inv_S hs) as (hh & hstl & Hd).
            destruct (vector_inv_S a) as (ah & atl & He).
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)];
            [|inversion hf].
            subst; cbn.
            cbn in Ha |- *.
            rewrite dec_true in Ha |- *.
            exact Ha.
          +
            intros * Ha ?.
            refine
              (match s as s' return s = s' -> _ 
              with 
              |(a; c; r) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & Hc).
            destruct (vector_inv_S hs) as (hh & hstl & Hd).
            destruct (vector_inv_S a) as (ah & atl & He).
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            subst; cbn in Ha |- *.
            eapply andb_true_iff in Ha.
            destruct Ha as [Hal Har].
            exact Hal.
            subst. cbn in Ha |- *.
            eapply andb_true_iff in Ha;
            destruct Ha as [Hal Har].
            specialize (IHn gstl hstl _ Har hf); 
            cbn in IHn.
            exact IHn.
        Qed.

        Lemma generalised_eq_accepting_conversations_correctness_backward : 
          forall (n : nat) (gs hs : Vector.t G (1 + n)) 
          (s : @sigma_proto (1 + n) 1 1),
          (∀ f : Fin.t (1 + n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation (nth gs f) (nth hs f)
              ([(nth a f)]; c; r) = true
          end) -> generalised_eq_accepting_conversations gs hs s = true.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            refine
              (match s as s' return s = s' -> _ 
              with 
              |(a; c; r) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & Hc).
            destruct (vector_inv_S hs) as (hh & hstl & Hd).
            destruct (vector_inv_S a) as (ah & atl & He).
            specialize (Ha Fin.F1).
            rewrite Hb in Ha.
            subst; cbn in Ha |- *;
            exact Ha.
          +

            intros * Ha.
            refine
              (match s as s' return s = s' -> _ 
              with 
              |(a; c; r) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & Hc).
            destruct (vector_inv_S hs) as (hh & hstl & Hd).
            destruct (vector_inv_S a) as (ah & atl & He).
            rewrite Hc, Hd, He; cbn.
            eapply andb_true_iff.
            split.
            specialize (Ha Fin.F1);
            rewrite Hb, Hc, Hd, He in Ha; 
            cbn in Ha; exact Ha.
            eapply IHn;
            intros f.
            pose proof (Ha (Fin.FS f)) as Hf.
            rewrite Hb, Hc, Hd, He in Hf; 
            cbn in Hf.
            exact Hf.
        Qed.
            


        Lemma generalised_eq_accepting_conversations_correctness : 
          forall (n : nat) (gs hs : Vector.t G (1 + n)) 
          (s : @sigma_proto (1 + n) 1 1),
          (∀ f : Fin.t (1 + n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation (nth gs f) (nth hs f)
              ([(nth a f)]; c; r) = true
          end) <-> generalised_eq_accepting_conversations gs hs s = true.
        Proof.
          intros *; 
          split.
          +
            eapply generalised_eq_accepting_conversations_correctness_backward;
            try assumption.
          +
            eapply generalised_eq_accepting_conversations_correctness_forward;
            try assumption.
        Qed.
      

        Lemma construct_eq_conversations_schnorr_challenge_and_response :
          forall (n : nat) (aw gs : Vector.t G (1 + n)) 
          (cw rw : Vector.t F 1) (c x u : F), 
          (aw; cw; rw) = construct_eq_conversations_schnorr x gs u c ->
          cw = [c] ∧ rw = [u + c * x].
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            destruct (vector_inv_S gs) as (gsh & gstl & Hb).
            subst; cbn in Ha.
            unfold schnorr_protocol in Ha; 
            inversion Ha; subst. 
            refine (conj _ _); reflexivity.
          +
            intros * Ha.
            destruct (vector_inv_S aw) as (awh & awtl & Hb).
            destruct (vector_inv_S gs) as (gsh & gstl & Hc).
            specialize (IHn awtl gstl cw rw c x u).
            rewrite Hc in Ha; cbn in Ha.
            remember (construct_eq_conversations_schnorr x gstl u c) 
            as s.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            rewrite Hd, Hb in Ha.
            inversion Ha; subst.
            refine(conj _ _);
            reflexivity.
        Qed.

        Lemma construct_eq_conversations_simulator_challenge_and_response :
          forall (n : nat) (aw gs hs : Vector.t G (1 + n)) 
          (cw rw : Vector.t F 1) (u c : F), 
          (aw; cw; rw) = construct_eq_conversations_simulator gs hs u c ->
          cw = [c] ∧ rw = [u].
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            destruct (vector_inv_S gs) as (gsh & gstl & Hb).
            destruct (vector_inv_S hs) as (hsh & hstl & Hc).
            subst; cbn in Ha.
            unfold schnorr_protocol in Ha; 
            inversion Ha; subst. 
            refine (conj _ _); reflexivity.
          +
            intros * Ha.
            destruct (vector_inv_S aw) as (awh & awtl & Hb).
            destruct (vector_inv_S gs) as (gsh & gstl & Hc).
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            specialize (IHn awtl gstl hstl cw rw u c).
            rewrite Hc in Ha; cbn in Ha.
            rewrite Hd in Ha; cbn in Ha.
            remember (construct_eq_conversations_simulator gstl hstl u c) 
            as s.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            rewrite Hd, Hb in Ha.
            inversion Ha; subst.
            refine(conj _ _);
            reflexivity.
        Qed.


        (* end of properties *)

        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}
          {n : nat}
          (x : F) (* common witness for all relations *)
          (gs hs : Vector.t G (1 + n))
          (R : forall (f : Fin.t (1 + n)), 
            (Vector.nth gs f)^x = Vector.nth hs f).

        
        (* completeness *)
        Lemma construct_eq_conversations_schnorr_completeness : 
          forall (u c : F),
          generalised_eq_accepting_conversations gs hs
            (construct_eq_conversations_schnorr x gs u c) = true.
        Proof.
          induction n as [|n' IHn].
          +
            intros *.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            specialize (R Fin.F1); subst; cbn in R |- *.
            eapply schnorr_completeness.
            rewrite <-R; reflexivity.
          +
            intros *; cbn.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            remember (construct_eq_conversations_schnorr x gstl u c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            eapply andb_true_iff.
            split.
            ++
              eapply schnorr_completeness.
              (* I need hsa = gsa^x *)
              subst.
              specialize (R Fin.F1); 
              cbn in R; subst; reflexivity.
            ++
              specialize (IHn gstl hstl).
              assert (Hg : (∀ f : Fin.t (1 + n'), gstl[@f] ^ x = hstl[@f])).
              intros f; subst.
              exact (R (Fin.FS f)).
              specialize (IHn Hg u c).
              rewrite <-Heqs, Hd in IHn.
              rewrite Hd in Heqs.
              eapply construct_eq_conversations_schnorr_challenge_and_response 
              in Heqs.
              destruct Heqs as [Heqsl Heqsr].
              subst; exact IHn.
        Qed.


        Lemma construct_eq_conversations_simulator_completeness : 
          forall (u c : F),
          generalised_eq_accepting_conversations gs hs
            (construct_eq_conversations_simulator gs hs u c) = true.
        Proof using -(x R).
          clear x R.
          induction n as [|n' IHn].
          +
            intros *.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            subst.
            eapply simulator_completeness.
          +
            intros *; cbn.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            remember (construct_eq_conversations_simulator gstl hstl u c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            eapply andb_true_iff.
            split.
            ++
              eapply simulator_completeness.
            ++
              specialize (IHn gstl hstl u c).
              rewrite <-Heqs, Hd in IHn.
              rewrite Hd in Heqs.
              eapply construct_eq_conversations_simulator_challenge_and_response
              in Heqs.
              destruct Heqs; subst.
              exact IHn.
        Qed.
              

        (* special soundness (proof of knowledge) *)
        (* This is bit challenging *)
        Lemma generalise_eq_sigma_soundness :
         forall (a : Vector.t G (1 + n)) 
         (c₁ c₂ : F) (r₁ r₂ : F),
         generalised_eq_accepting_conversations gs hs (a; [c₁]; [r₁]) = true ->
         generalised_eq_accepting_conversations gs hs (a; [c₂]; [r₂]) = true ->
         c₁ <> c₂ ->
         ∃ y : F, (forall (f : Fin.t (1 + n)),
          (nth gs f)^y = (nth hs f)).
        Proof using -(x R).
          clear x R. (* otherwise trival *)
          intros * Ha Hb Hc.
          pose proof 
            (generalised_eq_accepting_conversations_correctness_forward _ 
            gs hs _ Ha) as Hd.
          pose proof 
            (generalised_eq_accepting_conversations_correctness_forward _ 
            gs hs _ Hb) as He.
          clear Ha; clear Hb.
          rename Hd into Ha.
          rename He into Hb.
          induction n as [|n' IHn].
          +
            specialize (Ha Fin.F1). 
            specialize (Hb Fin.F1).
            cbn in Ha, Hb.
            destruct (vector_inv_S a) as (ah & atl & Hd).
            destruct (vector_inv_S gs) as (gsh & gstl & He).
            destruct (vector_inv_S hs) as (hsh & hstl & Hf).
            subst; cbn in Ha, Hb.
            rewrite dec_true in Ha, Hb.
            exists ((r₁ - r₂) * inv (c₁ - c₂));
            intros f.
            destruct (fin_inv_S _ f) as [hf | (hf & Hl)];
            [|inversion hf].
            subst; cbn.
            eapply f_equal with (f := ginv) in Hb.
            rewrite connection_between_vopp_and_fopp in Hb.
            rewrite group_inv_flip in Hb.
            rewrite commutative in Hb.
            pose proof (@rewrite_gop G gop _ _ _ _ Ha Hb) as Hcom.
            rewrite <-(@vector_space_smul_distributive_fadd 
              F (@eq F) zero one add mul sub div 
              opp inv G (@eq G) gid ginv gop gpow) in Hcom.
            rewrite <-ring_sub_definition in Hcom.
            assert (Hwt : gop ah (hsh ^ c₁) = gop (hsh ^ c₁) ah).
            rewrite commutative; reflexivity.
            rewrite Hwt in Hcom; clear Hwt.
            setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
            in Hcom.
            assert (Hwt : (gop ah (gop (ginv ah) (ginv (hsh ^ c₂)))) = 
            (ginv (hsh ^ c₂))).
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
            specialize (Hone hsh).
            rewrite Hone in Hcom.
            rewrite <-ring_sub_definition in Hcom.
            exact Hcom.
            intros Hf.
            pose proof ring_neq_sub_neq_zero c₁ c₂ Hc as Hw.
            apply Hw.
            rewrite ring_sub_definition.
            exact Hf.
            all:typeclasses eauto. 
          +
            destruct (vector_inv_S a) as (ah & atl & Hd).
            destruct (vector_inv_S gs) as (gsh & gstl & He).
            destruct (vector_inv_S hs) as (hsh & hstl & Hf).
            exists ((r₁ - r₂) * inv (c₁ - c₂)).
            intros f.
            destruct (fin_inv_S _ f) as [hf | (hf & Hl)].
            ++
              specialize (Ha f).
              specialize (Hb f).
              rewrite He, Hf, hf.
              cbn.
              subst. cbn in Ha, Hb.
              rewrite dec_true in Ha, Hb.
              eapply f_equal with (f := ginv) in Hb.
              rewrite connection_between_vopp_and_fopp in Hb.
              rewrite group_inv_flip in Hb.
              rewrite commutative in Hb.
              pose proof (@rewrite_gop G gop _ _ _ _ Ha Hb) as Hcom.
              rewrite <-(@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow) in Hcom.
              rewrite <-ring_sub_definition in Hcom.
              assert (Hwt : gop ah (hsh ^ c₁) = gop (hsh ^ c₁) ah).
              rewrite commutative; reflexivity.
              rewrite Hwt in Hcom; clear Hwt.
              setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
              in Hcom.
              assert (Hwt : (gop ah (gop (ginv ah) (ginv (hsh ^ c₂)))) = 
              (ginv (hsh ^ c₂))).
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
              specialize (Hone hsh).
              rewrite Hone in Hcom.
              rewrite <-ring_sub_definition in Hcom.
              exact Hcom.
              intros Hf.
              pose proof ring_neq_sub_neq_zero c₁ c₂ Hc as Hw.
              apply Hw.
              rewrite ring_sub_definition.
              exact Hf.
              all:typeclasses eauto.
            ++
              specialize (Ha f).
              specialize (Hb f).
              rewrite He, Hf, Hl in Ha, Hb |- *.
              cbn in Ha, Hb |- *.
              rewrite Hd in Ha, Hb.
              cbn in Ha, Hb.
              pose proof special_soundness_berry_gen 
              _ _ _ _ _ _ _ Hc Ha Hb as Hi.
              destruct Hi as (y & Hi & Hj).
              rewrite <-Hj.
              exact Hi.
        Qed.


        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (* zero-knowledge *)
        Lemma generalised_eq_schnorr_distribution_transcript_generic : 
          forall (l : dist F) (trans : sigma_proto) (pr : prob) (c : F ),
          List.In (trans, pr)
            (Bind l (λ u,
              Ret (construct_eq_conversations_schnorr x gs u c))) → 
          generalised_eq_accepting_conversations gs hs trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_eq_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_eq_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.
            


        Lemma generalised_eq_schnorr_distribution_probability_generic : 
          forall (l :  dist F) (trans : sigma_proto) 
          (pr : prob) (c : F) (m : nat),
          (∀ (trx : F) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr)
            (Bind l (λ u : F,
              Ret (construct_eq_conversations_schnorr x gs u c))) → 
          pr = 1 / m.
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

        
        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf| 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        Lemma generalised_eq_special_honest_verifier_schnorr_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_eq_schnorr_distribution lf Hlfn x gs c) ->
            (* it's an accepting conversation and probability is *)
          generalised_eq_accepting_conversations gs hs a = true ∧ 
          b = 1 / (List.length lf).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_eq_schnorr_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_eq_schnorr_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability; exact Hc|
            exact Ha].
        Qed.
        

        (* fact about simultor *)
        Lemma generalised_eq_simulator_distribution_transcript_generic : 
          forall (l :  dist F) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ u : F,
              Ret (construct_eq_conversations_simulator gs hs u c))) → 
          generalised_eq_accepting_conversations gs hs trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_eq_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_eq_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.
            


        Lemma generalised_eq_simulator_distribution_probability_generic : 
          forall (l :  dist F) (trans : sigma_proto) 
          (pr : prob) (c : F) (m : nat),
          (∀ (trx : F) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr)
            (Bind l (λ u : F,
              Ret (construct_eq_conversations_simulator gs hs u c))) → 
          pr = 1 / m.
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



         (* special honest verifier zero-knowledge *)
        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|
        *)
        Lemma generalised_eq_special_honest_verifier_simulator_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_eq_simulator_distribution lf Hlfn gs hs c) ->
            (* first component is true and probability is *)
          generalised_eq_accepting_conversations gs hs a = true ∧ 
          b = 1 / (List.length lf).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_eq_simulator_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_eq_simulator_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability; exact Hc|
            exact Ha].
        Qed.
        

      End Proofs.

    End EQ.


    Section Or.

      (* 
          What if I want to prove k-out-n Or proof? 
          https://www.win.tue.nl/~berry/papers/crypto94.pdf
      *)
      (* Generalised Or composition? 
      
        ∃ x : g₁^x = h₁ ∨ g₂^x = h₂ ∨ g₃^x= h₃ ... 

        One witness out of n statements
      
      *)
      Section Def.

        Definition compose_two_or_sigma_protocols {n m r u v w : nat} 
          (s₁ : @sigma_proto n m r) (s₂ : @sigma_proto u v w) :
          @sigma_proto (n + u) (m + v) (r + w) :=
        match s₁, s₂ with 
        |(a₁; c₁; r₁), (a₂; c₂; r₂) =>
          (a₁ ++ a₂; c₁ ++ c₂; r₁ ++ r₂)
        end.

        (* Does not involve the secret x *)
        (* gs hs us rs *)
        #[local]
        Definition construct_or_conversations_simulator_supplement :
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


        (* 
          x gs hs us rs c. 
          x is secret  
          gs and hs are public group elements 
          and prover knows the (m + 1)th relation.
          us and cs --verifier let prover cheat -- are randomness 
          c is challenge

          One way to simplify this API is 
          to combine us and cs into a single Vector. 
          In that case, in our DSL we don't need to 
          think about OR as an special case because 
          all our API will be uniform. 
          Important:Discuss this with Berry. 
        *)

        Definition construct_or_conversations_schnorr {m n : nat} :
          F -> Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F ((m + (1 + n)) + (m + n)) -> 
          F -> @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros x gs hs usrs c.
          destruct (splitat (m + (1 + n)) usrs) as (us & rs).
          destruct (splitat m gs) as (gsl & gsrt).
          destruct (vector_inv_S gsrt) as (g & gsr & _).
          destruct (splitat m hs) as (hsl & hsrt).
          (* discard h because it is not needed in schnorr protocol *)
          destruct (vector_inv_S hsrt) as (_ & hsr & _).
          (* us := usl ++ [r_i] ++ usr *)
          destruct (splitat m us) as (usl & rurt).
          destruct (vector_inv_S rurt) as (u_i & usr & _).
          (* rs := rsl ++ [_] ++ rsr *)
          destruct (splitat m rs) as (rsl & rsr).
          (* compute r_i  *)
          remember (c - (Vector.fold_right add (rsl ++ rsr) zero)) 
          as r_i.
          (* we will return rsl ++ [r_i] ++ rsr in c field *)
          (* run simulator on gsl hsl usl rsl *)
          remember (construct_or_conversations_simulator_supplement 
            gsl hsl usl rsl) as Ha.
          (* run protocol for known relation *)
          remember (schnorr_protocol x g u_i r_i) as Hb.
          (* run simulator on gsr hsr usr rsr *)
          remember (construct_or_conversations_simulator_supplement 
            gsr hsr usr rsr) as Hc.
          (* now combine all and put the 
            c at front of challenges *)
          refine 
            match Ha, Hb, Hc with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂), (a₃; c₃; r₃) => 
              ((a₁ ++ (a₂ ++ a₃)); c :: c₁ ++ (c₂ ++ c₃); (r₁ ++ (r₂ ++ r₃)))
            end.
        Defined.

        

        (* simulator *)
        (* does not involve secret x *)
        Definition construct_or_conversations_simulator {m n : nat} :
          Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F ((m + (1 + n)) + (m + n)) -> 
          F -> @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros gs hs usrs c.
          destruct (splitat (m + (1 + n)) usrs) as (us & rs).
          destruct (splitat m gs) as (gsl & gsrt).
          destruct (vector_inv_S gsrt) as (g & gsr & _).
          destruct (splitat m hs) as (hsl & hsrt).
          destruct (vector_inv_S hsrt) as (h & hsr & _).
          (* us := usl ++ [r_i] ++ usr *)
          destruct (splitat m us) as (usl & rurt).
          destruct (vector_inv_S rurt) as (u_i & usr & _).
          (* rs := rsl ++ [_] ++ rsr *)
          destruct (splitat m rs) as (rsl & rsr).
          (* compute r_i  *)
          remember (c - (Vector.fold_right add (rsl ++ rsr) zero)) 
          as r_i.
          (* we will return rsl ++ [r_i] ++ rsr in c field *)
          (* run simulator on gsl hsl usl rsl *)
          remember (construct_or_conversations_simulator_supplement 
            gsl hsl usl rsl) as Ha.
          (* run protocol for known relation *)
          remember (schnorr_simulator g h u_i r_i) as Hb.
          (* run simulator on gsr hsr usr rsr *)
          remember (construct_or_conversations_simulator_supplement 
            gsr hsr usr rsr) as Hc.
          (* now combine all and put the 
            c at front of challenges *)
          refine 
            match Ha, Hb, Hc with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂), (a₃; c₃; r₃) => 
              ((a₁ ++ (a₂ ++ a₃)); c :: c₁ ++ (c₂ ++ c₃); (r₁ ++ (r₂ ++ r₃)))
            end.
        Defined.
        



        #[local]
        Definition generalised_or_accepting_conversations_supplement : 
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
                generalised_or_accepting_conversations_supplement gs hs (a; cs; r)
            | right _ => false (* if it's false, there is 
              no point for checking further *)
            end.
        Defined.


        (* schnorr distribution *)
        Definition generalised_or_schnorr_distribution  
          {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (x : F) (gs hs : Vector.t G (m + (1 + n))) (c : F) : 
          dist (@sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
          (* draw ((m + (1 + n)) + (m + n)) random elements *)
          usrs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
          Ret (construct_or_conversations_schnorr x gs hs usrs c).

        (* simulator distribution *)
        Definition generalised_or_simulator_distribution  
          {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G (m + (1 + n))) (c : F) : 
          dist (@sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
          (* draw ((m + (1 + n)) + (m + n)) random elements *)
          usrs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
          Ret (construct_or_conversations_simulator gs hs usrs c).

         
          
          

      End Def.

      Section Proofs.


        (* properties about accepting funciton *)
        (* 
          when generalised_or_accepting_conversations return true 
          then every individual sigma protocol is an 
          accepting conversations and 
          hd c = sum of rest of c 
        *)
        Lemma generalised_or_accepting_conversations_correctness_supplement_forward : 
          forall {n : nat} (gs hs : Vector.t G n)
          (s :  @sigma_proto n n n),
          generalised_or_accepting_conversations_supplement gs hs s = true ->
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n, 
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end).
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            refine 
              (match s as s' return s = s' -> _ 
              with 
              | (a₁; c₁; r₁) => fun Hb => _ 
              end eq_refl).
            intros f;
            inversion f.
          +
            intros * Ha.
            refine 
              (match s as s' return s = s' -> _ 
              with 
              | (a₁; c₁; r₁) => fun Hb => _ 
              end eq_refl); intro f. 
            destruct (vector_inv_S gs) as (gsh & gstl & Hc).
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            destruct (vector_inv_S a₁) as (ah₁ & atl₁ & He).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            destruct (fin_inv_S _ f) as [Hi | (fs & Hi)];
            subst; simpl. 
            ++
              cbn in Ha.
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              exact Hal.
            ++
              simpl in Ha;
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              exact (IHn _ _ _ Har fs).
        Qed.
        

            
        Lemma generalised_or_accepting_conversations_correctness_supplement_backward : 
          forall {n : nat} (gs hs : Vector.t G n)
          (s :  @sigma_proto n n n),
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n,
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end) -> generalised_or_accepting_conversations_supplement gs hs s = true.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            rewrite (vector_inv_0 gs);
            rewrite (vector_inv_0 hs);
            cbn; reflexivity.
          + 
            intros * Ha.
            refine 
              (match s as s' return s = s' -> _ 
              with 
              | (a₁; c₁; r₁) => fun Hb => _ 
              end eq_refl).
            destruct (vector_inv_S gs) as (gsh & gstl & Hc).
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            destruct (vector_inv_S a₁) as (ah₁ & atl₁ & He).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            subst; cbn. 
            eapply andb_true_iff.
            split.
            ++ 
              pose proof (Ha Fin.F1) as Hi.
              cbn in Hi.
              exact Hi.
            ++
              specialize (IHn gstl hstl (atl₁; ctl₁; rtl₁)).
              assert (Hb : (∀ f : Fin.t n,
              match (atl₁; ctl₁; rtl₁) with
              | (a; c; r) =>
                  accepting_conversation gstl[@f] hstl[@f]
                    ([a[@f]]; [c[@f]]; [r[@f]]) = true
              end)).
              intros *; exact (Ha (Fin.FS f)).
              exact (IHn Hb).
        Qed.

      

        Lemma generalised_or_accepting_conversations_correctness_supplement : 
          forall {n : nat} (gs hs : Vector.t G n)
          (s :  @sigma_proto n n n),
          generalised_or_accepting_conversations_supplement gs hs s = true <-> 
          match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n,
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end.
        Proof.
          intros *.
          split; intros Ha.
          +
            eapply generalised_or_accepting_conversations_correctness_supplement_forward;
            exact Ha.
          +
            eapply generalised_or_accepting_conversations_correctness_supplement_backward;
            exact Ha.
        Qed.
        

        
        Lemma generalised_or_accepting_conversations_supplement_app :
          forall (n m : nat) 
          (gsl hsl al : Vector.t G n) (gsr hsr ar : Vector.t G m)
          (cl rl : Vector.t F n) (cr rr : Vector.t F m),
          generalised_or_accepting_conversations_supplement
            (gsl ++ gsr) (hsl ++ hsr) 
            ((al ++ ar); (cl ++ cr); (rl ++ rr)) = 
          generalised_or_accepting_conversations_supplement gsl hsl (al; cl; rl)  && 
          generalised_or_accepting_conversations_supplement gsr hsr (ar; cr; rr).
        Proof.
          induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 gsl).
            rewrite (vector_inv_0 hsl).
            rewrite (vector_inv_0 al).
            rewrite (vector_inv_0 cl).
            rewrite (vector_inv_0 rl).
            cbn; reflexivity.
          +
            intros *.
            destruct (vector_inv_S gsl) as (gslh & gsltl & Ha).
            destruct (vector_inv_S hsl) as (hslh & hsltl & Hb).
            destruct (vector_inv_S al) as (alh & altl & Hc).
            destruct (vector_inv_S cl) as (clh & cltl & Hd).
            destruct (vector_inv_S rl) as (rlh & rltl & He).
            subst; cbn.
            destruct (Gdec (gslh ^ rlh) (gop alh (hslh ^ clh))).
            ++
              cbn; eapply IHn.
            ++
              cbn; reflexivity.
        Qed.



        Lemma generalised_or_accepting_conversations_correctness_forward : 
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_or_accepting_conversations gs hs s = true -> 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end.
        Proof.
          intros * Ha. 
          unfold generalised_or_accepting_conversations in Ha.
          refine 
            (match s as s' return s = s' -> _ 
            with 
            | (a₁; c₁; r₁) => fun Hb => _ 
            end eq_refl).
          rewrite Hb in Ha.
          destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
          destruct (Fdec ch₁ (fold_right add ctl₁ zero)) eqn:Hd;
          [|inversion Ha].
          split.
          +
            rewrite Hc; cbn;
            exact e.
          +
            rewrite Hc; cbn.
            eapply generalised_or_accepting_conversations_correctness_supplement_forward in
            Ha; exact Ha.
        Qed.

        
    

        Lemma generalised_or_accepting_conversations_correctness_backward : 
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))), 
          (match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end) -> 
          generalised_or_accepting_conversations gs hs s = true.
        Proof.
          intros * Ha.
          unfold generalised_or_accepting_conversations.
          refine 
            (match s as s' return s = s' -> _ 
            with 
            | (a₁; c₁; r₁) => fun Hb => _ 
            end eq_refl).
          destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
          assert (Hd : ch₁ = (fold_right add ctl₁ zero)).
          rewrite Hb in Ha.
          destruct m as [|m].
          +
            destruct Ha as [Hal Har].
            specialize (Har Fin.F1).
            rewrite Hc in Hal; cbn 
            in Hal; exact Hal.
          +
            destruct Ha as [Hal Har].
            specialize (Har Fin.F1).
            rewrite Hc in Hal; cbn 
            in Hal; exact Hal.
          +
            rewrite <-Hd.
            destruct (Fdec ch₁ ch₁) eqn:He.
            eapply generalised_or_accepting_conversations_correctness_supplement;
            intros f.
            rewrite Hb in Ha.
            destruct Ha as [Hal Har].
            rewrite Hc in Har.
            specialize (Har f).
            cbn in Har; cbn.
            exact Har.
            congruence.
        Qed.


        Lemma generalised_or_accepting_conversations_correctness: 
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          (match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            @accepting_conversation (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
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

        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
            eq zero one opp add mul sub inv div vector_space_field).
          

      
        Lemma construct_or_conversations_simulator_challenge : 
          forall (n : nat) (gs hs : Vector.t G n)(us cs : Vector.t F n) 
          (a : Vector.t G n) (c r : Vector.t F n),
          (a; c; r) = construct_or_conversations_simulator_supplement gs hs us cs ->
          cs = c.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            rewrite (vector_inv_0 gs), 
            (vector_inv_0 hs),
            (vector_inv_0 us),
            (vector_inv_0 cs) in Ha.
            cbn in Ha; inversion Ha; subst.
            rewrite ((vector_inv_0 cs)); 
            reflexivity.
          +
            intros * Ha.
            destruct (vector_inv_S gs) as (gsh & gstl & Hb).
            destruct (vector_inv_S hs) as (hsh & hstl & Hc).
            destruct (vector_inv_S a) as (ah & atl & Hd).
            destruct (vector_inv_S c) as (ch & ctl & He).
            destruct (vector_inv_S r) as (rh & rtl & Hf).
            destruct (vector_inv_S us) as (ush & ustl & Hg).
            destruct (vector_inv_S cs) as (csh & cstl & Hi).
            subst; cbn in Ha.
            remember (construct_or_conversations_simulator_supplement gstl hstl ustl cstl)
            as s.
            refine 
            (match s as s' return s = s' -> _ 
            with 
            | (a₁; c₁; r₁) => fun Hb => _ 
            end eq_refl).
            rewrite Hb in Ha;
            inversion Ha; subst.
            f_equal.
            eapply Eqdep.EqdepTheory.inj_pair2 in H1, H3, H5.
            eapply IHn.
            apply eq_sym. 
            rewrite <-H3 in Hb.
            exact Hb.
        Qed.





        (* so in OR composition, we need simulator correctness first *)
        #[local]
        Lemma construct_or_conversations_simulator_completeness_supplement :
          forall (m : nat) (gsl hsl : Vector.t G m) (usa csa : Vector.t F m),
          generalised_or_accepting_conversations_supplement gsl hsl
            (construct_or_conversations_simulator_supplement gsl hsl usa csa) = true.
        Proof.
          induction m as [|m' IHm].
          +
            intros *.
            rewrite (vector_inv_0 gsl).
            rewrite (vector_inv_0 hsl).
            rewrite (vector_inv_0 usa).
            rewrite (vector_inv_0 csa).
            reflexivity.
          +
            intros *.
            destruct (vector_inv_S gsl) as (gslh & gsltl & Ha).
            destruct (vector_inv_S hsl) as (hslh & hsltl & Hb).
            destruct (vector_inv_S usa) as (usah & usatl & Hc).
            destruct (vector_inv_S csa) as (csah & csatl & Hd).
            subst; cbn.
            remember (construct_or_conversations_simulator_supplement gsltl hsltl usatl csatl)
            as s.
            refine 
            (match s as s' return s = s' -> _ 
            with 
            | (a₁; c₁; r₁) => fun Hb => _ 
            end eq_refl); cbn.
            eapply andb_true_iff; split.
            ++
              eapply simulator_completeness.
            ++
              rewrite <-Hb, Heqs.
              eapply IHm.
        Qed.


        Lemma fold_right_app :
          forall (n m : nat) (ul : Vector.t F n)
          (ur : Vector.t F m),
          fold_right add (ul ++ ur) zero = 
          (fold_right add ul zero) + (fold_right add ur zero).
        Proof.
          induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 ul);
            cbn. field.
          +
            intros *.
            destruct (vector_inv_S ul) as (ulh & ultl & Ha).
            subst; cbn. 
            rewrite IHn; cbn.
            field.
        Qed.


        Lemma generalise_or_sigma_soundness_base_case :
          forall (n : nat) gs hs 
          (a : Vector.t G (1 + n)) (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (1 + n))
          (r₁ r₂ : Vector.t F (1 + n)),
          @generalised_or_accepting_conversations 0 n 
            gs hs (a; c₁ :: cs₁; r₁) = true ->
          @generalised_or_accepting_conversations _ _
            gs hs (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ -> 
          (* I know an index where relation R is true and I can 
            extract a witness out of it *)
          ∃ (f : Fin.t (1 + n)) (y : F),
          (nth gs f)^y = (nth hs f).
        Proof.
          intros * Ha Hb.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            gs hs (a; c₁ :: cs₁; r₁) Ha as Hd.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            gs hs (a; c₂ :: cs₂; r₂) Hb as He.
          clear Ha; clear Hb.
          generalize dependent n.
          intros n gs hs a. revert c₂; revert c₁.
          generalize dependent n.          
          induction n as [|n IHn].
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            exists Fin.F1.
            destruct (vector_inv_S gs) as (gsh & gstl & Hf).
            rewrite (vector_inv_0 gstl) in Hf. 
            destruct (vector_inv_S hs) as (hsh & hstl & Hg).
            rewrite (vector_inv_0 hstl) in Hg.
            rewrite Hf, Hg; cbn.
            specialize (Har Fin.F1).
            specialize (Hbr Fin.F1).
            cbn in * |- *.
            rewrite dec_true, Hf, Hg in Har, Hbr.
            destruct (vector_inv_S a) as (ah & atl & Hh).
            rewrite (vector_inv_0 atl) in Hh.
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hi).
            rewrite (vector_inv_0 rtl₁) in Hi.
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hj).
            rewrite (vector_inv_0 cstl₁) in Hj.
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hk).
            rewrite (vector_inv_0 rtl₂) in Hk.
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hl).
            rewrite (vector_inv_0 cstl₂) in Hl.
            subst.
            assert (Hm : csh₁ <> csh₂).
            intros Hm; eapply Hc; 
            rewrite Hm; reflexivity.
            eapply special_soundness_berry; cbn;
            try (rewrite dec_true);
            [exact Hm | exact Har | exact Hbr].
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            cbn in Hal, Har, Hbl, Hbr.
            destruct (vector_inv_S gs) as (gsh & gstl & Hd).
            destruct (vector_inv_S hs) as (hsh & hstl & He).
            destruct (vector_inv_S a) as (ah & atl & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hh).
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hi).
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hj).
            subst; cbn in Hc.
            remember (fold_right add cstl₁ zero) as hcl.
            remember (fold_right add cstl₂ zero) as hcr.
            (* case analysis on challenges *)
            assert (Hd : csh₁ <> csh₂ ∨ 
              (csh₁ = csh₂ ∧ (hcl <> hcr))).
            case_eq (Fdec csh₁ csh₂);
            intros Hd He.
            right.
            refine (conj Hd _).
            intros Hf; eapply Hc;
            rewrite Hd, Hf;
            exact eq_refl. 
            left; exact Hd.
            (* I know that 
            Hd: csh₁ ≠ csh₂ ∨ csh₁ = csh₂ ∧ hcl ≠ hcr*)
            destruct Hd as [Hd | Hd].
            ++
              pose proof (Hbr Fin.F1) as Hk.
              pose proof (Har Fin.F1) as Hj.
              exists (Fin.F1).
              cbn in Hj, Hk |- *.
              rewrite dec_true in Hk, Hj. 
              eapply special_soundness_berry; cbn;
              try (rewrite dec_true);
              [exact Hd | exact Hj | exact Hk].
            ++
              (* inductive case *)
              cbn in IHn.
              destruct Hd as (Hdl & Hdr).
              assert (He : (∀ f : Fin.t (S n),
              (if
                Gdec (gstl[@f] ^ rtl₁[@f])
                  (gop atl[@f] (hstl[@f] ^ cstl₁[@f]))
              then true
              else false) = true)).
              intro f;
              specialize (Har (Fin.FS f));
              exact Har.
              assert (Hf : 
              (∀ f : Fin.t (S n),
                (if
                  Gdec (gstl[@f] ^ rtl₂[@f])
                    (gop atl[@f] (hstl[@f] ^ cstl₂[@f]))
                  then true
                  else false) = true)).
              intro f; 
              specialize (Hbr (Fin.FS f));
              exact Hbr.
              rewrite Heqhcl, Heqhcr in Hdr.
              destruct (IHn gstl hstl atl
                (fold_right add cstl₁ zero)
                (fold_right add cstl₂ zero) cstl₁ cstl₂ rtl₁ rtl₂
                (conj eq_refl He) (conj eq_refl Hf) Hdr) as 
              (f & y & IH).
              exists (Fin.FS f), y;
              exact IH.
        Qed.


        Lemma generalise_or_sigma_soundness_generic :
          forall (m n : nat) 
          (gs hs : Vector.t G (m + (1 + n)))
          (a : Vector.t G (m + (1 + n))) 
          (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (m + (1 + n)))
          (r₁ r₂ : Vector.t F (m + (1 + n))),
          generalised_or_accepting_conversations 
            gs hs (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations 
            gs hs (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ -> 
          (* I know an index where relation R is true and I can 
            extract a witness out of it *)
          ∃ (f : Fin.t (m + (1 + n))) (y : F),
          (nth gs f)^y = (nth hs f).
        Proof.
          intros * Ha Hb.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            gs hs (a; c₁ :: cs₁; r₁) Ha as Hd.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            gs hs (a; c₂ :: cs₂; r₂) Hb as He.
          cbn in Hd, He.
          clear Ha; clear Hb.
          generalize dependent n;
          intros n gs hs a; 
          revert c₂; revert c₁;
          generalize dependent n.
          induction m as [|m' IHm].
          +
            intros * Ha Hb Hc.
            eapply generalise_or_sigma_soundness_base_case;
            try assumption.
            eapply generalised_or_accepting_conversations_correctness_backward;
            exact Ha.
            eapply generalised_or_accepting_conversations_correctness_backward;
            exact Hb.
            exact Hc.
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            cbn in * |- .
            destruct (vector_inv_S gs) as (gsh & gstl & Hd).
            destruct (vector_inv_S hs) as (hsh & hstl & He).
            destruct (vector_inv_S a) as (ah & atl & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hh).
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hi).
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hj).
            subst; cbn in Hc.
            remember (fold_right add cstl₁ zero) as hcl.
            remember (fold_right add cstl₂ zero) as hcr.
            (* case analysis on challenges *)
            assert (Hd : csh₁ <> csh₂ ∨ 
              (csh₁ = csh₂ ∧ (hcl <> hcr))).
            case_eq (Fdec csh₁ csh₂);
            intros Hd He.
            right.
            refine (conj Hd _).
            intros Hf; eapply Hc;
            rewrite Hd, Hf;
            exact eq_refl. 
            left; exact Hd.
            (* I know that 
            Hd: csh₁ ≠ csh₂ ∨ csh₁ = csh₂ ∧ hcl ≠ hcr*)
            destruct Hd as [Hd | Hd].
            ++
              pose proof (Hbr Fin.F1) as Hk.
              pose proof (Har Fin.F1) as Hj.
              exists (Fin.F1).
              cbn in Hj, Hk |- *.
              rewrite dec_true in Hk, Hj. 
              eapply special_soundness_berry; cbn;
              try (rewrite dec_true);
              [exact Hd | exact Hj | exact Hk].
            ++
              (* inductive case *)
              cbn in IHm.
              destruct Hd as (Hdl & Hdr).
              assert (He : (∀ f : Fin.t (m' + S n),
              (if
                Gdec (gstl[@f] ^ rtl₁[@f])
                  (gop atl[@f] (hstl[@f] ^ cstl₁[@f]))
              then true
              else false) = true)).
              intro f;
              specialize (Har (Fin.FS f));
              exact Har.
              assert (Hf : 
              (∀ f : Fin.t (m' + S n),
                (if
                  Gdec (gstl[@f] ^ rtl₂[@f])
                    (gop atl[@f] (hstl[@f] ^ cstl₂[@f]))
                  then true
                  else false) = true)).
              intro f; 
              specialize (Hbr (Fin.FS f));
              exact Hbr.
              rewrite Heqhcl, Heqhcr in Hdr.
              destruct (IHm _ gstl hstl atl
                (fold_right add cstl₁ zero)
                (fold_right add cstl₂ zero) cstl₁ cstl₂ rtl₁ rtl₂
                (conj eq_refl He) (conj eq_refl Hf) Hdr) as 
              (f & y & IH).
              exists (Fin.FS f), y;
              exact IH.
        Qed.


        

        
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
          ∀ (uscs : Vector.t F (m + (1 + n) + (m + n))) (c : F),
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
            (construct_or_conversations_schnorr x
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
              uscs c) = true.
        Proof.
          intros *.
          unfold generalised_or_accepting_conversations,
          construct_or_conversations_schnorr.
          repeat rewrite VectorSpec.splitat_append.
          destruct (vector_inv_S ([g] ++ gsr)) as (ga & gt & Ha).
          destruct (vector_inv_S ([h] ++ hsr)) as (ha & ht & Hb).
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          destruct (splitat m us) as (usa & usb) eqn:Hc.
          destruct (vector_inv_S usb) as (usba & usbb & Hd).
          destruct (splitat m cs) as (csa & csb) eqn:He.
          remember (construct_or_conversations_simulator_supplement gsl hsl usa csa)
          as sa.
          refine
          (match sa as s'
          return sa = s' -> _ with 
          |(a₁; c₁; r₁) => fun Hg => _  
          end eq_refl).
          unfold schnorr_protocol.
          remember (construct_or_conversations_simulator_supplement gt ht usbb csb)
          as sb. 
          refine
          (match sb as s'
          return sb = s' -> _ with 
          |(a₂; c₂; r₂) => fun Hi => _  
          end eq_refl); cbn.
          (*
          fold_right add (csa ++ csbb) zero = c₁ + c₂
          *)
          assert (Hj : c = (fold_right add
          (c₁ ++ c - fold_right add (csa ++ csb) zero :: c₂) zero)).
          remember (c - fold_right add (csa ++ csb) zero :: c₂) as ct.
          rewrite fold_right_app.
          rewrite Heqct; cbn.
          rewrite fold_right_app.
          rewrite Hg in Heqsa;
          eapply construct_or_conversations_simulator_challenge in Heqsa;
          rewrite Heqsa.
          rewrite Hi in Heqsb; 
          eapply construct_or_conversations_simulator_challenge in Heqsb;
          rewrite Heqsb.
          remember (fold_right add c₁ zero) as ca.
          remember (fold_right add c₂ zero) as cb.
          field.
          rewrite <-Hj.
          destruct (Fdec c c) as [Hk | Hk].
          rewrite generalised_or_accepting_conversations_supplement_app.
          eapply andb_true_iff.
          split.
          (* use simulator correctness *)
          rewrite <-Hg, Heqsa.
          eapply construct_or_conversations_simulator_completeness_supplement.
          cbn; eapply andb_true_iff.
          split.
          remember ((c - fold_right add (csa ++ csb) zero)) as ct.
          inversion Ha.
          rewrite <-H0.
          clear Hk; clear H0; clear H1.
          rewrite dec_true, R.
          assert (Hl : (g ^ x) ^ ct = (g ^ (x * ct))).
          rewrite smul_pow_up; 
          reflexivity.
          rewrite Hl; clear Hl.
          assert (Hxc : x * ct = ct * x).
          rewrite commutative; reflexivity.
          rewrite Hxc; clear Hxc.
          rewrite (@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow).
          reflexivity.
          exact Hvec.
          (* simulator correctness *)
          rewrite <-Hi, Heqsb.
          inversion Ha; subst.
          inversion Hb; subst.
          eapply Eqdep.EqdepTheory.inj_pair2 in H1, H2.
          subst.
          eapply construct_or_conversations_simulator_completeness_supplement.
          congruence.
        Qed.



        (* This proof basically hinges on simulator_supplement proof. It's 
        here clear presentation *)
        (*simulator completeness*)
        Lemma construct_or_conversations_simulator_completeness : 
          ∀ (uscs : Vector.t F (m + (1 + n) + (m + n))) (c : F),
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
            (construct_or_conversations_simulator
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
              uscs c) = true.
        Proof using -(x R).
          clear x R. 
          intros *.
          unfold generalised_or_accepting_conversations,
          construct_or_conversations_simulator.
          repeat rewrite VectorSpec.splitat_append.
          destruct (vector_inv_S ([g] ++ gsr)) as (ga & gt & Ha).
          destruct (vector_inv_S ([h] ++ hsr)) as (ha & ht & Hb).
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          destruct (splitat m us) as (usa & usb) eqn:Hc.
          destruct (vector_inv_S usb) as (usba & usbb & Hd).
          destruct (splitat m cs) as (csa & csb) eqn:He.
          remember (construct_or_conversations_simulator_supplement gsl hsl usa csa)
          as sa.
          refine
          (match sa as s'
          return sa = s' -> _ with 
          |(a₁; c₁; r₁) => fun Hg => _  
          end eq_refl).
          unfold schnorr_simulator.
          remember (construct_or_conversations_simulator_supplement gt ht usbb csb)
          as sb. 
          refine
          (match sb as s'
          return sb = s' -> _ with 
          |(a₂; c₂; r₂) => fun Hi => _  
          end eq_refl); cbn.
          assert (Hj : c = (fold_right add
          (c₁ ++ c - fold_right add (csa ++ csb) zero :: c₂) zero)).
          remember (c - fold_right add (csa ++ csb) zero :: c₂) as ct.
          rewrite fold_right_app.
          rewrite Heqct; cbn.
          rewrite fold_right_app.
          rewrite Hg in Heqsa;
          eapply construct_or_conversations_simulator_challenge in Heqsa;
          rewrite Heqsa.
          rewrite Hi in Heqsb; 
          eapply construct_or_conversations_simulator_challenge in Heqsb;
          rewrite Heqsb.
          remember (fold_right add c₁ zero) as ca.
          remember (fold_right add c₂ zero) as cb.
          field.
          rewrite <-Hj.
          destruct (Fdec c c) as [Hk | Hk].
          rewrite generalised_or_accepting_conversations_supplement_app.
          eapply andb_true_iff.
          split.
          (* use simulator_supplement correctness *)
          rewrite <-Hg, Heqsa.
          eapply construct_or_conversations_simulator_completeness_supplement.
          cbn; eapply andb_true_iff.
          split.
          remember ((c - fold_right add (csa ++ csb) zero)) as ct.
          inversion Ha.
          rewrite <-H0.
          clear Hk; clear H0; clear H1.
          (* schnorr simulator correctness *)
          rewrite dec_true.
          rewrite <-associative.
          inversion Hb.
          rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow).
          rewrite field_zero_iff_left,
          vector_space_field_zero,
          monoid_is_right_identity.
          reflexivity.
          typeclasses eauto.
          (* simulator_supplement correctness *)
          rewrite <-Hi, Heqsb.
          inversion Ha; subst.
          inversion Hb; subst.
          eapply Eqdep.EqdepTheory.inj_pair2 in H1, H2.
          subst.
          eapply construct_or_conversations_simulator_completeness_supplement.
          congruence.
        Qed.

        (* end of completeness *)


        (* special soundness *)
        Lemma generalise_or_sigma_soundness :
         forall (a : Vector.t G (m + (1 + n))) 
         (c₁ c₂ : F)
         (cs₁ cs₂ : Vector.t F (m + (1 + n)))
         (r₁ r₂ : Vector.t F (m + (1 + n))),
         generalised_or_accepting_conversations 
          (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) (a; c₁ :: cs₁; r₁) = true ->
         generalised_or_accepting_conversations 
          (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) (a; c₂ :: cs₂; r₂) = true ->
         c₁ <> c₂ -> 
         (* I know an index where relation R is true and I can 
          extract a witness out of it *)
         ∃ (f : Fin.t (m + (1 + n))) (y : F),
         (nth (gsl ++ [g] ++ gsr) f)^y = (nth (hsl ++ [h] ++ hsr) f).
        Proof using -(x R).
          clear x R.
          intros * Ha Hb Hc.
          eapply generalise_or_sigma_soundness_generic;
          [exact Ha | exact Hb | exact Hc].
        Qed. 
        

         
        (* honest verifier zero knowledge proof *)

        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        Lemma generalised_or_schnorr_distribution_probability_generic : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F (m + (1 + n) + (m + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_schnorr x 
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) uscs c))) → 
          pr = 1 / q.
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

        

        Lemma generalised_or_schnorr_distribution_transcript_generic : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_schnorr x 
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) uscs c))) → 
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_or_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_or_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.




        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        (* This proof is very nice. *)
        (* From Berry's notes : we have (m = 0 ∧ n = 1) ∨
          (m = 1 ∧ n = 0). In both cases, probability is 
          1 / |lf|^3 *)
        Lemma generalised_or_special_honest_verifier_schnorr_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_or_schnorr_distribution lf Hlfn 
            x (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) c) ->
            (* it's an accepting conversation and probability is *)
          generalised_or_accepting_conversations 
          (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) (m + (1 + n) + (m + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_or_schnorr_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_or_schnorr_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.


        Lemma generalised_or_simulator_distribution_probability_generic : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F (m + (1 + n) + (m + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_simulator 
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) uscs c))) → 
          pr = 1 / q.
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



        Lemma generalised_or_simulator_distribution_transcript_generic : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_simulator
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) uscs c))) → 
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_or_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_or_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.




        (* Every element in generalised simulator distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        (* This proof is very nice. *)
        (* From Berry's notes : we have (m = 0 ∧ n = 1) ∨
          (m = 1 ∧ n = 0). In both cases, probability is 
          1 / |lf|^3 *)
        Lemma generalised_or_special_honest_verifier_simulator_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_or_simulator_distribution lf Hlfn 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) c) ->
            (* it's an accepting conversation and probability is *)
          generalised_or_accepting_conversations 
          (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) (m + (1 + n) + (m + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_or_simulator_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_or_simulator_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.


      End Proofs.


    End Or.


    Section NEQ.

      (* generalised NEQ *)
      Section Def.

        (* 
          In this section, we prove that 
          ∃ x₁ x₂ x₃ : g^x₁ = h₁ ∧ g^x₂ = h₂ ∧ g^x₃ = h₃ .... 
          ∧ x₁ <> x₂ ∧ x₁ <> x₃ ∧ x₁ <> ..... ∧ 
          x₂ <> x₃ <> x₂ <> x₄ ...... 
          ...
          ..
          .
        *)

        (* begin proofs for computations *)
        (* Just to make sure  that my proofs are transparent *)
        #[local]
        Definition nat_succ_eq : 
          ∀ (n m : nat), S (Nat.add n (S m)) = Nat.add n (S (S m)).
        Proof.
          refine(fix Fn n {struct n} :=
            match n with 
            | 0 => fun m => eq_refl 
            | S n' => fun m => eq_ind_r 
              (fun w => S w = S (n' + S (S m))) eq_refl (Fn n' m)
            end).
        Defined.
            
        
        #[local]
        Definition nat_eq_succ : 
          ∀ (n m : nat), S (Nat.add n (S m)) = S (S (Nat.add n m)).
        Proof.
          refine(fix Fn n {struct n} :=
            match n with 
            | 0 => fun m => eq_refl 
            | S n' => fun m => @eq_ind_r _ _  
              (λ x : nat, S x = S (S (S (n' + m)))) eq_refl _ (Fn n' m)
            end).
        Defined.
      

        #[local]
        Theorem subst_vector {A : Type} : forall {n m : nat},
          Vector.t A n -> n = m -> Vector.t A m.
        Proof.
          intros * u Ha.
          exact (@eq_rect nat n (fun x => Vector.t A x) u m Ha).
        Defined.

    
      

        Lemma divmod_simplification : 
          forall (x y q u : nat),
          fst (Nat.divmod x y q u) = (q + fst (Nat.divmod x y 0 u))%nat.
        Proof.
          induction x;
          intros *; simpl;
          [ | destruct u; rewrite IHx;
          [erewrite IHx with (q := 1) | erewrite IHx]];
          try nia.
        Defined.


        Lemma nat_divmod : 
          forall (n : nat),
          fst (Nat.divmod (n + S (S (n + S (S (n + n * S (S n)))))) 1 1 1) =
          (1 + S n + fst (Nat.divmod (n + S (n + n * S n)) 1 0 0))%nat.
        Proof.
          intros n.
          rewrite divmod_simplification;
          simpl; f_equal. 
          assert (Ha : 1 <= 1) by nia.
          pose proof PeanoNat.Nat.divmod_spec 
          (n + S (S (n + S (S (n + n * S (S n))))))%nat 1 0 1 Ha as Hb.
          destruct (PeanoNat.Nat.divmod 
            (n + S (S (n + S (S (n + n * S (S n)))))) 1 0 1) as 
          (qa & qb) eqn:Hc; simpl.
          assert (Hd : 0 <= 1) by nia. 
          pose proof PeanoNat.Nat.divmod_spec
          (n + S (n + n * S n)) 1 0 0 Hd as He. 
          destruct (Nat.divmod (n + S (n + n * S n)) 1 0 0) as 
          (qaa & qbb) eqn:Hf; simpl. 
          nia.
        Defined.
          
        (* end of proofs *)


        
        (*
          g₁ h₁ x₁ gs hs xs us c
          Proves that x₁ is not equal to any element in xs, i.e.,
          ∀ x : F, In x xs -> x <> x₁
          using Okamoto protocol
        *)
        (* don't reuse the random numbers! *)
        (* can I use the same challenge? *)
        #[local]
        Definition generalised_construct_neq_conversations_okamoto :
          ∀ {n : nat}, F -> G -> G ->     
          Vector.t F (1 + n) ->
          Vector.t G (1 + n) -> Vector.t G (1 + n) -> 
          Vector.t F  (2 * (1 + n)) -> F -> 
          @sigma_proto (1 + n) 1 (2 * (1 + n)).
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun  x₁ g₁ h₁ xs gs hs  us c => _
            | S n' => fun  x₁ g₁ h₁  xs gs hs  us c => _ 
            end); cbn in * |- *.
          +
            (* base case *)
            destruct (vector_inv_S xs) as (x₂ & _).
            destruct (vector_inv_S gs) as (g₂ & _).
            destruct (vector_inv_S hs) as (h₂ & _).
            destruct (vector_inv_S us) as (u₁ & ustl & _).
            destruct (vector_inv_S ustl) as (u₂ & _).
            exact ([gop ((gop g₁ g₂)^u₁) ((gop h₁ h₂)^u₂)]; [c];
              [u₁ + c * x₁ * inv (x₁ - x₂); u₂ + c * inv (x₂ - x₁)]).
          +
            (* induction case *)
            destruct (vector_inv_S gs) as (g₂ & gstl & _).
            destruct (vector_inv_S hs) as (h₂ & hstl & _).
            destruct (vector_inv_S xs) as (x₂ & xstl & _).
            destruct (vector_inv_S us) as (u₁ & ustl & _).
            destruct (vector_inv_S ustl) as (u₂ & ustll & _).
            refine 
              match (Fn _ x₁ g₁ h₁  xstl gstl hstl  
                (@subst_vector F _ _ ustll (eq_sym (nat_succ_eq n' (n' + 0)))) c)
              with 
              | (a; _ ; r) => ([gop ((gop g₁ g₂)^u₁) ((gop h₁ h₂)^u₂)] ++ a; [c]; 
                [u₁ + c * x₁ * inv (x₁ - x₂); u₂ + c * inv (x₂ - x₁)] ++ 
                (@eq_rect nat (S (n' + S (n' + 0)))
                  (fun x => Vector.t F x) r _  (nat_succ_eq n' (n' + 0))))
              end.
        Defined.


        (* 
          xs : secrets 
          gs  hs : public values such h := g^x 
          us: randomness 
          c : challenge  

          O (n^2) proof terms! 
          Is there efficient way to model NEQ
        
          Key question: how much randomness I need? 
          We have (2 + n) gs and hs and for 
          (2 * (1 + n) + 2 * n + ...... + 2 = 
          (1 + n) (2 + n)

          The amount of randomenss I need is : (1 + n) * (2 + n)
        *)
        (* 
          This function is going to call 
          generalised_construct_neq_conversations_okamoto
          for each pair 
        *)
        
        #[local]
        Definition generalised_construct_neq_conversations_schnorr_supplement :
          ∀ {n : nat}, Vector.t F (2 + n) -> 
          Vector.t G (2 + n) -> 
          Vector.t G (2 + n) ->  
          Vector.t F ((2 + n) * (1 + n))-> F -> 
          @sigma_proto (Nat.div ((2 + n) * (1 + n)) 2) 
            1 ((2 + n) * (1 + n)).
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun xs gs hs us c => _
            | S n' => fun xs gs hs us c => _ 
            end); cbn in * |- *.
          +
            (* call Okamoto construction *)
            refine 
              (generalised_construct_neq_conversations_okamoto 
              (hd xs) (hd gs) (hd hs) (tl xs) (tl gs) (tl hs) us c).
          +
            (* Wow! Look at assumptions *)
            (* requires some complicated reasoning about arithmatic *)
            (* inductive case *)
            (* massage the goal *)
            replace (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) 
            with ((2 * (2 + n')) + (S (n' + S (n' + n' * S n'))))%nat in us.
             (* Take 2 * (S (S n')) from us *)
            destruct (splitat (2 * (1 + S n')) us) as (usl & usr).
            refine
              match (generalised_construct_neq_conversations_okamoto 
              (hd xs) (hd gs) (hd hs) (tl xs) (tl gs) (tl hs) usl c)
              with
              |(a₁; _; r₁) => _ 
              end.
            refine 
              match Fn _ (tl xs) (tl gs) (tl hs)  usr c
              with 
              |(a₂; _; r₂) => _ 
              end.
            set (r := r₁ ++ r₂);
            clearbody r.
            set (a := a₁ ++ a₂);
            clearbody a.
            (* massage a *)
            replace ((1 + S n' + fst (Nat.divmod (n' + S (n' + n' * S n')) 1 0 0)))%nat
            with (fst (Nat.divmod (n' + S (S (n' + S (S (n' + n' * S (S n')))))) 1 1 1))
            in a.
            (* massage r *)
            replace (2 * (1 + S n') + S (n' + S (n' + n' * S n')))%nat with 
            (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) in r.
            refine (a; [c]; r).
            all:try nia.
            eapply nat_divmod.
        Defined.


        (* input xs, gs, hs, us, c *)
        (* size of proofs is O(n^2) for NEQ if 
        we have n statements. 
        *)
        Definition generalised_construct_neq_conversations_schnorr {n : nat} : 
          Vector.t F (2 + n) -> Vector.t G (2 + n) -> 
          Vector.t G (2 + n) -> 
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> F ->
          @sigma_proto ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          (* first I compute AND protocol *)
          intros xs gs hs us c.
          (* split the randomness us at 2 + n *)
          destruct (splitat (2 + n) us) as (usl & usr).
          (* Now run AND protocol *)
          (refine 
            match construct_and_conversations_schnorr xs gs usl c with 
            | (a; _; r) => _ 
            end).
          (* Now call supplement protocol *)
          (refine 
            match generalised_construct_neq_conversations_schnorr_supplement 
              xs gs hs usr c with 
            | (a₁; _; r₁) => (a ++ a₁; [c]; r ++ r₁)
            end).
        Defined.



        (* simulator *)
        (* Does not involve secret *)
        (* g₁ h₁ gh hs us c *)
        #[local]
        Definition generalised_construct_neq_conversations_simulator_okamoto :
          ∀ {n : nat}, G -> G ->
          Vector.t G (1 + n) -> 
          Vector.t G (1 + n) -> 
          Vector.t F  (2 * (1 + n)) -> F -> 
          @sigma_proto (1 + n) 1 (2 * (1 + n)).
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun g₁ h₁ gs hs us c => _
            | S n' => fun g₁ h₁ gs hs us c => _ 
            end); cbn in * |- *.
          +
            destruct (vector_inv_S gs) as (g₂ & _).
            destruct (vector_inv_S hs) as (h₂ & _).
            destruct (vector_inv_S us) as (u₁ & ustl & _).
            destruct (vector_inv_S ustl) as (u₂ & _).
            exact
            ([gop ((gop g₁ g₂)^u₁) (gop ((gop h₁ h₂)^u₂) g₂^(opp c))]; [c];
              [u₁; u₂]).
          +
            destruct (vector_inv_S gs) as (g₂ & gstl & _).
            destruct (vector_inv_S hs) as (h₂ & hstl & _).
            destruct (vector_inv_S us) as (u₁ & ustl & _).
            destruct (vector_inv_S ustl) as (u₂ & ustll & _).
            refine 
              match Fn _ g₁ h₁ gstl hstl 
                (@subst_vector F _ _ ustll (eq_sym (nat_succ_eq n' (n' + 0)))) c 
              with 
              | (a; _; r) => 
                ([gop ((gop g₁ g₂)^u₁) (gop ((gop h₁ h₂)^u₂) g₂^(opp c))] ++ a; [c]; _)
              end.
            replace (S (n' + S (n' + 0)))%nat with 
            (n' + S (S (n' + 0)))%nat in r.
            exact ([u₁; u₂] ++ r).
            nia.
        Defined.

        
        (* gs hs us c *)
        #[local]
        Definition generalised_construct_neq_conversations_simulator_supplement :
          ∀ {n : nat}, 
          Vector.t G (2 + n) -> 
          Vector.t G (2 + n) -> 
          Vector.t F ((2 + n) * (1 + n))-> F -> 
          @sigma_proto (Nat.div ((2 + n) * (1 + n)) 2) 1 ((2 + n) * (1 + n)).
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun gs hs us c => _
            | S n' => fun gs hs us c => _ 
            end); cbn in * |- *.
          +
            exact (generalised_construct_neq_conversations_simulator_okamoto
            (hd gs) (hd hs) (tl gs) (tl hs) us c).
          +
            replace (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) 
            with ((2 * (2 + n')) + (S (n' + S (n' + n' * S n'))))%nat in us.
             (* Take 2 * (S (S n')) from us *)
            destruct (splitat (2 * (1 + S n')) us) as (usl & usr).
            refine
              match (generalised_construct_neq_conversations_simulator_okamoto 
              (hd gs) (hd hs) (tl gs) (tl hs) usl c)
              with
              |(a₁; _; r₁) => _ 
              end.
            refine 
              match Fn _ (tl gs) (tl hs) usr c
              with 
              |(a₂; _; r₂) => _ 
              end.
            set (r := r₁ ++ r₂);
            clearbody r.
            set (a := a₁ ++ a₂);
            clearbody a.
            replace ((1 + S n' + fst (Nat.divmod (n' + S (n' + n' * S n')) 1 0 0)))%nat
            with (fst (Nat.divmod (n' + S (S (n' + S (S (n' + n' * S (S n')))))) 1 1 1))
            in a.
            (* massage r *)
            replace (2 * (1 + S n') + S (n' + S (n' + n' * S n')))%nat with 
            (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) in r.
            refine (a; [c]; r).
            all:try nia.
            eapply nat_divmod.
        Defined.


            
        (* input gs, hs, us, c *)
        (* does not involve secret *)
        Definition generalised_construct_neq_conversations_simulator {n : nat} : 
          Vector.t G (2 + n) -> Vector.t G (2 + n) -> 
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> F ->
          @sigma_proto ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          (* first I compute AND protocol simulator *)
          intros gs hs us c.
          (* split the randomness us at 2 + n *)
          destruct (splitat (2 + n) us) as (usl & usr).
          (* run AND protocol simulator *)
          refine 
            match construct_and_conversations_simulator gs hs usl c with 
            | (a; _; r) => _ 
            end.
          refine 
            match generalised_construct_neq_conversations_simulator_supplement 
              gs hs usr c with 
            | (a₁; _; r₁) => (a ++ a₁; [c]; r ++ r₁)
            end.
        Defined.

        (* end simulator *)


        (* verification equation *)

        (* verification equation of Okamoto protocol *)
        (* g₁ h₁ gs hs sigma_proof *)
        #[local]
        Definition generalised_neq_accepting_conversations_okamoto :
          ∀ {n : nat}, G -> G ->    
          Vector.t G (1 + n) -> Vector.t G (1 + n) -> 
          @sigma_proto (1 + n) 1 (2 * (1 + n)) -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun  g₁ h₁ gs hs us => _
            | S n' => fun  g₁ h₁ gs hs us => _ 
            end); cbn in * |- *.
          +
            refine 
              match us with 
              |(a; c; r) => _ 
              end.
            (*
              Verifies the following equation
              (g₁ * g₂)^r₁ * (h₁ * h₂)^r₂ = a₁ * g₂^c₁
            *)
            destruct (vector_inv_S gs) as (g₂ & _).
            destruct (vector_inv_S hs) as (h₂ & _).
            destruct (vector_inv_S a) as (a₁ & _).
            destruct (vector_inv_S c) as (c₁ & _).
            destruct (vector_inv_S r) as (r₁ & rtl & _).
            destruct (vector_inv_S rtl) as (r₂ & _).
            refine 
              match Gdec 
                (gop ((gop g₁ g₂)^r₁) ((gop h₁ h₂)^r₂)) 
                (gop a₁ (g₂^c₁))
              with 
              | left _ => true 
              | right _ => false 
              end.
          +
            refine 
              match us with 
              |(a; c; r) => _ 
              end.
            destruct (vector_inv_S gs) as (g₂ & gstl & _).
            destruct (vector_inv_S hs) as (h₂ & hstl & _).
            destruct (vector_inv_S a) as (a₁ & atl & _).
            destruct (vector_inv_S c) as (c₁ & _).
            destruct (vector_inv_S r) as (r₁ & rtl & _).
            destruct (vector_inv_S rtl) as (r₂ & rtll & _).
            refine 
              match Gdec 
                (gop ((gop g₁ g₂)^r₁) ((gop h₁ h₂)^r₂)) 
                (gop a₁ (g₂^c₁))
              with
              | left _ => Fn _ g₁ h₁ gstl hstl (atl; c; _) (* check the rest *)
              | right _ => false (* no point of checking the rest *)
              end.
            (* 
              massage rtll to the goal
            *)
            refine 
              (@eq_rect nat (n' + S (S (n' + 0)))%nat 
                (fun x => Vector.t F x) rtll (S (n' + S (n' + 0)))
                (eq_sym (nat_succ_eq n' (n' + 0)))).
        Defined.


        Definition generalised_neq_accepting_conversations_supplement :
          forall {n : nat}, 
          Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          @sigma_proto (Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) * (1 + n)) -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun gs hs sig => _
            | S n' => fun gs hs sig => _ 
            end); cbn in * |- *.
          +
            (* call Okamoto verification *)
            refine 
              (generalised_neq_accepting_conversations_okamoto 
                (hd gs) (hd hs) (tl gs) (tl hs) sig).
          +
            (* inductive case *)
            refine 
              match sig with 
              |(a; c; r) => _ 
              end.
            destruct (vector_inv_S gs) as (g₁ & gstl & _).
            destruct (vector_inv_S hs) as (h₁ & hstl & _).
            rewrite nat_divmod in a.
            destruct (splitat (2 + n') a) as (al & ar).
            replace (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) 
            with ((2 * (2 + n')) + (S (n' + S (n' + n' * S n'))))%nat in r.
            destruct (splitat (2 * (2 + n')) r) as (rl & rr).
            (* 
              Call generalised_neq_conversations_okamoto and if it 
              returns true than continue checking else 
              break. 
            *)
            refine 
              match generalised_neq_accepting_conversations_okamoto g₁ h₁ gstl hstl (al; c; rl)
              with 
              | true => Fn _ gstl hstl (ar ; c; rr)
              | _ => false
              end.
            nia.
        Defined.




        Definition generalised_neq_accepting_conversations {n : nat} :
          Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          @sigma_proto ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)) -> bool.
        Proof.
          intros gs hs sig.
          (* split the sig at (2 + n) *)
          refine 
            match sig with 
            |(a; c; r) => _ 
            end.
          (* split commitments at (2 + n )*)
          destruct (splitat (2 + n) a) as (al & ar).
          (* split responses at (2 + n)*)
          destruct (splitat (2 + n) r) as (rl & rr).
          (* Run AND verifier on (al; c; rl) *)
          refine 
            match 
              generalised_and_accepting_conversations gs hs (al; c; rl)
            with 
            | true => _ 
            | _ => false (* No point of checking futher *) 
            end.
          (* run Okamoto verifier on (ar; c; rr) *)
          exact (generalised_neq_accepting_conversations_supplement gs hs (ar; c; rr)).
        Defined.
          
        (* end verification *)

        (* distribution (zero-knowledge) *)

        Definition generalised_neq_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n)) (c : F) : 
          dist (@sigma_proto ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
          ((2 + n) + (2 + n) * (1 + n))) :=
          (* draw ((2 + n) + ((1 + n) + (1 + n))) random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((2 + n) + ((2 + n) * (1 + n))) ;;
          Ret (generalised_construct_neq_conversations_schnorr xs gs hs us c).


        Definition generalised_neq_simulator_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G (2 + n)) (c : F) : 
          dist (@sigma_proto ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
          ((2 + n) + (2 + n) * (1 + n))) :=
          (* draw ((2 + n) + ((1 + n) + (1 + n))) random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((2 + n) + ((2 + n) * (1 + n))) ;;
          Ret (generalised_construct_neq_conversations_simulator gs hs us c).


      End Def.


      Section Proofs.
      

        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).
        
        (* completeness *)
        Lemma construct_neq_conversations_schnorr_completeness : 
          forall (n : nat) (xs : t F (2 + n)) (gs hs : t G (2 + n)) 
          (us : t F (2 + n + (2 + n) * (1 + n))) (c : F),
          generalised_neq_accepting_conversations gs hs
            (generalised_construct_neq_conversations_schnorr xs gs hs us c) = true.
        Proof.
          
        Admitted.


        (* special soundness *)


        (* zero-knowledge proof *)


      End Proofs.

    End NEQ.


    

  End DL.

End Zkp.


