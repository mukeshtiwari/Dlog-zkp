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
     

    Local Infix "^" := gpow.
    Local Infix "*" := mul.
    Local Infix "/" := div.
    Local Infix "+" := add.
    Local Infix "-" := sub.



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
        (* h = g^x *)
      

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
        Lemma schnorr_completeness : forall r c,
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
        Proof.
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
        Proof.
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
        c₁ <> c₂ ->  (* Todo: Change this into a notation c₁ <|> c₂. *)
        accepting_conversation g h ([a]; [c₁]; [r₁]) = true -> (* and it's accepting *) 
        accepting_conversation g h ([a]; [c₂]; [r₂]) = true -> (* and it's accepting *)
        ∃ y : F, g^y = h. (* then we can find a witness y such that g^y = h *)
      Proof.
        clear R. (* remove the assumption, otherwise it's trivial :)*)
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
          [((a; c; r), prob); ((a; c; r), prop) ......]
      *)
      Definition schnorr_distribution (lf : list F) 
        (Hlfn : lf <> List.nil) (c : F) : dist sigma_proto :=
        u <- (uniform_with_replacement lf Hlfn) ;;
        Ret (schnorr_protocol x g u c).
      
      
      (* without secret *)
      Definition simulator_distribution 
        (lf : list F) (Hlfn : lf <> List.nil) (c : F) :=
        u <- (uniform_with_replacement lf Hlfn) ;;
        Ret (schnorr_simulator g h u c).

      
      Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      Lemma probability_schnorr_distribution_generic : 
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



      (* Every elements in @schnorr_distribution 
        has probability 1/ (List.length lf) where 
        lf the list of Field element from which the 
        random r is drawn *)
      Lemma probability_schnorr_distribution : 
        forall (lf : list F) 
        (Hlfn : lf <> List.nil) (c : F) a₁ c₁ r₁ prob n,
        n = List.length lf -> 
        List.In ((a₁; c₁; r₁), prob) 
          (@schnorr_distribution lf Hlfn c) ->
        prob = 1 / n. 
      Proof.
        cbn.
        intros * Hn Hl.
        assert (Hlt : List.length (uniform_with_replacement lf Hlfn) =
          List.length lf).
        unfold uniform_with_replacement.
        rewrite List.map_length;
        reflexivity.
        pose proof probability_schnorr_distribution_generic
        (uniform_with_replacement lf Hlfn)
        (a₁; c₁; r₁) prob c n as Ht.
        rewrite Hn.
        rewrite Hn in Ht.
        specialize (Ht 
          (uniform_probability lf Hlfn) Hl).
        exact Ht.
      Qed.

        
      Lemma probability_simulator_distribution_generic : 
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

      (* Every elements in @simulator_distribution 
        has probability 1/ (List.length lf) where 
        lf the list of Field element from which the 
        random r is drawn *)
      Lemma probability_simulator_distribution : 
        forall (lf : list F) 
        (Hlfn : lf <> List.nil) (c : F) a₁ c₁ r₁ prob n, 
        n = List.length lf -> 
        List.In ((a₁; c₁; r₁), prob) 
          (@simulator_distribution lf Hlfn c) ->
        prob = 1 / n.
      Proof.
        cbn.
        intros * Hn Hl.
        assert (Hlt : List.length (uniform_with_replacement lf Hlfn) =
          List.length lf).
        unfold uniform_with_replacement.
        rewrite List.map_length;
        reflexivity.
        pose proof probability_simulator_distribution_generic
        (uniform_with_replacement lf Hlfn)
        (a₁; c₁; r₁) prob c n as Ht.
        rewrite Hn.
        rewrite Hn in Ht.
        specialize (Ht 
          (uniform_probability lf Hlfn) Hl).
        exact Ht.
      Qed.
        
    

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

    Section Compose.

      Definition compose_two_sigma_protocols {n m r u v w : nat} 
      (s₁ : @sigma_proto n m r) (s₂ : @sigma_proto u v w) :
      @sigma_proto (n + u) (m + v) (r + w) :=
      match s₁, s₂ with 
      |(mk_sigma _ _ _ a₁ c₁ r₁), (mk_sigma _ _ _ a₂ c₂ r₂) =>
        mk_sigma _ _ _ (a₁ ++ a₂) (c₁ ++ c₂) (r₁ ++ r₂)
      end.

    End Compose.
    
    Section Parallel.

      Section Def.

        (*
          Construct parallel Sigma protocol for a relation R 

          h + g^x
        *)
        Definition construct_parallel_conversations_schnorr :
          forall {n : nat}, 
          F -> G ->  Vector.t F n -> Vector.t F n -> @sigma_proto n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun x g u c => _
          | S n' => fun x g u c  => _
          end).
          + refine (mk_sigma _ _ _ [] [] []).
          + 
            destruct (vector_inv_S u) as (uh & utl & _).
            destruct (vector_inv_S c) as (ch & ctl & _).
            exact (@compose_two_sigma_protocols _ _ _ _ _ _ 
              (schnorr_protocol x g uh ch)
              (Fn _ x g utl ctl)).
        Defined.


        (* Does not involve the secret x *)
        Definition construct_parallel_conversations_simulator :
          forall {n : nat}, 
          G ->  G -> Vector.t F n -> Vector.t F n -> @sigma_proto n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun g h u c => _
          | S n' => fun g h u c  => _
          end).
          + refine (mk_sigma _ _ _ [] [] []).
          + 
            destruct (vector_inv_S u) as (uh & utl & _).
            destruct (vector_inv_S c) as (ch & ctl & _).
            exact (@compose_two_sigma_protocols _ _ _ _ _ _ 
              (schnorr_simulator g h uh ch)
              (Fn _ g h utl ctl)).
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
        Proof.
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
            subst; simpl.
            eapply andb_true_iff in Ha.
            destruct Ha as (_ & Ha).
            exact (IHn _ Ha hf).
        Qed.
          
        (* When we have an accepting conversations, then 
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
        Proof.
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
        Proof.
          split;
          [apply generalised_parallel_accepting_conversations_correctness_backward |
          apply generalised_parallel_accepting_conversations_correctness_forward].
        Qed.

        (* completeness *)

        
           
        (* soundness *)
        Lemma generalise_parallel_sigma_soundenss : 
          ∀ (n : nat) 
          (s₁ s₂ : @sigma_proto (2 + n) (2 + n) (2 + n)),
          (match s₁, s₂ with 
          | (a₁ ; c₁; _), (a₂ ; c₂; _) => 
          two_challenge_vectors_disjoint_someelem c₁ c₂ ->
          two_challenge_vectors_same_everyelem a₁ a₂ ->
          (* accepting conversatation*)
          @generalised_parallel_accepting_conversations _ g h s₁ = true -> 
          (* accepting conversatation*)
          @generalised_parallel_accepting_conversations _ g h s₂ = true ->
          ∃ y : F, g^y = h
          end).
        Proof.

        Admitted.

        (* zero-knowledge-proof *)

        
        





      End Proofs.


    
    End Parallel.

    Section And.

      Section Def.
         
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

        


      End Proofs.
          

    End And.

    Section EQ.

    End EQ.


    Section Or.


    End Or.



    

  End DL.

    (* 
    Parallel Composition
    AND composition
    EQ Composition
    OR Composition  
    Section And_Sigma.
    *)
End Zkp.


  
