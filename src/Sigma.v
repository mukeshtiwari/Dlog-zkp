Require Import Setoid
  Sigma.Algebra.Hierarchy
  Sigma.Algebra.Group Sigma.Algebra.Monoid
  Sigma.Algebra.Field Sigma.Algebra.Integral_domain
  Sigma.Algebra.Ring Sigma.Algebra.Vector_space
  Lia Vector Coq.Unicode.Utf8 Sigma.Prob
  Psatz.

Import VectorNotations.

Module Zkp.

  (* Discrete Logarithm Zero Knowlege Proof *) 
  Section DL. 
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
      Context (x : F) (g h : G) (key_rel : h = g^x).


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
      *)
      Definition schnorr_protocol_correct (v : @sigma_proto 1 1 1) : Prop :=
        match v with
        | mk_sigma _ _ _ com chal res =>  
          g^(hd res) = gop (hd com) (h^(hd chal))
        end.


      (* Sigma protocol is correct *)  
      Lemma schnorr_correctness: forall r c, 
        schnorr_protocol_correct (schnorr_protocol r c). 
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
        reflexivity.
        typeclasses eauto.
      Qed.

      

  End Basic_sigma.
