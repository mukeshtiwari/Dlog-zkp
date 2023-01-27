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


Section PedCommit.


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
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec: @vector_space F (@eq F) zero one add mul sub 
        div opp inv G (@eq G) gid ginv gop gpow}.
      
  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "/" := div.
  Local Infix "+" := add.
  Local Infix "-" := sub.

  Section SingleCommit.
    (* g and h are independent. Their 
      discrete logarithm is unknown *)
    Context 
      (g h : G).

    Definition pedCommit (m r : F) : G :=
      gop (g^m) (h^r).

  End SingleCommit.


  Section VectorCommit.

    Context
      {n : nat}
      (g : G)
      (h : Vector.t G n).

    
    Definition pedVectorCommit (m : Vector.t F n) (r : F) : G :=
      let zpv := zip_with (λ (hi : G) (mi : F), (hi, mi)) h m in  
      gop (g^r) 
        (fold_right (λ '(hi, mi) (acc : G), 
          gop (hi^mi) acc) zpv gid).

  End VectorCommit.


  Section MatrixCommit.

    Context
      {n : nat}
      (g : G)
      (h : Vector.t G n).

    Definition pedMatrixCommit 
      (m : Vector.t (Vector.t F n) n) 
      (r : Vector.t F n) : Vector.t G n.
    Admitted.
    (* mj fetch jth column from m
       rj fetch jth entry from r
       call pedVectorCommit mj rj 
    
    *)
  End MatrixCommit.

End PedCommit.
    



    

    