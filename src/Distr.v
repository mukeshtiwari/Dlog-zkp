Require Import ExtLib.Structures.Monad
  ExtLib.Structures.Functor
  ExtLib.Structures.Applicative
  ExtLib.Structures.MonadLaws
  ExtLib.Structures.FunctorLaws
  Coq.Unicode.Utf8 
  Coq.Logic.FunctionalExtensionality
  Coq.PArith.Pnat Coq.NArith.BinNatDef
  Coq.PArith.BinPos Lia Coq.Lists.List
  Coq.Classes.Morphisms 
  Coq.Classes.SetoidClass 
  Coq.Sorting.Permutation
  Coq.Relations.Relation_Definitions
  Coq.Logic.FunctionalExtensionality 
  Prob.


Section Distr.



  (* Probability Distribution on a type A *)
  Definition dist (A : Type) :=  list (A * prob).
    
  (* Equality on probability distributions. Two probability 
    distributions are equal when they are same list but 
    in different order.
  *)
  Definition dist_equiv {A : Type} : relation (dist A) := 
    fun xs ys => 
    (∀ x, In x xs <-> In x ys) ∧ 
    (List.length xs = List.length ys).

   
  Local Infix "=r=" := dist_equiv 
    (at level 70, no associativity).


  (* dist_equiv is Equivalence relation *)  
  Global Instance dist_refl {A : Type} : 
    Reflexive (@dist_equiv A).
  Proof.
    unfold dist_equiv, Reflexive.
    firstorder.
  Qed.

  Global Instance dist_sym {A : Type} : 
    Symmetric (@dist_equiv A).
  Proof.
    unfold dist_equiv, Symmetric.
    intros * [Hx Hy].
    split; 
    [firstorder |
    nia].
  Qed.

  Global Instance dist_trans {A : Type} : 
    Transitive (@dist_equiv A).
  Proof.
    unfold dist_equiv, Transitive;
    try firstorder; try nia.
  Qed.

  Global Instance dist_Equiv {A : Type} : 
    Equivalence (@dist_equiv A).
  Proof.
    constructor; 
    [apply dist_refl | 
     apply dist_sym | 
     apply dist_trans].
  Qed.
  
 (* end of equivalence relation *) 


