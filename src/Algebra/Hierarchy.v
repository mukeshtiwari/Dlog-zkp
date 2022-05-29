Require Import 
  Coq.Classes.Morphisms.

Local Close Scope nat_scope. 
Local Close Scope type_scope.
Local Close Scope core_scope.

(* This code is inspired/taken from Fiat-Crypto and extended with 
  Vector Space to avoid the scalor_mult type class. Moreover, 
  some improvements have been added (pull request already 
  sent: https://github.com/mit-plv/fiat-crypto/pull/1012 
*)

Section Algebra.

    (* A Set S with one operation *)
  Section OneTypeOneOp.

    Context 
      {T : Type} 
      {eq : T -> T -> Prop}
      {op : T -> T -> T} 
      {id : T}.

    Local Infix "=" := eq : type_scope. 
    Local Notation "a <> b" := (not (a = b)) : type_scope.


  
    Class is_associative :=
      associative : forall x y z, 
        op x (op y z) = op (op x y) z.
  
    Class is_left_identity := 
      left_identity : forall x, op id x = x.
    
    Class is_right_identity :=
      right_identity : forall x, op x id = x.
    
    Class monoid :=
    {
      monoid_is_associative : is_associative;
      monoid_is_left_idenity : is_left_identity;
      monoid_is_right_identity : is_right_identity;
      monoid_op_Proper: Proper (eq ==> eq ==> eq) op;
      monoid_Equivalence : Equivalence eq
    }.


    Global Existing Instance monoid_is_associative.
    Global Existing Instance monoid_is_left_idenity.
    Global Existing Instance monoid_is_right_identity.
    Global Existing Instance monoid_op_Proper.
    Global Existing Instance monoid_Equivalence.

    Context {inv : T -> T}.
    
    Class is_left_inverse :=
      left_inverse : forall x, op (inv x) x = id.
    
    Class is_right_inverse :=
      right_inverse : forall x, op x (inv x) = id. 
    
    Class group :=
    {
      group_monoid : monoid;
      group_is_left_inverse : is_left_inverse;
      group_is_right_inverse : is_right_inverse;
      group_inv_Proper : Proper (eq ==> eq) inv
    }.

    Global Existing Instance group_monoid.
    Global Existing Instance group_is_left_inverse.
    Global Existing Instance group_is_right_inverse.
    Global Existing Instance group_inv_Proper.

    Class is_commutative :=
      commutative : forall x y, op x y = op y x.

    (* commutative group is declared as record in fiat-crypto *)
    Class commutative_group :=
    {
      commutative_group_group : group;
      commutative_group_is_commutative : is_commutative
    }.

    Global Existing Instance commutative_group_group.
    Global Existing Instance commutative_group_is_commutative.

  End OneTypeOneOp.
  
  Section OneTypeTwoOp.

    Context 
      {T : Type} 
      {eq : T -> T -> Prop} 
      {zero one : T} 
      {opp : T -> T} 
      {add : T -> T -> T}
      {sub : T -> T -> T} 
      {mul : T -> T -> T}.


    Local Infix "=" := eq : type_scope. 
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := zero.
    Local Notation "1" := one.
    Local Notation "- x" := (opp x).
    Local Infix "+" := add.
    Local Infix "-" := sub. 
    Local Infix "*" := mul.

    Class is_left_distributive := 
      left_distributive : forall x y z, 
        x * (y + z) = x * y + x * z. 
    
    Class is_right_distributive :=
      right_distributive : forall x y z, (y + z) * x = y * x + z * x.

    Class ring :=
    {
      ring_commutative_group_add : 
        commutative_group (eq := eq) (op := add) (id := zero) (inv := opp);
      ring_monoid_mul : monoid (eq := eq) (op := mul) (id := one);
      ring_is_left_distributive : is_left_distributive;
      ring_is_right_distributive : is_right_distributive;
      ring_sub_definition : forall x y, x - y = x + opp y;
      (* ring_mul_Proper : Proper (eq ==> eq ==> eq) mul; *)
      ring_sub_Proper : Proper (eq ==> eq ==> eq) sub

    }.

    Global Existing Instance ring_commutative_group_add.
    Global Existing Instance ring_monoid_mul.
    Global Existing Instance ring_is_left_distributive.
    Global Existing Instance ring_is_right_distributive.
    (* Global Existing Instance ring_mul_Proper. *)
    Global Existing Instance ring_sub_Proper.

    

  
