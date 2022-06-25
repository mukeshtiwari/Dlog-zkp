Require Import Vector 
  Fin.

Import VectorNotations.
Section Vect.

    Context 
      {A : Type}.

    Lemma vector_head : 
      forall {n : nat} (v : Vector.t A (S n)), {h & {t | v = h :: t}}.
    Proof.
      intros n v.
      refine 
      (match v as v' in Vector.t _ (S n') return 
        forall (pf : n' = n),
          v = eq_rect n' (fun w => Vector.t A (S w))
                v' n pf -> {h : A & {t | v' = h :: t}}
      with
      | cons _ h _ t => fun pf Hv => _ 
      end eq_refl eq_refl).
      exists h, t.
      exact eq_refl.
    Defined.

End Vect. 