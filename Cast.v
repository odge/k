Require Import Eqdep_dec_defined.

Section Cast.
  
  Variable U : Type.
  Variable F : U -> Type.
  
  Variable eq_dec : forall x y:U, {x = y} + {x <> y}.
  
  Definition eq_decide : forall x y:U, x = y \/ x <> y.
  intros x y; destruct (eq_dec x y); [ left | right ]; assumption.
  Defined.
  
  Definition cast (i j : U) : F j -> option (F i) :=
    fun J =>
      match eq_dec j i with
        | left Eql => match Eql in _ = i return option (F i) with
                        | refl_equal => Some J
                      end
        | right _ => None
      end.
  
  Theorem cast_reflexivity (i : U) (I : F i) : cast i i I = Some I.
    unfold cast; intro i; destruct (eq_dec i i);
      [ subst | absurd (i = i); tauto ].
    rewrite (eq_proofs_unicity eq_decide e (refl_equal i)).
    reflexivity.
  Defined.
  
  Definition cast_injective (i : U) (I I' : F i) :
    cast i i I = cast i i I' -> I = I'.
  intros i I I'; repeat rewrite cast_reflexivity.
  intro SomeEq; injection SomeEq; tauto.
  Defined.
  
  Set Implicit Arguments.

  (** Heq is pretty useless since Heq n n x x doesn't reduce to x = x
      without applying unicity **)

  Definition Heq (i j : U) : F i -> F j -> Prop :=
    match eq_dec j i with
      | left Eql => match Eql in _ = i return F i -> F j -> Prop with
                      | refl_equal => fun I J => I = J
                    end
      | right _ => fun _ _ => False
    end.
  
  Inductive INeq (i : U)(I : F i) : forall (j : U)(J : F j), Prop :=
  | INeq_refl : INeq I I.
  
  Hint Resolve INeq_refl.
  
  Lemma eq_INeq (i : U)(I I' : F i) : I = I' -> INeq I I'.
  intros i I I' Eq; elim Eq; reflexivity.
  Defined.
  
  Definition INeq_eq (i : U)(I I' : F i) : INeq I I' -> I = I'.
  intros i I I' inEq; apply cast_injective.
  change ((fun i' I' => cast i i I = cast i i' I') i I').
  elim inEq; reflexivity.
  Defined.
  
  Lemma INeq_ind_r :
    forall (i:U) (I J:F i) (P:F i -> Prop), P J -> INeq I J -> P I.
    intros i I J P H Eql; rewrite (INeq_eq Eql); assumption.
  Defined.
  
  Lemma INeq_rec_r :
    forall (i:U) (I J:F i) (P:F i -> Set), P J -> INeq I J -> P I.
    intros i I J P H Eql; rewrite (INeq_eq Eql); assumption.
  Defined.
  
  Lemma INeq_rect_r :
    forall (i:U) (I J:F i) (P:F i -> Type), P J -> INeq I J -> P I.
    intros i I J P H Eql; rewrite (INeq_eq Eql); assumption.
  Defined.
  
  Definition INeq_dec_dec :
    (forall (i:U)(j:U)(I:F i)(J:F j), i = j -> {INeq I J} + {~INeq I J}) ->
    (forall (i:U)(I J:F i), {I = J} + {I <> J}).
  intros ineq_dec i I J.
  destruct (ineq_dec i i I J); [ reflexivity | left | right ].
  apply INeq_eq; assumption.
  contradict n; subst; reflexivity.
  Defined.
  
End Cast.

Implicit Arguments INeq [U i j].
Implicit Arguments INeq [U i].
