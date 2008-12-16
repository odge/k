Require Import List.

Set Implicit Arguments.

Section ListPlus.

Variables A : Set.
Variables P : A -> Prop.
Variables P_dec : forall a : A, {P a} + {~P a}.

Fixpoint filter_dec (l:list A) : list A := 
  match l with 
    | nil => nil
    | x :: l => if P_dec x then x::(filter_dec l) else filter_dec l
  end.

Lemma filter_dec_In : forall x l, In x (filter_dec l) <-> In x l /\ P x.
Proof.
  induction l; simpl.
  intuition.
  intros.
  case_eq (P_dec a); intros; simpl; intuition congruence.
Qed.

Lemma filter_subset : forall x l, In x (filter_dec l) -> In x l.
Proof.
  induction l; simpl.
  intuition.
  case_eq (P_dec a); intros; simpl; intuition.
  simpl in H0; destruct H0; auto.
Qed.


Definition sublist (l s : list A) := forall x, In x s -> In x l.

Lemma sublist_cons X Y (o : A) :
  sublist X (o :: Y) -> sublist X Y.
unfold sublist; simpl; intros X Y o H x in_Y.
apply H; right; assumption.
Qed.


Definition sublist_satisfies (l : list A) (P : list A -> Prop) :=
  exists s, sublist l s /\ P s.



End ListPlus.

Unset Implicit Arguments.

Inductive AllDifferent A : list A -> Prop :=
| nil'  :
  AllDifferent A nil
| cons' : forall x xs,
  AllDifferent A xs -> ~In x xs -> AllDifferent A (x :: xs).
Implicit Arguments AllDifferent [A].

Lemma AllDifferent_injection A B (f : A -> B) x : (forall u v, f u = f v -> u = v) -> AllDifferent x -> AllDifferent (map f x).
  intros; induction x; simpl.
  apply nil'.
  apply cons'; inversion H0.
  apply IHx; assumption.
  contradict H4.
  destruct (in_map_iff f x (f a)).
  destruct (H5 H4).
  destruct H7.
  rewrite <- (H _ _ H7).
  assumption.
Qed.


Lemma In_P_reduce X (P : X -> Prop) o xs :
  (forall x : X, In x (o :: xs) -> P x) ->
   forall x : X, In x xs -> P x.
  intros.
  apply H.
  right.
  assumption.
Qed.

Definition map' X Y (P : X -> Prop) (f : forall x : X, P x -> Y) :
  forall xs : list X, (forall x, In x xs -> P x) -> list Y.
fix 5.
intros X Y P f xs P'.
destruct xs.
exact nil.
refine (f x (P' _ _) :: map' _ _ _ f xs (In_P_reduce _ _ _ _ P')).
left; reflexivity.
Defined.

Theorem map'_length X Y P f xs O : length xs = length (map' X Y P f xs O).
  intros; induction xs.
  reflexivity.
  simpl; rewrite (IHxs (In_P_reduce _ _ _ _ O)).
  reflexivity.
Qed.

Definition Cardinality : nat -> Set -> Prop :=
  fun n A => exists l : list A, length l = n /\ AllDifferent l.

