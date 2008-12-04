Require Import List.
Require Import Cast.

Notation "'!'" := (False_rect _ _).
Notation "V <- U" := (U -> V) (no associativity, at level 0, only parsing).

Definition compose {X Y Z} (f : Z <- Y) (g : Y <- X) : Z <- X
  := fun x =>  f (g x).

Infix "∘" := compose (right associativity, at level 30).

Ltac inject := repeat
  match goal with
(*    | H : _ + ?k = _ + ?k |- _ =>  *)
    | H : S _ = S _ |- _ => injection H; clear H; intro
    | H : Some _ = Some _ |- _ => injection H; clear H; intro
    | H : _ :: _ = _ :: _ |- _ => injection H; clear H; intro; intro
    | H : ?x ++ ?y = ?x ++ ?z |- _ =>
      assert (y = z) by (apply (app_inv_head _ _ _ H)); clear H
    | H : _ /\ _ |- _ => destruct H
  end.

Ltac negatory :=
  match goal with
    | H : _ <> _ |- _ => elimtype False; apply H; congruence
    | H : _ = _ -> False |- _ => elimtype False; apply H; congruence
  end.

Ltac noConf :=
  intros;
    match goal with Eql : ?x = _ |- _ =>
      elim Eql; elim x; simpl; tauto end.
