Require Import List.
Require Import Cast.

Require Import Arith.
Require Import Omega.

Notation "'!'" := (False_rect _ _).
Notation "V <- U" := (U -> V) (no associativity, at level 0, only parsing).
Notation "[[ Foo ]]" := (exist _ Foo _).
Notation "{ ( x , y )  :  A  |  P }" := (* stolen from Program *)
  (sig (fun anonymous : A => let (x,y) := anonymous in P))
  (x ident, y ident, at level 10) : type_scope.


Definition compose {X Y Z} (f : Z <- Y) (g : Y <- X) : Z <- X
  := fun x =>  f (g x).

Infix "∘" := compose (right associativity, at level 30).

Definition Exhibit {A} (P : A -> Prop) := ({ o | P o } + ~ exists o, P o)%type.
Definition Decide (P : Prop) := {P} + {~P}.


Ltac inject := repeat
  match goal with
(*    | H : _ + ?k = _ + ?k |- _ =>  *)
    | H : S _ = S _ |- _ => injection H; clear H; intro
    | H : Some _ = Some _ |- _ => injection H; clear H; intro
    | H : _ :: _ = _ :: _ |- _ => injection H; clear H; intro; intro
    | H : ?x ++ ?y = ?x ++ ?z |- _ =>
      assert (y = z) by (apply (app_inv_head _ _ _ H)); clear H
    | H : _ <-> _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : _ * _ |- _ => destruct H
    | H : ex _ |- _ => destruct H
    | H : sig _ |- _ => destruct H
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

Ltac acyclic size eql :=
  let eql' := fresh eql in
  let ineql := fresh "ineql" in
  pose (f_equal size eql) as eql'; simpl in eql';
  match type of eql' with ?x = ?y =>
  assert (x < y) as ineql by omega
  end;
  rewrite <- eql' in ineql;
  elimtype False;
  exact (lt_irrefl _ ineql).

Ltac instantiation n H :=
  let H' := fresh H in
    match type of H with
      | forall _ : ?T, _ =>
        match goal with
          | phi : T |- _ =>
            match type of (H phi) with
              | ?U =>
                assert U as H' by exact (H phi); clear H; rename H' into H;
                  match n with
                    | O => idtac
                    | S ?n => instantiation n H
                  end
            end
        end
    end.

