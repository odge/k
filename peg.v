Require Import List.
Require Import Arith.
Require Import Max.
Require Import Omega.
Require Import Coven.
Require Import Fin.

Set Implicit Arguments.

Reserved Notation "[  e ',' x ==> n ',' o  ]" (no associativity, at level 0).
Reserved Notation "[  e ',' x ==>+ o  ]".
Reserved Notation "e --> o" (no associativity, at level 30).

Section PEG.

Variable Symbol : Set.
Variable eq_Symbol_dec : forall (s t : Symbol), {s = t} + {s <> t}.

Definition String := list Symbol.

Inductive PE (Vn : nat) : Type :=
| epsilon : PE Vn
| any : PE Vn
| terminal : Symbol -> PE Vn
| nonterminal : Fin Vn -> PE Vn
| sequence : PE Vn -> PE Vn -> PE Vn
| choice : PE Vn -> PE Vn -> PE Vn
| star : PE Vn -> PE Vn
| negate : PE Vn -> PE Vn.

Definition PEG (Vn : nat) : Type := ((Fin Vn -> PE Vn) * PE Vn)%type.

Section Semantics.

Variable Vn : nat.
Variable G : PEG Vn.

Definition R := fst G.
Definition eS := snd G.

Inductive step : PE Vn -> String -> nat -> option String -> Prop :=
| Empty :
  [ epsilon _, nil ==> 1, Some nil ]

| Dot a xs :
  [ any _, a :: xs ==> 1, Some (a :: nil) ]

| Terminal_Success a xs :
  [ terminal _ a, a :: xs ==> 1, Some (a :: nil) ]
| Terminal_Failure a b xs : a <> b ->
  [ terminal _ a, b :: xs ==> 1, None ]

| Nonterminal A x n o :
  [ R A, x ==> n, o ] ->
  [ nonterminal A, x ==> n + 1, o ]

| Sequence_Success e1 e2 x1 x2 y n1 n2 :
  [ e1, x1 ++ x2 ++ y ==> n1, Some x1 ] ->
  [ e2, x2 ++ y ==> n2, Some x2 ] ->
  [ sequence e1 e2, x1 ++ x2 ++ y ==> n1 + n2 + 1, Some (x1 ++ x2) ]
| Sequence_Failure1 e1 e2 x n1 :
  [ e1, x ==> n1, None ] ->
  [ sequence e1 e2, x ==> n1 + 1, None ]
| Sequence_Failure2 e1 e2 x y n1 n2 :
  [ e1, x ++ y ==> n1, Some x ] ->
  [ e2, y ==> n2, None ] ->
  [ sequence e1 e2, x ++ y ==> n1 + n2 + 1, None ]

| Alternation1 e1 e2 x y n1 :
  [ e1, x ++ y ==> n1, Some x ] ->
  [ choice e1 e2, x ++ y ==> n1 + 1, Some x ]
| Alternation2 e1 e2 x n1 n2 o :
  [ e1, x ==> n1, None ] ->
  [ e2, x ==> n2, o ] ->
  [ choice e1 e2, x ==> n1 + n2 + 1, o ]

| Loop_Repeat e x1 x2 y n1 n2 :
  [ e, x1 ++ x2 ++ y ==> n1, Some x1 ] ->
  [ star e, x2 ++ y ==> n2, Some x2 ] ->
  [ star e, x1 ++ x2 ++ y ==> n1 + n2 + 1, Some (x1 ++ x2) ]
| Loop_Terminate e x n1 :
  [ e, x ==> n1, None ] ->
  [ star e, x ==> n1 + 1, Some nil ]

| Predicate_1 e x y n :
  [ e, x ++ y ==> n, Some x ] ->
  [ negate e, x ++ y ==> n + 1, None ]
| Predicate_2 e x n :
  [ e, x ==> n, None ] ->
  [ negate e, x ==> n + 1, Some nil ]

where "[  e ',' x ==> n ',' o  ]" := (step e x n o).
Notation "[  e ',' x ==>+ o  ]" := (exists n, step e x n o).

Theorem prefix e x y : [ e, x ==>+ Some y ] -> exists z, x = y ++ z.
  Lemma prefix' e x o y : o = Some y -> [ e, x ==>+ o ] -> exists z, x = y ++ z.
    intros e x o y Eql [n D]; induction D; inject; subst;
      solve [ discriminate
            | exists nil; reflexivity
            | exists x; reflexivity
            | exists xs; reflexivity
            | exists y0; rewrite app_ass; reflexivity
            | exact (IHD (refl_equal _))
            | exact (IHD2 (refl_equal _))
            ].
  Qed.
  intros e x y D; exact (@prefix' e x (Some y) y (refl_equal (Some y)) D).
Qed.

Theorem functional e x n1 o1 n2 o2 :
  [ e, x ==> n1, o1 ] -> [ e, x ==> n2, o2 ] -> n1 = n2 /\ o1 = o2.

  Lemma functional' m e x n1 o1 n2 o2 : n1 <= m -> n2 <= m ->
    [ e, x ==> n1, o1 ] -> [ e, x ==> n2, o2 ] -> n1 = n2 /\ o1 = o2.
    
    apply (well_founded_induction lt_wf (fun (m : nat) =>
      forall e x n1 o1 n2 o2, n1 <= m -> n2 <= m ->
        [ e, x ==> n1, o1 ] -> [ e, x ==> n2, o2 ] -> n1 = n2 /\ o1 = o2));
    intros m Induction.

    Ltac assumption' := match goal with H : _ |- _ => apply H end.
    Ltac step_induction Induction D1 D2 :=
      match type of D1 with [ _, _ ==> ?n1, ?o1 ] =>
      match type of D2 with [ _, _ ==> ?n2, ?o2 ] =>
        assert (n1 = n2 /\ o1 = o2);
          [ eapply Induction with (y := max n1 n2);
            [ destruct (max_dec n1 n2); omega
            | apply le_max_l
            | apply le_max_r
            | assumption'
            | assumption'
            ]
          | idtac ]
      end
      end.

    Ltac step_induction' Induction D1 D2 :=
      match type of D1 with [ _, ?x1 ==> _, _ ] =>
      match type of D2 with [ _, ?x2 ==> _, _ ] =>
        let Q := fresh "Q" in
        assert (x1 = x2) as Q;
          [ congruence || inject; subst; inject; subst; congruence
          | rewrite <- Q in D2; step_induction Induction D1 D2 ]
      end
      end.

    Ltac step_induction'' Induction :=
      repeat
      match goal with D1 : [ _, _ ==> _, _ ] |- _ =>
      match reverse goal with D2 : [ _, _ ==> _, _ ] |- _ =>
      step_induction' Induction D1 D2; clear D1 D2
      end
      end;
      repeat
      match goal with D1 : [ _, _ ==> _, _ ] |- _ =>
      match reverse goal with D2 : [ _, _ ==> _, _ ] |- _ =>
      step_induction Induction D1 D2; clear D1 D2
      end
      end.
    
    destruct e; intros x n1 o1 n2 o2 Le1 Le2 D1 D2;
      inversion D1; inversion D2; step_induction'' Induction;
        inject; solve [ discriminate
                      | negatory
                      | subst; intuition
                      | subst; inject; subst; intuition ].
  Qed.
  
  intros; eapply (@functional' (S (n1 + n2)));
    auto with arith || apply H || apply H0.
Qed.

Definition handles (text : String) := exists o, exists n, step eS text n o.
Definition matches (text : String) := exists p, exists n, step eS text n (Some p).

Inductive abstractEval : PE Vn -> option bool -> Prop :=
| Empty' :
  epsilon _ --> Some false

| Any' :
  any _ --> Some true

| Terminal1' a :
  terminal _ a --> Some true
| Terminal2' a :
  terminal _ a --> None

| Nonterminal' A o :
  R A --> o ->
  nonterminal A --> o

| Sequence1' e1 e2 :
  e1 --> Some false ->
  e2 --> Some false ->
  sequence e1 e2 --> Some false
| Sequence2' e1 e2 s :
  e1 --> Some true ->
  e2 --> Some s ->
  sequence e1 e2 --> Some true
| Sequence3' e1 e2 s :
  e1 --> Some s ->
  e2 --> Some true ->
  sequence e1 e2 --> Some true
| Sequence4' e1 e2 :
  e1 --> None ->
  sequence e1 e2 --> None
| Sequence5' e1 e2 s :
  e1 --> Some s ->
  e2 --> None ->
  sequence e1 e2 --> None

| Alternation1' e1 e2 s :
  e1 --> Some s ->
  choice e1 e2 --> Some s
| Alternation2' e1 e2 o :
  e1 --> None ->
  e2 --> o ->
  choice e1 e2 --> o

| Star1' e :
  e --> Some true ->
  star e --> Some true
| Star2' e :
  e --> None ->
  star e --> Some false

| Predicate1' e s :
  e --> Some s ->
  negate e --> None
| Predicate2' e :
  e --> None ->
  negate e --> Some false

where "e --> o" := (abstractEval e o).

Lemma abstractEval_approximates' m e x y n : n < m ->
  ([ e, x ==> n, Some nil ] -> e --> Some false) /\
  ([ e, x ==> n, Some y ] -> y <> nil -> e --> Some true) /\
  ([ e, x ==> n, None ] -> e --> None).

    apply (well_founded_induction lt_wf (fun (m : nat) =>
      forall e x y n, n < m ->
        ([ e, x ==> n, Some nil ] -> e --> Some false) /\
        ([ e, x ==> n, Some y ] -> y <> nil -> e --> Some true) /\
        ([ e, x ==> n, None ] -> e --> None)));
    intros m Induction.
  
  Ltac step_induction1 Induction Le y D :=
    match type of D with [ ?e, ?x ==> ?n', ?o ] =>
    match goal with n : nat |- _ =>
    assert (n' < n) as Q by omega;
    pose (Induction n Le e x y n' Q); inject
    end
    end.
  
  Ltac step_induction1' Induction Le y := repeat
    match goal with D : [ _, _ ==> _, _ ] |- _ =>
    step_induction1 Induction Le y D; subst; intuition; clear D
    end.
  
    destruct e; intros x y n Le;
      (split; [ intro D | split; [ intros D ne | intro D ] ]);
      try solve 
        [ constructor
        | inversion D; negatory
        | inversion D; step_induction1' Induction Le y;
          constructor; intuition
        ].

    inversion D.
    destruct (app_eq_nil _ _ H1).
    subst x1; subst x2.
    clear H1.
    simpl in H2.
    subst y0.
    simpl in *.
info    step_induction1' Induction Le y.
    constructor; intuition.
    clear H2; clear H6.
    clear D.
    clear Q.

assert (n2 + 1 < m) as Q' by complete omega.
assert (n2 < n2 + 1) as QQ by omega.
pose (Induction (n2 + 1) Q' e2 x y n2 QQ).
destruct a.
apply H0.
assumption.


Focus 8.
inversion D.
assert (n0 < n) as Q by complete omega;
  pose (Induction n Le e (x0 ++ y0) x0 n0 Q); 
    destruct a; destruct H4; subst.
destruct x0; econstructor.
apply H3.
subst; simpl in *; subst.
assumption.
subst; simpl in *; subst.
apply H4.
assumption.
discriminate.



End Semantics.




End PEG.

Section anbncn.

Definition a := 1.
Definition b := 2.
Definition c := 3.

(* A <- (a A b)?
 * B <- (b B c)?
 * D <- &(A !b) a* B !.
 *
 * =
 *
 * A <- a A b / epsilon
 * B <- b B c / epsilon
 * D <- !(!(A !b)) a* B !.
 *
 * =
 *)

Definition anbncn : PEG nat 3 :=
  (fun i =>
    match i with
      | fz _ =>
        (choice
          (sequence (terminal _ a)
            (sequence (nonterminal _ fz)
              (terminal _ b)))
          (epsilon _ _))
      | fs _ (fz _) =>
        (choice
          (sequence (terminal _ b)
            (sequence (nonterminal _ (fs fz))
              (terminal _ c)))
          (epsilon _ _))
      | fs _ (fs _ _) =>
        (sequence (negate (negate (sequence
                                    (nonterminal _ fz)
                                    (negate (terminal _ b)))))
          (sequence (star (terminal _ a))
            (sequence (nonterminal _ (fs fz))
              (negate (any _ _)))))
    end,
    nonterminal _ (fs (fs (fz)))).

Theorem test1 : matches anbncn (a::a::b::b::c::c::nil).
econstructor.
econstructor.

apply Nonterminal.
simpl R.
assert (a :: a :: b :: b :: c :: c :: nil = nil ++ (a :: a :: b :: b :: nil) ++ (c :: c :: nil)) as Q by reflexivity; rewrite Q at 1; clear Q.
instantiate (2 := _ + _ + 1).
apply Sequence_Success.
simpl.
constructor.
instantiate (1 := _ + 1).
assert (a :: a :: b :: b :: c :: c :: nil = (a :: a :: b :: b :: nil) ++ (c :: c :: nil)) as Q by reflexivity; rewrite Q at 1; clear Q.
apply Predicate_1.
simpl.
assert (a :: a :: b :: b :: c :: c :: nil = (a :: a :: b :: b :: nil) ++ nil ++ (c :: c :: nil)) as Q by reflexivity; rewrite Q at 1; clear Q.
instantiate (1 := _ + _ + 1).
apply Sequence_Success.
constructor.
simpl R.

Focus 2.
constructor.
constructor.
discriminate.

Focus 2.




End anbncn.

| Predicate_1 e x y n :
  [ e, x ++ y ==> n, Some x ] ->
  [ negate e, x ++ y ==> n + 1, None ]
