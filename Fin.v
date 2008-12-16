Require Import List ListPlus Arith.
Require Import Cast Coven.

Implicit Arguments INeq [U i j].
Implicit Arguments INeq_refl [U i].
(** Why these settings aren't taken from the Import? **)

(*
Ltac ineq_eq :=
  match goal with
    | Eql : INeq ?F ?x ?y |- _ =>
      (apply (yo_INeq_eq eq_nat_dec Eql); clear Eql; intro Eql)||
      (apply (yo_INeq_eq_type eq_nat_dec Eql); clear Eql; intro Eql)
  end.
*)
Ltac ineq_eq :=
  match goal with
    | Eql : INeq ?F ?x ?y |- _ =>
      assert (x = y);
        [ apply INeq_eq;
          [ apply eq_nat_dec (** TODO: find a good replacement for this (not 'decide equality') **)
          | apply Eql
          ]
        | clear Eql
        ]
  end.
(* Why can't this be in Cast? *)


Ltac ineq_tyeq :=
  match goal with Q : INeq _ _ _ |- _ => pose (INeq_tyeq Q) end.


Inductive Fin : nat -> Set :=
| fz {n} : Fin (S n)
| fs {n} : Fin n -> Fin (S n).

Definition no_Fin0 {P:Prop} : Fin 0 -> P :=
  fun f =>
    match f in Fin zero return
      match zero with
        | O => P
        | S _ => True
      end
      with
      | fz _ => I
      | fs _ _ => I
    end.

Definition NoConfusion_Fin (P : Type) (i : nat) (x y : Fin i) : Type :=
  match x, y with
    | fz _, fz _ => P -> P
    | fz _, fs _ _ => P
    | fs _ _, fz _=> P
    | fs x_i x, fs y_i y => (INeq Fin x y -> P) -> P
  end.
Theorem noConfusion_Fin (P : Type) (i : nat) (x y : Fin i) :
  x = y -> NoConfusion_Fin P i x y.
noConf.
Defined.

Definition discriminate_fz_fs {n} {f : Fin n} : fz <> fs f :=
  noConfusion_Fin False (S n) fz (fs f).
Definition discriminate_fs_fz {n} {f : Fin n} : fs f <> fz :=
  noConfusion_Fin False (S n) (fs f) fz.
Definition injection_fs_fs {n} {f f' : Fin n} : fs f = fs f' -> f = f' :=
  fun Eql =>
    noConfusion_Fin (f = f') (S n) (fs f) (fs f') Eql
    (fun Eql => INeq_eq eq_nat_dec Eql).

Ltac Fin_inject :=
  match goal with
    | Eql : fs ?u = fs ?v |- _ =>
      assert (u = v);
        [ exact (injection_fs_fs Eql)
        | clear Eql
        ]
  end.

Ltac no_Fin0 :=
  match goal with pink_elephant : Fin 0 |- _ => exact (no_Fin0 pink_elephant) end.

Ltac cleanse := repeat
  match goal with Evil : existT _ _ _ = existT _ _ _ |- _ => clear Evil end.

Ltac specializer :=
  do 2 ( (* this specializer is careful to use Fin_inject
            only when it must, so that reductions can happen in functions *)
  repeat (cleanse; subst; inject);
  try discriminate;
  try reflexivity;
  try congruence;
  try no_Fin0;
  repeat ineq_eq;
  try discriminate;
  try reflexivity;
  try congruence;
  try no_Fin0;
  repeat Fin_inject;
  try discriminate;
  try reflexivity;
  try congruence;
  try no_Fin0).

Definition eq_Fin_dec {n} (u v : Fin n) : {u = v} + {u <> v}.
apply INeq_dec_dec. exact eq_nat_dec.
refine (fix eq_Fin_dec i j (u : Fin i) (v : Fin j) {struct u} :
  i = j -> {INeq Fin u v} + {~ INeq Fin u v} := _).
refine (match u as u' in Fin i',
              v as v' in Fin j'
        return INeq Fin u u' ->
               i = i' ->
               INeq Fin v v' ->
               j = j' ->
               i = j ->
               {INeq Fin u' v'} + {~ INeq Fin u' v'}
        with fz _, fz _ => fun e1 e2 e3 e4 e5 => left _ _
           | fz _, fs _ _ => fun e1 e2 e3 e4 e5 => right _ _
           | fs _ _, fz _ => fun e1 e2 e3 e4 e5 => right _ _
           | fs i u, fs j v => fun e1 e2 e3 e4 e5 =>
             match eq_Fin_dec i j u v _ with
               | left Eql => left _ _
               | right notEql => right _ _
             end
        end
        (INeq_refl Fin u)
        (refl_equal i)
        (INeq_refl Fin v)
        (refl_equal j));
try contradict notEql;
specializer;
try (intro; ineq_eq; discriminate).
Defined.

Definition Fin_case {n} (f : Fin n) :
  { n' : nat & ( { f' : Fin n' | INeq Fin f (fs f') } + { INeq Fin f (@fz n') } ) }.
intros n f; destruct f.
exists n; right; reflexivity.
exists n; left; exists f; reflexivity.
Defined.

Ltac Fin_case y :=
  let y' := fresh y in
  let yN := fresh "N" in
  let yN' := fresh y in
  let yF := fresh "F" in
  let yFS := fresh "FS" in
    destruct (Fin_case y) as [yN y'];
      destruct y' as [yFS|yF];
        [ destruct yFS as [yN' yF]|];
        inversion yF; cleanse; try solve [ specializer ].


(*
 * thin : Fin Sn -> Fin n -> Fin Sn
 * thin_n   fz     y     := fs y
 * thin_Sn (fs x)  fz    := fz
 * thin_Sn (fs x) (fs y) := fs (thin_n x y)
 *)

Definition thin n (x : Fin (S n)) (y : Fin n) : Fin (S n).
refine (fix thin n (x : Fin (S n)) (y : Fin n) : Fin (S n) := _).
refine (match n as n',
              x as x' in Fin Sn',
              y as y' in Fin n''
        return n = n' ->
               S n = Sn' ->
               INeq Fin x x' ->
               n = n'' ->
               INeq Fin y y' ->
               Fin (S n)
        with
          | _, fz _, y => fun e1 e2 e3 e4 e5 => fs y
          | _, fs _ x, fz _ => fun e1 e2 e3 e4 e5 => fz
          | O, fs _ x, fs _ y => fun e1 e2 e3 e4 e5 => !
          | S n, fs _ x, fs _ y => fun e1 e2 e3 e4 e5 =>
            let x' := eq_rect _ Fin x _ _ in
            let y' := eq_rect _ Fin y _ _ in
              eq_rect _ Fin (fs (thin n x' y')) _ _
        end
        (refl_equal n)
        (refl_equal (S n))
        (INeq_refl Fin x)
        (refl_equal n)
        (INeq_refl Fin y));
specializer.
Defined.

Theorem thin_injective {n} {x y z} : thin n x y = thin n x z -> y = z.
  induction n; intros; specializer.
  Fin_case x; [ Fin_case y; Fin_case z |]; specializer; simpl in *; specializer.
  rewrite (IHn _ _ _ H0).
  reflexivity.
Qed.

Theorem thin_wedges {n} {x y} : thin n x y <> x.
  induction n; intros; specializer.
  Fin_case x; Fin_case y; specializer; simpl.
  pose (IHn x1 y1) as X; contradict X; specializer.
Qed.

Theorem thin_inverse {n} {x y} : x <> y -> exists y', thin n x y' = y.
  induction n; intros; specializer.
  Fin_case x; Fin_case y; specializer; try negatory.
  Fin_case x; Fin_case y; specializer; try negatory;
    try (exists fz; reflexivity);
    try (exists y1; reflexivity).
  assert (x1 <> y1) as X by (intro X; contradict H; specializer).
  destruct (IHn x1 y1 X) as [y' Eql]; exists (fs y').
  simpl; congruence.
Qed.

(*
 * thick : Fin Sn -> Fin Sn > option (Fin n)
 * thick_n fz fz := None
 * thick_n fz (fs y) := Some y
 * thick_Sn (fs x) fz := Some fz
 * thick_Sn (fs x) (fs y) := fmap fs (thick_n x y)
 *)

Definition thick n : Fin (S n) -> Fin (S n) -> option (Fin n).
refine (fix thick n (x y : Fin (S n)) {struct n} : option (Fin n) := _).
refine (match n as n',
              x as x' in Fin Sn,
              y as y' in Fin Sn
        return n = n' ->
               S n = Sn ->
               INeq Fin x x' ->
               S n = Sn ->
               INeq Fin y y' ->
               option (Fin n)
        with
          | O, fz _, fz _ => fun e1 e2 e3 e4 e5 =>
            None
          | S _, fz _, fz _ => fun e1 e2 e3 e4 e5 =>
            None
          | O, fz _, fs _ y => fun e1 e2 e3 e4 e5 => !
          | S _, fz _, fs _ y => fun e1 e2 e3 e4 e5 =>
            Some (eq_rect _ Fin y _ _)
          | O, fs _ _, fz _ => fun e1 e2 e3 e4 e5 => !
          | O, fs _ _, fs _ _ => fun e1 e2 e3 e4 e5 => !
          | S n, fs _ x, fz _ => fun e1 e2 e3 e4 e5 =>
            Some (eq_rect _ Fin fz _ _)
          | S n, fs _ x, fs _ y => fun e1 e2 e3 e4 e5 =>
            match thick n (eq_rect _ Fin x _ _) (eq_rect _ Fin y _ _) with
              | None => None
              | Some f => Some (eq_rect _ Fin (fs f) _ _)
            end
        end
        (refl_equal n)
        (refl_equal (S n))
        (INeq_refl Fin x)
        (refl_equal (S n))
        (INeq_refl Fin y));
specializer.
ineq_tyeq; specializer.
ineq_tyeq; specializer.
Defined.

Lemma one_Fin1 (f : Fin 1) : f = fz.
  intros; Fin_case f.
Qed.

Theorem thick_inverse n x y r : thick n x y = r ->
  (y = x /\ r = None) \/ (exists y', y = thin n x y' /\ r = Some y').
  
  induction n.
  
  intros x y; rewrite (one_Fin1 x); rewrite (one_Fin1 y); clear x y; simpl.
  destruct r; specializer; left; split; reflexivity.

  intros x y; Fin_case x; Fin_case y; specializer;
    intros r rEq; rewrite <- rEq; clear r rEq.
  
  destruct (IHn x1 y1 (thick n x1 y1) (refl_equal _)); inject.
    left; simpl; subst; split; [ reflexivity | rewrite H1; reflexivity ].
    right; exists (fs x); simpl; split; [ rewrite H0 | rewrite H1 ]; reflexivity.
  
  destruct (IHn x1 fz (thick n x1 fz) (refl_equal _)); right; specializer.
  exists fz.
  split; reflexivity.
  
  exists fz; split; reflexivity.
  
  right; exists y1; split; reflexivity.
  
  left; split; reflexivity.
Qed.

Definition thick_inverse' n x y r : thick n x y = r ->
  {y' | y = thin n x y' /\ r = Some y'} + {y = x /\ r = None}.
  induction n.
  
  intros x y; rewrite (one_Fin1 x); rewrite (one_Fin1 y); clear x y; simpl.
  destruct r; specializer; right; split; reflexivity.

  intros x y; Fin_case x; Fin_case y; specializer;
    intros r rEq; rewrite <- rEq; clear r rEq.
  
  destruct (IHn x1 y1 (thick n x1 y1) (refl_equal _)); inject.
    left; exists (fs x); simpl; split; [ rewrite H0 | rewrite H1 ]; reflexivity.
    right; simpl; subst; split; [ reflexivity | rewrite H1; reflexivity ].
  
  destruct (IHn x1 fz (thick n x1 fz) (refl_equal _)); left; specializer.
  exists fz.
  split; reflexivity.
  
  exists fz; split; reflexivity.
  
  left; exists y1; split; reflexivity.
  
  right; split; reflexivity.
Defined.

Fixpoint bump {n} (f : Fin n) : Fin (S n) :=
  match f with
    | fz _ => fz
    | fs _ f => fs (bump f)
  end.

Lemma bump_injection {n} {u v : Fin n} : bump u = bump v -> u = v.
  induction n; intros; Fin_case u; Fin_case v; specializer.
  simpl in H; specializer.
  rewrite (IHn _ _ H0); reflexivity.
Qed.

Fixpoint scum {n} : Fin (S n) :=
  match n with
    | O => fz
    | S n => fs scum
  end.

Lemma bump_isn't_scum {n} {f : Fin n} : bump f <> scum.
  induction f; try discriminate.
  simpl; contradict IHf; specializer.
Qed.

Lemma bump_AllDifferent {n} (l : list (Fin n)) : AllDifferent l -> AllDifferent (map bump l).
induction l.
simpl; constructor.
simpl.
intro H; constructor.
apply IHl; inversion H; auto.
inversion H.
destruct (in_map_iff (@bump n) l (bump a)).
intro.
pose (H4 H6).
destruct e.
inject.
assert (x0 = a).
apply bump_injection.
assumption.
apply H3; subst; apply H8.
Qed.


Definition thicken' n (wedge e : Fin (S n)) : wedge <> e -> Fin n.
intros; pose (thick _ wedge e).
destruct (thick_inverse' _ wedge e _ (refl_equal _)).
destruct s.
exact x.
absurd (wedge = e); inject; auto.
Defined.

Lemma thick_and_thin n o e ne : e = @thin n o (@thicken' n o e ne).
  intros.
  set (k := thick_inverse _ o e _ (refl_equal (thick _ o e))).
  destruct k.
  elimtype False; inject; absurd (e = o); auto.
  destruct H.
  destruct H.
  unfold thicken'.
  destruct (thick_inverse' n o e (thick n o e) (refl_equal (thick n o e)));
    inject.
  congruence.
  absurd (e = o); inject; auto.
Qed.

Lemma thicken_In_inj n o a x H H' :
  In (@thicken' n o a H)
     (map' _ _ (fun e => o <> e) (@thicken' n o) x H') ->
  In a x.
  intros; induction x.
  inversion H0.
  simpl in H0.
  destruct H0.
  left.
  rewrite (@thick_and_thin _ o a H).
  rewrite (@thick_and_thin _ o a0 (H' a0 (or_introl (In a0 x) (refl_equal a0)))).
  rewrite H0.
  reflexivity.
  right.
  eapply IHx.
  apply H0.
Qed.

Lemma saturation n : forall x : list (Fin n),
  AllDifferent x -> length x = n -> forall f, In f x.
  intros; induction n.
  apply (no_Fin0 f).
  destruct x.
  inversion H0.
  destruct (eq_Fin_dec f f0).
  left; congruence.
  right.
  injection H0; clear H0; intro H0.
  inversion H.
  clear H1 H2 x0 xs.
  
  assert (forall e, In e x -> f0 <> e).
  intros; contradict H4; congruence.
  pose (map' _ _ _ (@thicken' _ f0) x H1).
  
  Lemma AllDifferent_map'_thicken' n o x (H : (forall e, In e x -> o <> e)) :
    AllDifferent x ->
    (AllDifferent
      (map' _ _
        (fun e => o <> e)
        (@thicken' n o) x
        H)).
    intros; induction x.
    apply nil'.
    simpl; apply cons'; inversion H0.
    apply IHx; assumption.
    contradict H4.
    eapply thicken_In_inj.
    apply H4.
  Qed.
  pose (AllDifferent_map'_thicken' _ _ _ H1 H3).
  
  assert (length l = n).
  rewrite <- H0.
  rewrite (map'_length _ _ _ (@thicken' n f0) x H1).
  reflexivity.
  
  pose (IHn _ a H2).
  pose (i (@thicken' _ f f0 n0)).
  assert (f0 <> f).
  auto.
  pose (thicken_In_inj _ f0 f x H5 H1).
  apply i1.
  apply i.
Qed.



Theorem pigeonhole_principle m : ~ Cardinality (S m) (Fin m).
  unfold Cardinality.
  intros; intro.
  destruct H; destruct H.
  destruct x.
  inversion H.
  case (In_dec (@eq_Fin_dec _) f x); inversion H0.
  contradiction.
  injection H; intro H'.
  pose (saturation _ x H3 H' f).
  contradiction.
Qed.


Fixpoint freshFins {n} : list (Fin n) :=
  match n with
    | O => nil
    | S n => scum :: map bump freshFins
  end.

Theorem freshFins_length {n} : length (@freshFins n) = n.
  induction n; try reflexivity.
  simpl; rewrite map_length; congruence.
Qed.

Theorem freshFins_AllDifferent {n} : AllDifferent (@freshFins n).
  induction n.
  constructor.
  simpl.
  
  constructor.
  apply AllDifferent_injection.
  intros; apply bump_injection.
  assumption.
  assumption.
  
  Lemma aeouoeu {n} (x : list (Fin n)) : AllDifferent x -> ~ In scum (map bump x).
    induction x.
    intuition.
    simpl; intros.
    inversion H.
    pose (IHx H2).
    intro.
    destruct H4.
    absurd (bump a = scum); auto.
    apply bump_isn't_scum.
    contradiction.
  Qed.
  apply aeouoeu.
  assumption.
Qed.
  
Theorem everyFinFresh {n} {f : Fin n} : In f freshFins.
intro n; exact (saturation n freshFins freshFins_AllDifferent freshFins_length).
Qed.

Theorem Cardinality_n_Fin_n n : Cardinality n (Fin n).
  induction n.
  
  exists nil; split; [ reflexivity | apply nil'].
  
  destruct IHn.
  destruct H.
  exists (scum :: map (@bump _) x); split.
  
  simpl.
  rewrite map_length.
  congruence.
  
  apply cons'.
  apply AllDifferent_injection.
  intros; apply bump_injection.
  assumption.
  assumption.
  clear H.
  induction x.
  auto.
  intro.
  inversion H0.
  pose (IHx H3).
  simpl in H.
  destruct H.
  absurd (bump a = scum); auto.
  apply bump_isn't_scum.
  contradiction.
Qed.

Theorem not_gt_Cardinality_n_Fin_m n m : n > m -> ~Cardinality n (Fin m).
  intros.
  
  Lemma lt_diff n m : n > m -> exists d, n = S d + m.
    unfold gt; unfold lt.
    intros n m H; induction H.
    exists 0; reflexivity.
    destruct IHle.
    exists (S x).
    rewrite H0.
    reflexivity.
  Qed.
  destruct (lt_diff n m); auto.
  rewrite H0; clear H0 H n.
  induction x.
  
  exact (pigeonhole_principle m).
  
  contradict IHx.
  destruct IHx.
  destruct H.
  inversion H0.
  rewrite <- H1 in H; inversion H.
  exists xs; split; auto.
  rewrite <- H3 in H; injection H.
  auto.
Qed.
(* Another triumph of the pigeonhole principle *)

Require Import Arith.
Theorem fin_different n m : n <> m -> Fin n <> Fin m.
  intros n m ne; intro H.
  destruct (not_eq _ _ ne);
    [ pose (Cardinality_n_Fin_n m) as p; rewrite <- H in p |
      pose (Cardinality_n_Fin_n n) as p; rewrite    H in p ];
    eapply not_gt_Cardinality_n_Fin_m;
      try apply p; auto with arith.
Qed.

Theorem fin_injective n m : Fin n = Fin m -> n = m.
  intros; destruct (eq_nat_dec n m).
  assumption.
  pose (fin_different _ _ n0); contradiction.
Qed.


