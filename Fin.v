Require Import List Arith.
Require Import Cast Coven.

Implicit Arguments INeq [U i j].
Implicit Arguments INeq_refl [U i].
(** Why these settings aren't taken from the Import? **)

Ltac ineq_eq :=
  match goal with
    | Eql : INeq ?F ?x ?y |- _ =>
      assert (x = y);
        [ apply INeq_eq;
          [ apply eq_nat_dec (** TODO: find a good replacement for this **)
          | apply Eql
          ]
        | clear Eql
        ]
  end.
(* Why can't this be in Cast? *)


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
    (fun INEql => INeq_eq eq_nat_dec INEql).

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

Ltac specializer :=
  repeat (subst; inject; repeat ineq_eq; repeat Fin_inject);
  try discriminate;
  try reflexivity;
  try no_Fin0.


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
(* is it morally wrong to program that using tactics? *)

Ltac Fin_case y :=
  let y' := fresh y in
  let yN := fresh "N" in
  let yN' := fresh y in
  let yF := fresh "F" in
  let yFS := fresh "FS" in
    destruct (Fin_case y) as [yN y'];
      destruct y' as [yFS|yF];
        [ destruct yFS as [yN' yF]|];
        inversion yF; try solve [ specializer ].


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
  rewrite (IHn x1 y1 z1 H0); reflexivity.
Qed.

Theorem thin_wedges {n} {x y} : thin n x y <> x.
  induction n; intros; specializer.
  Fin_case x; Fin_case y; specializer; simpl.
  pose (IHn x1 y1) as X; contradict X; specializer.
  assumption.
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

(** thick **)
(***********)

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
  assumption.
Qed.

Fixpoint freshFins {n} : list (Fin n) :=
  match n with
    | O => nil
    | S n => fz :: map bump freshFins
  end.

Theorem freshFins_length {n} : length (@freshFins n) = n.
  induction n; try reflexivity.
  simpl; rewrite map_length; congruence.
Qed.

