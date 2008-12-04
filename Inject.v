Require Import Cast.
Require Import Fin.

Ltac prove_noConfusion :=
  intros;
    match goal with Eql : ?x = _ |- _ =>
      elim Eql; elim x; simpl; tauto end.



(*
Inductive nat : Set :=
| O : nat
| S : nat -> nat.
*)

Definition NoConfusion_nat (P : Type) (x y : nat) : Type :=
  match x, y with
    | O, O => P -> P
    | O, S y => P
    | S x, O => P
    | S x, S y => (x = y -> P) -> P
  end.

Definition noConfusion_nat (P : Type) (x y : nat) :
  x = y -> NoConfusion_nat P x y.
prove_noConfusion.
Defined.

Definition eq_nat_dec : forall x y : nat, {x = y} + {x <> y}.
decide equality.
Defined.
Hint Resolve eq_nat_dec.

Definition eq_nat_dec' : forall x y : nat, x = y \/ x <> y.
decide equality.
Defined.


Require Import Bvector.

Section Empty_Vectors.
 Variable A : Set.
 
  Theorem vector_eq_0' : forall z (v : vector A z), z = 0 -> INeq (vector A) v (Vnil A).
    induction v.
    reflexivity.
    discriminate.
  Qed.
  
  Theorem vector_eq_0 : forall v : vector A 0, v = Vnil A.
    intro; rewrite (vector_eq_0' 0 v (refl_equal _)); auto.
 Qed.

End Empty_Vectors.


(*
Inductive Fin : nat -> Set :=
| fz : forall n, Fin (S n)
| fs : forall n, Fin n -> Fin (S n).
*)

Notation FinINeq f g := (INeq Fin f g).

Definition NoConfusion_Fin (P : Type) (i : nat) (x y : Fin i) : Type :=
  match x, y with
    | fz _, fz _ => P -> P
    | fz _, fs _ _ => P
    | fs _ _, fz _=> P
    | fs x_i x, fs y_i y => (FinINeq x y -> P) -> P
  end.

Definition noConfusion_Fin (P : Type) (i : nat) (x y : Fin i) :
  x = y -> NoConfusion_Fin P i x y.
prove_noConfusion.
Defined.

Definition fz_fs_clash (P : Type) (n : nat) (f : Fin n)
  : fz = fs f -> P
  := fun Eq =>
    noConfusion_Fin P (S n) (fz) (fs f) Eq.

Definition fs_inj {n} {f f' : Fin n}
  : fs f = fs f' -> f = f'
  := fun Eq =>
    noConfusion_Fin (f = f') _ _ _ Eq (fun Eq => INeq_eq eq_nat_dec Eq).

Inductive type : Set :=
| Nat : type
| Arrow : type -> type -> type.

Definition eq_type_dec (s t : type) : { s = t } + { s <> t }.
decide equality.
Defined.

Section equand.

Variable vars : nat.

Inductive equand : type -> Set :=
| Zero : equand Nat
| Succ : equand (Arrow Nat Nat)
| VAR (V : Fin vars) : equand Nat
| APP {A B} : equand (Arrow A B) -> equand A -> equand B.

Notation equandINeq f g := (INeq equand f g).

Definition NoConfusion_equand (P : Type) (i : type) (x y : equand i) : Type :=
  match x, y with
    | Zero, Zero => P -> P
    | Succ, Succ => P -> P
    | VAR f, VAR f' => (f = f' -> P) -> P
    | APP xi xj xf xo, APP yi yj yf yo =>
      (equandINeq xf yf -> equandINeq xo yo -> P) -> P
    | _, _ => P
  end.

Definition noConfusion_equand (P : Type) (i : type) (x y : equand i) : x = y -> NoConfusion_equand P i x y.
prove_noConfusion.
Defined.

Definition Zero_One_clash (P : Type) (i : type)
  : Zero = APP Succ Zero -> P
  := fun Eq =>
    noConfusion_equand P Nat Zero (APP Succ Zero) Eq.

Definition APP_f_inj (u v : type) (F F' : equand (Arrow u v)) (O O' : equand u)
  : @APP u v F O = @APP u v F' O' -> F = F'
  := fun Eq =>
    noConfusion_equand (F = F') _ _ _ Eq
    (fun FEq OEq => INeq_eq eq_type_dec FEq).

Definition APP_o_inj (u v : type) (F F' : equand (Arrow u v)) (O O' : equand u)
  : @APP u v F O = @APP u v F' O' -> O = O'
  := fun Eq =>
    noConfusion_equand (O = O') _ _ _ Eq
    (fun FEq OEq => INeq_eq eq_type_dec OEq).

Definition eq_equand_dec : forall (t : type)(u v : equand t), {u = v} + {u <> v}.
apply INeq_dec_dec.
apply eq_type_dec.

cut (
   forall (i j : type) (I : equand i) (J : equand j),
   {equandINeq I J} + {~ equandINeq I J}
).

intros.
subst j.
apply (H i i I J).

refine (fix eq_equand_dec (i : type) (i' : type) (I : equand i)
                          (I' : equand i') {struct I} :
                          {@INeq _ equand i I i' I'} + {~ @INeq _ equand i I i' I'} := _).
refine (match I as I in equand i, I' as I' in equand i'
        return {@INeq _ _ i I i' I'} + {~ @INeq _ _ i I i' I'}
        with
          | Zero, Zero => _
          | Zero, Succ => _
          | Zero, VAR _ => _
          | Zero, APP _ _ _ _ => _
          | Succ, Zero => _
          | Succ, Succ => _
          | Succ, VAR _ => _
          | Succ, APP _ _ _ _ => _
          | VAR _, Zero => _
          | VAR _, Succ => _
          | VAR _, VAR _ => _
          | VAR _, APP _ _ _ _ => _
          | APP _ _ _ _, Zero => _
          | APP _ _ _ _, Succ => _
          | APP _ _ _ _, VAR _ => _
          | APP _ _ _ _, APP _ _ _ _ => _
        end);

try solve [ discriminate
          | left; reflexivity
          | right; intro Q; inversion Q
          | destruct B; right; intro Q; inversion Q; discriminate
          ].

destruct (eq_Fin_dec V V0); subst.
left; reflexivity.
right; intro Q; inversion Q; contradiction.

destruct (eq_type_dec B B0);
(destruct (eq_equand_dec _ _ e0 e2) as [Q|N];[inversion Q|idtac]);
(destruct (eq_equand_dec _ _ e e1) as [Q'|N'];[inversion Q'|idtac]);
  subst;

try solve [ left;
  rewrite Q; try apply eq_type_dec;
  rewrite Q'; try apply eq_type_dec;
    reflexivity ];

right; intro NQ;
  try inversion NQ;
  try inversion Q;
  try inversion Q';
  try contradiction;
  try subst;
  try pose (APP_f_inj _ _ _ _ _ _ (INeq_eq eq_type_dec NQ));
  try pose (APP_o_inj _ _ _ _ _ _ (INeq_eq eq_type_dec NQ)).

apply N'; rewrite e3; reflexivity.
apply N; rewrite e4; reflexivity.
apply N; rewrite e4; reflexivity.
Defined.

Eval compute in (eq_equand_dec _
  (APP Succ (APP Succ Zero))
  (APP Succ (APP Succ Zero))
).

End equand.

Print Assumptions eq_equand_dec.


(*
 *  = left (APP Succ (APP Succ Zero) = APP Succ (APP Succ Zero) -> False)
 *      (refl_equal (APP Succ (APP Succ Zero)))
 *  : {APP Succ (APP Succ Zero) = APP Succ (APP Succ Zero)} +
 *    {APP Succ (APP Succ Zero) <> APP Succ (APP Succ Zero)}
 *
 * Computed fully, no JMeq_eq axiom stopping reduction
 *
 *)

Require Import Coven.
Require Import Arith.
Require Import Omega.
Print le.

Lemma le_irrelevent : forall n m (H1 H2:le n m), H1=H2.
refine (fix le_irrelevent n m (H1 H2:le n m) {struct H1} : H1=H2 := _).
apply INeq_eq; auto with arith.

refine (
  match H1 as H1' in _ <= m', H2 as H2' in _ <= m''
  return m = m' ->
         m = m'' ->
         @INeq nat (le n) m H1 m' H1' ->
         @INeq nat (le n) m H2 m'' H2' ->
         @INeq nat (le n) m H1 m H2
  with
    | le_n, le_n => fun m'eq m''eq H1eq H2eq => _
    | le_n, le_S p_m p_le => fun m'eq m''eq H1eq H2eq => !
    | le_S p_m p_le, le_n => fun m'eq m''eq H1eq H2eq => !
    | le_S p_m p_le, le_S p_m' p_le' => fun m'eq m''eq H1eq H2eq => _
  end
  (refl_equal _)
  (refl_equal _)
  (INeq_refl _ _)
  (INeq_refl _ _)
); subst; subst.

rewrite (INeq_eq eq_nat_dec H1eq).
rewrite (INeq_eq eq_nat_dec H2eq).
reflexivity.

omega.

omega.

injection m''eq; intro; subst.
rewrite (INeq_eq eq_nat_dec H1eq).
rewrite (INeq_eq eq_nat_dec H2eq).
rewrite (le_irrelevent _ _ p_le p_le').
reflexivity.
Qed.

Print Assumptions le_irrelevent.
(** Closed under the global context **)

Section IM.

Variable A B : Type.

Inductive Im (f : A -> B) : B -> Type := im : forall s, Im f (f s).
