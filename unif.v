(* Conors Structural Recursive Unification in Coq *)

Require Import List.
Require Import Coven.
Require Import Fin.

Definition empty P : Fin 0 -> P.
intros P f; inversion f.
Defined.

Inductive Term (n : nat) : Set :=
| iota : Fin n -> Term n
| leaf : Term n
| fork : Term n -> Term n -> Term n.

Definition funcL (m n : nat) (r : Fin m -> Fin n) : Fin m -> Term n :=
fun f => iota _ (r f).
Fixpoint funcR (m n : nat) (f : Fin m -> Term n) (o : Term m) {struct o} : Term n :=
match o with
| iota i => f i
| leaf => leaf _
| fork s t => fork _ (funcR _ _ f s) (funcR _ _ f t)
end.

Definition eqSubst (m n : nat) (f g : Fin m -> Term n) := forall i, f i = g i.
Definition compSubst (l m n : nat)
(f : Fin m -> Term n)
(g : Fin l -> Term m)
: Fin l -> Term n :=
fun x => (funcR _ _ f) (g x).

Print eq_rect.

Theorem eq_pred : forall m n, S m = S n -> m = n.
intros m n Eq; injection Eq; tauto.
Defined.

Fixpoint thin (n : nat) (x : Fin (S n)) (y : Fin n) {struct y} : Fin (S n) :=
 match x in Fin Sn, y in Fin n return Sn = S n -> Fin (S n) with
 | fz _, y => fun _ => fs y
 | fs _ x, fz _ => fun _ => fz
 | fs n' x, fs n y => fun eq : S n' = S (S n) =>
 let x' := eq_rect _ Fin x (S n) (eq_pred _ _ eq) in
 fs (thin n x' y)
 end (refl_equal (S n)).

Fixpoint optionMap A B (f : A -> B) (o : option A) : option B :=
 match o with
 | None => None
 | Some i => Some (f i)
 end.

Print trans_eq.

Fixpoint thick (n : nat) (x y : Fin (S n)) {struct x} : option (Fin n) :=
 match x in Fin Sn'x, y in Fin Sn'y return Sn'x = Sn'y -> option (Fin
(pred Sn'y)) with
 | fz _, fz _ => fun _ => None
 | fz _, fs _ y => fun _ => Some y
 | fs n'x x, fz n'y => match n'x as n'x' return Fin n'x' -> S n'x' =
S n'y -> option (Fin n'y) with
   | O => fun x => empty _ x
   | S n'x' => fun _ (eq : S (S n'x') = S n'y) =>
   let fz' := eq_rect _ Fin (fz) _ (eq_pred _ _ eq) in
   Some fz'
   end x
 | fs n'x x, fs n'y y =>
   match n'x as n'x', n'y as n'y' return
   Fin n'x' -> Fin n'y' ->
   n'x = n'x' -> n'y = n'y' ->
   S n'x' = S n'y' ->
   option (Fin n'y') with
   | O, _ => fun x' _ _ _ _ => empty _ x'
   | _, O => fun _ y' _ _ _ => empty _ y'
   | S n'x'', S n'y'' => fun _ _ xEq yEq xyEq =>
   let xEq' := trans_eq xEq (eq_pred _ _ xyEq) in
   let x' := eq_rect _ Fin x _ xEq' in
   let y' := eq_rect _ Fin y _ yEq in
   optionMap _ _ (fs) (thick n'y'' x' y')
   end x y (refl_equal n'x) (refl_equal n'y)
 end (refl_equal (S n)).

Definition leftO A (f : A -> option A) : option A -> option A :=
 fun x => match x with None => None | Some x' => f x' end.

Definition liftO A {B} (f : A -> B) : option A -> option B :=
 fun x => match x with None => None | Some x' =>
 Some (f x')
 end.

Definition liftO2 A (f : A -> A -> A) : option A -> option A -> option A :=
 fun x => match x with None => fun _ => None | Some x' =>
 fun y => match y with None => None | Some y' =>
 Some  (f x' y')
 end
 end.

Fixpoint check (n : nat) (x : Fin (S n)) (t : Term (S n)) {struct t} :
option (Term n) :=
match t with
| iota y => optionMap _ _ (iota _) (thick _ x y)
| leaf => Some (leaf _)
| fork s t => liftO2 _ (fork _) (check _ x s) (check _ x t)
end.

Definition fore (n : nat) (x : Fin (S n)) (t' : Term n) (y : Fin (S n)) :=
 match thick _ x y with
 | None => t'
 | Some y' => iota _ y'
 end.

Inductive AList : nat -> nat -> Type :=
| anil n : AList n n
| asnoc m n : forall (sigma : AList m n) (t' : Term m) (x : Fin (S m)), AList (S m) n.

Fixpoint sub m n (sigma : AList m n) {struct sigma} : Fin m -> Term n :=
match sigma in AList m n return Fin m -> Term n with
| anil _ => iota _
| asnoc _ _ sigma t' x => compSubst _ _ _ (sub _ _ sigma) (fore _ x t')
end.

Fixpoint AAppend (l m n : nat) (rho : AList m n) (sigma : AList l m) {struct sigma} : AList l n :=
match sigma in AList l' m' return m = m' -> AList l' n with
| anil _ => fun Eql => eq_rect _ (fun i => AList i _) rho _ Eql
| asnoc _ _ sigma t' x => fun Eql =>
 let sigma' := eq_rect _ (fun i => AList _ i) sigma _ (sym_eq Eql) in
 asnoc _ _ (AAppend _ _ _ rho sigma') t' x
end (refl_equal m).

Definition flexRigid' (m : nat) (x : Fin (S m)) (t : Term (S m)) : option (sigT (AList (S m))) :=
match check _ x t with
| Some t' => Some (existT _ m (asnoc _ _ (anil _) t' x))
| None => None
end.
Definition flexRigid (m : nat) (x : Fin m) (t : Term m) : option (sigT (AList m)) :=
match m as m return forall (x : Fin m) (t : Term m), option (sigT (AList m)) with
| O => fun x t => empty _ x
| S _ => fun x t => flexRigid' _ x t
end x t.

Definition flexFlex' (m : nat) (x y : Fin (S m)) : sigT (AList (S m)) :=
match thick _ x y with
| Some y' => existT _ m (asnoc _ _ (anil _) (iota _ y') x)
| None => existT _ (S m) (anil _)
end.
Definition flexFlex (m : nat) (x y : Fin m) : sigT (AList m) :=
match m as m return forall (x y : Fin m), sigT (AList m) with
| O => fun x y => empty _ x
| S _ => fun x y => flexFlex' _ x y
end x y.

Lemma zero_succ_discriminate {P x} : O = S x -> P.
  discriminate.
Qed.

Definition amgu (m : nat) (s t : Term m) (acc : sigT (AList m)) : option (sigT (AList m)).
refine (
  fix amgu_rec_m (m : nat) {struct m} :
    forall (s t : Term m) (acc : sigT (AList m)), option (sigT (AList m)) := _).
refine (
  fix amgu_rec_s (s t : Term m) (acc : sigT (AList m)) {struct s} :
    option (sigT (AList m)) := _).
refine (
  let (n, a) := acc in
  match m as m', s, t, a in AList m'' _
  return _ = m' -> m' = m'' -> option (sigT (AList m))
  with
    | _, leaf,     leaf,         acc => fun _ _ => Some (existT _ _ acc)
    | _, leaf,     fork _ _,     acc => fun _ _ => None
    | _, fork _ _, leaf    ,     acc => fun _ _ => None
    | _, fork s1 s2, fork t1 t2, acc => fun _ _ =>
      leftO _ (amgu_rec_s s2 t2) (amgu_rec_s s1 t1 (existT _ _ acc))
    | _, iota x,   iota y,       anil _ => fun _ _ => Some (flexFlex _ x y)
    | _, iota x,   t,            anil _ => fun _ _ => flexRigid _ x t
    | _, t,        iota x,       anil _ => fun _ _ => flexRigid _ x t
    | O, _, _, _                    => fun (eql : m = 0) eql' => zero_succ_discriminate eql'
    | S m'', s, t, asnoc _ _ a t' x => fun (eql : m = S _) eql' =>
      let Ea' := eq_rect _ (fun m => sigT (AList m)) (existT _ _ a) _ (sym_eq (eq_pred _ _ eql')) in
      let s'' := eq_rect _ Term s _ eql in
      let t'' := eq_rect _ Term t _ eql in
      let x' := eq_rect _ Fin x _ (sym_eq eql') in
      let t''' := eq_rect _ Term t' _ (sym_eq (eq_pred _ _ eql')) in
      let R := @liftO (sigT (AList m'')) (sigT (AList (S m'')))
        (fun sigma =>
          match sigma with
            | existT n a => existT _ n (asnoc _ _ a t''' x')
          end)
        (amgu_rec_m _
          (funcR _ _ (fore m'' x' t''') s'')
          (funcR _ _ (fore m'' x' t''') t'') 
          Ea')
        in
        (eq_rect _ (fun m => option (sigT (AList m))) R _ (sym_eq eql))
  end (refl_equal m) (refl_equal m)).
Defined.

Definition mgu (m : nat) (s t : Term m) : option (sigT (AList m)) := amgu m s t (existT _ m (anil _)).

