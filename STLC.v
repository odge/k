Require Import Coven Fin.

Inductive ST : Set :=
| NAT : ST
| ARR : ST -> ST -> ST.
Infix "-->" := ARR (right associativity, at level 20).
Fixpoint ST_interpret (ty : ST) : Type :=
  match ty with
    | NAT => nat
    | u --> v => ST_interpret u -> ST_interpret v
  end.
Definition eq_ST_dec : forall sigma tau : ST, {sigma = tau} + {sigma <> tau}.
decide equality.
Defined.


Definition kast {Index : Type} {i j : Index}
  (F : Index -> Type) : F i -> i = j -> F j.
intros.
elim H.
assumption.
Defined.

Inductive Context : nat -> Set :=
| empty : Context O
| extend {n} : Context n -> ST -> Context (S n).
Definition lookup {n : nat} (gamma : Context n) (i : Fin n) : ST.
refine (fix lookup {n : nat} (gamma : Context n) (i : Fin n) : ST :=
  match i in Fin n',
        gamma in Context n''
  return n = n' -> n = n'' -> _
  with
    | fz _, empty => fun _ _ => !
    | fz _, extend _ _ ty => fun _ _ => ty
    | fs _ i, empty => fun _ _ => !
    | fs _ i, extend _ gamma _ => fun _ _ =>
      let i' := kast Fin i _ in
      lookup _ gamma i'
  end
  (refl_equal n) (refl_equal n)); congruence.
Defined.

Definition whack {l r : nat} : Context l -> Context r -> Context (r + l).
refine (fix whack {l r : nat} (gamma : Context l)(delta : Context r) : Context (r + l) := _).
refine (
  match delta in Context r
  return Context (r + l)
  with
    | empty => gamma
    | extend _ delta' Tau => extend (whack _ _ gamma delta') Tau
  end
).
Defined.

Theorem whack_ext l r gamma delta tau :
  extend (@whack l r gamma delta) tau = whack gamma (extend delta tau).
induction delta; intuition.
Defined. (* worried that I can't reduce something if I used Qed, but check it out to be sure once everything is finished *)

Definition wedge {l r : nat} : Context l -> ST -> Context r -> Context (S (r + l)).
refine (fix wedge {l r : nat} (gamma : Context l)(Tau : ST)(delta : Context r) : Context (S (r + l)) := _).
refine (
  match delta in Context r
  return Context (S (r + l))
  with
    | empty => extend gamma Tau
    | extend _ delta' Sigma => extend (wedge _ _ gamma Tau delta') Sigma
  end
).
Defined.

Theorem wedge_ext l r gamma sigma delta tau :
  wedge gamma sigma (extend delta tau) = extend (@wedge l r gamma sigma delta) tau.
induction gamma; intuition.
Defined. (* ditto whack_ext *)


Inductive STLC (n : nat) (gamma : Context n) : ST -> Set :=
| var : forall i : Fin n, 
  STLC n gamma (lookup gamma i)
| lam : forall U V : ST,
  STLC (S n) (extend gamma U) V -> STLC n gamma (ARR U V)
| app : forall M N : ST,
  STLC n gamma (ARR M N) -> STLC n gamma M -> STLC n gamma N.


Definition lift
  (l : nat)
  (r : nat)
  (gamma : Context l)
  (delta : Context r)
  (sigma : ST)
  (i : Fin (r + l)) :
  { j : Fin (S (r + l)) |
    lookup (whack gamma delta) i = lookup (wedge gamma sigma delta) j }.
refine (fix lift l r gamma delta sigma i {struct delta}
  : { j : Fin (S (r + l)) |
    lookup (whack gamma delta) i = lookup (wedge gamma sigma delta) j }
  := _).

Require Import Cast Arith.

refine (
  match delta as delta' in Context r'', i as i' in Fin r'l
  return r + l = r'l -> r = r'' -> INeq Fin i i' -> INeq Context delta delta' ->
  { j : Fin (S (r + l)) |
    lookup (whack gamma delta) i = lookup (wedge gamma sigma delta) j }
  with
    | empty, i => fun e1 e2 e3 e4 => [[ fs i ]]
    | extend _ delta' Tau, fz _ => fun e1 e2 e3 e4 => [[ fz ]]
    | extend _ delta' Tau, fs _ j => fun e1 e2 e3 e4 =>
      let QQ := _ in
      let QQ' := _ in
      let (j', j'Prf) := lift _ _ gamma delta' sigma (kast Fin j QQ) in
        [[ fs (kast Fin j' QQ') ]]
  end
  (refl_equal (r + l)) (refl_equal r) (INeq_refl Fin i) (INeq_refl Context delta)
).

clear e1 e3.
subst r.
rewrite e4.
apply eq_nat_dec.
reflexivity.

subst r.
injection e1; clear e1; intro e1.
subst n0.
rewrite e3.
apply eq_nat_dec.
clear e3.
rewrite e4.
apply eq_nat_dec.
clear e4.
reflexivity.

omega.
omega.

Set Printing Implicit.
clear lift.
subst r.
rewrite e4; try apply eq_nat_dec.
clear delta e4.
simpl in QQ'.
simpl in e1.
simpl in i.
Require Import Eqdep_dec_defined.
pose (eq_proofs_unicity dec_eq_nat QQ' (refl_equal _)).
rewrite e.
clear e QQ'.
unfold kast; fold @kast.
unfold eq_rect; fold eq_rect.
symmetry.
transitivity (lookup (wedge gamma sigma delta') j').
reflexivity.
simpl in e3.
Unset Printing Implicit.
idtac.
rewrite <- j'Prf.
clear j'Prf.
clear j'.

Definition helper :
  forall
    (n n' : nat)
    (QQ : n' = n)
    (foo : Context n) Tau
    (j : Fin n')
    (i : Fin (S n))
    (IQ : INeq Fin i (fs j)),
    lookup foo (kast Fin j QQ) = lookup (extend foo Tau) i.

Definition awesome_induction
  (P : forall n n' : nat, n' = n -> Prop)
  (HYP : forall (n : nat), P n n (refl_equal n))
  (n n' : nat)(QQ : n' = n) : P n n' QQ :=
  match QQ as QQ' in _ = n
    return P n n' QQ'
    with
    | refl_equal => HYP n'
  end.

intros n n' QQ.

refine (
  awesome_induction
  (fun n n' (QUAIL : n' = n) =>
    forall
      (foo : Context n) Tau
      (j : Fin n')
      (i : Fin (S n))
      (IQ : INeq Fin i (fs j)),
      lookup foo (kast Fin j QUAIL) = lookup (extend foo Tau) i)
  _
  n n' QQ
).

clear n n' QQ.
intros n foo Tau j i IQ.
rewrite IQ.
apply eq_nat_dec.
reflexivity.
Defined.

eapply helper; assumption.
Defined.

Definition thinSTLC
  (l r : nat)
  (gamma : Context l) (delta : Context r)
  (sigma Tau : ST) :
  STLC (r + l) (whack gamma delta) Tau ->
  STLC (S (r + l)) (wedge gamma sigma delta) Tau.
refine (fix thinSTLC (l r : nat)
  (gamma : Context l) (delta : Context r)
  (sigma Tau : ST)
  (t : STLC (r + l) (whack gamma delta) Tau) : 
  STLC (S (r + l)) (wedge gamma sigma delta) Tau := _).
refine (
  match t in STLC _ _ Tau
  return STLC (S (r + l)) (wedge gamma sigma delta) Tau
  with
    | var i => let (j,jPrf) := lift l r gamma delta sigma i in
      kast (fun T => STLC (S (r + l)) (wedge gamma sigma delta) T)
      (var _ _ j) (sym_eq jPrf)
    | lam U V b =>
      let QQ := wedge_ext l r gamma sigma delta U in
      let QQ' := whack_ext l r gamma delta U in
        lam (S (r + l)) (wedge gamma sigma delta) U V
        (kast (fun idk => STLC (S (S (r + l))) idk V)
          (thinSTLC l (S r) gamma (extend delta U) sigma V
            (kast (fun idk => STLC (S (r + l)) idk V) b QQ')) QQ)
    | app M N m n =>
      app (S (r + l)) (wedge gamma sigma delta) M N
      (thinSTLC l r gamma delta sigma (M --> N) m)
      (thinSTLC l r gamma delta sigma M n)
  end
).
Defined.

Definition strength l r (gamma : Context l) Sigma (delta : Context r) Tau i :
  lookup (wedge gamma Sigma delta) i = Tau ->
  { j | lookup (whack gamma delta) j = Tau } + { Sigma = Tau }.
refine (fix strength
  l r (gamma : Context l) Sigma (delta : Context r) Tau i
  {struct delta}
  : lookup (wedge gamma Sigma delta) i = Tau ->
  { j | lookup (whack gamma delta) j = Tau } + { Sigma = Tau } := _).
refine (
match delta as delta in Context r
return forall (i : Fin (S (r + l))),
  lookup (wedge gamma Sigma delta) i = Tau ->
  {j : Fin (r + l) | lookup (whack gamma delta) j = Tau} + {Sigma = Tau}
with
  | empty => _
  | extend _ delta' Rho => _
end i
); clear i.

intro i; Fin_case i; specializer; [ left | right ].
exists i1; apply H0.
apply H0.

intro i; Fin_case i; specializer.
intro Hyp; destruct (strength _ _ gamma Sigma delta' Tau i1 Hyp).
destruct s.
left; exists (fs x).
apply e.
right; assumption.

simpl.
intro; subst.
left.
exists fz.
reflexivity.
Defined.


Definition subst' l r gamma Sigma delta Tau
  (t : STLC (S (r + l)) (wedge gamma Sigma delta) Tau)
  (q : STLC (r + l) (whack gamma delta) Sigma) :
  STLC (r + l) (whack gamma delta) Tau.
refine (fix subst' l r gamma Sigma delta Tau
  (t : STLC (S (r + l)) (wedge gamma Sigma delta) Tau)
  (q : STLC (r + l) (whack gamma delta) Sigma) :
  STLC (r + l) (whack gamma delta) Tau := _).
refine (
  match t as t' in STLC _ _ Tau'
  return Tau = Tau' -> INeq (STLC _ _) t t' ->
         STLC (r + l) (whack gamma delta) Tau'
  with
    | var j => fun e1 e2 =>
      match strength l r gamma Sigma delta
        (lookup (wedge gamma Sigma delta) j) j (refl_equal _) with
        | inleft (exist j' j'Prf) => kast (STLC _ _) (var _ _ j') _
        | inright QQ => kast (STLC _ _) q _
      end
    | lam U V b => fun _ _ =>
      lam _ _ U V
      (subst' _ _ gamma Sigma (extend delta U) V b
        (thinSTLC (r + l) 0 (whack gamma delta) empty U Sigma q))
    | app M N m n => fun _ _ =>
      app _ _ M N
      (subst' l r gamma Sigma delta _ m q)
      (subst' l r gamma Sigma delta _ n q)
  end
  (refl_equal Tau) (INeq_refl (STLC _ _) t)
); congruence.
Defined.

Recursive Extraction subst'.

Inductive STLC_beta n gamma : forall T, STLC n gamma T -> STLC n gamma T -> Prop :=
| beta_rule : forall U T,
              forall (b : STLC (S n) (extend gamma U) T),
              forall (x : STLC n gamma U),
               STLC_beta n gamma T
                 (app n gamma U T (lam n gamma U T b) x)
                 (subst' _ _ gamma U empty T b x).

Inductive STLC_eta n gamma : forall T, STLC n gamma T -> STLC n gamma T -> Prop :=
| eta_rule : forall U V,
             forall (f : STLC n gamma (U --> V)),
              STLC_eta n gamma (U --> V)
                f
                (lam n gamma _ _
                  (app (S n) (extend gamma _) _ _ (thinSTLC _ _ gamma empty _ _ f)
                    (var _ (extend gamma _) fz))).

Section Refl_Symm_Trans_Closure.
  
  Variables r : forall n gamma T, STLC n gamma T -> STLC n gamma T -> Prop.
  
  Inductive refl_closure n gamma : forall T, STLC n gamma T -> STLC n gamma T -> Prop :=
  | refl_r_rule : forall T (t t' : STLC n gamma T), r n gamma T t t' -> refl_closure n gamma T t t'
  | refl_rule : forall T (t : STLC n gamma T), refl_closure n gamma T t t.
  
  Inductive symm_closure n gamma : forall T, STLC n gamma T -> STLC n gamma T -> Prop :=
  | symm_r_rule : forall T (t t' : STLC n gamma T), r n gamma T t t' -> symm_closure n gamma T t t'
  | symm_rule : forall T (t t' : STLC n gamma T),
                  symm_closure n gamma T t t' ->
                  symm_closure n gamma T t' t.
  
  Inductive trans_closure n gamma : forall T, STLC n gamma T -> STLC n gamma T -> Prop :=
  | trans_r_rule : forall T (t t' : STLC n gamma T), r n gamma T t t' -> trans_closure n gamma T t t'
  | trans_rule : forall T (t t' t'' : STLC n gamma T),
                   trans_closure n gamma T t t' ->
                   trans_closure n gamma T t' t'' ->
                   trans_closure n gamma T t t''.

End Refl_Symm_Trans_Closure.

Section ReflSymmTrans_Closure.
  
  Variables r : forall n gamma T, STLC n gamma T -> STLC n gamma T -> Prop.
  
  Definition reflsymmtrans_closure n gamma : forall T, STLC n gamma T -> STLC n gamma T -> Prop :=
    refl_closure (symm_closure (trans_closure r)) n gamma.

End ReflSymmTrans_Closure.

Section Contextual_Closure.

Variables r1 r2 : forall n gamma T, STLC n gamma T -> STLC n gamma T -> Prop.

Inductive contextual_closure : forall n gamma T, STLC n gamma T -> STLC n gamma T -> Prop :=
| context_r1_rule : forall n gamma T t t',
                      r1 n gamma T t t' ->
                      contextual_closure n gamma T t t'
| context_r2_rule : forall n gamma T t t',
                      r2 n gamma T t t' ->
                      contextual_closure n gamma T t t'
| context_app_l_rule : forall n gamma U V p p' q,
                         contextual_closure n gamma (U --> V) p p' ->
                         contextual_closure n gamma V (app _ _ _ _ p q) (app _ _ _ _ p' q)
| context_app_r_rule : forall n gamma U V p q q',
                         contextual_closure n gamma (U --> V) q q' ->
                         contextual_closure n gamma V (app _ _ _ _ p q) (app _ _ _ _ p q')
| context_lam_rule : forall n gamma R T b b',
                         contextual_closure (S n) (extend gamma R) T b b' ->
                         contextual_closure n gamma (R --> T) (lam _ _ _ _ b) (lam _ _ _ _ b').

End Contextual_Closure.







Inductive VAL (n : nat) (gamma : Context n) : ST -> Set :=
| Vlam : forall U V : ST,
  (STLC n gamma U -> VAL n gamma V) -> VAL n gamma (U --> V)
| Vneu : forall T : ST,
  NEU n gamma T -> VAL n gamma T
with NEU (n : nat) (gamma : Context n) : ST -> Set :=
| Nvar : forall i : Fin n,
  NEU n gamma (lookup gamma i)
| Napp : forall U V : ST,
  NEU n gamma (U --> V) -> VAL n gamma U -> NEU n gamma V.






Definition apply (n : nat) (gamma : Context n) (U V : ST) :
  VAL n gamma (ARR U V) -> VAL n gamma U -> VAL n gamma V.
Admitted.

Definition reflect (n : nat) (gamma : Context n) (T : ST) :
  STLC n gamma T -> VAL n gamma T.
refine (fix reflect (n : nat) (gamma : Context n) (T : ST)
  (tm : STLC n gamma T) : VAL n gamma T := _).
refine (
  match T as T', tm in STLC _ _ T''
  return T = T' -> T = T'' -> VAL n gamma T
  with
    | NAT, var i => fun _ _ => cast (fun T => VAL n gamma T)
      (Vneu _ _ _ (Nvar _ _ i)) _
    | NAT, lam U' V' b => fun _ _ => !
    | NAT, app U' V' f x => fun _ _ => _
    | U --> V, var i => fun _ _ =>
      Vlam _ _ _ _ (fun x =>
        apply _ _ _ _
          (Vneu _ _ (Nvar _ i))
          (reflect _ _ _ x))
    | U --> V, lam U' V' b => fun _ _ => _
    | U --> V, app U' V' f x => fun _ _ => _
  end (refl_equal T) (refl_equal T)
).

congruence.
congruence.





Definition apply (n : nat) (gamma : Context n) (U V : ST) :
  VAL n gamma (ARR U V) -> VAL n gamma U -> VAL n gamma V.
refine (fun n gamma U V f x =>
  match f with
    | Vlam _ _ f =>
      (cast (fun U => STLC n gamma U -> VAL n gamma V)
        (fun x =>
          (cast (fun V => VAL n gamma V) (f x) _)) _)
      (cast (fun V => STLC n gamma V) x _)
    | Vneu _ n => _
  end).

Definition reflect (n : nat) (gamma : Context n) (T : ST) :
  STLC n gamma T -> VAL n gamma T.
refine (fix reflect (n : nat) (gamma : Context n) (T : ST)
  (tm : STLC n gamma T) : VAL n gamma T := _).
refine (
  match T as T', tm in STLC _ _ T''
  return T = T' -> T = T'' -> VAL n gamma T
  with
    | NAT, var i => fun _ _ => cast (fun T => VAL n gamma T)
      (Vneu _ _ _ (Nvar _ _ i)) _
    | NAT, lam U' V' b => fun _ _ => !
    | NAT, app U' V' f x => fun _ _ =>        !
    | U --> V, var i => fun _ _ =>            !
    | U --> V, lam U' V' b => fun _ _ => cast (fun T => VAL n gamma T)
      (Vlam _ _ _ _ (fun x =>
        match reflect n (extend gamma _) _ x with
        )) _
    | U --> V, app U' V' f x => fun _ _ =>    !
  end (refl_equal T) (refl_equal T)
).
