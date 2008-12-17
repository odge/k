Require Import List ListPlus Arith Omega Eqdep_dec_defined Cast Fin Coven.
Set Implicit Arguments.

Section Topological.
  
  Section Preliminaries.
    
    Variable n : nat.
    
    Inductive constraint :=
    | less : Fin n -> Fin n -> constraint.
    
    Definition constraints := list constraint.
    
    Section Specification.
      
      Definition denotation := Fin n -> nat.
      
      Fixpoint interpretation (sigma : denotation) (G : constraints) :=
        match G with
          | nil => True
          | less x y :: G' => sigma x < sigma y /\ interpretation sigma G'
        end.
    
    End Specification.
    
    Section Language.
      
      Definition subject c := match c with less s _ => s end.
      Definition master c := match c with less _ m => m end.
      
      Fixpoint mentioned G b :=
        match G with
          | nil => False
          | c::G' => (b = subject c \/ b = master c) \/ mentioned G' b
        end.
      
      Fixpoint about G b :=
        match G with
          | nil => True
          | c::G' => (b = subject c \/ b = master c) /\ about G' b
        end.
      
      Fixpoint below G b :=
        match G with
          | nil => True
          | c::G' => b <> master c /\ below G' b
        end.
      
      Definition minimum G b := mentioned G b /\ below G b.
      
      Definition bottomless G := ~ exists b, minimum G b.
    
    End Language.
    
    Section Theory.
      
      Variable b : Fin n.
      Variables G G' : constraints.
      
      Theorem Permutation_mentioned : Permutation G G' ->
        mentioned G b -> mentioned G' b.
      Proof.
        intro P; induction P; simpl; intuition.
      Qed.
      
      Theorem Permutation_below : Permutation G G' ->
        below G b -> below G' b.
      Proof.
        intro P; induction P; simpl; intuition.
      Qed.
      
      Theorem Permutation_minimum : Permutation G G' ->
        minimum G b -> minimum G' b.
      Proof.
        intro P.
        unfold minimum; split; inject;
          apply Permutation_mentioned ||
          apply Permutation_below;
            assumption.
      Qed.
      
      Lemma In_mentioned u v :
        In (less u v) G -> mentioned G u /\ mentioned G v.
      Proof.
        induction G; simpl; intuition; subst; simpl; intuition.
        pose (IHc u v H0); right; intuition.
        pose (IHc u v H0); right; intuition.
      Qed.
    
    End Theory.
    
    Section Workers.
      
      Definition Decide_mentioned G b : Decide (mentioned G b).
      refine (
      fix Decide_mentioned G b : Decide (mentioned G b) :=
      match G with
        | nil => right _ _
        | c::G' =>
          if eq_Fin_dec b (subject c)
            then left _ _
            else if eq_Fin_dec b (master c)
              then left _ _
              else if Decide_mentioned G' b
                then left _ _
                else right _ _
      end
      ); simpl; tauto.
      Defined.
      
      Definition Decide_below G b : Decide (below G b).
      refine (
      fix Decide_below G b : Decide (below G b) :=
      match G with
        | nil => left _ _
        | c::G' =>
          if eq_Fin_dec b (master c)
            then right _ _
            else if Decide_below G' b
              then left _ _
              else right _ _
      end
      ); simpl; tauto.
      Defined.
      
      Definition Decide_minimum G b : Decide (minimum G b).
      refine (
      fun G b =>
        if Decide_mentioned G b
          then if Decide_below G b
            then left _ _
            else right _ _
          else right _ _
      ); unfold minimum in *; simpl in *; tauto.
      Defined.
      
      Definition Exhibit_minimum G : Exhibit (minimum G).
      refine (
      fun G =>
      let sublist := filter_dec (minimum G) (Decide_minimum G) freshFins in
      let sublistPrf b := filter_dec_In (minimum G) (Decide_minimum G) b freshFins in
        match sublist as sublist
        return (
          forall b : Fin n,
            In b sublist  <-> In b freshFins /\ minimum G b
               ) -> Exhibit (minimum G)
        with
          | nil => fun sublistPrf' => inr _ _
          | c::_ => fun sublistPrf' => inl _ (exist _ c _)
        end sublistPrf
      ).
      intros [bot botMinProof];
        destruct (sublistPrf' bot) as [L R];
          apply (R (conj everyFinFresh botMinProof)).
      destruct (sublistPrf' c) as [L R];
        destruct (L (or_introl _ (refl_equal c)));
          assumption.
      Defined.
      
      Definition eq_constraint_dec : forall u v : constraint, {u = v} + {u <> v}.
      refine (
        fun u v =>
          match u, v with
            | less d b, less p q =>
              if eq_Fin_dec d p
                then if eq_Fin_dec b q
                  then left _ _
                  else right _ _
                else right _ _
          end
      ); subst; auto.
      contradict _H0; injection _H0; auto.
      contradict _H; injection _H; auto.
      Defined.
      
      Definition thin_sigma {X} (f : Fin n -> X) (o : Fin (S n)) x : Fin (S n) -> X :=
        fun o' => match thick n o o' with
                    | Some o => f o
                    | None => x
                  end.
      
      Definition mentioned_not_below G b x :=
        In (less x b) G /\ ~ below G b.
      
      Definition not {A} P (x:A) := ~ P x.
      Definition negate {A} P (f : forall x:A, Decide (P x)) : forall x, Decide (~ P x).
      unfold Decide.
      intros A P f x.
      case (f x); tauto.
      Defined.
      
    End Workers.
  
  End Preliminaries.
  
  Section Thick_And_Thin.
      
    Definition thin_constraint {n} (bot : Fin (S n)) (k : constraint n) :=
      match k with less u v => less (thin _ bot u) (thin _ bot v) end.

    Definition thin_constraints {n} (bot : Fin (S n)) :
      constraints n -> constraints (S n) := map (thin_constraint bot).
    
    Definition thicken_constraint {n} (bot : Fin (S n)) (k : constraint (S n)) :=
      match k with
        | less u v =>
          match thick _ bot u, thick _ bot v with
            | Some u', Some v' => Some (less u' v')
            | _, _ => None
          end
      end.
    
    Definition thicken_constraint_inv {n} (u v : Fin (S n)) bot r :
      thicken_constraint bot (less u v) = r ->
      (exists u', exists v',
        r = Some (less u' v') /\ u = thin n bot u' /\ v = thin n bot v') \/
      (r = None /\ (u = bot \/ v = bot)).
      
      intros.
     
      unfold thicken_constraint in *.
      
      (case_eq (thick n bot u); [intros u'' uEq| intro uEq]);
      (case_eq (thick n bot v); [intros v'' vEq| intro vEq]);
      try rewrite uEq in *;
      try rewrite vEq in *;
      destruct (thick_inverse' n bot u _ uEq);
      destruct (thick_inverse' n bot v _ vEq);
      inject; try discriminate;
      (destruct r as [k|]; [destruct k as [u' v']|]); try discriminate;
      inject; intros.
      
      left; exists u'; exists v'; subst; intuition; subst; intuition.
      right; subst; intuition.
      right; subst; intuition.
      right; subst; intuition.
    Defined.
    
    Definition splitConstraints {n} (G : constraints (S n)) (bot : Fin (S n)) :
      { (l, r) : constraints (S n) * constraints n |
        Permutation G (l ++ thin_constraints bot r) /\ about l bot }.
    refine (
    fix splitConstraints {n} (G : constraints (S n)) (bot : Fin (S n)) {struct G} :
      { (l, r) : constraints (S n) * constraints n |
        Permutation G (l ++ thin_constraints bot r) /\ about l bot } :=
      match G as G
      return
      { (l, r) : constraints (S n) * constraints n |
        Permutation G (l ++ thin_constraints bot r) /\ about l bot }
      with
        | nil => [[ (nil, nil) ]]
        | less u v::G' =>
          let (lr,lr_proof') := splitConstraints n G' bot in
          match lr as lr
          return
          (fun anonymous : constraints (S n) * constraints n =>
            let (l,r) := anonymous in
              Permutation G' (l ++ thin_constraints bot r) /\ about l bot) lr ->
          { (l, r) : constraints (S n) * constraints n |
            Permutation (less u v::G') (l ++ thin_constraints bot r) /\ about l bot }
          with
            | (l,r) => fun lr_proof =>
              match thicken_constraint bot (less u v) as thick'
              return thicken_constraint bot (less u v) = thick' ->
              { (l, r) : constraints (S n) * constraints n |
                Permutation (less u v::G') (l ++ thin_constraints bot r) /\ about l bot }
              with
                | Some (less u' v') => fun e1 => [[ (l, less u' v'::r) ]]
                | None => fun e1 => [[ (less u v::l, r) ]]
              end (refl_equal (thicken_constraint bot (less u v)))
          end lr_proof'
      end
    ); inject.
    
    split; [ constructor | simpl; tauto ].
    
    split; auto; simpl.
    destruct (@thicken_constraint_inv _ _ _ _ _ e1);
      inject; intros; try discriminate; subst.
    eapply Permutation_trans.
    apply perm_skip.
    apply H.
    apply Permutation_sym.
    eapply Permutation_trans.
    apply Permutation_app_swap.
    simpl; apply perm_skip.
    apply Permutation_app_swap.
    
    destruct (@thicken_constraint_inv _ _ _ _ _ e1);
      inject; intros; try discriminate; subst.
    split; simpl.
    apply perm_skip.
    assumption.
    split; intuition.
  Defined.
  
  End Thick_And_Thin.
  
  Section Fudging.
    
    Lemma In_interpretation {n} (G : constraints n) (u v : Fin n) sigma :
      In (less u v) G -> interpretation sigma G -> sigma u < sigma v.
    Proof.
      induction G as [| [u v] G' IHG]; simpl.
      tauto.
      intros u' v' sigma' [L | R] [X Y].
      injection L; intros; subst; assumption.
      apply IHG; assumption.
    Qed.
   
    Lemma Permutation_interpretation {n} sigma (G G' : constraints n) :
      Permutation G G' -> interpretation sigma G -> interpretation sigma G'.
      intros n sigma G G' P; induction P; simpl in *; intuition.
      destruct x; intuition.
      destruct x; intuition.
      destruct y; intuition.
      destruct y; intuition.
    Qed.
    
    Lemma interpretation_sublist {n} (G sub : constraints n) sigma :
      interpretation sigma G -> sublist G sub -> interpretation sigma sub.
    Proof.
      induction sub as [| [u v] G' IHsub]; simpl.
      tauto.
      intros; split.
      assert (In (less u v) G) by intuition.
      apply In_interpretation with G; assumption.
      apply IHsub.
      assumption.
      apply sublist_cons with (o := less u v); assumption.
    Qed.
    
    Lemma interpretation_thining {n} (G : constraints n) sigma bot :
      interpretation sigma G -> interpretation (thin_sigma sigma bot 0) (thin_constraints bot G).
    Proof.
      intros n G sigma bot; induction G; simpl; try tauto.
      destruct a; split; inject; intuition.
      
      Lemma thin_sigma_thin {n} sigma bot (i : nat) f :
        thin_sigma sigma bot i (thin n bot f) = sigma f.
        intros; unfold thin_sigma.
        pose (@thin_wedges n bot f).
        destruct (thick_inverse n bot (thin n bot f) _ (refl_equal _)); inject.
        contradiction.
        pose (thin_injective H).
        rewrite H0; congruence.
      Qed.
      
      repeat rewrite thin_sigma_thin; assumption.
    Qed.
    
    Theorem solution_lifting {n} sigma (G : constraints n) :
      interpretation sigma G -> interpretation (S ∘ sigma) G.
      induction G; intuition; simpl in *; destruct a; split; inject.
      unfold compose; omega.
      apply IHG; assumption.
    Qed.
    
    Theorem solution_extension {n} sigma l r (bot : Fin (S n)) :
      interpretation sigma r ->
      interpretation (thin_sigma (S ∘ sigma) bot 0) (thin_constraints bot r) ->
      minimum (l ++ thin_constraints bot r) bot -> about l bot ->
      interpretation (thin_sigma (S ∘ sigma) bot 0) (l ++ thin_constraints bot r).
    Proof.
      Lemma solution_extension' {n} sigma l r G (bot : Fin (S n)) :
        interpretation sigma r ->
        (forall c, In c (l ++ thin_constraints bot r) -> In c G) ->
        interpretation (thin_sigma (S ∘ sigma) bot 0) (thin_constraints bot r) ->
        minimum G bot -> about l bot ->
        interpretation (thin_sigma (S ∘ sigma) bot 0) (l ++ thin_constraints bot r).
      Proof.
        induction l.
        tauto.
        simpl; intros; inject.
        destruct a; split.
        Focus 2.
        eapply IHl; try assumption; try apply H2.
        intros c X; apply (H0 c).
        right; assumption.
        
        pose (H0 (less f f0) (or_introl _ (refl_equal _))).
        unfold minimum in *; inject.
        assert (bot <> f0).
        
        Lemma below_In {n} cs (bot : Fin n) c : below cs bot -> In c cs -> bot <> master c.
          induction cs.
          intuition.
          simpl.
          intros.
          destruct a.
          inject.
          destruct H0.
          injection H0.
          intros; subst.
          simpl; assumption.
          apply IHcs.
          assumption.
          assumption.
        Qed.
        
        pose (below_In G _ H5 i).
        simpl in n0; assumption.
        
        assert (bot = f).
        destruct H3; simpl in *; intuition.
        unfold thin_sigma.
        
        subst f.
        rename f0 into v.
        
        (case_eq (thick n bot bot); [intros u'' uEq| intro uEq]);
        (case_eq (thick n bot v); [intros v'' vEq| intro vEq]);
        try rewrite uEq in *;
        try rewrite vEq in *;
        destruct (thick_inverse n bot bot _ uEq);
        destruct (thick_inverse n bot v _ vEq);
        inject; try discriminate.
        pose (@thin_wedges n bot x0).
        elimtype False; apply n0; auto.
        pose (@thin_wedges n bot x).
        elimtype False; apply n0; auto.
        unfold compose; omega.
        elimtype False; apply H6; auto.
      Qed.
    intros; eapply solution_extension'; eauto.
  Qed.
      
  End Fudging.
  
  Section Cyclicity.
  
    Fixpoint loop_helper {n} (G : constraints n) (u v : Fin n) :=
      match G with
        | nil => u = v
        | less v' w::G' => v = v' /\ loop_helper G' u w
      end.
    
    Definition loop {n} (G : constraints n) :=
      match G with
        | nil => False
        | less u v::G' => loop_helper G' u v
      end.
    
    Definition cycle {n} (G : constraints n) := sublist_satisfies G loop.
    
    Definition descending {n} (G : constraints n) := forall y d, In (less y d) G -> exists x, In (less x y) G.
    
    Lemma loop_helper_inconsistency {n} :
      forall (G : constraints n) (u v : Fin n), loop_helper G u v ->
        forall sigma, interpretation sigma G -> u = v \/ sigma v < sigma u.
    Proof.
      induction G as [|[u v] G' IHG]; simpl; intuition; subst.
      instantiation 4 IHG; destruct IHG; subst.
      right; assumption.
      right; apply lt_trans with (sigma v); assumption.
    Qed.
    
    Theorem loop_inconsistency {n} (G : constraints n) :
      loop G -> ~ exists sigma, interpretation sigma G.
    Proof.
      intros n G Loop [sigma Interp]; destruct G as [| c G' ].
      tauto.
      destruct c; simpl in *; inject.
      pose @loop_helper_inconsistency as helper; unfold constraints in helper.
      instantiation 6 helper; destruct helper; subst; omega.
    Qed.
    
    Theorem cycle_inconsistency {n} (G : constraints n) :
      cycle G -> ~ exists sigma, interpretation sigma G.
    Proof.
      intros n G [sub Sub_Loop] [sigma Interp]; destruct Sub_Loop as [Sub Loop].
      apply (loop_inconsistency _ Loop); exists sigma.
      apply interpretation_sublist with G; assumption.
    Qed.
    
    Theorem bottomless_descending {n} c (G : constraints n) : bottomless (c::G) -> descending (c::G).
    Proof.
      unfold bottomless; unfold descending.
      intros.
      assert (forall b, ~ minimum (c :: G) b).
      Focus 2.
      pose (H1 y).
      unfold minimum in n0.
      assert (mentioned (c :: G) y).
      Focus 2.
      assert (~ below (c :: G) y).
      intro; apply n0; auto.
      
      Lemma mentioned_above {n} (G : constraints n) y :
        mentioned G y -> ~ below G y ->
        exists x : Fin n, In (less x y) G.
        intros.
        destruct (Decide_mentioned_not_below G y).
        
      Proof.
        
      Admitted.
    
      exact (mentioned_above (c :: G) _ H2 H3).
    
    intros; intro.
    apply H.
    exists b; assumption.
  
  (* VERY difficult proof *)
    
    Admitted.
    
    Theorem descending_cycle {n} c (G : constraints n) : descending (c::G) -> cycle (c::G).
    Proof.
      unfold descending; unfold cycle.
      intros.
      unfold sublist_satisfies.
      unfold loop.
      destruct c.
      destruct (H f  f0 (or_introl _ (refl_equal _))) as [f1 X1].
      
      destruct (H _ _ X1) as [f2 X2].
      destruct (H _ _ X2) as [f3 X3].
      destruct (H _ _ X3) as [f4 X4].
      destruct (H _ _ X4) as [f5 X5].
      (* ... *)
    
      (* cardinality argument *)
    Admitted.
    
    Theorem bottomless_cycle {n} c (G : constraints n) : bottomless (c::G) -> cycle (c::G).
    Proof.
      exact (fun n c G P => descending_cycle (bottomless_descending P)).
    Qed.
    
    Lemma cycle_permutation' {n} (G G' : constraints n) :
      sublist G G' -> sublist G' G -> cycle G -> cycle G'.
    Proof.
      intros n G G' subl subl' Cy; destruct Cy; inject.
      exists x; split; auto.
      unfold sublist in *; intros.
      pose (H x0 H1).
      apply subl'; assumption.
    Qed.
    
    Lemma cycle_permutation {n} (G G' : constraints n) :
      Permutation G G' -> cycle G -> cycle G'.
    Proof.
      intros n G G' P.
      destruct (permutation_sub_sub P); apply cycle_permutation'; auto.
    Qed.
    
    Lemma cycle_extension {n} (G : constraints n) (l : constraints n) :
      cycle G -> cycle (l ++ G).
    Proof.
      intros; induction l; simpl; auto.
      unfold cycle in *.
      unfold sublist_satisfies in *.
      inject.
      exists x.
      split; auto.
      apply sublist_cons'; assumption.
    Qed.
  
    Lemma cycle_thin {n} bot (G : constraints n) : cycle G -> cycle (thin_constraints bot G).
    Proof.
      unfold cycle.
      unfold sublist_satisfies.
      intros; inject.
      exists (thin_constraints bot x).
      split.
      intro; intro.
    Admitted.

  End Cyclicity.
  
End Topological.


Definition topological_sort {n} (G : constraints n) : Exhibit (fun sigma => interpretation sigma G).

Definition topological_sort' {n} (G : constraints n) : {o : denotation n | interpretation o G} + (cycle G /\ ~ (exists o : denotation n, interpretation o G)).
refine (
fix topological_sort' {n} (G : constraints n) {struct n} : {o : denotation n | interpretation o G} + (cycle G /\ ~ (exists o : denotation n, interpretation o G)) :=
match n as n'
return n = n' -> {o : denotation n | interpretation o G} + (cycle G /\ ~ (exists o : denotation n, interpretation o G))
with
  | O => fun e1 =>
    match G with
      | nil => inl _ [[ fun _ => 0 ]]
      | less x _:: _ => !
    end
  | S n => fun e1 =>
    let G' := eq_rect _ constraints G (S n) e1 in
    let G_eq_G' := _ : INeq constraints G G' in
    match Exhibit_minimum G' with
      | inl (exist bot botPrf) => let (lr,lrProof) := splitConstraints G' bot in
        match lr as lr
        return
        (fun anonymous : constraints (S n) * constraints n =>
          let (l, r) := anonymous in
            Permutation G' (l ++ thin_constraints bot r) /\ about l bot) lr ->
               {o : denotation _ | interpretation o G} + (cycle G /\ ~ (exists o : denotation _, interpretation o G))
        with
          | (l,r) => fun lrProof' =>
            match topological_sort' n r with
              | inl (exist sigmaR sigmaRProof) =>
                let sigma := thin_sigma (S ∘ sigmaR) bot 0 in
                let sigma' := eq_rect _ (fun n => Fin n -> nat) sigma _ (sym_eq e1) in
                  inl _ [[ sigma' ]]
              | inr bottomless' => inr _ _
            end
        end lrProof
      | inr bottomless =>
        match G' as G'' return G' = G'' -> (~ exists bot, minimum  G'' bot) -> _ with
          | nil => fun _ _ => inl _ [[ fun _ => 0 ]]
          | _::_ => fun e1 bottomless' => inr _ _
        end (refl_equal G') bottomless
    end
end (refl_equal n)
).

simpl; trivial.

subst n; apply no_Fin0; assumption.

destruct n; [ discriminate |]; injection e1; intros.
unfold G'; clear G'; subst n0.
rewrite (eq_proofs_unicity dec_eq_nat e1 (refl_equal (S n))); simpl.
reflexivity.

destruct n; [ discriminate |]; injection e1; inject; intros.
unfold sigma'; unfold sigma; clear sigma'; clear sigma.
unfold G' in *; clear G'; subst n0.
rewrite (eq_proofs_unicity dec_eq_nat e1 (refl_equal (S n))) in *; simpl in *.
pose
  (@solution_extension _ sigmaR l r bot sigmaRProof
    (interpretation_thining _ _ bot (solution_lifting _ _ sigmaRProof))
    (Permutation_minimum H botPrf)
    H0).
eapply Permutation_interpretation; eauto.
apply Permutation_sym; assumption.


destruct n; [ discriminate |]; injection e1; intros.
unfold G' in *; clear G'; subst n0.
inject; assert (cycle G).
eapply cycle_permutation.
apply Permutation_sym.
rewrite (eq_proofs_unicity dec_eq_nat e1 (refl_equal (S n))) in *; simpl.
rewrite G_eq_G'.
apply eq_nat_dec.
apply H1.
apply cycle_extension.

apply cycle_thin; assumption.

split; auto.
eapply cycle_inconsistency; eauto.

subst G'.
destruct n; [ discriminate |]; injection e1; intros; subst n0.
rewrite (eq_proofs_unicity dec_eq_nat e1 (refl_equal (S n))) in *; simpl in *.
subst G.
simpl; trivial.

subst G'.
destruct n; [ discriminate |]; injection e1; intros; subst n0.
rewrite (eq_proofs_unicity dec_eq_nat e1 (refl_equal (S n))) in *; simpl in *.
subst G.
pose (bottomless_cycle bottomless0).
split; auto.
eapply cycle_inconsistency; eauto.

Defined.
refine (fun n G =>
  match topological_sort' G with
    | inl X => inl _ X
    | inr (conj _ Y) => inr _ Y
  end).
Defined.



Eval lazy in
  (if (@topological_sort 2 (less (fs fz) fz::nil))
    then true
    else false).

