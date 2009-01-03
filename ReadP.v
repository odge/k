Set Implicit Arguments.
Require Import Omega Coven List.

Section P.

  Variable Token : Set.
  Variable eq_Token_dec : forall u v : Token, {u = v} + {u <> v}.
  Definition String := list Token.

  Inductive P (a : Set) : Set :=
  | Get : (Token -> P a) -> P a
  | Look : (String -> P a) -> P a
  | Fail : P a
  | Result : a -> P a -> P a.
  
  Fixpoint run {a} (p : P a) (s : String) : list (a * String) :=
    match p with
      | Get f =>
        match s with
          | nil => nil
          | c::s => run (f c) s
        end
      | Look f => run (f s) s
      | Fail => nil
      | Result r p => (r, s) :: run p s
    end.
  
  Definition add {a} (p q : P a) : P a.
  refine (fun a => _).
  refine (fix add_rec_p (p : P a) {struct p} : P a -> P a := _).
  refine (fix add_rec_q (q : P a) {struct q} : P a := _).
  refine (
    match p, q with
      | Get f, Get f' => Get (fun c => add_rec_p (f c) (f' c))
      | Look f, Look f' => Look (fun s => add_rec_p (f s) (f' s))
      | Look f, q => Look (fun s => add_rec_p (f s) q)
      | p, Look f => Look (fun s => add_rec_q (f s))
      | Fail, q => q
      | p, Fail => p
      | Result x p, q => Result x (add_rec_p p q)
      | p, Result x q => Result x (add_rec_q q)
    end
  ).
  Defined.
  
  Definition bind {a b} (p : P a) (k : a -> P b) : P b.
  refine (fun a b => _).
  refine (fix bind (p : P a) : (a -> P b) -> P b := _).
  refine (fun k => _).
  refine (
    match p with
      | Get f => Get (fun c => bind (f c) k)
      | Look f => Look (fun c => bind (f c) k)
      | Fail => Fail _
      | Result x p => add (k x) (bind p k)
    end
  ).
  Defined.

  Theorem run_add {a} (p q : P a) (input : String) :
    forall (parse : a * String),
      In parse (run p input) ->
      In parse (run (add p q) input).
  (* Functional Scheme add_rec := Induction for add Sort Prop.
  Anomaly: add_args : todo. Please report. *)
    refine (fun a => _).
    refine (fix run_add_rec_p (p : P a) {struct p} : P a -> _ := _).
    refine (fix run_add_rec_q (q : P a) {struct q} : _ := _).
    refine (
      match p as p', q
      return p = p' -> _
      with
        | Get f, Get f' => fun _ =>
          let hyp1 := fun c => run_add_rec_p (f c) (f' c) in _
        | Look f, Look f' => fun _ =>
          let hyp2 := fun s => run_add_rec_p (f s) (f' s) in _
        | Look f, q => fun _ =>
          let hyp3 := fun s => run_add_rec_p (f s) q in _
        | p, Look f => fun e1 =>
          let hyp4 := fun s => run_add_rec_q (f s) in _
        | Fail, q => fun _ => _
        | p, Fail => fun _ => _
        | Result x p, q => fun _ =>
          let hyp5 := run_add_rec_p p q in _
        | p, Result x q => fun _ =>
          let hyp6 := run_add_rec_q q in _
      end
      (refl_equal p)
    );
    match reverse goal with
      | hyp : ?foo |- _ =>
        assert foo by exact hyp;
          clear hyp; clear run_add_rec_p; clear run_add_rec_q
    end;
    try solve [destruct input; simpl; intuition];
    try solve [intros; subst p; simpl in *; apply H; assumption].
    simpl.
    subst p.
    intros.
    right.
    apply H.
    assumption.
  Qed.

  Theorem run_add' {a} (p q : P a) (input : String) :
    forall (parse : a * String),
      In parse (run q input) ->
      In parse (run (add p q) input).
  (* Functional Scheme add_rec := Induction for add Sort Prop.
  Anomaly: add_args : todo. Please report. *)
    refine (fun a => _).
    refine (fix run_add_rec_p (p : P a) {struct p} : P a -> _ := _).
    refine (fix run_add_rec_q (q : P a) {struct q} : _ := _).
    refine (
      match p as p', q
      return p = p' -> _
      with
        | Get f, Get f' => fun _ =>
          let hyp1 := fun c => run_add_rec_p (f c) (f' c) in _
        | Look f, Look f' => fun _ =>
          let hyp2 := fun s => run_add_rec_p (f s) (f' s) in _
        | Look f, q => fun _ =>
          let hyp3 := fun s => run_add_rec_p (f s) q in _
        | p, Look f => fun e1 =>
          let hyp4 := fun s => run_add_rec_q (f s) in _
        | Fail, q => fun _ => _
        | p, Fail => fun _ => _
        | Result x p, q => fun _ =>
          let hyp5 := run_add_rec_p p q in _
        | p, Result x q => fun _ =>
          let hyp6 := run_add_rec_q q in _
      end
      (refl_equal p)
    );
    match reverse goal with
      | hyp : ?foo |- _ =>
        assert foo by exact hyp;
          clear hyp; clear run_add_rec_p; clear run_add_rec_q
    end;
    try solve [destruct input; simpl; intuition];
    try solve [intros; subst p; simpl in *; apply H; assumption].
    
    subst p; simpl in *; intros.
    destruct H0; [ left | right ]; intuition.
    
    subst p; simpl in *; intros.  
    pose (H _ _ H0).
    unfold q1 in *.
    right; assumption.
  Qed.
  
  Theorem fair_choice
    {a} (p q : P a) (input : String) :
    forall (parse : a * String),
      (In parse (run p input) -> In parse (run (add p q) input)) /\
      (In parse (run q input) -> In parse (run (add p q) input)).
  intros; split; [ apply run_add | apply run_add' ].
  Qed.
  
  Theorem add_sound {a} (p q : P a) (input : String) :
    forall (parse : a * String),
      In parse (run (add p q) input) ->
      In parse (run p input) \/
      In parse (run q input).
    refine (fun a => _).
    refine (fix add_sound_rec_p (p : P a) {struct p} : P a -> _ := _).
    refine (fix add_sound_rec_q (q : P a) {struct q} : _ := _).
    refine (
      match p as p', q
      return p = p' -> _
      with
        | Get f, Get f' => fun _ =>
          let hyp1 := fun c => add_sound_rec_p (f c) (f' c) in _
        | Look f, Look f' => fun _ =>
          let hyp2 := fun s => add_sound_rec_p (f s) (f' s) in _
        | Look f, q => fun _ =>
          let hyp3 := fun s => add_sound_rec_p (f s) q in _
        | p, Look f => fun e1 =>
          let hyp4 := fun s => add_sound_rec_q (f s) in _
        | Fail, q => fun _ => _
        | p, Fail => fun _ => _
        | Result x p, q => fun _ =>
          let hyp5 := add_sound_rec_p p q in _
        | p, Result x q => fun _ =>
          let hyp6 := add_sound_rec_q q in _
      end
      (refl_equal p)
    );
    match reverse goal with
      | hyp : ?foo |- _ =>
        assert foo by exact hyp;
          clear hyp; clear add_sound_rec_p; clear add_sound_rec_q
    end; subst p;
    try solve [ simpl in *; intros; apply H; assumption ];
      try solve [ simpl in *; tauto ].
    
    destruct input; simpl in *; intros.
    tauto.
    apply H; assumption.
    
    simpl.
    intros.
    destruct H0.
    subst parse; tauto.
    cut (
         In parse match input with
            | nil => nil
            | c :: s => run (f c) s
            end \/ In parse (run q0 input)).
   tauto.
   apply H.
   assumption.
   
   simpl in *.
   intros.
   destruct H0.
   subst parse; tauto.
   cut (
     In parse (run p0 input) \/
     In parse match input with
                | nil => nil
                | c :: s => run (p2 c) s
              end
   ).
   tauto.
   apply H.
   assumption.
   
   simpl in *; intros.
   destruct H0.
   subst parse; tauto.
   cut  (
     In parse (run p0 input) \/
   (x0, input) = parse \/ In parse (run q0 input)).
   tauto.
   apply H.
   assumption.
 Qed.

