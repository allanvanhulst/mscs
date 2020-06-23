Require Import List.
Require Import Max.
Require Import Omega.

Axiom LEM : forall (P : Prop), P \/ ~ P.

Parameter A : Set.

Inductive T :=
  | zero : T
  | act : A -> T
  | plus : T -> T -> T
  | mult : T -> T -> T
  | star : T -> T -> T.

Notation "0" := zero.
Notation "p + q" := (plus p q).
Notation "p · q" := (mult p q) (at level 45, right associativity).
Notation "p * q" := (star p q).

Inductive V :=
  | term : V
  | emb : T -> V.

Inductive step : V -> A -> V -> Prop := 
  | step_act : forall (a : A), step (emb (act a)) a term
  | step_plus_left : forall (p q : T) (v : V) (a : A), 
    step (emb p) a v -> step (emb (p + q)) a v
  | step_plus_right : forall (p q : T) (v : V) (a : A),
    step (emb q) a v -> step (emb (p + q)) a v
  | step_mult_left : forall (p q p' : T) (a : A),
    step (emb p) a (emb p') -> step (emb (p · q)) a (emb (p' · q))
  | step_mult_right : forall (p q : T) (a : A),
    step (emb p) a term -> step (emb (p · q)) a (emb q)
  | step_star_left : forall (p q p' : T) (a : A),
    step (emb p) a (emb p') -> step (emb (p * q)) a (emb (p' · (p * q)))
  | step_star_term : forall (p q : T) (a : A),
    step (emb p) a term -> step (emb (p * q)) a (emb (p * q))
  | step_star_right : forall (p q : T) (a : A) (v : V),
    step (emb q) a v -> step (emb (p * q)) a v.

Notation "p '-(' a ')->' q" := (step p a q) (at level 30).

Definition bisim (u v : V) : Prop := exists (R : V -> V -> Prop),
  R u v /\ forall (x y : V), R x y -> 
    (x = term <-> y = term) /\
    (forall (a : A) (x' : V), x -(a)-> x' ->
      exists (y' : V), y -(a)-> y' /\ R x' y') /\
    (forall (a : A) (y' : V), y -(a)-> y' ->
      exists (x' : V), x -(a)-> x' /\ R x' y').

Inductive ax : T -> T -> Prop :=
  | refl : forall (x : T), ax x x
  | symm : forall (x y : T), ax x y -> ax y x
  | trans : forall (x y z : T), ax x y -> ax y z -> ax x z
  | comp_plus : forall (w x y z : T), ax w y -> ax x z -> ax (w + x) (y + z)
  | comp_mult : forall (w x y z : T), ax w y -> ax x z -> ax (w · x) (y · z)
  | comp_star : forall (w x y z : T), ax w y -> ax x z -> ax (w * x) (y * z)
  | B1 : forall (x y : T), ax (x + y) (y + x)
  | B2 : forall (x y z : T), ax ((x + y) + z) (x + (y + z))
  | B3 : forall (x : T), ax (x + x) x
  | B4 : forall (x y z : T), ax ((x + y) · z) (x · z + y · z)
  | B5 : forall (x y z : T), ax ((x · y) · z) (x · (y · z))
  | B6 : forall (x : T), ax (x + 0) x
  | B7 : forall (x : T), ax (0 · x) 0
  | BKS1 : forall (x y : T), ax (x · (x * y) + y) (x * y)
  | BKS2 : forall (x y z : T), ax ((x * y) · z) (x * (y · z))
  | RSP : forall (x y z : T), ax x (y · x + z) -> ax x (y * z).

Notation "u '<=>' v" := (bisim u v) (at level 25).
Notation "p '==' q"  := (ax p q) (at level 25).

Fixpoint sum (L : list (A * V)) : T :=
  match L with
  | nil => 0
  | (a, u) :: L' => match u with
                   | term => act a + sum L'
                   | emb p => act a · p + sum L'
                   end
  end.

Fixpoint mult_list (L : list (A * V)) (q : T) : list (A * V) :=
  match L with
  | nil => nil
  | (a, u) :: L' => match u with
                    | term => (a, emb q) :: mult_list L' q
                    | emb p => (a, emb (p · q)) :: mult_list L' q
                    end
  end.

Inductive clos_step : T -> T -> Prop :=
  | clos_refl : forall (p : T), clos_step p p
  | clos_trans : forall (p q r : T) (a : A),
    emb p -(a)-> emb q -> clos_step q r -> clos_step p r.

Definition clos_plus (p r : T) : Prop :=
  exists (a : A) (q : T), emb p -(a)-> emb q /\ clos_step q r.

Notation "p '-->*' q" := (clos_step p q) (at level 25).
Notation "p '-->+' q" := (clos_plus p q) (at level 25).

Definition congr (p q : T) : Prop :=
  forall (t : T), p -->+ t -> emb (t · q) <=> emb q -> False.

Fixpoint depth (p : T) : nat :=
  match p with
  | 0 => 0 % nat
  | act a => 0 % nat
  | r + s => max (depth r) (depth s)
  | r · s => max (depth r) (depth s)
  | r * s => max (1 + depth r) (depth s)
  end.

Definition bisimR (R : V -> V -> Prop) :=
  forall (u v : V), R u v ->
    (u = term <-> v = term) /\
    (forall (a : A) (u' : V), u -(a)-> u' ->
      exists (v' : V), v -(a)-> v' /\ R u' v') /\
    (forall (a : A) (v' : V), v -(a)-> v' ->
      exists (u' : V), u -(a)-> u' /\ R u' v').

Fixpoint Rclos (R : V -> V -> Prop) (n : nat) (x z : V) : Prop :=
  match n with
  | 0%nat => R x z
  | S n => exists (y : V), Rclos R n x y /\ R y z
  end.

Definition exRclos (R : V -> V -> Prop) (x y : V) : Prop :=
  exists (n : nat), Rclos R n x y.

Fixpoint nf_mult (p q : T) : Prop :=
  match p with
  | 0 => True
  | act a => True
  | r + s => nf_mult r q /\ nf_mult s q
  | r · s => nf_mult r (s · q) /\ nf_mult s q
  | r * s => nf_mult r (r * s · q) /\ nf_mult s q /\ congr r (r * s · q)
  end.

Fixpoint nf (p : T) : Prop :=
  match p with
  | 0 => True
  | act a => True
  | r + s => nf r /\ nf s
  | r · s => nf_mult r s /\ nf s
  | r * s => nf_mult r (r * s) /\ nf s /\ congr r (r * s)
  end.

Definition eqlist (M N : list (A * V)) : Prop :=
  forall (a : A) (u : V), In (a, u) M <-> In (a, u) N.

Definition mult' (u : V) (q : T) : T :=
  match u with
  | term => q
  | emb p => p · q
  end.

Definition teq (u v : V) : Prop :=
  match (u, v) with
  | (term, term) => True
  | (emb p, emb q) => p == q
  | _ => False
  end.

Lemma strong_ind : forall (P : nat -> Prop),
  (forall (n : nat), (forall (m : nat), m < n -> P m) -> P n) ->
    forall (n : nat), P n.
Proof.
  intros P H n ; apply H ; induction n ; intros m H' ; inversion H' ; auto.
Qed.

Lemma step_plus_fmt : forall (p q : T) (a : A) (u : V),
  emb (p + q) -(a)-> u -> emb p -(a)-> u \/ emb q -(a)-> u.
Proof.
  intros p q a u H ; inversion H ; auto.
Qed.

Lemma step_mult_fmt : forall (p q : T) (a : A) (u : V), emb (p · q) -(a)-> u ->
  (exists (p' : T), u = emb (p' · q) /\ emb p -(a)-> emb p') \/
  emb p -(a)-> term /\ u = emb q.
Proof.
  intros p q a u H ; inversion H ; eauto.
Qed.

Lemma step_star_fmt : forall (p q : T) (a : A) (u : V),
  emb (p * q) -(a)-> u ->
    (exists (p' : T), u = emb (p' · (p * q)) /\ emb p -(a)-> emb p') \/
    (u = emb (p * q) /\ emb p -(a)-> term) \/
    emb q -(a)-> u.
Proof.
  intros p q a u H ; inversion H ; eauto.
Qed.

Lemma step_gen_cases : forall (p : T) (a : A) (u : V), emb p -(a)-> u -> 
  (exists (p' : T), u = emb p' /\ emb p -(a)-> emb p') \/ u = term.
Proof.
  intro p ; induction p ; intros a' u H ; solve [ inversion H ; eauto ] || auto.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply IHp1 in H ; destruct H as [ H | H ] ; eauto.
  destruct H as [ p' [ Heq Hstep ] ] ; rewrite Heq in *.
  left ; exists p' ; split ; apply step_plus_left || auto ; auto.
  apply IHp2 in H ; destruct H as [ H | H ] ; eauto.
  destruct H as [ p' [ Heq Hstep ] ] ; rewrite Heq in *.
  left ; exists p' ; split ; apply step_plus_right || auto ; auto.
  apply step_mult_fmt in H ; destruct H as [ H | H ] ; eauto.
  destruct H as [ p' [ Heq Hstep ] ] ; rewrite Heq in *.
  left ; exists (p' · p2) ; split ; apply step_mult_left || auto ; auto.
  destruct H as [ Hstep Heq ] ; left ; exists p2 ; split ;
    apply step_mult_right || auto ; auto.
  apply step_star_fmt in H ; destruct H as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq Hstep ] ] ; rewrite Heq in *.
  left ; exists (p' · p1 * p2) ; split ;
    apply step_star_left || auto ; auto.
  destruct H as [ Heq Hstep ] ; rewrite Heq in *.
  left ; exists (p1 * p2) ; split ; apply step_star_term || auto ; auto.
  apply IHp2 in H ; destruct H as [ H | H ] ; auto.
  destruct H as [ p' [ Heq Hstep ] ] ; rewrite Heq in *.
  left ; exists p' ; split ; apply step_star_right || auto ; auto.
Qed.

Lemma bisim_next : forall (u v : V),
  (u = term <-> v = term) ->
  (forall (a : A) (u' : V), u -(a)-> u' ->
    exists (v' : V), v -(a)-> v' /\ u' <=> v') ->
  (forall (a : A) (v' : V), v -(a)-> v' ->
    exists (u' : V), u -(a)-> u' /\ u' <=> v') -> u <=> v.
Proof.
  intros u v Hiff Hltr Hrtl.
  exists (fun x y => x = u /\ y = v \/ x <=> y) ; split ; auto.
  intros x y H ; destruct H as [ [ Hu Hv ] | H ].
  rewrite Hu, Hv in * ; split ; auto ; split.
  intros a u' H ; apply Hltr in H ; destruct H as [ v' [ Hstep H ] ] ; eauto.
  intros a v' H ; apply Hrtl in H ; destruct H as [ u' [ Hstep H ] ] ; eauto.
  destruct H as [ R [ HinR HrelR ] ] ; apply HrelR in HinR ; split ; try tauto.
  split ; [ intros a x' H | intros a y' H ] ; apply HinR in H.
  destruct H as [ y' [ H HR ] ] ; exists y' ; split ; auto.
  right ; exists R ; split ; auto.
  destruct H as [ x' [ H HR ] ] ; exists x' ; split ; auto.
  right ; exists R ; split ; auto.
Qed.

Lemma bisim_fwd : forall (u v : V), u <=> v ->
  (u = term <-> v = term) /\
  (forall (a : A) (u' : V), u -(a)-> u' ->
    exists (v' : V), v -(a)-> v' /\ u' <=> v') /\ 
  (forall (a : A) (v' : V), v -(a)-> v' ->
    exists (u' : V), u -(a)-> u' /\ u' <=> v').
Proof.
  intros u v H ; destruct H as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  split ; [ tauto | split ].
  intros a u' H ; apply HinR in H.
  destruct H as [ v' [ H HR ] ] ; exists v' ; split ; auto.
  exists R ; split ; auto.
  intros a v' H ; apply HinR in H.
  destruct H as [ u' [ H HR ] ] ; exists u' ; split ; auto.
  exists R ; split ; auto.
Qed.

Lemma bisim_refl : forall (u : V), u <=> u.
Proof.
  intro u ; exists (fun x y => x = y) ; split ; auto.
  intros x y H ; rewrite H in * ; split ; [ tauto | split ] ; intros ; eauto.
Qed.

Lemma bisim_symm : forall (u v : V), u <=> v -> v <=> u.
Proof.
  intros u v H ; destruct H as [ R [ HinR HrelR ] ].
  exists (fun x y => R y x) ; split ; auto.
  intros x y H ; apply HrelR in H ; split ; [ tauto | split ].
  intros a x' H' ; apply H in H' ; eauto.
  intros a y' H' ; apply H in H' ; eauto.
Qed.

Lemma bisim_trans : forall (u v w : V), 
  u <=> v -> v <=> w -> u <=> w.
Proof.
  intros u v w H H'.
  destruct H as [ R [ HinR HrelR ] ].
  destruct H' as [ R' [ HinR' HrelR' ] ].
  exists (fun x z => exists (y : V), R x y /\ R' y z) ; split ; eauto.
  intros x z H ; destruct H as [ y [ HR HR' ] ].
  apply HrelR in HR ; apply HrelR' in HR' ; split ; [ tauto | split ].
  intros a x' H ; apply HR in H ; destruct H as [ y' [ H HRxy ] ].
  apply HR' in H ; destruct H as [ z' [ H HRyz ] ] ; eauto.
  intros a z' H ; apply HR' in H ; destruct H as [ y' [ H HRzy ] ].
  apply HR in H ; destruct H as [ x' [ H HRyx ] ] ; eauto.
Qed.

Lemma bisim_comp_plus : forall (p q r s : T),
  emb p <=> emb r -> emb q <=> emb s -> emb (p + q) <=> emb (r + s).
Proof.
  intros p q r s H H' ; apply bisim_fwd in H ; apply bisim_fwd in H'.
  apply bisim_next ; [ split ; intro H'' ; inversion H'' | | ].
  intros a u Hstep ; apply step_plus_fmt in Hstep.
  destruct Hstep as [ Hstep | Hstep ].
  apply H in Hstep ; destruct Hstep as [ r' [ Hstep Hbisim ] ].
  exists r' ; split ; auto ; apply step_plus_left ; auto.
  apply H' in Hstep ; destruct Hstep as [ s' [ Hstep Hbisim ] ].
  exists s' ; split ; auto ; apply step_plus_right ; auto.
  intros a u Hstep ; apply step_plus_fmt in Hstep.
  destruct Hstep as [ Hstep | Hstep ].
  apply H in Hstep ; destruct Hstep as [ p' [ Hstep Hbisim ] ].
  exists p' ; split ; auto ; apply step_plus_left ; auto.
  apply H' in Hstep ; destruct Hstep as [ q' [ Hstep Hbisim ] ].
  exists q' ; split ; auto ; apply step_plus_right ; auto.
Qed.
 
Lemma bisim_comp_mult : forall (p q r s : T),
  emb p <=> emb r -> emb q <=> emb s -> emb (p · q) <=> emb (r · s).
Proof.
  intros p q r s H H'.
  destruct H as [ R [ HinR HrelR ] ].
  destruct H' as [ R' [ HinR' HrelR' ] ].
  exists (fun u v => (exists (p' q' : T), u = emb (p' · q) /\ 
    v = emb (q' · s) /\ R (emb p') (emb q')) \/ R' u v) ; split.
  left ; exists p ; exists r ; tauto.
  intros u v H ; destruct H as [ H | H ].
  destruct H as [ p' [ q' [ Heq_u [ Heq_v HR ] ] ] ].
  rewrite Heq_u, Heq_v in * ; split ; [ | split ] ; clear Heq_u Heq_v u v.
  split ; intro H ; inversion H.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p'' [ Heq H ] ] ; rewrite Heq in *.
  apply HrelR in HR ; apply HR in H.
  destruct H as [ v [ H HR' ] ].
  apply step_gen_cases in H ; destruct H as [ H | H ].
  destruct H as [ q'' [ Heq_v H ] ] ; rewrite Heq_v in *.
  exists (emb (q'' · s)) ; split ; eauto.
  apply step_mult_left ; auto.
  left ; exists p'' ; exists q'' ; split ; auto.
  rewrite H in * ; apply HrelR in HR'.
  assert (term = term) as H' by auto.
  apply HR' in H' ; inversion H'.
  destruct H as [ H Heq_u ] ; rewrite Heq_u in *.
  apply HrelR in HR ; apply HR in H.
  destruct H as [ v [ H HR' ] ].
  assert (emb q' -(a)-> v) as Hstep_bak by auto.
  apply step_gen_cases in H ; destruct H as [ H | H ].
  destruct H as [ q'' [ Heq_v H ] ] ; rewrite Heq_v in *.
  apply HrelR in HR' ; assert (term = term) as H' by auto.
  apply HR' in H' ; inversion H'.
  rewrite H in * ; exists (emb s) ; split ; auto.
  apply step_mult_right ; auto.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ q'' [ Heq H ] ] ; rewrite Heq in *.
  apply HrelR in HR ; apply HR in H.
  destruct H as [ v [ H HR' ] ].
  apply step_gen_cases in H ; destruct H as [ H | H ].
  destruct H as [ p'' [ Heq_v H ] ] ; rewrite Heq_v in *.
  exists (emb (p'' · q)) ; split ; eauto.
  apply step_mult_left ; auto.
  left ; exists p'' ; exists q'' ; split ; auto.
  rewrite H in * ; apply HrelR in HR'.
  assert (term = term) as H' by auto.
  apply HR' in H' ; inversion H'.
  destruct H as [ H Heq_u ] ; rewrite Heq_u in *.
  apply HrelR in HR ; apply HR in H.
  destruct H as [ v [ H HR' ] ].
  assert (emb p' -(a)-> v) as Hstep_bak by auto.
  apply step_gen_cases in H ; destruct H as [ H | H ].
  destruct H as [ p'' [ Heq_v H ] ] ; rewrite Heq_v in *.
  apply HrelR in HR' ; assert (term = term) as H' by auto.
  apply HR' in H' ; inversion H'.
  rewrite H in * ; exists (emb q) ; split ; auto.
  apply step_mult_right ; auto.
  apply HrelR' in H ; split ; [ tauto | split ].
  intros a u' H' ; apply H in H'.
  destruct H' as [ v' [ H' HR' ] ] ; exists v' ; split ; auto.
  intros a u' H' ; apply H in H'.
  destruct H' as [ v' [ H' HR' ] ] ; exists v' ; split ; auto.
Qed.

Lemma bisim_comp_star : forall (p q r s : T),
  emb p <=> emb r -> emb q <=> emb s -> emb (p * q) <=> emb (r * s).
Proof.
  intros p q r s H H'.
  destruct H as [ R [ HinR HrelR ] ].
  destruct H' as [ R' [ HinR' HrelR' ] ].
  exists (fun u v => u = emb (p * q) /\ v = emb (r * s) \/
    (exists (p' r' : T), u = emb (p' · p * q) /\ v = emb (r' · r * s) /\
      R (emb p') (emb r')) \/ R' u v) ; split ; auto.
  intros u v H ; destruct H as [ H | [ H | H ] ].
  destruct H as [ Heq_u Heq_v ] ; rewrite Heq_u, Heq_v in *.
  clear Heq_u Heq_v u v ; split ; [ | split ].
  split ; intro H ; inversion H.
  intros a u H ; apply step_star_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq H ] ] ; rewrite Heq in *.
  apply HrelR in HinR ; apply HinR in H.
  destruct H as [ v [ Hstep HR ] ].
  apply step_gen_cases in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ r' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  exists (emb (r' · r * s)) ; split ; eauto.
  apply step_star_left ; auto.
  right ; left ; eauto.
  rewrite H in HR ; apply HrelR in HR.
  assert (term = term) as H' by auto ; apply HR in H' ; inversion H'.
  destruct H as [ [ Heq Hstep ] | Hstep ].
  exists (emb (r * s)) ; split ; auto.
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ v [ Hstep HR ] ].
  assert (emb r -(a)-> v) as Hstep_bak by auto.
  apply step_gen_cases in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ r' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  apply HrelR in HR ; assert (term = term) as H by auto.
  apply HR in H ; inversion H.
  rewrite H in * ; apply step_star_term ; auto.
  apply HrelR' in HinR' ; apply HinR' in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  exists v ; split ; auto.
  apply step_star_right ; auto.
  intros a u H ; apply step_star_fmt in H ; destruct H as [ H | H ].
  destruct H as [ r' [ Heq H ] ] ; rewrite Heq in *.
  apply HrelR in HinR ; apply HinR in H.
  destruct H as [ v [ Hstep HR ] ].
  apply step_gen_cases in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  exists (emb (p' · p * q)) ; split ; eauto.
  apply step_star_left ; auto.
  right ; left ; eauto.
  rewrite H in HR ; apply HrelR in HR.
  assert (term = term) as H' by auto ; apply HR in H' ; inversion H'.
  destruct H as [ [ Heq Hstep ] | Hstep ].
  exists (emb (p * q)) ; split ; auto.
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ v [ Hstep HR ] ].
  assert (emb p -(a)-> v) as Hstep_bak by auto.
  apply step_gen_cases in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  apply HrelR in HR ; assert (term = term) as H by auto.
  apply HR in H ; inversion H.
  rewrite H in * ; apply step_star_term ; auto.
  apply HrelR' in HinR' ; apply HinR' in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  exists v ; split ; auto.
  apply step_star_right ; auto.
  destruct H as [ p' [ r' [ Heq_u [ Heq_v HR ] ] ] ].
  rewrite Heq_u, Heq_v in * ; clear Heq_u Heq_v u v ; split ; [ | split ].
  split ; intro H ; inversion H.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p'' [ Heq Hstep ] ] ; rewrite Heq in *.
  apply HrelR in HR ; apply HR in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  apply step_gen_cases in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ r'' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  exists (emb (r'' · r * s)) ; split ; eauto.
  apply step_mult_left ; auto.
  right ; left ; eauto.
  rewrite H in * ; apply HrelR in HR'.
  assert (term = term) as H' by auto.
  apply HR' in H' ; inversion H'.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  apply HrelR in HR ; apply HR in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  assert (emb r' -(a)-> v) as Hstep_bak by auto.
  apply step_gen_cases in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ r'' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  apply HrelR in HR' ; assert (term = term) as H' by auto.
  apply HR' in H' ; inversion H'.
  rewrite H in * ; exists (emb (r * s)) ; split ; auto.
  apply step_mult_right ; auto.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ r'' [ Heq Hstep ] ] ; rewrite Heq in *.
  apply HrelR in HR ; apply HR in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  apply step_gen_cases in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p'' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  exists (emb (p'' · p * q)) ; split ; eauto.
  apply step_mult_left ; auto.
  right ; left ; eauto.
  rewrite H in * ; apply HrelR in HR'.
  assert (term = term) as H' by auto.
  apply HR' in H' ; inversion H'.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  apply HrelR in HR ; apply HR in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  assert (emb p' -(a)-> v) as Hstep_bak by auto.
  apply step_gen_cases in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p'' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  apply HrelR in HR' ; assert (term = term) as H' by auto.
  apply HR' in H' ; inversion H'.
  rewrite H in * ; exists (emb (p * q)) ; split ; auto.
  apply step_mult_right ; auto.
  apply HrelR' in H ; split ; [ tauto | split ].
  intros a u' Hstep ; apply H in Hstep.
  destruct Hstep as [ v' [ Hstep HR' ] ].
  exists v' ; split ; auto.
  intros a v' Hstep ; apply H in Hstep.
  destruct Hstep as [ u' [ Hstep HR' ] ].
  exists u' ; split ; auto.
Qed.

Lemma B1_sound : forall (p q : T), emb (p + q) <=> emb (q + p).
Proof.
  intros p q ; apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; inversion H.
  exists u ; split ; apply bisim_refl || auto.
  apply step_plus_right ; auto.
  exists u ; split ; apply bisim_refl || auto.
  apply step_plus_left ; auto.
  intros a u H ; inversion H.
  exists u ; split ; apply bisim_refl || auto.
  apply step_plus_right ; auto.
  exists u ; split ; apply bisim_refl || auto.
  apply step_plus_left ; auto.
Qed.

Lemma B2_sound : forall (p q r : T), 
  (emb ((p + q) + r)) <=> (emb (p + (q + r))).
Proof.
  intros p q r ; apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; exists u ; split ; apply bisim_refl || auto.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_plus_left ; auto.
  apply step_plus_right ; apply step_plus_left ; auto.
  apply step_plus_right ; apply step_plus_right ; auto.
  intros a u H ; exists u ; split ; apply bisim_refl || auto.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_plus_left ; apply step_plus_left ; auto.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_plus_left ; apply step_plus_right ; auto.
  apply step_plus_right ; auto.
Qed.

Lemma B3_sound : forall (p : T), (emb (p + p)) <=> (emb p).
Proof.
  intro p ; apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; inversion H ; exists u ; 
    split ; apply bisim_refl || auto.
  intros a u H ; exists u ; split ; apply bisim_refl ||
    apply step_plus_left ; auto.
Qed.

Lemma B4_sound : forall (p q r : T), 
  (emb ((p + q) · r)) <=> (emb (p · r + q · r)).
Proof.
  intros p q r ; apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; exists u ; split ; apply bisim_refl || auto.
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq H ] ] ; rewrite Heq in *.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_plus_left ; apply step_mult_left ; auto.
  apply step_plus_right ; apply step_mult_left ; auto.
  destruct H as [ H Heq ] ; rewrite Heq in *.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_plus_left ; apply step_mult_right ; auto.
  apply step_plus_right ; apply step_mult_right ; auto.
  intros a u H ; apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq H ] ] ; rewrite Heq in *.
  exists (emb (p' · r)) ; split ; apply bisim_refl || auto.
  apply step_mult_left ; apply step_plus_left ; auto.
  destruct H as [ H Heq ] ; rewrite Heq in *.
  exists (emb r) ; split ; apply bisim_refl || auto.
  apply step_mult_right ; apply step_plus_left ; auto.
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ q' [ Heq H ] ] ; rewrite Heq in *.
  exists (emb (q' · r)) ; split ; apply bisim_refl || auto.
  apply step_mult_left ; apply step_plus_right ; auto.
  destruct H as [ H Heq ] ; rewrite Heq in *.
  exists (emb r) ; split ; apply bisim_refl || auto.
  apply step_mult_right ; apply step_plus_right ; auto.
Qed.

Lemma B5_sound : forall (p q r : T),
  (emb ((p · q) · r)) <=> (emb (p · (q · r))).
Proof.
  intros p q r ; exists (fun u v => (exists (p' : T), u = emb ((p' · q) · r) /\ 
    v = emb (p' · q · r)) \/ u = v) ; split ; eauto.
  intros u v H ; destruct H as [ [ p' [ Heq_u Heq_v ] ] | H ].
  rewrite Heq_u, Heq_v in * ; split ; [ | split ] ; clear Heq_u Heq_v u v.
  split ; intro H ; inversion H.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ v [ Heq Hstep ] ] ; rewrite Heq in *.
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p'' [ Heq' Hstep ] ].
  exists (emb (p'' · q · r)) ; split.
  apply step_mult_left ; auto.
  left ; exists p'' ; split ; auto.
  replace v with (p'' · q) in * by ( inversion Heq' ; auto ) ; auto.
  destruct H as [ Hstep Heq' ].
  replace v with q in * by ( inversion Heq' ; auto ).
  exists (emb (q · r)) ; split ; auto.
  apply step_mult_right ; auto.
  destruct H as [ Hstep Heq ] ; inversion Hstep.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p'' [ Heq Hstep ] ].
  exists (emb ((p'' · q) · r)) ; split ; eauto.
  apply step_mult_left ; apply step_mult_left ; auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  exists (emb (q · r)) ; split ; auto.
  apply step_mult_left ; apply step_mult_right ; auto.
  rewrite H in * ; split ; [ tauto | split ] ; intros ; eauto.
Qed.

Lemma B6_sound : forall (p : T), (emb (p + 0)) <=> emb p.
Proof.
  intro p ; apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; inversion H.
  exists u ; split ; apply bisim_refl || auto.
  assert (emb 0 -(a)-> u) as H' by auto ; inversion H'.
  intros a u H ; exists u ; split ; apply bisim_refl ||
    apply step_plus_left ; auto.
Qed.

Lemma B7_sound : forall (p : T), (emb (0 · p)) <=> emb 0.
Proof.
  intro p ; apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; inversion H.
  assert (exists (x : T), emb 0 -(a)-> emb x) as H' by eauto.
  destruct H' as [ x H' ] ; inversion H'.
  assert (emb 0 -(a)-> term) as H' by auto ; inversion H'.
  intros a u H ; inversion H.
Qed.

Lemma BKS1_sound : forall (p q : T), emb (p · (p * q) + q) <=> emb (p * q).
Proof.
  intros p q ; apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; apply step_plus_fmt in H ; destruct H as [ H | H ].
  exists u ; split ; apply bisim_refl || auto.
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq H ] ] ; rewrite Heq in *.
  apply step_star_left ; auto.
  destruct H as [ H Heq ] ; rewrite Heq in *.
  apply step_star_term ; auto.
  exists u ; split ; apply bisim_refl || auto.
  apply step_star_right ; auto.
  intros a u H ; apply step_star_fmt in H.
  destruct H as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq H ] ] ; rewrite Heq in *.
  exists (emb (p' · p * q)) ; split ; apply bisim_refl || auto.
  apply step_plus_left ; apply step_mult_left ; auto.
  destruct H as [ Heq H ] ; rewrite Heq in *.
  exists (emb (p * q)) ; split ; apply bisim_refl || auto.
  apply step_plus_left ; apply step_mult_right ; auto.
  exists u ; split ; apply bisim_refl || auto.
  apply step_plus_right ; auto.
Qed.

Lemma BKS2_sound : forall (p q r : T), emb ((p * q) · r) <=> emb (p * (q · r)).
Proof.
  intros p q r.
  exists (fun u v => u = emb (p * q · r) /\ v = emb (p * (q · r)) \/ 
    (exists (p' : T), u = emb ((p' · p * q) · r) /\ 
      v = emb (p' · p * (q · r))) \/ u = v) ; split ; auto.
  intros u v H ; destruct H as [ H | [ H | H ] ].
  destruct H as [ Heq_u Heq_v ] ; rewrite Heq_u, Heq_v in *.
  clear Heq_u Heq_v u v ; split ; [ | split ].
  split ; intro H ; inversion H.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ s [ Heq H ] ] ; apply step_star_fmt in H.
  destruct H as [ H | H ].
  destruct H as [ p' [ Heq' Hstep ] ].
  replace s with (p' · p * q) in * by ( inversion Heq' ; auto ).
  exists (emb (p' · p * (q · r))) ; split ; eauto.
  apply step_star_left ; auto.
  destruct H as [ [ Heq' Hstep ] | Hstep ].
  exists (emb (p * (q · r))) ; split ; auto.
  apply step_star_term ; auto.
  replace s with (p * q) in * by ( inversion Heq' ; auto ) ; auto.
  exists (emb (s · r)) ; split ; auto.
  apply step_star_right ; apply step_mult_left ; auto.
  exists (emb r) ; split ; tauto || auto.
  apply step_star_right ; destruct H as [ Hstep Heq ].
  inversion Hstep ; apply step_mult_right ; auto.
  intros a u H ; apply step_star_fmt in H.
  destruct H as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq Hstep ] ].
  exists (emb ((p' · p * q) · r)) ; split ; eauto.
  apply step_mult_left ; apply step_star_left ; auto.
  destruct H as [ Heq Hstep ].
  exists (emb (p * q · r)) ; split ; auto.
  apply step_mult_left ; apply step_star_term ; auto.
  exists u ; split ; auto.
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ q' [ Heq Hstep ] ] ; rewrite Heq in *.
  apply step_mult_left ; apply step_star_right ; auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  apply step_mult_right ; apply step_star_right ; auto.
  destruct H as [ p' [ Heq_u Heq_v ] ] ; rewrite Heq_u, Heq_v in *.
  clear Heq_u Heq_v u v ; split ; [ | split ].
  split ; intro H ; inversion H.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ s [ Heq Hstep ] ] ; rewrite Heq in *.
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p'' [ Heq' Hstep ] ].
  replace s with (p'' · p * q) in * by ( inversion Heq' ; auto ).
  exists (emb (p'' · p * (q · r))) ; split ; eauto.
  apply step_mult_left ; auto.
  destruct H as [ Hstep Heq' ].
  replace s with (p * q) in * by ( inversion Heq' ; auto ).
  exists (emb (p * (q · r))) ; split ; auto.
  apply step_mult_right ; auto.
  destruct H as [ Hstep Heq ] ; inversion Hstep.
  intros a u H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p'' [ Heq Hstep ] ] ; rewrite Heq in *.
  exists (emb ((p'' · p * q) · r)) ; split ; eauto.
  apply step_mult_left ; apply step_mult_left ; auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  exists (emb (p * q · r)) ; split ; auto.
  apply step_mult_left ; apply step_mult_right ; auto.
  rewrite H in * ; split ; [ tauto | split ] ; intros ; eauto.
Qed.

Lemma ex_clos_bisim : forall (R : V -> V -> Prop),
  bisimR R -> bisimR (exRclos R).
Proof.
  intros R HbisimR ; unfold bisimR in *.
  intros u v H ; destruct H as [ n HexR ] ; revert HexR ; revert u v.
  induction n ; intros u v HexR.
  simpl in HexR ; apply HbisimR in HexR ; split ; [ | split ] ; try tauto.
  intros a u' Hstep ; apply HexR in Hstep.
  destruct Hstep as [ v' [ Hstep HR ] ] ; exists v' ; split ; auto.
  exists 0%nat ; simpl ; auto.
  intros a v' Hstep ; apply HexR in Hstep.
  destruct Hstep as [ u' [ Hstep HR ] ] ; exists u' ; split ; auto.
  exists 0%nat ; simpl ; auto.
  simpl in HexR ; destruct HexR as [ w [ Hclos HR ] ].
  apply IHn in Hclos ; apply HbisimR in HR.
  split ; [ | split ] ; try tauto.
  intros a u' Hstep ; apply Hclos in Hstep.
  destruct Hstep as [ w' [ Hstep Hclos' ] ].
  apply HR in Hstep ; destruct Hstep as [ v' [ Hstep HR' ] ].
  exists v' ; split ; auto.
  destruct Hclos' as [ k Hclos' ].
  exists (S k) ; simpl ; eauto.
  intros a v' Hstep ; apply HR in Hstep.
  destruct Hstep as [ w' [ Hstep HR' ] ].
  apply Hclos in Hstep ; destruct Hstep as [ u' [ Hstep Hclos' ] ].
  exists u' ; split ; auto.
  destruct Hclos' as [ k Hclos' ].
  exists (S k) ; simpl ; eauto.
Qed.

Lemma RSP_sound : forall (p q r : T), 
  emb p <=> emb (q · p + r) -> emb p <=> emb (q * r).
Proof.
  intros p q r H ; destruct H as [ R [ HinR HrelR ] ].
  assert (bisimR (exRclos R)) as Hex_bisim.
  apply ex_clos_bisim ; unfold bisimR ; auto.
  exists (fun u v => u = emb p /\ v = emb (q * r) \/
    (exists (p' q' : T), u = emb p' /\ v = emb (q' · q * r) /\
      exRclos R (emb p') (emb (q' · p))) \/
    (exists (p' : T), u = emb p' /\ v = emb (q * r) /\
      exRclos R (emb p') (emb p)) \/ exRclos R u v) ; split ; auto.

  (* Start case, i.e. p and q * r *)
  intros u v H ; destruct H as [ [ Heq_u Heq_v ] | H ].
  rewrite Heq_u, Heq_v in * ; clear Heq_u Heq_v u v ; split ; [ | split ].
  split ; intro H ; inversion H.
  intros a u Hstep ; apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ v [ Hstep HR ] ] ; apply step_plus_fmt in Hstep.
  destruct Hstep as [ Hstep | Hstep ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ q' [ Heq Hstep ] ] ; rewrite Heq in *.
  exists (emb (q' · q * r)) ; split.
  apply step_star_left ; auto.
  destruct u as [ | p' ].
  apply HrelR in HR ; assert (term = term) as H by auto.
  apply HR in H ; inversion H.
  right ; left ; exists p' ; exists q' ; split ; [ | split ] ; auto.
  exists 0%nat ; simpl ; auto.
  destruct H as [ Hstep_q Heq ] ; rewrite Heq in *.
  destruct u as [ | p' ].
  apply HrelR in HR ; assert (term = term) as H by auto.
  apply HR in H ; inversion H.
  exists (emb (q * r)) ; split ; apply step_star_term || auto ; auto.
  right ; right ; left ; exists p' ; split ; [ | split ] ; auto.
  exists 0%nat ; simpl ; auto.
  exists v ; split ; apply step_star_right || auto ; auto.
  right ; right ; right ; exists 0%nat ; simpl ; auto.
  intros a v H ; apply step_star_fmt in H ; destruct H as [ H | [ H | ] ].
  destruct H as [ q' [ Heq Hstep ] ] ; rewrite Heq in *.
  assert (emb (q · p + r) -(a)-> emb (q' · p)) as Hstep_qp by
    ( apply step_plus_left ; apply step_mult_left ; auto ).
  apply HrelR in HinR ; apply HinR in Hstep_qp.
  destruct Hstep_qp as [ u [ Hstep_p HR ] ].
  destruct u as [ | p' ] ; [ apply HrelR in HR | ].
  assert (term = term) as H by auto ; apply HR in H ; inversion H.
  exists (emb p') ; split ; auto.
  right ; left ; exists p' ; exists q' ; split ; [ | split ] ; auto.
  exists 0%nat ; simpl ; auto.
  destruct H as [ Heq Hstep_q ] ; rewrite Heq in *.
  assert (emb (q · p + r) -(a)-> emb p) as H by
    ( apply step_plus_left ; apply step_mult_right ; auto ).
  apply HrelR in HinR ; apply HinR in H.
  destruct H as [ u [ Hstep_p HR ] ].
  destruct u as [ | p' ] ; [ apply HrelR in HR | ].
  assert (term = term) as H by auto ; apply HR in H ; inversion H.
  exists (emb p') ; split ; auto.
  right ; right ; left ; exists p' ; split ; [ | split ] ; auto.
  exists 0%nat ; simpl ; auto.
  assert (emb (q · p + r) -(a)-> v) as Hstep by
    ( apply step_plus_right ; auto ).
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ u [ Hstep HR ] ] ; exists u ; split ; auto.
  right ; right ; right ; exists 0%nat ; simpl ; auto.

  (* Case for (p', q'q * r) such that (p', q'p) in R-closure *)
  destruct H as [ H | H ].
  destruct H as [ p' [ q' [ Heq_u [ Heq_v HRclos ] ] ] ].
  rewrite Heq_u, Heq_v in * ; clear Heq_u Heq_v u v.
  apply Hex_bisim in HRclos ; split ; [ | split ].
  split ; intro H ; inversion H.
  intros a u Hstep ; apply HRclos in Hstep.
  destruct Hstep as [ v [ Hstep HexR ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ q'' [ Heq Hstep ] ] ; rewrite Heq in *.
  exists (emb (q'' · q * r)) ; split ; auto.
  apply step_mult_left ; auto.
  destruct u as [ | p'' ] ; [ apply Hex_bisim in HexR | ].
  assert (term = term) as H by auto ; apply HexR in H ; inversion H.
  right ; left ; exists p'' ; exists q'' ; split ; [ | split ] ; auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  exists (emb (q * r)) ; split ; auto.
  apply step_mult_right ; auto.
  destruct u as [ | p'' ] ; [ apply Hex_bisim in HexR | ].
  assert (term = term) as H by auto ; apply HexR in H ; inversion H.
  right ; right ; left ; exists p'' ; split ; [ | split ] ; auto.
  intros a v H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ q'' [ Heq Hstep ] ] ; rewrite Heq in *.
  assert (emb (q' · p) -(a)-> emb (q'' · p)) as H by
    ( apply step_mult_left ; auto ).
  apply HRclos in H ; destruct H as [ u [ Hstep' HclosR ] ].
  destruct u as [ | p'' ].
  apply ex_clos_bisim in HclosR ; auto.
  assert (term = term) as H by auto ; apply HclosR in H ; inversion H.
  exists (emb p'') ; split ; auto.
  right ; left ; exists p'' ; exists q'' ; split ; auto.
  destruct H as [ Hstep_q' Heq ] ; rewrite Heq in *.
  assert (emb (q' · p) -(a)-> emb p) as H by ( apply step_mult_right ; auto ).
  apply HRclos in H ; destruct H as [ u [ Hstep_p' Hclos' ] ].
  destruct u as [ | p'' ].
  apply ex_clos_bisim in Hclos' ; auto.
  assert (term = term) as H by auto ; apply Hclos' in H ; inversion H.
  exists (emb p'') ; split ; auto.
  right ; right ; left ; eauto.

  (* Case for (p', q * r) such that (p', p) in R-closure *)
  destruct H as [ H | H ].
  destruct H as [ p' [ Heq_u [ Heq_v Hclos ] ] ].
  rewrite Heq_u, Heq_v in * ; clear Heq_u Heq_v u v ; split ; [ | split ].
  split ; intro H ; inversion H.
  intros a u Hstep ; apply ex_clos_bisim in Hclos ; auto.
  apply Hclos in Hstep ; destruct Hstep as [ v [ Hstep Hclos' ] ].
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ w [ Hstep HR' ] ].
  apply step_plus_fmt in Hstep ; destruct Hstep as [ H | Hstep ].
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ q' [ Heq Hstep_q ] ] ; rewrite Heq in *.
  exists (emb (q' · q * r)) ; split ; auto.
  apply step_star_left ; auto.
  right ; left ; destruct u as [ | p'' ].
  destruct v as [ | r' ].
  apply HrelR in HR' ; assert (term = term) as H by auto.
  apply HR' in H ; inversion H.
  apply ex_clos_bisim in Hclos' ; auto.
  assert (term = term) as H by auto ; apply Hclos' in H ; inversion H.
  exists p'' ; exists q' ; split ; [ | split ] ; eauto.
  destruct Hclos' as [ k H ] ; exists (S k) ; simpl ; eauto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  exists (emb (q * r)) ; split ; [ apply step_star_term | ] ; auto.
  right ; right ; left ; destruct u as [ | p'' ].
  destruct v as [ | r' ].
  apply HrelR in HR' ; assert (term = term) as H by auto.
  apply HR' in H ; inversion H.
  apply ex_clos_bisim in Hclos' ; auto.
  assert (term = term) as H by auto ; apply Hclos' in H ; inversion H.
  exists p'' ; split ; [ | split ] ; auto.
  destruct Hclos' as [ k Hclos' ].
  exists (S k) ; simpl ; eauto.
  exists w ; split ; [ apply step_star_right | ] ; auto.
  right ; right ; right.
  destruct Hclos' as [ k Hclos' ].
  exists (S k) ; simpl ; eauto.
  intros a v Hstep ; apply step_star_fmt in Hstep.
  destruct Hstep as [ H | [ H | H ] ].
  destruct H as [ q' [ Heq Hstep ] ] ; rewrite Heq in *.
  assert (emb (q · p + r) -(a)-> emb (q' · p)) as H by
    ( apply step_plus_left ; apply step_mult_left ; auto ).
  apply HrelR in HinR ; apply HinR in H.
  destruct H as [ u [ Hstep' HR' ] ].
  apply Hex_bisim in Hclos ; apply Hclos in Hstep'.
  destruct Hstep' as [ w [ Hstep' Hclos' ] ] ; exists w ; split ; auto.
  right ; left ; destruct w as [ | p'' ].
  destruct u as [ | r' ] ; apply HrelR in HR' ; auto.
  assert (term = term) as H by auto ; apply HR' in H ; inversion H.
  apply Hex_bisim in Hclos' ; assert (term = term) as H by auto.
  apply Hclos' in H ; inversion H.
  exists p'' ; exists q' ; split ; [ | split ] ; auto.
  destruct Hclos' as [ k Hclos' ] ; exists (S k) ; simpl ; eauto.
  destruct H as [ Heq Hstep ] ; rewrite Heq in *.
  assert (emb (q · p + r) -(a)-> emb p) as H by
    ( apply step_plus_left ; apply step_mult_right ; auto ).
  apply HrelR in HinR ; apply HinR in H.
  destruct H as [ u [ Hstep' HR' ] ].
  apply Hex_bisim in Hclos ; apply Hclos in Hstep'.
  destruct Hstep' as [ w [ Hstep' Hclos' ] ] ; exists w ; split ; auto.
  right ; right ; left ; destruct w as [ | p'' ].
  destruct u as [ | r' ] ; apply HrelR in HR'.
  assert (term = term) as H by auto ; apply HR' in H ; inversion H.
  apply Hex_bisim in Hclos' ; assert (term = term) as H by auto.
  apply Hclos' in H ; inversion H.
  exists p'' ; split ; [ | split ] ; auto.
  destruct Hclos' as [ k Hclos' ] ; exists (S k) ; simpl ; eauto.
  assert (emb (q · p + r) -(a)-> v) as Hstep by
    ( apply step_plus_right ; auto ).
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ u [ Hstep HR' ] ].
  apply Hex_bisim in Hclos ; apply Hclos in Hstep.
  destruct Hstep as [ w [ Hstep Hclos' ] ].
  exists w ; split ; auto.
  right ; right ; right ; destruct Hclos' as [ k Hclos' ].
  exists (S k) ; simpl ; eauto.

  (* Final and simplest case: (u,v) in R-closure *)
  apply Hex_bisim in H ; split ; [ | split ] ; tauto || auto.
  intros a u' Hstep ; apply H in Hstep.
  destruct Hstep as [ v' [ Hstep Hclos ] ] ; exists v' ; split ; auto.
  intros a v' Hstep ; apply H in Hstep.
  destruct Hstep as [ u' [ Hstep Hclos ] ] ; exists u' ; split ; auto.
Qed.

Lemma soundness : forall (p q : T), p == q -> emb p <=> emb q.
Proof.
  intros p q H ; induction H.
  apply bisim_refl.
  apply bisim_symm ; auto.
  apply bisim_trans with (emb y) ; auto.
  apply bisim_comp_plus ; auto.
  apply bisim_comp_mult ; auto.
  apply bisim_comp_star ; auto.
  apply B1_sound.
  apply B2_sound.
  apply B3_sound.
  apply B4_sound.
  apply B5_sound.
  apply B6_sound.
  apply B7_sound.
  apply BKS1_sound.
  apply BKS2_sound.
  apply RSP_sound ; auto.
Qed.

Lemma in_mult_list_term : forall (L : list (A * V)) (a : A) (q : T),
  In (a, term) L -> In (a, emb q) (mult_list L q).
Proof.
  intro L ; induction L as [ | [ a u ] ] ; intros a' q Hin ; simpl in * ; auto.
  destruct u as [ | p ] ; [ destruct Hin as [ H | H ] | ].
  replace a' with a in * by ( inversion H ; auto ) ; simpl ; auto.
  apply IHL with (q := q) in H ; simpl ; auto.
  destruct Hin as [ H | H ] ; [ inversion H | simpl ; right ; auto ].
Qed.

Lemma in_mult_list_mult : forall (L : list (A * V)) (a : A) (p q : T),
  In (a, emb p) L -> In (a, emb (p · q)) (mult_list L q).
Proof.
  intro L ; induction L as [ | [ a u ] ] ; intros a' p q Hin ; simpl in *; auto.
  destruct u as [ | r ] ; [ destruct Hin as [ H | H ] ; [ inversion H | ] | ].
  apply IHL with (q := q) in H ; simpl ; auto.
  destruct Hin as [ H | H ] ; [ | simpl ; right ; auto ].
  replace r with p in * by ( inversion H ; auto ).
  replace a' with a in * by ( inversion H ; auto ).
  simpl in * ; auto.
Qed.

Lemma in_mult_list_cases : forall (L : list (A * V)) (a : A) (u : V) (q : T),
  In (a, u) (mult_list L q) -> u = emb q /\ In (a, term) L \/
    exists (p : T), u = emb (p · q) /\ In (a, emb p) L.
Proof.
  intro L ; induction L as [ | [ a v ] L ] ; 
    intros a' u q Hin ; simpl in * ; contradiction || auto.
  destruct v as [ | s ] ; simpl in *.
  destruct Hin as [ H | H ] ; auto.
  replace a' with a in * by ( inversion H ; auto ).
  replace u with (emb q) in * by ( inversion H ; auto ) ; tauto.
  apply IHL in H ; destruct H as [ H | H ] ; [ tauto | ].
  destruct H as [ p [ Heq Hin ] ] ; rewrite Heq in * ; eauto.
  destruct Hin as [ H | H ].
  replace a' with a in * by ( inversion H ; auto ).
  replace u with (emb (s · q)) in * by ( inversion H ; auto ).
  right ; exists s ; split ; auto.
  apply IHL in H ; destruct H as [ H | H ] ; [ tauto | ].
  destruct H as [ p [ Heq Hin ] ] ; rewrite Heq in *.
  right ; exists p ; split ; auto.
Qed.
  
Lemma sum_app : forall (M N : list (A * V)), sum (M ++ N) == (sum M + sum N).
Proof.
  intro M ; induction M as [ | [ a u ] M ] ; intro N ; simpl.
  apply symm ; apply trans with (sum N + 0) ; apply B1 || apply B6.
  destruct u as [ | p ].
  apply trans with (act a + (sum M + sum N)).
  apply comp_plus ; apply refl || auto.
  apply symm ; apply B2.
  apply trans with (act a · p + (sum M + sum N)).
  apply comp_plus ; apply refl || auto.
  apply symm ; apply B2.
Qed.

Lemma sum_mult_list : forall (M : list (A * V)) (q : T),
  sum (mult_list M q) == (sum M · q).
Proof.
  intro M ; induction M as [ | [ a u ] ] ; intro q ; simpl.
  apply symm ; apply B7.
  destruct u as [ | p ] ; simpl.
  apply trans with (act a · q + sum M · q).
  apply comp_plus ; apply refl || auto.
  apply symm ; apply B4.
  apply trans with ((act a · p) · q + sum M · q).
  apply comp_plus ; auto.
  apply symm ; apply B5.
  apply symm ; apply B4.
Qed.

Lemma summation : forall (p : T), exists (L : list (A * V)), 
  (forall (a : A) (u :V), emb p -(a)-> u <-> In (a, u) L) /\ sum L == p.
Proof.
  intro p ; induction p.
  exists nil ; split ; simpl ; apply refl || auto.
  intros a u ; split ; intro H ; contradiction || inversion H.
  exists ((a, term) :: nil) ; split ; simpl ; [ | apply B6 ].
  intros a' u ; split ; intro H ; [ inversion H ; auto | ].
  destruct H as [ H | H ] ; contradiction || auto.
  replace a' with a in * by ( inversion H ; auto ).
  replace u with term in * by ( inversion H ; auto ).
  apply step_act ; auto.

  (* Case for p1 + p2 starts here *)
  destruct IHp1 as [ L1 [ Hiff_L1 Hsum_L1 ] ].
  destruct IHp2 as [ L2 [ Hiff_L2 Hsum_L2 ] ].
  exists (L1 ++ L2) ; split.
  intros a u ; split ; intro H.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply in_or_app ; left ; apply Hiff_L1 ; auto.
  apply in_or_app ; right ; apply Hiff_L2 ; auto.
  apply in_app_or in H ; destruct H as [ H | H ].
  apply step_plus_left ; apply Hiff_L1 ; auto.
  apply step_plus_right ; apply Hiff_L2 ; auto.
  apply trans with (sum L1 + sum L2) ; [ apply sum_app | ].
  apply comp_plus ; auto.

  (* Case for p1 · p2 starts here *)
  destruct IHp1 as [ L1 [ Hiff_L1 Hsum_L1 ] ].
  exists (mult_list L1 p2) ; split.
  intros a u ; split ; intro H.
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq H ] ] ; rewrite Heq in *.
  apply in_mult_list_mult ; apply Hiff_L1 in H ; auto.
  destruct H as [ H Heq ] ; rewrite Heq in *.
  apply in_mult_list_term ; apply Hiff_L1 ; auto.
  apply in_mult_list_cases in H.
  destruct H as [ [ Heq H ] | [ p [ Heq H ] ] ] ; rewrite Heq in *.
  apply Hiff_L1 in H ; apply step_mult_right ; auto.
  apply step_mult_left ; apply Hiff_L1 ; auto.
  apply trans with (sum L1 · p2).
  apply sum_mult_list.
  apply comp_mult ; apply refl || auto.

  (* Case for p1 * p2 starts here *)
  destruct IHp1 as [ L1 [ Hiff_L1 Hsum_L1 ] ].
  destruct IHp2 as [ L2 [ Hiff_L2 Hsum_L2 ] ].
  exists (mult_list L1 (p1 * p2) ++ L2) ; split.
  intros a u ; split ; intro H.
  apply step_star_fmt in H ; destruct H as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq H ] ] ; rewrite Heq in *.
  apply in_or_app ; left ; apply in_mult_list_mult ; apply Hiff_L1 ; auto.
  destruct H as [ Heq H ] ; rewrite Heq in *.
  apply in_or_app ; left ; apply in_mult_list_term ; apply Hiff_L1 ; auto.
  apply in_or_app ; right ; apply Hiff_L2 ; auto.
  apply in_app_or in H ; destruct H as [ H | H ].
  apply in_mult_list_cases in H ; destruct H as [ H | H ].
  destruct H as [ Heq H ] ; rewrite Heq in *.
  apply Hiff_L1 in H ; apply step_star_term ; auto.
  destruct H as [ p [ Heq H ] ] ; rewrite Heq in *.
  apply step_star_left ; apply Hiff_L1 ; auto.
  apply step_star_right ; apply Hiff_L2 ; auto.
  apply trans with (p1 · p1 * p2 + p2) ; [ | apply BKS1 ].
  apply trans with (sum (mult_list L1 (p1 * p2)) + sum L2) ; 
    [ apply sum_app | apply comp_plus ; auto ].
  apply trans with (sum L1 · p1 * p2).
  apply sum_mult_list ; auto.
  apply comp_mult ; apply refl || auto.
Qed.

Lemma clos_end_step : forall (p q r : T) (a : A),
  p -->+ q -> emb q -(a)-> emb r -> p -->+ r.
Proof.
  intros p q r a H H'.
  destruct H as [ a' [ s [ Hstep Htr ] ] ].
  exists a' ; exists s ; split ; auto.
  clear Hstep p a' ; revert H' ; revert a r.
  induction Htr ; intros a' s Hstep.
  apply clos_trans with s a' ; apply clos_refl || auto.
  apply IHHtr in Hstep.
  apply clos_trans with q a ; auto.
Qed.

Lemma congruence : forall (p q r : T), emb (p · r) <=> emb (q · r) ->
  congr (p + q) r -> emb p <=> emb q.
Proof.
  intros p q r Hbisim Hcongr.
  destruct Hbisim as [ R [ HinR HrelR ] ].
  exists (fun u v => u = term /\ v = term \/ u = emb p /\ v = emb q \/
    exists (p' q' : T), u = emb p' /\ v = emb q' /\ p -->+ p' /\
      q -->+ q' /\ R (emb (p' · r)) (emb (q' · r))) ; split ; auto.
  intros x y H ; destruct H as [ H | [ H | H ] ].
  destruct H as [ Heq_x Heq_y ] ; rewrite Heq_x, Heq_y in *.
  split ; [ tauto | split ; intros a u H ; inversion H ].

  (* Case for p, q (i.e. start case) *)
  destruct H as [ Heq_x Heq_y ] ; rewrite Heq_x, Heq_y in *.
  split ; [ split ; intro H ; inversion H | split ].
  intros a u H ; assert (emb p -(a)-> u) as Hstep_bak by auto.
  apply step_gen_cases in H.
  destruct H as [ H | H ].
  destruct H as [ p' [ Heq H ] ] ; rewrite Heq in *.
  assert (emb (p · r) -(a)-> emb (p' · r)) as Hstep by
    ( apply step_mult_left ; auto ).
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ v [ Hstep HR ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H' | H' ].
  destruct H' as [ q' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  exists (emb q') ; split ; auto.
  right ; right ; exists p' ; exists q' ; split ; auto ; split ; auto ; split.
  exists a ; exists p' ; split ; auto ; apply clos_refl.
  split ; [ exists a ; exists q' ; split ; auto ; apply clos_refl | auto ].
  destruct H' as [ Hstep Heq' ] ; rewrite Heq' in *.
  assert (emb (p' · r) <=> emb r) as Hbisim by ( exists R ; split ; auto ).
  apply Hcongr in Hbisim ; contradiction || auto.
  exists a ; exists p' ; split ; apply clos_refl || auto.
  apply step_plus_left ; auto.
  rewrite H in * ; clear H u.
  assert (emb (p · r) -(a)-> emb r) as Hstep by 
    ( apply step_mult_right ; auto ).
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ v [ Hstep HR ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ q' [ Heq Hstep ] ] ; rewrite Heq in *.
  assert (emb (q' · r) <=> emb r) as Hbisim.
  apply bisim_symm ; exists R ; split ; auto.
  apply Hcongr in Hbisim ; contradiction || auto.
  exists a ; exists q' ; split ; apply clos_refl || auto.
  apply step_plus_right ; auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  exists term ; split ; auto.
  intros a u H ; assert (emb q -(a)-> u) as Hstep_bak by auto.
  apply step_gen_cases in H.
  destruct H as [ H | H ].
  destruct H as [ q' [ Heq H ] ] ; rewrite Heq in *.
  assert (emb (q · r) -(a)-> emb (q' · r)) as Hstep by
    ( apply step_mult_left ; auto ).
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ v [ Hstep HR ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H' | H' ].
  destruct H' as [ p' [ Heq' Hstep ] ] ; rewrite Heq' in *.
  exists (emb p') ; split ; auto.
  right ; right ; exists p' ; exists q' ; split ; auto ; split ; auto ; split.
  exists a ; exists p' ; split ; auto ; apply clos_refl.
  split ; [ exists a ; exists q' ; split ; auto ; apply clos_refl | auto ].
  destruct H' as [ Hstep Heq' ] ; rewrite Heq' in *.
  assert (emb (q' · r) <=> emb r) as Hbisim by 
    ( apply bisim_symm ; exists R ; split ; auto ).
  apply Hcongr in Hbisim ; contradiction || auto.
  exists a ; exists q' ; split ; apply clos_refl || auto.
  apply step_plus_right ; auto.
  rewrite H in * ; clear H u.
  assert (emb (q · r) -(a)-> emb r) as Hstep by 
    ( apply step_mult_right ; auto ).
  apply HrelR in HinR ; apply HinR in Hstep.
  destruct Hstep as [ v [ Hstep HR ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p' [ Heq Hstep ] ] ; rewrite Heq in *.
  assert (emb (p' · r) <=> emb r) as Hbisim by ( exists R ; split ; auto ).
  apply Hcongr in Hbisim ; contradiction || auto.
  exists a ; exists p' ; split ; apply clos_refl || auto.
  apply step_plus_left ; auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  exists term ; split ; auto.

  (* Case for p',q' (i.e. such that R (p'r) (q'r) *)
  destruct H as [ p' [ q' [ Heq_x [ Heq_y H ] ] ] ].
  rewrite Heq_x, Heq_y in * ; destruct H as [ Hp [ Hq HR ] ].
  split ; [ split ; intro H ; inversion H | split ].
  intros a u H ; assert (emb p' -(a)-> u) as Hstep_bak by auto.
  apply step_gen_cases in H.
  destruct H as [ [ p'' [ Heq_u H ] ] | Heq_u ].
  assert (emb (p' · r) -(a)-> emb (p'' · r)) as Hstep by
    ( apply step_mult_left ; auto ).
  apply HrelR in HR ; apply HR in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H' | H' ].
  destruct H' as [ q'' [ Heq_v Hstep ] ] ; rewrite Heq_v in *.
  exists (emb q'') ; split ; auto ; right ; right.
  exists p'' ; exists q'' ; repeat split ; auto.
  apply clos_end_step with p' a ; auto.
  apply clos_end_step with q' a ; auto.
  destruct H' as [ Hstep Heq_v ] ; rewrite Heq_v in *.
  assert (emb (p'' · r) <=> emb r) as Hbisim by
    ( exists R ; split ; auto ).
  apply Hcongr in Hbisim ; contradiction || auto.
  apply clos_end_step with p' a ; auto.
  destruct Hp as [ a' [ s [ Hstep' Htr ] ] ].
  exists a' ; exists s ; split ; auto.
  apply step_plus_left ; auto.
  rewrite Heq_u in *.
  assert (emb (p' · r) -(a)-> emb r) as Hstep by
    ( apply step_mult_right ; auto ).
  apply HrelR in HR ; apply HR in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ q'' [ Heq_v Hstep ] ] ; rewrite Heq_v in *.
  assert (emb (q'' · r) <=> emb r) as Hbisim by
    ( apply bisim_symm ; exists R ; split ; auto ).
  apply Hcongr in Hbisim ; contradiction || auto.
  apply clos_end_step with q' a ; auto.
  destruct Hq as [ a' [ s [ Hstep' Htr ] ] ].
  exists a' ; exists s ; split ; apply step_plus_right || auto ; auto.
  destruct H as [ Hstep Heq_v ] ; rewrite Heq_v in *.
  exists term ; split ; auto.
  intros a u H ; assert (emb q' -(a)-> u) as Hstep_bak by auto.
  apply step_gen_cases in H.
  destruct H as [ [ q'' [ Heq_u H ] ] | Heq_u ].
  assert (emb (q' · r) -(a)-> emb (q'' · r)) as Hstep by
    ( apply step_mult_left ; auto ).
  apply HrelR in HR ; apply HR in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H' | H' ].
  destruct H' as [ p'' [ Heq_v Hstep ] ] ; rewrite Heq_v in *.
  exists (emb p'') ; split ; auto ; right ; right.
  exists p'' ; exists q'' ; repeat split ; auto.
  apply clos_end_step with p' a ; auto.
  apply clos_end_step with q' a ; auto.
  destruct H' as [ Hstep Heq_v ] ; rewrite Heq_v in *.
  assert (emb (q'' · r) <=> emb r) as Hbisim by
    ( apply bisim_symm ; exists R ; split ; auto ).
  apply Hcongr in Hbisim ; contradiction || auto.
  apply clos_end_step with q' a ; auto.
  destruct Hq as [ a' [ s [ Hstep' Htr ] ] ].
  exists a' ; exists s ; split ; auto.
  apply step_plus_right ; auto.
  rewrite Heq_u in *.
  assert (emb (q' · r) -(a)-> emb r) as Hstep by
    ( apply step_mult_right ; auto ).
  apply HrelR in HR ; apply HR in Hstep.
  destruct Hstep as [ v [ Hstep HR' ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p'' [ Heq_v Hstep ] ] ; rewrite Heq_v in *.
  assert (emb (p'' · r) <=> emb r) as Hbisim by
    ( exists R ; split ; auto ).
  apply Hcongr in Hbisim ; contradiction || auto.
  apply clos_end_step with p' a ; auto.
  destruct Hp as [ a' [ s [ Hstep' Htr ] ] ].
  exists a' ; exists s ; split ; apply step_plus_left || auto ; auto.
  destruct H as [ Hstep Heq_v ] ; rewrite Heq_v in *.
  exists term ; split ; auto.
Qed.

Lemma comp_plus_left : forall (p q r : T), 
  congr p r -> congr q r -> congr (p + q) r.
Proof.
  intros p q r Hp Hq t Hplus Hbisim.
  destruct Hplus as [ a [ s [ Hstep Htr ] ] ].
  apply step_plus_fmt in Hstep ; destruct Hstep as [ Hstep | Hstep ].
  apply Hp with t ; auto.
  exists a ; exists s ; split ; auto.
  apply Hq with t ; auto.
  exists a ; exists s ; split ; auto.
Qed.

Lemma congr_right_compat : forall (p q r : T),
  congr p q -> emb q <=> emb r -> congr p r.
Proof.
  intros p q r Hcongr Hbisim t Hplus Hbisim' ; apply Hcongr with t ; auto.
  apply bisim_trans with (emb r) ; [ | apply bisim_symm ; auto ].
  apply bisim_trans with (emb (t · r)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
Qed.

Lemma nf_mult_right_compat : forall (p q r : T),
  nf_mult p q -> emb q <=> emb r -> nf_mult p r.
Proof.
  intro p ; induction p ; intros q r Hnf Hbisim ; simpl ; auto.
  simpl in Hnf ; destruct Hnf as [ Hp1 Hp2 ] ; split.
  apply IHp1 with q ; auto.
  apply IHp2 with q ; auto.
  simpl in Hnf ; destruct Hnf as [ Hp1 Hp2 ] ; split.
  apply IHp1 with (p2 · q) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply IHp2 with q ; auto.
  simpl in Hnf ; destruct Hnf as [ Hp1 [ Hp2 Hcongr ] ] ; split ; [ | split ].
  apply IHp1 with (p1 * p2 · q) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply IHp2 with q ; auto.
  apply congr_right_compat with (p1 * p2 · q) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
Qed.

Lemma clos_init_cases : forall (p r : T), p -->* r -> p = r \/
  exists (a : A) (q : T), emb p -(a)-> emb q /\ q -->* r.
Proof.
  intros p r H ; inversion H ; eauto.
Qed.

Lemma star_plus_zero_bisim : forall (p q : T),
  emb ((p * q) * 0) <=> emb ((p + q) * 0).
Proof.
  intros p q ; apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb (p * q · (p + q) * 0)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * (q · (p + q) * 0))) ; 
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply RSP_sound ; apply bisim_trans with (emb ((p + q) · (p + q) * 0)).
  apply bisim_trans with (emb ((p + q) · (p + q) * 0 + 0)) ; 
    apply B6_sound || auto.
  apply bisim_symm ; apply BKS1_sound.
  apply B4_sound.
Qed.

Lemma star_order_zero_bisim : forall (p q : T),
  emb ((p · q) * 0) <=> emb (p · (q · p) * 0).
Proof.
  intros p q ; apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb ((p · q) · p · (q · p) * 0)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p · q · p · (q · p) * 0)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_trans with (emb ((q · p) · (q · p) * 0 + 0)).
  apply bisim_symm ; apply BKS1_sound.
  apply bisim_trans with (emb ((q · p) · (q · p) * 0)) ; 
    apply B6_sound || apply B5_sound.
Qed.

Lemma nf_mult_pres_step : forall (p q r : T) (a : A),
  nf_mult p r -> emb p -(a)-> emb q -> nf_mult q r.
Proof.
  intro p ; induction p ; intros q r a' Hnf H ; solve [ inversion H ] || auto.
  simpl in Hnf ; apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply IHp1 with a' ; tauto.
  apply IHp2 with a' ; tauto.
  simpl in Hnf ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq Hstep ] ].
  replace q with (p' · p2) in * by ( inversion Heq ; auto ).
  simpl ; split ; try tauto.
  apply IHp1 with a' ; tauto.
  destruct H as [ _ H ].
  replace q with p2 in * by ( inversion H ; auto ) ; tauto.
  apply step_star_fmt in H ; destruct H as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq Hstep ] ].
  replace q with (p' · p1 * p2) in * by ( inversion Heq ; auto ).
  simpl ; simpl in Hnf ; repeat split ; try tauto.
  apply IHp1 with a' ; tauto.
  destruct H as [ H _ ].
  replace q with (p1 * p2) in * by ( inversion H ; auto ) ; auto.
  apply IHp2 with a' ; simpl in * ; tauto.
Qed.

Lemma nf_mult_pres_clos : forall (p q r : T),
  nf_mult p r -> p -->* q -> nf_mult q r.
Proof.
  intros p q r Hnf Htr ; induction Htr ; auto.
  apply IHHtr ; apply nf_mult_pres_step with (r := r) in H ; auto.
Qed.

Lemma nf_mult_pres_plus : forall (p q r : T),
  nf_mult p r -> p -->+ q -> nf_mult q r.
Proof.
  intros p q r Hnf H ; destruct H as [ a [ s [ Hstep Htr ] ] ].
  apply nf_mult_pres_step with (r := r) in Hstep ; auto.
  apply nf_mult_pres_clos with (r := r) in Htr ; auto.
Qed.

Lemma clos_clos : forall (p q r : T),
  p -->* q -> q -->* r -> p -->* r.
Proof.
  intros p q r H H' ; induction H ; auto.
  apply clos_trans with q a ; auto.
Qed.

Lemma plus_plus_clos : forall (p q r : T),
  p -->+ q -> q -->+ r -> p -->+ r.
Proof.
  intros p q r Hplus H ; destruct H as [ a [ s [ Hstep Htr ] ] ].
  assert (p -->+ s) as Hplus'.
  apply clos_end_step with q a ; auto.
  destruct Hplus' as [ a' [ t [ Hstep' Htr' ] ] ].
  exists a' ; exists t ; split ; auto.
  apply clos_clos with s ; auto.
Qed.

Lemma congr_pres_plus : forall (p q r : T),
  congr p r -> p -->+ q -> congr q r.
Proof.
  intros p q r Hcongr Hplus t Hplus' Hbisim.
  apply Hcongr with t ; auto.
  apply plus_plus_clos with q ; auto.
Qed.

Lemma depth_pres_step : forall (p q : T) (a : A),
  emb p -(a)-> emb q -> depth q <= depth p.
Proof.
  intro p ; induction p ; intros q a' H ; solve [ inversion H ] || auto.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply IHp1 in H ; simpl ; transitivity (depth p1) ; apply le_max_l || auto.
  apply IHp2 in H ; simpl ; transitivity (depth p2) ; apply le_max_r || auto.
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq Hstep ] ] ; apply IHp1 in Hstep.
  replace q with (p' · p2) in * by ( inversion Heq ; auto ).
  simpl ; apply max_lub ; apply le_max_r || auto.
  transitivity (depth p1) ; apply le_max_l || auto.
  destruct H as [ _ H ].
  replace q with p2 in * by ( inversion H ; auto ).
  simpl ; apply le_max_r.
  apply step_star_fmt in H ; destruct H as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq Hstep ] ].
  replace q with (p' · p1 * p2) in * by ( inversion Heq ; auto ).
  simpl ; destruct (depth p2) as [ | m ] ; apply max_lub ; auto.
  apply IHp1 in Hstep ; transitivity (depth p1) ; omega || auto.
  apply IHp1 in Hstep ; transitivity (depth p1) ; auto.
  rewrite succ_max_distr ; transitivity (S (depth p1)) ; apply le_max_l || auto.
  destruct H as [ H _ ].
  replace q with (p1 * p2) in * by ( inversion H ; auto ) ; auto.
  apply IHp2 in H ; simpl ; destruct (depth p2) as [ | m ] ; omega || auto.
  transitivity (S m) ; auto.
  rewrite succ_max_distr ; apply le_max_r.
Qed.

Lemma depth_pres_clos : forall (p q : T),
  p -->* q -> depth q <= depth p.
Proof.
  intros p q H ; induction H ; auto.
  apply depth_pres_step in H ; omega.
Qed.

Lemma depth_pres_plus : forall (p q : T),
  p -->+ q -> depth q <= depth p.
Proof.
  intros p q H ; destruct H as [ a [ r [ Hstep Htr ] ] ].
  apply depth_pres_step in Hstep ; apply depth_pres_clos in Htr ; omega.
Qed.

Lemma mult_clos_fmt : forall (p q r : T), (p · q) -->* r ->
  (exists (p' : T), r = p' · q /\ p -->* p') \/ q -->* r.
Proof.
  intros p q r H ; assert (exists (s : T), s = p · q) as H' by eauto.
  destruct H' as [ s Heq ] ; rewrite <- Heq in * ; revert Heq ; revert p q.
  induction H ; intros t u Heq ; rewrite Heq in *.
  left ; exists t ; split ; apply clos_refl || auto.
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ v [ Heq' Hstep ] ].
  replace q with (v · u) in * by ( inversion Heq' ; auto ).
  destruct (IHclos_step v u) as [ H | H ] ; auto.
  destruct H as [ w [ Heq'' Htr ] ] ; rewrite Heq'' in *.
  left ; exists w ; split ; auto.
  apply clos_trans with v a ; auto.
  destruct H as [ Hstep Heq' ].
  replace q with u in * by ( inversion Heq' ; auto ) ; auto.
Qed.

Lemma mult_plus_fmt : forall (p q r : T), (p · q) -->+ r ->
  (exists (p' : T), r = p' · q /\ p -->+ p') \/ q = r \/ q -->+ r.
Proof.
  intros p q r Hplus ; destruct Hplus as [ a [ s [ Hstep Htr ] ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ t [ Heq Hstep ] ].
  replace s with (t · q) in * by ( inversion Heq ; auto ).
  apply mult_clos_fmt in Htr ; destruct Htr as [ H | H ].
  destruct H as [ u [ Heq' Htr ] ] ; rewrite Heq' in *.
  left ; exists u ; split ; auto.
  exists a ; exists t ; split ; auto.
  apply clos_init_cases in H ; auto.
  destruct H as [ Hstep Heq ].
  replace s with q in * by ( inversion Heq ; auto ).
  apply clos_init_cases in Htr ; auto.
Qed.

Lemma star_clos_fmt_helper : forall (t p q r s : T), 
  (s = p * q \/ s = t · p * q /\ p -->+ t) -> s -->* r ->
    (exists (u : T), p -->+ u /\ r = u · p * q) \/ r = p * q \/ q -->+ r.
Proof.
  intros t p q r s Hor H ; revert Hor ; revert p q t.
  induction H ; intros x y t H' ; destruct H' as [ H' | H' ] ; auto.
  destruct H' as [ Heq Hplus ] ; rewrite Heq in * ; eauto.
  rewrite H' in * ; apply step_star_fmt in H ; destruct H as [ H | [ H | H ] ].
  destruct H as [ u [ Heq Hstep ] ].
  replace q with (u · x * y) in * by ( inversion Heq ; auto ).
  destruct (IHclos_step x y u) as [ H | [ H | H ] ] ; auto.
  right ; split ; auto.
  exists a ; exists u ; split ; apply clos_refl || auto.
  destruct H as [ Heq Hstep ].
  replace q with (x * y) in * by ( inversion Heq ; auto ).
  destruct (IHclos_step x y x) as [ H | [ H | H ] ] ; auto.
  right ; right ; exists a ; exists q ; split ; auto.
  destruct H' as [ Heq Hplus ] ; rewrite Heq in *.
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ u [ Heq' Hstep ] ].
  replace q with (u · x * y) in * by ( inversion Heq' ; auto ).
  destruct (IHclos_step x y u) as [ H | [ H | H ] ] ; auto.
  right ; split ; auto.
  apply clos_end_step with t a ; auto.
  destruct H as [ Hstep Heq' ].
  replace q with (x * y) in * by ( inversion Heq' ; auto ).
  destruct (IHclos_step x y x) as [ H | [ H | H ] ] ; auto.
Qed.

Lemma star_clos_fmt : forall (p q r : T), (p * q) -->* r ->
  (exists (t : T), r = t · p * q /\ p -->+ t) \/ r = p * q \/ q -->+ r.
Proof.
  intros p q r H ; apply clos_init_cases in H ; destruct H as [ H | H ] ; auto.
  destruct H as [ a [ s [ Hstep Htr ] ] ].
  apply step_star_fmt in Hstep ; destruct Hstep as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq Hstep ] ].
  replace s with (p' · p * q) in * by ( inversion Heq ; auto ).
  apply star_clos_fmt_helper with (t := p') (p := p) (q := q) in Htr ; auto.
  destruct Htr as [ H | H ].
  destruct H as [ u [ Hplus Heq' ] ] ; rewrite Heq' in * ; eauto.
  destruct H as [ H | H ] ; [ rewrite H in * | ] ; auto.
  right ; split ; auto.
  exists a ; exists p' ; split ; apply clos_refl || auto.
  destruct H as [ Heq Hstep ].
  replace s with (p * q) in * by ( inversion Heq ; auto ).
  apply star_clos_fmt_helper with (t := p) (p := p) (q := q) in Htr ; auto.
  destruct Htr as [ H | [ H | H ] ] ; auto.
  destruct H as [ u [ Hplus Heq' ] ] ; eauto.
  right ; right ; exists a ; exists s ; split ; auto.
Qed.

Lemma star_plus_fmt : forall (p q r : T), (p * q) -->+ r ->
  (exists (t : T), r = t · p * q /\ p -->+ t) \/ r = p * q \/ q -->+ r.
Proof.
  intros p q r Hplus ; destruct Hplus as [ a [ s [ Hstep Htr ] ] ].
  apply step_star_fmt in Hstep ; destruct Hstep as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq Hstep ] ].
  replace s with (p' · p * q) in * by ( inversion Heq ; auto ).
  apply star_clos_fmt_helper with (t := p') (p := p) (q := q) in Htr ; auto.
  destruct Htr as [ H | [ H | H ] ] ; auto.
  destruct H as [ u [ Hplus Heq' ] ] ; rewrite Heq' in * ; eauto.
  right ; split ; auto.
  exists a ; exists p' ; split ; apply clos_refl || auto.
  destruct H as [ Heq Hstep ].
  replace s with (p * q) in * by ( inversion Heq ; auto ).
  apply star_clos_fmt in Htr ; destruct Htr as [ H | [ H | H ] ] ; auto.
  right ; right ; exists a ; exists s ; split ; auto.
Qed.

Lemma comp_mult_ex : forall (p q r : T), nf_mult (p · q) r -> congr q r ->
  (exists (s : T), emb (p · q · r) <=> emb (s · r) /\ nf_mult s r /\
    congr s r /\ depth s <= depth (p · q)) \/
  (exists (s : T), emb r <=> emb (s · 0) /\ nf (s · 0) /\ 
    depth s <= 1 + depth (p · q)).
Proof.
  intro p ; assert (exists (d : nat), depth p <= d) as H by eauto.
  destruct H as [ d Heq_depth ] ; revert Heq_depth ; revert p.
  induction d using strong_ind ; rename H into IHdepth.
  intro p ; induction p ; intros Heq_depth q r Hnf Hcongr.
  left ; exists 0 ; split ; [ | split ; [ | split ] ] ; simpl ; omega || auto.
  apply bisim_trans with (emb 0) ; [ | apply bisim_symm ] ; apply B7_sound.
  intros t H ; destruct H as [ a [ s [ H _ ] ] ] ; inversion H.

  (* Case for a \in A *)
  left ; destruct (LEM (emb (q · r) <=> emb r)) as [ Hbisim | Hnot_bisim ].
  exists (act a) ; split ; [ | split ; [ | split ] ] ; simpl ; omega || auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  intros t Hplus Hbisim' ; destruct Hplus as [ a' [ s [ H _ ] ] ] ; inversion H.
  exists (act a · q) ; split ; [ | split ; [ | split ] ] ; 
    simpl ; omega || auto.
  apply bisim_symm ; apply B5_sound.
  intros t Hplus Hbisim ; destruct Hplus as [ a' [ s [ Hstep Htr ] ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ u [ _ H ] ] ; inversion H.
  destruct H as [ Hstep Heq ].
  apply clos_init_cases in Htr ; destruct Htr as [ H | H ].
  rewrite <- H in *.
  replace s with q in * by ( inversion Heq ; auto ) ; contradiction.
  destruct H as [ a'' [ u [ Hstep' Htr ] ] ].
  apply Hcongr with t ; auto.
  exists a'' ; exists u ; split ; auto.
  replace s with q in * by ( inversion Heq ; auto ) ; auto.

  (* Case for p1 + p2 *)
  simpl in Hnf ; destruct Hnf as [ [ Hnf_p1 Hnf_p2 ] Hnf_q ].
  destruct IHp1 with (q := q) (r := r) as [ [ s1 Hs1 ] | Hs1 ] ; 
    solve [ simpl in * ; tauto ] || auto.
  transitivity (depth (p1 + p2)) ; apply le_max_l || auto.
  destruct IHp2 with (q := q) (r := r) as [ [ s2 Hs2 ] | Hs2 ] ; 
    solve [ simpl in * ; tauto ] || auto.
  transitivity (depth (p1 + p2)) ; apply le_max_r || auto.
  destruct Hs1 as [ Hbisim_s1 [ Hnf_s1 [ Hcongr_s1 Hleq_s1 ] ] ].
  destruct Hs2 as [ Hbisim_s2 [ Hnf_s2 [ Hcongr_s2 Hleq_s2 ] ] ].
  left ; exists (s1 + s2) ; split ; [ | split ; [ | split ] ].
  apply bisim_trans with (emb (p1 · q · r + p2 · q · r)) ; 
    apply B4_sound || auto.
  apply bisim_trans with (emb (s1 · r + s2 · r)) ;
    [ | apply bisim_symm ; apply B4_sound ].
  apply bisim_comp_plus ; auto.
  simpl ; split ; auto.
  apply comp_plus_left ; auto.
  simpl ; apply max_lub.
  transitivity (depth (p1 · q)) ; simpl ; auto.
  rewrite <- max_assoc ; rewrite (max_comm (depth p2)).
  rewrite max_assoc ; apply le_max_l.
  transitivity (depth (p2 · q)) ; simpl ; auto.
  rewrite <- max_assoc ; apply le_max_r.
  destruct Hs2 as [ s [ Hbisim [ Hnf Hleq ] ] ].
  right ; exists s ; split ; [ | split ] ; auto.
  transitivity ((1 + (depth (p2 · q)))%nat) ; auto.
  assert (depth (p2 · q) <= depth ((p1 + p2) · q)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite <- max_assoc ; rewrite (max_comm (depth p2)) ; 
    rewrite max_assoc ; apply le_max_r.
  destruct Hs1 as [ s [ Hbisim [ Hnf Hleq ] ] ].
  right ; exists s ; split ; [ | split ] ; auto.
  transitivity (1 + depth (p1 · q))%nat ; auto.
  assert (depth (p1 · q) <= depth ((p1 + p2) · q)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite <- max_assoc ; apply le_max_l.

  (* Case for p1 · p2 *)
  simpl in Hnf ; destruct Hnf as [ [ Hnf_p1 Hnf_p2 ] Hnf_q ].
  destruct IHp2 with (q := q) (r := r) as [ [ s2 H ] | Hs2_top ] ; 
    solve [ simpl in * ; tauto ] || auto.
  transitivity (depth (p1 · p2)) ; apply le_max_r || auto.
  destruct H as [ Hbisim_s2 [ Hnf_s2 [ Hcongr_s2 Hleq_s2 ] ] ].
  destruct IHp1 with (q := s2) (r := r) as [ [ s1 H ] | Hs1_top ] ; 
    solve [ simpl in * ; tauto ] || auto.
  transitivity (depth (p1 · p2)) ; apply le_max_l || auto.
  simpl ; split ; auto.
  apply nf_mult_right_compat with (p2 · q · r) ; auto.
  destruct H as [ Hbisim_s1 [ Hnf_s1 [ Hcongr_s1 Hleq_s1 ] ] ].
  left ; exists s1 ; split ; [ | split ; [ | split ] ] ; auto.
  apply bisim_trans with (emb (p1 · p2 · q · r)) ; apply B5_sound || auto.
  apply bisim_trans with (emb (p1 · s2 · r)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  transitivity (depth (p1 · s2)) ; auto.
  simpl ; apply max_lub.
  rewrite <- max_assoc ; apply le_max_l.
  transitivity (depth (p2 · q)) ; auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite (max_comm (depth p1)) ; rewrite <- max_assoc ; apply le_max_l.
  destruct Hs1_top as [ s [ Hbisim [ Hnf Hleq ] ] ].
  right ; exists s ; split ; [ | split ] ; auto.
  transitivity (1 + depth (p1 · s2))%nat ; auto.
  assert (depth (p1 · s2) <= depth ((p1 · p2) · q)) ; omega || auto.
  simpl ; apply max_lub.
  rewrite <- max_assoc ; apply le_max_l.
  transitivity (depth (p2 · q)) ; auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite <- max_assoc ; rewrite (max_comm (depth p2)) ;
    rewrite max_assoc ; apply le_max_r.
  destruct Hs2_top as [ s [ Hbisim [ Hnf Hleq ] ] ].
  right ; exists s ; split ; [ | split ] ; auto.
  transitivity (1 + depth (p2 · q))%nat ; auto.
  assert (depth (p2 · q) <= depth ((p1 · p2) · q)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite <- max_assoc ; rewrite (max_comm (depth p2)) ;
    rewrite max_assoc ; apply le_max_r.

  (* Case for p1 * p2 *)
  rename p1 into p ; destruct IHp2 with (q := q) (r := r) as [ [ q2 H ] | H ] ; 
    solve [ simpl in * ; tauto ] || auto.
  transitivity (depth (p * p2)) ; apply le_max_r || auto.
  destruct H as [ Hbisim_q2 [ Hnf_q2 [ Hcongr_q2 Hleq_q2 ] ] ] ; 
    clear IHp1 IHp2.
  assert (emb (p * p2 · q · r) <=> emb (p * q2 · r)) as Hbasic_eq.
  apply bisim_trans with (emb (p * (p2 · q · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q2 · r))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl || auto.
  destruct (LEM (emb (p * q2 · r) <=> emb r)) as [ Hbisim_r | Hnot_bisim_r ].

  (* Case for p * q2 · r <=> r *)
  assert (emb ((p + q2) * 0) <=> emb (p * q2 · r)) as Hplus_eq.
  apply bisim_trans with (emb ((p * q2) * 0)).
  apply bisim_symm ; apply star_plus_zero_bisim.
  apply bisim_trans with (emb r) ; [ | apply bisim_symm ; auto ].
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb (p * q2 · r)) ; apply bisim_symm ;
    apply B6_sound || auto.
  assert (emb ((p + q2) * 0) <=> emb ((p + q2) * 0 · 0)) as Hhelp_eq.
  apply bisim_trans with (emb ((p + q2) * (0 · 0))).
  apply bisim_comp_star ; apply bisim_refl || 
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  right ; exists ((p + q2) * 0) ; split ; [ | split ] ; auto.
  apply bisim_trans with (emb (p * q2 · r)) ; [ apply bisim_symm | ] ; auto.
  apply bisim_trans with (emb ((p + q2) * 0)) ; auto.
  apply bisim_symm ; auto.
  simpl ; repeat split ; auto.
  simpl in Hnf ; apply nf_mult_right_compat with (p * p2 · q · r) ; 
    tauto || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_trans with (emb ((p + q2) * 0)) ; auto.
  apply bisim_symm ; auto.
  apply nf_mult_right_compat with r ; auto.
  apply bisim_trans with (emb ((p + q2) * 0)) ; auto.
  apply bisim_trans with (emb (p * q2 · r)) ; apply bisim_symm ; auto.
  apply comp_plus_left.
  simpl in Hnf ; apply congr_right_compat with (p * p2 · q · r) ; 
    tauto || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_trans with (emb ((p + q2) * 0)) ; auto.
  apply bisim_symm ; auto.
  apply congr_right_compat with r ; auto.
  apply bisim_trans with (emb (p * q2 · r)) ; [ apply bisim_symm | ] ; auto.
  apply bisim_trans with (emb ((p + q2) * 0)) ; auto.
  apply bisim_symm ; auto.
  simpl in * ; destruct (depth p2) as [ | m ].
  assert (max (depth p) (depth q2) <= max (S (depth p)) (depth q)) ; try omega.
  apply max_lub.
  transitivity (S (depth p)) ; apply le_max_l || omega.
  rewrite max_0_l in Hleq_q2.
  transitivity (depth q) ; apply le_max_r || auto.
  assert (max (depth p) (depth q2) <= max (S (max (depth p) m)) (depth q)) ;
    omega || apply max_lub.
  transitivity (S (max (depth p) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr.
  transitivity (S (depth p)) ; apply le_max_l || omega.
  transitivity (max (S m) (depth q)) ; auto.
  apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_r.

  (* Case where NOT p * q2 · r <=> r *)
  destruct (LEM (exists (t : T), p -->+ t /\ 
    emb (t · p * q2 · r) <=> emb r)) as [ Hplus_ex | Hplus_not_ex ].
  destruct Hplus_ex as [ t [ Hplus Hbisim ] ].

  (* Case where p -->+ t such that t · p * q2 · r <=> r exists *)
  assert (emb ((t · p * q2) * 0) <=> emb r) as HRSP_eq.
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb ((t · p * q2) · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (t · p * q2 · r)).
  apply bisim_symm ; auto.
  apply bisim_symm ; apply B5_sound.
  assert (emb ((p * q2 · t) * 0) <=> emb ((p + q2 · t) * 0)) as Hplus_eq.
  apply bisim_trans with (emb ((p * (q2 · t)) * 0)).
  apply bisim_comp_star ; apply bisim_refl || apply BKS2_sound.
  apply star_plus_zero_bisim.
  assert (emb (t · (p + q2 · t) * 0) <=> emb r) as Hplus_eq'.
  apply bisim_trans with (emb ((t · p * q2) * 0)) ; auto.
  apply bisim_trans with (emb (t · (p * q2 · t) * 0)).
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_symm ; apply star_order_zero_bisim.
  destruct (LEM (exists (u : T), q2 -->+ u /\
    emb (u · t · p * q2 · r) <=> emb (p * q2 · r))) as [ Hu | Hnot_u ].
 
  (* Case where q2 -->+ u such that u · t · p * q2 · r <=> p * q2 · r *)
  destruct Hu as [ u [ Hplus' Hbisim_u ] ].
  assert (emb ((u · t) · p * q2 · r + 0) <=> emb (p * q2 · r)) as Hstar_eq.
  apply bisim_trans with (emb ((u · t) · p * q2 · r)) ; apply B6_sound || auto.
  apply bisim_trans with (emb (u · t · p * q2 · r)) ; apply B5_sound || auto.
  apply bisim_symm in Hstar_eq ; apply RSP_sound in Hstar_eq.
  assert (emb (t · (u · t) * 0) <=> emb r) as HRSP_eq'.
  apply bisim_trans with (emb (t · p * q2 · r)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  assert (emb ((t · u) * 0) <=> emb r) as HRSP_eq''.
  apply bisim_trans with (emb (t · (u · t) * 0)) ; auto.
  apply star_order_zero_bisim.
  destruct IHdepth with (m := depth t) (p := t) 
    (q := u) (r := r) as [ H | H ] ; auto.
  assert (depth t < depth (p * p2)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ].
  assert (depth t <= depth p) ; omega || auto.
  apply depth_pres_plus ; auto.
  assert (depth t <= max (depth p) m) ; omega || auto.
  transitivity (depth p) ; apply le_max_l || auto.
  apply depth_pres_plus ; auto.
  simpl ; split.
  apply nf_mult_pres_plus with p ; auto.
  simpl in Hnf ; apply nf_mult_right_compat with (p * p2 · q · r) ; 
    tauto || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_trans with (emb (u · t · p * q2 · r)).
  apply bisim_symm ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply nf_mult_pres_plus with q2 ; auto. 
  apply congr_pres_plus with q2 ; auto.
  
  (* Case where s is now normalized w.r.t. (t · u) * 0 *)
  destruct H as [ s [ Hbisim_s [ Hnf_s [ Hcongr_s Hleq_s ] ] ] ].
  assert (emb (s * 0) <=> emb r) as Hstar_eq'.
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb (s · r)) ; 
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (t · u · r)) ; auto.
  apply bisim_trans with (emb ((t · u) * 0)) ;
    [ apply bisim_symm ; auto | ].
  apply bisim_trans with (emb (t · u · (t · u) * 0)).
  apply bisim_trans with (emb ((t · u) · (t · u) * 0)) ; apply B5_sound || auto.
  apply bisim_trans with (emb ((t · u) · (t · u) * 0 + 0)) ;
    apply B6_sound || auto.
  apply bisim_symm ; apply BKS1_sound.
  apply bisim_trans with (emb ((t · u) · (t · u) * 0)) ;
    [ apply bisim_symm ; apply B5_sound | ].
  apply bisim_trans with (emb ((t · u) · r)) ; apply B5_sound || auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  right ; exists (s * 0) ; split ; [ | split ] ; auto.
  apply bisim_trans with (emb (s * 0)) ; [ apply bisim_symm ; auto | ].
  apply bisim_trans with (emb (s * (0 · 0))).
  apply bisim_comp_star ; apply bisim_refl || 
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; repeat split ; auto.
  apply nf_mult_right_compat with r ; auto.
  apply bisim_trans with (emb (s * 0)) ; [ apply bisim_symm | ] ; auto.
  apply bisim_trans with (emb (s * (0 · 0))) ; apply BKS2_sound || auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  apply congr_right_compat with r ; auto.
  apply bisim_trans with (emb (s * 0)) ; [ apply bisim_symm | ] ; auto.
  apply bisim_trans with (emb (s * (0 · 0))) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  simpl in * ; destruct (depth p2) as [ | m ].
  assert (depth s <= max (S (depth p)) (depth q)) ; omega || auto.
  transitivity (depth (t · u)) ; auto.
  simpl ; apply max_lub ; destruct (depth q) as [ | n ].
  transitivity (depth p) ; omega || auto.
  apply depth_pres_plus ; auto.
  rewrite succ_max_distr.
  transitivity (S (depth p)) ; apply le_max_l || auto.
  transitivity (depth p) ; omega || apply depth_pres_plus ; auto.
  rewrite max_0_l in Hleq_q2.
  assert (depth u <= 0) ; omega || auto.
  transitivity (depth q2) ; auto.
  apply depth_pres_plus ; auto.
  transitivity (depth q2) ; auto.
  apply depth_pres_plus ; auto.
  rewrite succ_max_distr.
  transitivity (S n) ; apply le_max_r || auto.
  assert (depth s <= max (S (max (depth p) m)) (depth q)) ; omega || auto.
  transitivity (max (depth t) (depth u)) ; apply max_lub || auto.
  transitivity (S (max (depth p) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr.
  transitivity (S (depth p)) ; apply le_max_l || auto.
  transitivity (depth p) ; omega || apply depth_pres_plus ; auto.
  transitivity (depth q2).
  apply depth_pres_plus ; auto.
  transitivity (max (S m) (depth q)) ; auto.
  apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p) m)) ; apply le_max_l || auto.
  assert (m <= max (depth p) m) by ( apply le_max_r) ; omega.

  (* Case where depth-induction results in an r-equivalent nf (s · 0) *)
  destruct H as [ s [ Hbisim_s [ Hnf_s Hleq_s ] ] ].
  right ; exists s ; split ; [ | split ] ; auto.
  transitivity (1 + depth (t · u))%nat ; auto.
  assert (depth (t · u) <= depth (p * p2 · q)) ; omega || auto.
  simpl in * ; apply max_lub ; destruct (depth p2) as [ | m ].
  transitivity (S (depth p)) ; apply le_max_l || auto.
  transitivity (depth p) ; omega || apply depth_pres_plus ; auto.
  transitivity (S (max (depth p) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr.
  transitivity (S (depth p)) ; apply le_max_l || auto.
  transitivity (depth p) ; omega || apply depth_pres_plus ; auto.
  transitivity (depth q2).
  apply depth_pres_plus ; auto.
  rewrite max_0_l in Hleq_q2.
  transitivity (depth q) ; apply le_max_r || auto.
  transitivity (depth q2).
  apply depth_pres_plus ; auto.
  transitivity (max (S m) (depth q)) ; auto.
  apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p) m)) ; apply le_max_l || auto.
  assert (m <= max (depth p) m) by ( apply le_max_r ) ; omega.

  (* Case where q2 -->+ u with u · t · p* q2 · r <=> p * q2 · r NOT exists *)
  right ; exists (t · (p + q2 · t) * 0) ; split ; [ | split ] ; auto.
  apply bisim_trans with (emb (t · (p + q2 · t) * 0)).
  apply bisim_symm ; auto.
  apply bisim_trans with (emb (t · (p + q2 · t) * 0 · 0)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_trans with (emb ((p + q2 · t) * (0 · 0))) ;
    apply BKS2_sound || auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; repeat split ; auto.
  apply nf_mult_pres_plus with p ; auto.
  simpl in Hnf.
  apply nf_mult_right_compat with (p * p2 · q · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * (0 · 0))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_trans with (emb ((p * q2 · t) * 0)).
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q2 · t) · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q2 · t · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * 0)) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  simpl in Hnf.
  apply nf_mult_right_compat with (p * p2 · q · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * (0 · 0))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_trans with (emb ((p * q2 · t) * 0)).
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q2 · t) · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q2 · t · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * 0)) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply nf_mult_right_compat with r ; auto.
  apply bisim_trans with (emb (t · (p + q2 · t) * 0)) ;
    [ apply bisim_symm ; auto | ].
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_trans with (emb ((p + q2 · t) * (0 · 0))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  simpl in Hnf.
  apply nf_mult_pres_plus with p ; auto.
  apply nf_mult_right_compat with (p * p2 · q · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * (0 · 0))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_trans with (emb ((p * q2 · t) * 0)).
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q2 · t) · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q2 · t · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * 0)) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply comp_plus_left.
  apply congr_right_compat with (p * p2 · q · r) ;
    solve [ simpl in * ; tauto ] || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * (0 · 0))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_trans with (emb ((p * q2 · t) * 0)).
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q2 · t) · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q2 · t · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * 0)) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply congr_right_compat with (p * q2 · r).
  intros v Hplus_v Hbisim'.
  apply mult_plus_fmt in Hplus_v.
  destruct Hplus_v as [ H | [ H | H ] ].
  destruct H as [ q' [ Heq Hplus_q2 ] ] ; rewrite Heq in *.
  apply Hnot_u ; exists q' ; split ; auto.
  apply bisim_trans with (emb ((q' · t) · p * q2 · r)) ; auto.
  apply bisim_symm ; apply B5_sound.
  rewrite <- H in * ; simpl in Hnf.
  destruct Hnf as [ [ _ [ _ Hcongr' ] ] _ ].
  apply Hcongr' with t ; auto.
  apply bisim_trans with (emb (t · p * q2 · r)).
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_symm ; auto.
  simpl in Hnf ; destruct Hnf as [ [ _ [ _ Hcongr' ] ] _ ].
  apply Hcongr' with v ; auto.
  apply plus_plus_clos with t ; auto.
  apply bisim_trans with (emb (v · p * q2 · r)).
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_trans with (emb (p * q2 · r)) ; auto.
  apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * (0 · 0))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_trans with (emb ((p * q2 · t) * 0)).
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q2 · t) · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q2 · t · p * q2 · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + q2 · t) * 0)) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  simpl in * ; apply max_lub ; destruct (depth p2) as [ | m ].
  rewrite succ_max_distr.
  transitivity (S (S (depth p))) ; apply le_max_l || auto.
  transitivity (depth p) ; omega || apply depth_pres_plus ; auto.
  rewrite succ_max_distr.
  transitivity (S (S (max (depth p) m))) ; apply le_max_l || auto.
  rewrite succ_max_distr ; rewrite succ_max_distr.
  transitivity (S (S (depth p))) ; apply le_max_l || auto.
  transitivity (depth p) ; omega || apply depth_pres_plus ; auto.
  rewrite succ_max_distr ; rewrite succ_max_distr ;
    rewrite succ_max_distr ; apply max_lub.
  transitivity (S (S (depth p))) ; apply le_max_l || omega.
  apply max_lub.
  rewrite max_0_l in Hleq_q2.
  transitivity (S (depth q)) ; omega || apply le_max_r.
  transitivity (S (S (depth p))) ; apply le_max_l || auto.
  assert (depth t <= depth p) by ( apply depth_pres_plus ; auto) ; omega.
  rewrite succ_max_distr ; apply max_lub.
  rewrite succ_max_distr.
  transitivity (S (S (max (depth p) m))) ; apply le_max_l || auto.
  rewrite succ_max_distr ; rewrite succ_max_distr.
  transitivity (S (S (depth p))) ; apply le_max_l || omega.
  rewrite succ_max_distr ; apply max_lub.
  transitivity (S (max (S m) (depth q))) ; omega || auto.
  rewrite succ_max_distr ; apply max_lub.
  rewrite succ_max_distr.
  transitivity (S (S (max (depth p) m))) ; apply le_max_l || auto.
  rewrite succ_max_distr ; rewrite succ_max_distr ; apply le_max_r.
  rewrite succ_max_distr ; apply le_max_r.
  transitivity (S (depth p)).
  assert (depth t <= depth p) by ( apply depth_pres_plus ; auto ) ; omega.
  rewrite succ_max_distr.
  transitivity (S (S (max (depth p) m))) ; apply le_max_l || auto.
  rewrite succ_max_distr ; rewrite succ_max_distr.
  transitivity (S (S (depth p))) ; apply le_max_l || omega.

  (* Case where p -->+ t and t · p * q2 · r <=> r does NOT exist *)
  left ; exists (p * q2) ; split ; [ | split ; [ | split ] ] ; auto.
  simpl ; split ; [ | split ] ; auto.
  simpl in Hnf ; apply nf_mult_right_compat with (p * p2 · q · r) ;
    tauto || auto.
  simpl in Hnf ; apply congr_right_compat with (p * p2 · q · r) ;
    tauto || auto.
  intros t Hplus Hbisim' ; apply star_plus_fmt in Hplus.
  destruct Hplus as [ H | [ H | H ] ].
  destruct H as [ t' [ Heq Hplus ] ] ; rewrite Heq in *.
  apply Hplus_not_ex ; exists t' ; split ; auto.
  apply bisim_trans with (emb ((t' · p * q2) · r)) ; auto.
  apply bisim_symm ; apply B5_sound.
  rewrite H in * ; apply Hnot_bisim_r ; auto.
  apply Hcongr_q2 with t ; auto.
  simpl in * ; destruct (depth q2) as [ | m ] ; 
    destruct (depth p2) as [ | n ] ; apply le_max_l || auto.
  transitivity (S (max (depth p) n)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_l.
  rewrite succ_max_distr ; apply max_lub ; apply le_max_l || auto.
  rewrite max_0_l in Hleq_q2.
  transitivity (depth q) ; apply le_max_r || auto.
  rewrite succ_max_distr ; apply max_lub.
  transitivity (S (max (depth p) n)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_l.
  transitivity (max (S n) (depth q)) ; auto.
  apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p) n)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_r.

  (* Case where IHp2 results in an r-equivalent in (s * 0) - form *)
  destruct H as [ s [ Hbisim_s [ Hnf_s Hleq_s ] ] ].
  right ; exists s ; split ; [ | split ] ; auto.
  transitivity (1 + (depth (p2 · q)))%nat ; auto.
  assert (depth (p2 · q) <= depth (p * p2 · q)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ].
  rewrite max_0_l ; apply le_max_r.
  apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_r.
Qed.

Lemma congr_ex : forall (p r : T), nf_mult p r -> 
  (exists (q : T), emb (p · r) <=> emb (q · r) /\ nf_mult q r /\ 
    congr q r /\ depth q <= depth p) \/
  (exists (q : T), emb r <=> emb (q · 0) /\ nf (q · 0) /\ 
    depth q <= 1 + depth p).
Proof.
  intro p ; induction p ; intros r Hnf_mult.
  left ; exists 0 ; split ; [ | split ; [ | split ] ] ; 
    simpl ; apply bisim_refl || auto.
  intros t H ; destruct H as [ a [ s [ H _ ] ] ] ; inversion H.
  left ; exists (act a) ; split ; [ | split ; [ | split ] ] ;
    simpl ; apply bisim_refl || auto.
  intros t H ; destruct H as [ a' [ s [ H _ ] ] ] ; inversion H.

  (* Case for p1 + p2 *)
  simpl in Hnf_mult ; destruct Hnf_mult as [ Hp1 Hp2 ].
  destruct (IHp1 r Hp1) as 
    [ [ q1 [ Hbisim_q1 [ Hnf_q1 [ Hcongr_q1 Hleq_q1 ] ] ] ] | Hp1_top ].
  destruct (IHp2 r Hp2) as
    [ [ q2 [ Hbisim_q2 [ Hnf_q2 [ Hcongr_q2 Hleq_q2 ] ] ] ] | Hp2_top ].
  left ; exists (q1 + q2) ; split ; [ | split ; [ | split ] ].
  apply bisim_trans with (emb (p1 · r + p2 · r)) ; apply B4_sound || auto.
  apply bisim_trans with (emb (q1 · r + q2 · r)) ; auto.
  apply bisim_comp_plus ; auto.
  apply bisim_symm ; apply B4_sound.
  simpl ; split ; auto.
  apply comp_plus_left ; auto.
  simpl ; apply max_lub.
  transitivity (depth p1) ; apply le_max_l || auto.
  transitivity (depth p2) ; apply le_max_r || auto.
  
  destruct Hp2_top as [ q [ Hbisim [ Hnf Hleq ] ] ].
  right ; exists q ; split ; [ | split ] ; auto.
  transitivity (1 + depth p2)%nat ; apply le_max_r || auto.
  assert (depth p2 <= depth (p1 + p2)) ; omega || auto.
  simpl ; apply le_max_r || auto.
  destruct Hp1_top as [ q [ Hbisim [ Hnf Hleq ] ] ].
  right ; exists q ; split ; [ | split ] ; auto.
  transitivity (1 + depth p1)%nat ; auto.
  assert (depth p1 <= depth (p1 + p2)) ; omega || auto.
  simpl ; apply le_max_l.

  (* Case for p1 · p2 *)
  simpl in Hnf_mult ; destruct Hnf_mult as [ Hp1 Hp2 ].
  destruct (IHp2 r Hp2) as 
    [ [ q2 [ Hbisim_q2 [ Hnf_q2 [ Hcongr_q2 Hleq_q2 ] ] ] ] | Hp2_top ].
  destruct (comp_mult_ex p1 q2 r) as [ [ s H ] | Hp1_top ] ; auto.
  simpl ; split ; auto.
  apply nf_mult_right_compat with (p2 · r) ; auto.
  destruct H as [ Hbisim_s [ Hnf_s [ Hcongr_s Hleq_s ] ] ].
  left ; exists s ; split ; [ | split ; [ | split ] ] ; auto.
  apply bisim_trans with (emb (p1 · p2 · r)) ; apply B5_sound || auto.
  apply bisim_trans with (emb (p1 · q2 · r)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  transitivity (depth (p1 · q2)) ; auto.
  simpl ; apply max_lub ; apply le_max_l || auto.
  transitivity (depth p2) ; apply le_max_r || auto.
  destruct Hp1_top as [ s [ Hbisim [ Hnf Hleq ] ] ].
  right ; exists s ; split ; [ | split ] ; auto.
  transitivity (1 + depth (p1 · q2))%nat ; auto.
  assert (depth (p1 · q2) <= depth (p1 · p2)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_l || auto.
  transitivity (depth p2) ; apply le_max_r || auto.
  destruct Hp2_top as [ s [ Hbisim [ Hnf Hleq ] ] ].
  right ; exists s ; split ; [ | split ] ; auto.
  transitivity (1 + depth p2)%nat ; auto.
  assert (depth p2 <= depth (p1 · p2)) ; omega || auto.
  simpl ; apply le_max_r.

  (* Case for p1 * p2 *)
  destruct (IHp2 r) as [ [ q H ] | H ] ; solve [ simpl in * ; tauto ] || auto.
  destruct H as [ Hbisim_q [ Hnf_q [ Hcongr_q Hleq_q ] ] ].
  rename p1 into p ; clear IHp1 IHp2.
  destruct (LEM (emb (p * q · r) <=> emb r)) as [ Hbisim_star | Hbisim_star ].

  (* Case where p * q · r <=> r *)
  assert (emb (p * q · r + 0) <=> emb r) as Hstar_eq.
  apply bisim_trans with (emb (p * q · r)) ; apply B6_sound || auto.
  apply bisim_symm in Hstar_eq ; apply RSP_sound in Hstar_eq.
  assert (emb r <=> emb ((p + q) * 0)) as Hstar_eq'.
  apply bisim_trans with (emb (p * q * 0)) ; auto.
  apply star_plus_zero_bisim.
  right ; exists ((p + q) * 0) ; split ; [ | split ].
  apply bisim_trans with (emb ((p + q) * 0)) ; auto.
  apply bisim_trans with (emb ((p + q) * (0 · 0))) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; repeat split ; auto.
  simpl in Hnf_mult.
  apply nf_mult_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q · r)).
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ; auto.
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS2_sound.
  apply bisim_trans with (emb r) ; auto.
  apply bisim_trans with (emb ((p + q) * 0)) ; auto.
  apply bisim_trans with (emb ((p + q) * (0 · 0))) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  apply nf_mult_right_compat with r ; auto.
  apply bisim_trans with (emb ((p + q) * 0)) ; auto.
  apply bisim_trans with (emb ((p + q) * (0 · 0))) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  apply comp_plus_left.
  simpl in Hnf_mult.
  apply congr_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q · r)).
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ; auto.
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS2_sound.
  apply bisim_trans with (emb r) ; auto.
  apply bisim_trans with (emb ((p + q) * 0)) ; auto.
  apply bisim_trans with (emb ((p + q) * (0 · 0))) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  apply congr_right_compat with r ; auto.
  apply bisim_trans with (emb ((p + q) * 0)) ; auto.
  apply bisim_trans with (emb ((p + q) * (0 · 0))) ; auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; destruct (depth p2) as [ | m ].
  replace (depth q) with 0%nat in * by omega.
  rewrite max_0_r ; omega.
  assert (max (depth p) (depth q) <= S (max (depth p) m)) ; omega || auto.
  apply max_lub ; rewrite succ_max_distr.
  transitivity (S (depth p)) ; omega || apply le_max_l.
  transitivity (S m) ; omega || apply le_max_r.

  (* Case where NOT p * q · r <=> r *)
  destruct (LEM (exists (t : T), p -->+ t /\ emb (t · p * q · r) <=> emb r)) as 
    [ Hplus_ex | Hplus_ex ].

  (* Case where p -->+ t such that t · p * q · r <=> r exists *)
  destruct Hplus_ex as [ t [ Hplus Hbisim_t ] ].
  assert (emb ((t · p * q) · r + 0) <=> emb r) as Hstar_eq.
  apply bisim_trans with (emb ((t · p * q) · r)) ; apply B6_sound || auto.
  apply bisim_trans with (emb (t · p * q · r)) ; apply B5_sound || auto.
  apply bisim_symm in Hstar_eq ; apply RSP_sound in Hstar_eq.
  assert (emb r <=> emb (t · (p * q · t) * 0)) as Hstar_eq'.
  apply bisim_trans with (emb ((t · p * q) * 0)) ; auto.
  apply star_order_zero_bisim.
  assert (emb ((p * q · t) * 0) <=> emb ((p + q · t) * 0)) as Hplus_eq.
  apply bisim_trans with (emb ((p * (q · t)) * 0)).
  apply bisim_comp_star ; apply bisim_refl || apply BKS2_sound.
  apply star_plus_zero_bisim.
  destruct (comp_mult_ex q t ((p * q · t) * 0)) as [ [ s H ] | H ].
  simpl ; split.
  apply nf_mult_right_compat with r ; auto.
  apply nf_mult_pres_plus with p ; auto.
  simpl in Hnf_mult ; apply nf_mult_right_compat with (p * p2 · r) ; 
    tauto || auto.
  apply bisim_trans with (emb (p * q · r)).
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))).
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS2_sound.
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q · t) · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q · t · p * q · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_symm ; auto.
  simpl in Hnf_mult.
  apply congr_pres_plus with p ; auto.
  apply congr_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q · r)).
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ; auto.
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS2_sound.
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q · t) · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q · t · p * q · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_symm ; auto.
  destruct H as [ Hbisim_s [ Hnf_s [ Hcongr_s Hleq_s ] ] ].
  assert (emb ((p + s) * 0) <=> emb (p * q · r)) as Hcomp_eq.
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb ((p + s) · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p · p * q · r + s · p * q · r)) ;
    [ | apply bisim_symm ; apply B4_sound ].
  apply bisim_trans with (emb ((p · p * q + q) · r)).
  apply bisim_comp_mult ; apply bisim_refl ||
    apply bisim_symm ; apply BKS1_sound.
  apply bisim_trans with (emb ((p · p * q) · r + q · r)) ;
    apply B4_sound || auto.
  apply bisim_comp_plus ; apply B5_sound || auto.
  apply bisim_trans with (emb (q · t · (p * q · t) * 0)).
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_trans with (emb (s · (p * q · t) * 0)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb ((p * q · t) · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q · t · p * q · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || 
    apply bisim_symm ; auto.
  right ; exists (t · (p + s) * 0) ; split ; [ | split ].
  apply bisim_trans with (emb (t · (p + s) * 0 · 0)) ; 
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_trans with (emb (t · (p + s) * (0 · 0))) ; apply B5_sound || auto.
  apply bisim_trans with (emb (t · (p + s) * 0)).
  apply bisim_trans with (emb ((t · p * q) * 0)) ; auto.
  apply bisim_trans with (emb (t · (p * q · r))).
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb ((t · p * q) · t · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb ((t · p * q) · r)) ; 
    [ apply bisim_symm ; apply B5_sound | ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; repeat split ; auto.
  apply nf_mult_pres_plus with p ; auto.
  simpl in Hnf_mult.
  apply nf_mult_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q · r)).
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_trans with (emb ((p + s) * 0)) ; auto.
  apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + s) * (0 · 0))).
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  simpl in Hnf_mult.
  apply nf_mult_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q · r)).
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_trans with (emb ((p + s) * 0)) ; [ apply bisim_symm ; auto | ].
  apply bisim_trans with (emb ((p + s) * (0 · 0))).
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  apply nf_mult_right_compat with ((p * q · t) * 0) ; auto.
  apply bisim_trans with (emb (p * q · r)).
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb ((p * q · t) · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q · t · p * q · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + s) * 0)) ; [ apply bisim_symm | ] ; auto.
  apply bisim_trans with (emb ((p + s) * (0 · 0))) ; apply BKS2_sound || auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  apply comp_plus_left.
  simpl in Hnf_mult.
  apply congr_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q · r)) ; [ | apply bisim_symm ] ; auto.
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_trans with (emb ((p + s) * 0)) ; auto.
  apply bisim_trans with (emb ((p + s) * (0 · 0))) ; apply BKS2_sound || auto.
  apply bisim_comp_star ; apply bisim_refl || apply B7_sound.
  apply congr_right_compat with ((p * q · t) * 0) ; auto.
  apply bisim_trans with (emb (p * q · r)).
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb ((p * q · t) · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q · t · p * q · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  apply bisim_trans with (emb ((p + s) * 0)) ; [ apply bisim_symm | ] ; auto.
  apply bisim_trans with (emb ((p + s) * (0 · 0))) ;
    apply BKS2_sound || auto.
  apply bisim_comp_star ; apply bisim_refl ||
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; destruct (depth p2) as [ | m ].
  apply max_lub.
  transitivity (depth p) ; omega || auto.
  apply depth_pres_plus ; auto.
  assert (max (depth p) (depth s) <= S (depth p)) ; omega || auto.
  apply max_lub ; omega || auto.
  simpl in Hleq_s.
  replace (depth q) with 0%nat in * by omega.
  rewrite max_0_l in Hleq_s.
  transitivity (depth t) ; auto.
  transitivity (depth p) ; auto.
  apply depth_pres_plus ; auto.
  apply max_lub.
  assert (depth t <= max (depth p) m) ; omega || auto.
  transitivity (depth p) ; apply le_max_l || auto.
  apply depth_pres_plus ; auto.
  assert (max (depth p) (depth s) <= S (max (depth p) m)) ; omega || auto.
  apply max_lub.
  rewrite succ_max_distr.
  transitivity (S (depth p)) ; omega || apply le_max_l.
  transitivity (depth (q · t)) ; auto.
  simpl ; apply max_lub.
  rewrite succ_max_distr.
  transitivity (S m) ; apply le_max_r || auto.
  rewrite succ_max_distr.
  transitivity (depth p).
  apply depth_pres_plus ; auto.
  transitivity (S (depth p)) ; apply le_max_l || auto.

  (* Invocation of comp_mult_ex results in a different nf *)
  destruct H as [ s [ Hbisim_s [ Hnf_s Hleq_s ] ] ].
  right ; exists (t · s) ; split ; [ | split ].
  apply bisim_trans with (emb (t · p * q · r)) ; 
    [ apply bisim_symm | ] ; auto.
  apply bisim_trans with (emb (t · s · 0)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_trans with (emb ((p * q · t) * 0)) ; auto.
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q · t) · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q · t · p * q · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  simpl ; repeat split ; auto.
  apply nf_mult_pres_plus with p ; auto.
  simpl in Hnf_mult.
  apply nf_mult_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * q · r)) ; auto.
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_trans with (emb ((p * q · t) * 0)) ; auto.
  apply RSP_sound.
  apply bisim_trans with (emb ((p * q · t) · p * q · r)) ;
    [ | apply bisim_symm ; apply B6_sound ].
  apply bisim_trans with (emb (p * q · t · p * q · r)) ; 
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
  simpl in Hnf_s ; tauto.
  simpl ; destruct (depth p2) as [ | m ] ; apply max_lub.
  transitivity (depth p) ; omega || auto.
  apply depth_pres_plus ; auto.
  simpl in Hleq_s ; replace (depth q) with 0%nat in * by omega.
  rewrite max_0_l in Hleq_s ; transitivity (S (depth t)) ; auto.
  assert (depth t <= depth p) by ( apply depth_pres_plus ; auto ) ; omega.
  assert (depth t <= max (depth p) m) ; omega || auto.
  transitivity (depth p) ; apply le_max_l || auto.
  apply depth_pres_plus ; auto.
  transitivity (1 + (depth (q · t)))%nat ; simpl ; auto.
  assert (max (depth q) (depth t) <= S (max (depth p) m)) ; omega || auto.
  apply max_lub.
  transitivity (S m) ; auto.
  assert (m <= max (depth p) m) ; omega || apply le_max_r.
  transitivity (depth p).
  apply depth_pres_plus ; auto.
  rewrite succ_max_distr.
  transitivity (S (depth p)) ; apply le_max_l || auto.

  (* Case where p -->+ t such that t · p * q · r <=> r does NOT exist *)
  left ; exists (p * q) ; split ; [ | split ; [ | split ] ].
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl || auto.
  simpl ; simpl in Hnf_mult ; repeat split ; auto.
  apply nf_mult_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ;
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply congr_right_compat with (p * p2 · r) ; tauto || auto.
  apply bisim_trans with (emb (p * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (p * (q · r))) ; 
    [ | apply bisim_symm ; apply BKS2_sound ].
  apply bisim_comp_star ; apply bisim_refl || auto.
  intros t Hplus Hbisim'.
  apply star_plus_fmt in Hplus ; destruct Hplus as [ H | [ H | H ] ].
  destruct H as [ t' [ Heq Hplus ] ] ; rewrite Heq in *.
  apply Hplus_ex ; exists t' ; split ; auto.
  apply bisim_trans with (emb ((t' · p * q) · r)) ; auto.
  apply bisim_symm ; apply B5_sound.
  rewrite H in * ; contradiction.
  apply Hcongr_q in H ; contradiction.
  simpl ; destruct (depth q) as [ | m ] ; 
    destruct (depth p2) as [ | n ] ; omega || auto.
  assert (depth p <= max (depth p) n) ; omega || apply le_max_l.
  assert (max (depth p) m <= max (depth p) n) ; omega || auto.
  apply max_lub ; apply le_max_l || auto.
  transitivity n ; omega || apply le_max_r.

  (* Case where IHp2 results in a different nf *)
  destruct H as [ q [ Hbisim_q [ Hnf_q Hleq_q ] ] ].
  right ; exists q ; split ; [ | split ] ; auto.
  simpl ; destruct (depth p2) as [ | m ] ; omega || auto.
  transitivity (S (S m)) ; omega || auto.
  assert (m <= max (depth p1) m) ; omega || apply le_max_r.
Qed. 

Lemma nf_mult_ex : forall (p r : T), exists (q : T), 
  emb (p · r) <=> emb (q · r) /\ nf_mult q r /\ depth q <= depth p.
Proof.
  intro p ; induction p ; intro r.
  exists 0 ; split ; [ | split ] ; simpl ; apply bisim_refl || auto.
  exists (act a) ; split ; [ | split ] ; simpl ; apply bisim_refl || auto.

  (* Case for p1 + p2 *)
  destruct (IHp1 r) as [ q1 [ Hbisim_q1 [ Hnf_q1 Hleq_q1 ] ] ].
  destruct (IHp2 r) as [ q2 [ Hbisim_q2 [ Hnf_q2 Hleq_q2 ] ] ].
  exists (q1 + q2) ; split ; [ | split ] ; simpl ; try tauto.
  apply bisim_trans with (emb (p1 · r + p2 · r)) ; apply B4_sound || auto.
  apply bisim_trans with (emb (q1 · r + q2 · r)) ; auto.
  apply bisim_comp_plus ; auto.
  apply bisim_symm ; apply B4_sound.
  apply max_lub.
  transitivity (depth p1) ; apply le_max_l || auto.
  transitivity (depth p2) ; apply le_max_r || auto.

  (* Case for p1 · p2 *)
  destruct (IHp1 (p2 · r)) as [ q1 [ Hbisim_q1 [ Hnf_q1 Hleq_q1 ] ] ].
  destruct (IHp2 r) as [ q2 [ Hbisim_q2 [ Hnf_q2 Hleq_q2 ] ] ].
  exists (q1 · q2) ; split ; [ | split ] ; auto.
  apply bisim_trans with (emb (p1 · p2 · r)) ; apply B5_sound || auto.
  apply bisim_trans with (emb (q1 · q2 · r)) ; auto.
  apply bisim_trans with (emb (q1 · p2 · r)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_symm ; apply B5_sound.
  simpl ; split ; auto.
  apply nf_mult_right_compat with (p2 · r) ; auto.
  simpl ; apply max_lub.
  transitivity (depth p1) ; apply le_max_l || auto.
  transitivity (depth p2) ; apply le_max_r || auto.

  (* Case for p1 * p2 *)
  destruct (IHp2 r) as [ q2 [ Hbisim_q2 [ Hnf_q2 Hleq_q2 ] ] ].
  destruct (IHp1 (p1 * p2 · r)) as [ q1 [ Hbisim_q1 [ Hnf_q1 Hleq_q1 ] ] ].
  assert (emb (p1 * p2 · r) <=> emb (q1 · p1 * p2 · r + p2 · r)) as Hstar_eq.
  apply bisim_trans with (emb ((p1 · p1 * p2 + p2) · r)).
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS1_sound.
  apply bisim_trans with (emb ((p1 · p1 * p2) · r + p2 · r)).
  apply B4_sound.
  apply bisim_comp_plus ; apply bisim_refl || auto.
  apply bisim_trans with (emb (p1 · p1 * p2 · r)) ; apply B5_sound || auto.
  apply RSP_sound in Hstar_eq.
  destruct (congr_ex q1 (q1 * p2 · r)) as [ [ s H ] | H ].
  apply nf_mult_right_compat with (p1 * p2 · r) ; auto.
  apply bisim_trans with (emb (q1 * (p2 · r))) ; auto.
  apply bisim_symm ; apply BKS2_sound.
  destruct H as [ Hbisim_s [ Hnf_s [ Hcongr_s Hleq_s ] ] ].
  assert (emb (s * p2 · r) <=> emb (q1 * p2 · r)) as Hstar_eq'.
  apply bisim_trans with (emb (s * (p2 · r))).
  apply BKS2_sound.
  apply bisim_symm ; apply RSP_sound.
  apply bisim_trans with (emb (q1 · q1 * p2 · r + p2 · r)).
  apply bisim_trans with (emb ((q1 · q1 * p2 + p2) · r)).
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS1_sound.
  apply bisim_trans with (emb ((q1 · q1 * p2) · r + p2 · r)).
  apply B4_sound.
  apply bisim_comp_plus ; apply bisim_refl || apply B5_sound.
  apply bisim_comp_plus ; apply bisim_refl || auto.
  exists (s * q2) ; split ; [ | split ] ; auto.
  apply bisim_trans with (emb (q1 * (p2 · r))) ; auto.
  apply bisim_trans with (emb (q1 * p2 · r)).
  apply bisim_symm ; apply BKS2_sound.
  apply bisim_symm ; auto.
  apply bisim_trans with (emb (s * p2 · r)) ; auto.
  apply bisim_trans with (emb (s * (q2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (s * (p2 · r))).
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_symm ; auto.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; split ; [ | split ] ; auto.
  apply nf_mult_right_compat with (q1 * p2 · r) ; auto.
  apply bisim_trans with (emb (s * p2 · r)) ; auto.
  apply bisim_symm ; auto.
  apply bisim_trans with (emb (s * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (s * (q2 · r))).
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS2_sound.
  apply congr_right_compat with (q1 * p2 · r) ; auto.
  apply bisim_trans with (emb (s * p2 · r)) ; auto.
  apply bisim_symm ; auto.
  apply bisim_trans with (emb (s * (p2 · r))) ; apply BKS2_sound || auto.
  apply bisim_trans with (emb (s * (q2 · r))) ; auto.
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; destruct (depth q2) as [ | m ] ; 
    destruct (depth p2) as [ | n ] ; omega || auto.
  assert (depth s <= max (depth p1) n) ; omega || auto.
  transitivity (depth q1) ; auto.
  transitivity (depth p1) ; apply le_max_l || auto.
  assert (max (depth s) m <= max (depth p1) n) ; omega || auto.
  apply max_lub.
  transitivity (depth q1) ; auto.
  transitivity (depth p1) ; apply le_max_l || auto.
  transitivity n ; omega || apply le_max_r.

  (* Congruence derivation results in a different nf *)
  destruct H as [ s [ Hbisim_s [ Hnf_s Hleq_s ] ] ].
  exists (s · 0) ; split ; [ | split ] ; auto.
  apply bisim_trans with (emb (s · 0)) ; auto.
  apply bisim_trans with (emb (q1 * (p2 · r))) ; auto.
  apply bisim_trans with (emb (q1 * p2 · r)) ; auto.
  apply bisim_symm ; apply BKS2_sound.
  apply bisim_trans with (emb (s · 0 · r)).
  apply bisim_comp_mult ; apply bisim_refl || 
    apply bisim_symm ; apply B7_sound.
  apply bisim_symm ; apply B5_sound.
  simpl in * ; split ; auto.
  apply nf_mult_right_compat with 0 ; tauto || auto.
  apply bisim_symm ; apply B7_sound.
  simpl ; destruct (depth p2) as [ | m ] ; rewrite max_0_r.
  transitivity (1 + depth q1)%nat ; simpl ; omega || auto.
  transitivity (1 + depth q1)%nat ; simpl ; omega || auto.
  assert (depth q1 <= max (depth p1) m) ; omega || auto.
  transitivity (depth p1) ; apply le_max_l || auto.
Qed.

Lemma normalization : forall (p : T),
  exists (q : T), emb p <=> emb q /\ nf q /\ depth q <= depth p.
Proof.
  intro p ; induction p.
  exists 0 ; split ; [ | split ] ; simpl ; apply bisim_refl || auto.
  exists (act a) ; split ; [ | split ] ; simpl ; apply bisim_refl || auto.

  (* Case for p1 + p2 *)
  destruct IHp1 as [ q1 [ Hbisim_q1 [ Hnf_q1 Hleq_q1 ] ] ].
  destruct IHp2 as [ q2 [ Hbisim_q2 [ Hnf_q2 Hleq_q2 ] ] ].
  exists (q1 + q2) ; split ; [ | split ] ; simpl ; try tauto.
  apply bisim_comp_plus ; auto.
  apply max_lub.
  transitivity (depth p1) ; [ auto | apply le_max_l ].
  transitivity (depth p2) ; [ auto | apply le_max_r ].

  (* Case for p1 · p2 *)
  destruct IHp2 as [ q2 [ Hbisim_q2 [ Hnf_q2 Hleq_q2 ] ] ].
  destruct (nf_mult_ex p1 q2) as [ q1 [ Hbisim_q1 [ Hnf_q1 Hleq_q1 ] ] ].
  exists (q1 · q2) ; split ; [ | split ] ; simpl ; try tauto.
  apply bisim_trans with (emb (p1 · q2)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || auto.
  apply max_lub.
  transitivity (depth p1) ; [ auto | apply le_max_l ].
  transitivity (depth p2) ; [ auto | apply le_max_r ].

  (* Case for p1 * p2 *)
  destruct IHp2 as [ q2 [ Hbisim_q2 [ Hnf_q2 Hleq_q2 ] ] ].
  destruct (nf_mult_ex p1 (p1 * p2)) as [ q1 [ Hbisim_q1 [ Hnf_q1 Hleq_q1 ] ] ].
  assert (emb (p1 * p2) <=> emb (q1 · p1 * p2 + p2)) as Hstar_eq.
  apply bisim_trans with (emb (p1 · p1 * p2 + p2)).
  apply bisim_symm ; apply BKS1_sound.
  apply bisim_comp_plus ; apply bisim_refl || auto.
  apply RSP_sound in Hstar_eq.
  destruct (congr_ex q1 (q1 * p2)) as [ H | H ] ; auto.
  apply nf_mult_right_compat with (p1 * p2) ; auto.
  destruct H as [ s [ Hbisim_s [ Hnf_s [ Hcongr_s Hleq_s ] ] ] ].
  assert (emb (q1 * p2) <=> emb (s * p2)) as Hstar_eq'.
  assert (emb (q1 * p2) <=> emb (s · q1 * p2 + p2)) as H.
  apply bisim_trans with (emb (q1 · q1 * p2 + p2)).
  apply bisim_symm ; apply BKS1_sound.
  apply bisim_comp_plus ; apply bisim_refl || auto.
  apply RSP_sound in H ; auto.
  exists (s * q2) ; split ; [ | split ] ; auto.
  apply bisim_trans with (emb (q1 * p2)) ; auto.
  apply bisim_trans with (emb (s * p2)) ; auto.
  apply bisim_comp_star ; apply bisim_refl || auto.
  simpl ; split ; [ | split ] ; auto.
  apply nf_mult_right_compat with (q1 * p2) ; auto.
  apply bisim_trans with (emb (s * p2)) ; auto.
  apply bisim_comp_star ; apply bisim_refl || auto.
  apply congr_right_compat with (q1 * p2) ; auto.
  apply bisim_trans with (emb (s * p2)) ; auto.
  apply bisim_comp_star ; apply bisim_refl || auto.
  simpl ; destruct (depth q2) as [ | m ] ; 
    destruct (depth p2) as [ | n ] ; omega || auto.
  assert (depth s <= max (depth p1) n) ; omega || auto.
  transitivity (depth q1) ; auto.
  transitivity (depth p1) ; apply le_max_l || auto.
  assert (max (depth s) m <= max (depth p1) n) ; omega || auto.
  apply max_lub.
  transitivity (depth q1) ; auto.
  transitivity (depth p1) ; apply le_max_l || auto.
  transitivity n ; apply le_max_r || omega.

  (* Congruence derivation results in different nf *)
  destruct H as [ q [ Hbisim_q [ Hnf_q Hleq_q ] ] ].
  exists (q · 0) ; split ; [ | split ] ; auto.
  apply bisim_trans with (emb (q1 * p2)) ; auto.
  simpl ; destruct (depth p2) as [ | m ] ; rewrite max_0_r.
  transitivity (1 + depth q1)%nat ; omega.
  transitivity (1 + depth q1)%nat ; simpl ; auto.
  assert (depth q1 <= max (depth p1) m) ; omega || auto.
  transitivity (depth p1) ; apply le_max_l || auto.
Qed.

Lemma next_term_in : forall (N : list (A * V)) (a : A),
  In (a, term) N -> sum N == (sum N + act a).
Proof.
  intro N ; induction N as [ | [ a' u ] N ] ; 
    intros a Hin ; simpl in * ; contradiction || auto.
  destruct Hin as [ H | Hin ].
  replace a' with a in * by ( inversion H ; auto ).
  replace u with term in * by ( inversion H ; auto ).
  apply trans with (act a + (act a + sum N)) ; apply B1 || auto.
  apply trans with (act a + act a + sum N) ; apply B2 || auto.
  apply comp_plus ; apply refl || apply symm ; apply B3.
  destruct u as [ | p ].
  apply trans with (act a' + (sum N + act a)) ; 
    [ | apply symm ; apply B2 ].
  apply comp_plus ; apply refl || apply IHN ; auto.
  apply trans with (act a' · p + (sum N + act a)) ;
    [ | apply symm ; apply B2 ].
  apply comp_plus ; apply refl || apply IHN ; auto.
Qed.

Lemma next_emb_in : forall (N : list (A * V)) (a : A) (p : T),
  In (a, emb p) N -> sum N == (sum N + act a · p).
Proof.
  intro N ; induction N as [ | [ a' u ] N ] ;
    intros a p Hin ; simpl in * ; contradiction || auto.
  destruct Hin as [ H | Hin ].
  replace a' with a in * by ( inversion H ; auto ).
  replace u with (emb p) in * by ( inversion H ; auto ).
  apply trans with (act a · p + (act a · p + sum N)) ; apply B1 || auto.
  apply trans with (act a · p + act a · p + sum N) ; apply B2 || auto.
  apply comp_plus ; apply refl || apply symm ; apply B3.
  destruct u as [ | q ].
  apply trans with (act a' + (sum N + act a · p)) ; 
    [ | apply symm ; apply B2 ].
  apply comp_plus ; apply refl || apply IHN ; auto.
  apply trans with (act a' · q + (sum N + act a · p)) ;
    [ | apply symm ; apply B2 ].
  apply comp_plus ; apply refl || apply IHN ; auto.
Qed.

Lemma next : forall (p q : T),
  (forall (a : A) (u : V), emb p -(a)-> u ->
    exists (v : V), emb q -(a)-> v /\ teq u v) ->
  (forall (a : A) (v : V), emb q -(a)-> v ->
    exists (u : V), emb p -(a)-> u /\ teq u v) -> p == q.
Proof.
  assert (forall (M N : list (A * V)), 
    (forall (a : A) (u : V), In (a, u) M ->
      exists (v : V), In (a, v) N /\ teq u v) -> 
    (sum M + sum N) == sum N) as Hmain.
  intro M ; induction M as [ | [ a u ] M ] ; intros N Hcond.
  simpl ; apply trans with (sum N + 0) ; apply B1 || apply B6.
  destruct u as [ | p ] ; simpl.
  apply trans with (sum N + act a).
  apply trans with (act a + sum N) ; apply B1 || auto.
  apply trans with (act a + (sum M + sum N)) ; [ apply B2 | ].
  apply comp_plus ; apply refl || apply IHM.
  intros a' u' Hin ; apply Hcond ; simpl ; auto.
  apply symm ; apply next_term_in.
  assert (In (a, term) ((a, term) :: M)) as H by ( simpl ; auto ).
  apply Hcond in H ; destruct H as [ v [ Hin Hteq ] ].
  destruct v as [ | q ] ; auto.
  unfold teq in Hteq ; contradiction.
  assert (In (a, emb p) ((a, emb p) :: M)) as H by ( simpl ; auto ).
  apply Hcond in H ; destruct H as [ v [ Hin Hteq ] ].
  destruct v as [ | q ] ; [ unfold teq in * ; contradiction | ].
  apply trans with (sum N + act a · q).
  apply trans with (act a · q + sum N) ; apply B1 || auto.
  apply trans with (act a · p + (sum M + sum N)) ; apply B2 || auto.
  apply comp_plus ; auto.
  apply comp_mult ; apply refl || unfold teq in * ; auto.
  apply IHM ; intros a' u' Hin'.
  apply Hcond ; simpl ; auto.
  apply symm ; apply next_emb_in ; auto.
  intros p q Hltr Hrtl.
  destruct (summation p) as [ Np [ Hiff_p Heq_p ] ].
  destruct (summation q) as [ Nq [ Hiff_q Heq_q ] ].
  apply trans with (sum Np) ; [ apply symm ; auto | ].
  apply trans with (sum Nq) ; [ | auto ].
  apply trans with (sum Np + sum Nq) ; [ apply symm | ].
  apply trans with (sum Nq + sum Np) ; apply B1 || auto.
  apply Hmain ; intros a u Hin.
  apply Hiff_q in Hin ; apply Hrtl in Hin.
  destruct Hin as [ v [ Hstep Hteq ] ].
  apply Hiff_p in Hstep ; exists v ; split ; auto.
  destruct u as [ | p' ] ; destruct v as [ | q' ] ; auto.
  unfold teq in * ; apply symm ; auto.
  apply Hmain ; intros a u Hin.
  apply Hiff_p in Hin ; apply Hltr in Hin.
  destruct Hin as [ v [ Hstep Hteq ] ].
  apply Hiff_q in Hstep ; exists v ; split ; auto.
Qed.

Lemma sum_step : forall (M : list (A * V)) (a : A) (u : V),
  emb (sum M) -(a)-> u -> In (a, u) M.
Proof.
  intro M ; induction M as [ | [ a' u' ] M ] ; intros a u Hstep.
  simpl in Hstep ; inversion Hstep.
  simpl in Hstep ; destruct u' as [ | p' ] ; simpl.
  apply step_plus_fmt in Hstep ; destruct Hstep as [ H | H ].
  replace a' with a in * by ( inversion H ; auto ).
  replace u with term in * by ( inversion H ; auto ) ; auto.
  apply IHM in H ; auto.
  apply step_plus_fmt in Hstep ; destruct Hstep as [ Hstep | H ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p'' [ _ H ] ] ; inversion H.
  destruct H as [ H Heq ] ; rewrite Heq in *.
  replace a' with a in * by ( inversion H ; auto ) ; auto.
  apply IHM in H ; auto.
Qed.

Lemma step_sum : forall (M : list (A * V)) (a : A) (u : V),
  In (a, u) M -> emb (sum M) -(a)-> u.
Proof.
  intro M ; induction M as [ | [ a' u' ] M ] ; intros a u Hin.
  simpl in Hin ; contradiction.
  simpl in Hin ; destruct Hin as [ H | Hin ] ; simpl ; destruct u' as [ | q ].
  replace a' with a in * by ( inversion H ; auto ).
  replace u with term in * by ( inversion H ; auto ).
  apply step_plus_left ; apply step_act.
  replace a' with a in * by ( inversion H ; auto ).
  replace u with (emb q) in * by ( inversion H ; auto ).
  apply step_plus_left ; apply step_mult_right ; apply step_act.
  apply IHM in Hin ; apply step_plus_right ; auto.
  apply IHM in Hin ; apply step_plus_right ; auto.
Qed.

Lemma eq_list_eq_sum : forall (M N : list (A * V)),
  eqlist M N -> sum M == sum N.
Proof.
  intros M N Heqlist ; apply next.
  intros a u Hstep ; apply sum_step in Hstep.
  apply Heqlist in Hstep ; exists u ; split ; auto.
  apply step_sum ; auto.
  destruct u ; unfold teq ; apply refl || auto.
  intros a u Hstep ; apply sum_step in Hstep.
  apply Heqlist in Hstep ; exists u ; split ; auto.
  apply step_sum ; auto.
  destruct u ; unfold teq ; apply refl || auto.
Qed.

Lemma single_split : forall (M : list (A * V)) (p : T),
  exists (N : list (A * V)), forall (a : A) (u : V),
    In (a, u) N <-> In (a, u) M /\ exists (v : V), emb p -(a)-> v /\ u <=> v.
Proof.
  intro M ; induction M as [ | [ a w ] M ] ; intro p.
  exists nil ; intros a u ; split ; intro H ; simpl in * ; try tauto.
  destruct (IHM p) as [ N Hiff ].
  destruct (LEM (exists (v : V), emb p -(a)-> v /\ w <=> v)) as [ H | H ].
  destruct H as [ v [ Hstep Hbisim ] ].
  exists ((a, w) :: N) ; intros a' u ; split ; intro H.
  simpl in H ; destruct H as [ H | H ].
  simpl ; split ; auto.
  replace a' with a in * by ( inversion H ; auto ).
  exists v ; split ; auto.
  replace w with u in * by ( inversion H ; auto ) ; auto.
  apply Hiff in H ; simpl ; split ; tauto || auto.
  simpl in H ; destruct H as [ [ H | H ] Hex ].
  simpl ; auto.
  simpl ; right ; apply Hiff ; split ; auto.
  exists N ; intros a' u ; split ; intro H'.
  apply Hiff in H' ; destruct H' as [ Hin Hex ].
  simpl ; split ; auto.
  simpl in H' ; destruct H' as [ [ H' | H' ] Hex ].
  replace a' with a in * by ( inversion H' ; auto ).
  replace w with u in * by ( inversion H' ; auto ) ; contradiction.
  apply Hiff ; split ; auto.
Qed.

Lemma single_split_mult : forall (M : list (A * V)) (p q : T),
  exists (N : list (A * V)), forall (a : A) (u : V),
    In (a, u) N <-> In (a, u) M /\ exists (v : V), emb p -(a)-> v /\ 
      emb (mult' u q) <=> v.
Proof.
  intro M ; induction M as [ | [ a w ] M ] ; intros p q.
  exists nil ; intros a u ; split ; intro H ; simpl in * ; try tauto.
  destruct (IHM p q) as [ N Hiff ].
  destruct (LEM (exists (v : V), emb p -(a)-> v /\ 
    emb (mult' w q) <=> v)) as [ H | H ].
  destruct H as [ v [ Hstep Hbisim ] ].
  exists ((a, w) :: N) ; intros a' u ; split ; intro H.
  simpl in H ; destruct H as [ H | H ].
  simpl ; split ; auto.
  replace a' with a in * by ( inversion H ; auto ).
  exists v ; split ; auto.
  replace w with u in * by ( inversion H ; auto ) ; auto.
  apply Hiff in H ; simpl ; split ; tauto || auto.
  simpl in H ; destruct H as [ [ H | H ] Hex ].
  simpl ; auto.
  simpl ; right ; apply Hiff ; split ; auto.
  exists N ; intros a' u ; split ; intro H'.
  apply Hiff in H' ; destruct H' as [ Hin Hex ].
  simpl ; split ; auto.
  simpl in H' ; destruct H' as [ [ H' | H' ] Hex ].
  replace a' with a in * by ( inversion H' ; auto ).
  replace w with u in * by ( inversion H' ; auto ) ; contradiction.
  apply Hiff ; split ; auto.
Qed.

Lemma double_split : forall (p q r : T) (M N : list (A * V)),
  emb (sum M · p + sum N) <=> emb (q + r) -> exists (Mq Mr Nq Nr : list (A * V)),
    eqlist M (Mq ++ Mr) /\ eqlist N (Nq ++ Nr) /\
      emb (sum Mq · p + sum Nq) <=> emb q /\
      emb (sum Mr · p + sum Nr) <=> emb r.
Proof.
  intros p q r M N Hbisim.
  destruct (single_split_mult M q p) as [ Mq Hiff_Mq ].
  destruct (single_split_mult M r p) as [ Mr Hiff_Mr ].
  destruct (single_split N q) as [ Nq Hiff_Nq ].
  destruct (single_split N r) as [ Nr Hiff_Nr ].
  exists Mq ; exists Mr ; exists Nq ; exists Nr ;
    split ; [ | split ; [ | split ] ].

  (* eqlist M (Mq ++ Mr) *)
  intros a u ; split ; intro Hin.
  destruct u as [ | s ].
  assert (emb (sum M · p + sum N) -(a)-> emb p) as Hstep.
  apply step_plus_left ; apply step_mult_right ; apply step_sum ; auto.
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  apply HinR in Hstep ; destruct Hstep as [ v [ Hstep HR ] ].
  apply step_plus_fmt in Hstep ; destruct Hstep as [ Hstep | Hstep ].
  apply in_or_app ; left ; apply Hiff_Mq ; split ; auto.
  exists v ; split ; auto.
  simpl ; exists R ; split ; auto.
  apply in_or_app ; right ; apply Hiff_Mr ; split ; auto.
  exists v ; split ; auto.
  simpl ; exists R ; split ; auto.
  assert (emb (sum M · p + sum N) -(a)-> emb (s · p)) as Hstep.
  apply step_plus_left ; apply step_mult_left ; apply step_sum ; auto.
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  apply HinR in Hstep ; destruct Hstep as [ v [ Hstep HR ] ].
  apply step_plus_fmt in Hstep ; destruct Hstep as [ Hstep | Hstep ].
  apply in_or_app ; left ; apply Hiff_Mq ; split ; auto.
  exists v ; split ; simpl ; auto.
  exists R ; split ; auto.
  apply in_or_app ; right ; apply Hiff_Mr ; split ; auto.
  exists v ; split ; simpl ; auto.
  exists R ; split ; auto.
  apply in_app_or in Hin ; destruct Hin as [ Hin | Hin ].
  apply Hiff_Mq in Hin ; tauto.
  apply Hiff_Mr in Hin ; tauto.

  (* eqlist N (Nq ++ Nr) *)
  intros a u ; split ; intro Hin.
  assert (emb (sum M · p + sum N) -(a)-> u) as Hstep.
  apply step_plus_right ; apply step_sum ; auto.
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  apply HinR in Hstep ; destruct Hstep as [ v [ Hstep HR ] ].
  apply step_plus_fmt in Hstep ; destruct Hstep as [ Hstep | Hstep ].
  apply in_or_app ; left ; apply Hiff_Nq ; split ; auto.
  exists v ; split ; auto.
  exists R ; split ; auto.
  apply in_or_app ; right ; apply Hiff_Nr ; split ; auto.
  exists v ; split ; auto.
  exists R ; split ; auto.
  apply in_app_or in Hin ; destruct Hin as [ Hin | Hin ].
  apply Hiff_Nq in Hin ; tauto.
  apply Hiff_Nr in Hin ; tauto.

  (* sum Mq · p + sum Nq <=> q *)
  apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ s [ Heq Hstep ] ] ; rewrite Heq in *.
  apply sum_step in Hstep ; apply Hiff_Mq in Hstep.
  destruct Hstep as [ _ [ v [ Hstep Hbisim' ] ] ].
  exists v ; split ; simpl in * ; auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  apply sum_step in Hstep ; apply Hiff_Mq in Hstep.
  destruct Hstep as [ _ [ v [ Hstep Hbisim' ] ] ].
  exists v ; split ; simpl in * ; auto.
  apply sum_step in H ; apply Hiff_Nq in H.
  destruct H as [ _ [ v [ Hstep Hbisim' ] ] ].
  exists v ; split ; auto.
  intros a v Hstep ; assert (emb (q + r) -(a)-> v) as H by
    ( apply step_plus_left ; auto ).
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  apply HinR in H ; destruct H as [ u [ H HR ] ].
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ s [ Heq H ] ] ; rewrite Heq in *.
  apply sum_step in H ; exists (emb (s · p)) ; split.
  apply step_plus_left ; apply step_mult_left ; apply step_sum.
  apply Hiff_Mq ; split ; auto.
  exists v ; split ; auto.
  simpl ; exists R ; split ; auto.
  simpl ; exists R ; split ; auto.
  destruct H as [ Hstep' Heq ] ; rewrite Heq in *.
  exists (emb p) ; split ; auto.
  apply step_plus_left ; apply step_mult_right.
  apply step_sum ; apply Hiff_Mq.
  apply sum_step in Hstep' ; split ; auto.
  exists v ; split ; auto.
  simpl ; exists R ; split ; auto.
  simpl ; exists R ; split ; auto.
  exists u ; split ; auto.
  apply step_plus_right ; apply step_sum.
  apply Hiff_Nq ; apply sum_step in H ; split ; auto.
  exists v ; split ; auto.
  exists R ; split ; auto.
  exists R ; split ; auto.

  (* sum Mr · p + sum Nr <=> r *)
  apply bisim_next.
  split ; intro H ; inversion H.
  intros a u H ; apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ s [ Heq Hstep ] ] ; rewrite Heq in *.
  apply sum_step in Hstep ; apply Hiff_Mr in Hstep.
  destruct Hstep as [ _ [ v [ Hstep Hbisim' ] ] ].
  exists v ; split ; simpl in * ; auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  apply sum_step in Hstep ; apply Hiff_Mr in Hstep.
  destruct Hstep as [ _ [ v [ Hstep Hbisim' ] ] ].
  exists v ; split ; simpl in * ; auto.
  apply sum_step in H ; apply Hiff_Nr in H.
  destruct H as [ _ [ v [ Hstep Hbisim' ] ] ].
  exists v ; split ; auto.
  intros a v Hstep ; assert (emb (q + r) -(a)-> v) as H by
    ( apply step_plus_right ; auto ).
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  apply HinR in H ; destruct H as [ u [ H HR ] ].
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ s [ Heq H ] ] ; rewrite Heq in *.
  apply sum_step in H ; exists (emb (s · p)) ; split.
  apply step_plus_left ; apply step_mult_left ; apply step_sum.
  apply Hiff_Mr ; split ; auto.
  exists v ; split ; auto.
  simpl ; exists R ; split ; auto.
  simpl ; exists R ; split ; auto.
  destruct H as [ Hstep' Heq ] ; rewrite Heq in *.
  exists (emb p) ; split ; auto.
  apply step_plus_left ; apply step_mult_right.
  apply step_sum ; apply Hiff_Mr.
  apply sum_step in Hstep' ; split ; auto.
  exists v ; split ; auto.
  simpl ; exists R ; split ; auto.
  simpl ; exists R ; split ; auto.
  exists u ; split ; auto.
  apply step_plus_right ; apply step_sum.
  apply Hiff_Nr ; apply sum_step in H ; split ; auto.
  exists v ; split ; auto.
  exists R ; split ; auto.
  exists R ; split ; auto.
Qed.

Lemma teq_symm : forall (u v : V), teq u v -> teq v u.
Proof.
  intros u v H ; destruct u as [ | p ] ; destruct v as [ | q ] ; auto.
  unfold teq in * ; apply symm ; auto.
Qed.

Lemma RSP_inv_sound : forall (p q r : T),
  emb p <=> emb (q * r) -> emb p <=> emb (q · p + r).
Proof.
  intros p q r H ; apply bisim_trans with (emb (q * r)) ; auto.
  apply bisim_trans with (emb (q · q * r + r)).
  apply bisim_symm ; apply BKS1_sound.
  apply bisim_comp_plus ; apply bisim_refl || auto.
  apply bisim_comp_mult ; apply bisim_refl || apply bisim_symm ; auto.
Qed.

Lemma complete_split_mult : forall (p q r s t : T) (M N : list (A * V)),
  emb (sum M · p * q + sum N) <=> emb (r · s) -> nf (p * q) ->
  (forall (u v : V) (a : A), emb q -(a)-> u -> u <=> v -> teq u v) ->
  (forall (x y : T), depth x < depth (p * q) -> emb x <=> emb y -> x == y) ->
  (forall (t u : V) (a : A), In (a, t) N -> t <=> u -> teq t u) ->
  p -->* t -> (forall (a : A) (u : V), In (a, u) M -> emb t -(a)-> u) ->
  (forall (M' N' : list (A * V)) (u : T), 
    emb (sum M' · p * q + sum N') <=> emb s -> p -->* u ->
    (forall (a : A) (v : V), In (a, v) M' -> emb u -(a)-> v) ->
    (forall (v w : V) (a : A), In (a, v) N' -> v <=> w -> teq v w) ->
    (sum M' · p * q + sum N') == s) ->
  (sum M · p * q + sum N) == (r · s).
Proof.
  intros p q r ; revert p q ; induction r ;
    intros p q s t M N Hbisim Hnf Hleft_top IHprov IHN Hclos HM Hright_top.

  (* Case for 0 *)
  apply next ; apply bisim_fwd in Hbisim.
  intros a u Hstep ; apply Hbisim in Hstep.
  destruct Hstep as [ v [ Hstep Hbisim' ] ].
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ x [ Heq Hstep ] ] ; inversion Hstep.
  destruct H as [ H _ ] ; inversion H.
  intros a v Hstep ; apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ x [ _ H ] ] ; inversion H.
  destruct H as [ H _ ] ; inversion H.

  (* Case for a \in A *)
  assert (forall (a' : A) (u v : V),
    emb (sum M · p * q + sum N) -(a')-> u -> 
    emb (act a · s) -(a')-> v -> u <=> v -> teq u v) as Hnext.
  intros a' u v Hstep_l Hstep_r Hbisim'.
  apply step_mult_fmt in Hstep_r ; destruct Hstep_r as [ H | H ].
  destruct H as [ x [ Heq Hstep ] ] ; rewrite Heq in * ; inversion Hstep.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  apply step_plus_fmt in Hstep_l ; destruct Hstep_l as [ H | H ].
  replace a' with a in * by ( inversion Hstep ; auto ).
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq' Hstep' ] ] ; rewrite Heq' in *.
  unfold teq ; destruct (summation p') as [ K [ Hiff_K Heq_K ] ].
  apply trans with (sum K · p * q).
  apply comp_mult ; apply refl || apply symm ; auto.
  apply trans with (sum K · p * q + sum nil) ; 
    [ apply symm ; apply B6 | ].
  apply Hright_top with p'.
  simpl ; apply bisim_trans with (emb (sum K · p * q)) ; apply B6_sound || auto.
  apply bisim_trans with (emb (p' · p * q)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || apply soundness ; auto.
  apply sum_step in Hstep' ; apply HM in Hstep'.
  apply clos_clos with t ; auto.
  apply clos_trans with p' a ; apply clos_refl || auto.
  intros a'' w Hin ; apply Hiff_K ; auto.
  intros u' v' a'' Hin ; simpl in Hin ; contradiction.
  destruct H as [ Hstep' Heq' ] ; rewrite Heq' in * ; unfold teq.
  apply trans with (p · p * q + q) ; [ apply symm ; apply BKS1 | ].
  destruct (summation p) as [ K [ Hiff_K Heq_K ] ].
  destruct (summation q) as [ L [ Hiff_L Heq_L ] ].
  apply trans with (sum K · p * q + sum L).
  apply comp_plus ; [ | apply symm ; auto ].
  apply comp_mult ; apply refl || apply symm ; auto.
  apply Hright_top with p ; apply clos_refl || auto.
  apply bisim_trans with (emb (p · p * q + q)) ; auto.
  apply bisim_comp_plus ; auto.
  apply bisim_comp_mult ; apply bisim_refl || apply soundness ; auto.
  apply soundness ; auto.
  apply bisim_trans with (emb (p * q)) ; apply BKS1_sound || auto.
  intros a'' w Hin ; apply Hiff_K ; auto.
  intros u' v' a'' Hin Hbisim''.
  apply Hleft_top with a'' ; auto.
  apply Hiff_L ; auto.
  apply sum_step in H.
  apply IHN with a' ; auto.
  apply bisim_fwd in Hbisim ; apply next.
  intros a' x Hstep_x.
  assert (emb (sum M · p * q + sum N) -(a')-> x) as Hstep by auto.
  apply Hbisim in Hstep ; destruct Hstep as [ y [ Hstep_y Hbisim' ] ].
  exists y ; split ; auto.
  apply Hnext with a' ; auto.
  intros a' y Hstep_y.
  assert (emb (act a · s) -(a')-> y) as Hstep by auto.
  apply Hbisim in Hstep ; destruct Hstep as [ x [ Hstep_x Hbisim' ] ].
  exists x ; split ; auto.
  apply Hnext with a' ; auto.

  (* Case for r1 + r2 *)
  apply trans with (r1 · s + r2 · s) ; [ | apply symm ; apply B4 ].
  destruct (double_split (p * q) (r1 · s) (r2 · s) M N) as
    [ M1 [ M2 [ N1 [ N2 H ] ] ] ] ; auto.
  apply bisim_trans with (emb ((r1 + r2) · s)) ; apply B4_sound || auto.
  destruct H as [ HMeqlist [ HNeqlist [ Hbisim_r1 Hbisim_r2 ] ] ].
  apply trans with (sum M1 · p * q + sum N1 + (sum M2 · p * q + sum N2)).
  apply trans with (sum M1 · p * q + sum N1 + sum M2 · p * q + sum N2) ;
    [ | apply B2 ].
  apply trans with (sum M1 · p * q + sum M2 · p * q + sum N1 + sum N2).
  apply trans with (sum M1 · p * q + sum M2 · p * q + (sum N1 + sum N2)) ;
    [ | apply symm ; apply B2 ].
  apply comp_plus.
  apply trans with ((sum M1 + sum M2) · p * q) ; apply B4 || auto.
  apply comp_mult ; apply refl || auto.
  apply trans with (sum (M1 ++ M2)) ; apply sum_app || auto.
  apply eq_list_eq_sum ; auto.
  apply trans with (sum (N1 ++ N2)) ; apply sum_app || auto.
  apply eq_list_eq_sum ; auto.
  apply comp_plus ; apply refl || auto.
  apply trans with (sum M1 · p * q + (sum M2 · p * q + sum N1)) ;
    [ apply B2 | ].
  apply trans with (sum M1 · p * q + (sum N1 + sum M2 · p * q)) ;
    [ | apply symm ; apply B2 ].
  apply comp_plus ; apply refl || apply B1.
  apply comp_plus ; [ apply IHr1 with t | apply IHr2 with t ] ; auto.
  intros u v a Hin Hbisim' ; apply IHN with a ; auto.
  apply HNeqlist ; apply in_or_app ; auto.
  intros a u Hin ; apply HM ; auto.
  apply HMeqlist ; apply in_or_app ; auto.
  intros u v a Hin Hbisim' ; apply IHN with a ; auto.
  apply HNeqlist ; apply in_or_app ; auto.
  intros a u Hin ; apply HM ; auto.
  apply HMeqlist ; apply in_or_app ; auto.
 
  (* Case for r1 · r2 *)
  apply trans with (r1 · r2 · s) ; [ | apply symm ; apply B5 ].
  apply IHr1 with t ; auto.
  apply bisim_trans with (emb ((r1 · r2) · s)) ; apply B5_sound || auto.
  intros M' N' u Hbisim' Hclos' HM' HN'.
  apply IHr2 with u ; auto.

  (* Case for r1 * r2 *)
  apply trans with (r1 * (r2 · s)) ; [ | apply symm ; apply BKS2 ].
  apply RSP.
  destruct (double_split (p * q) (r1 · (sum M · p * q + sum N)) (r2 · s) M N) as
    [ M1 [ M2 [ N1 [ N2 H ] ] ] ] ; auto.
  assert (emb (sum M · p * q + sum N) <=> emb (r1 * (r2 · s))) as Hbisim_inv.
  apply bisim_trans with (emb (r1 * r2 · s)) ; apply BKS2_sound || auto.
  apply RSP_inv_sound in Hbisim_inv ; auto.
  destruct H as [ HeqlistM [ HeqlistN [ Hbisim_r1 Hbisim_r2 ] ] ].
  apply trans with (sum M1 · p * q + sum N1 + (sum M2 · p * q + sum N2)).
  apply trans with (sum M1 · p * q + sum N1 + sum M2 · p * q + sum N2) ;
    apply B2 || auto.
  apply trans with (sum M1 · p * q + sum M2 · p * q + sum N1 + sum N2).
  apply trans with (sum M1 · p * q + sum M2 · p * q + (sum N1 + sum N2)) ;
    [ | apply symm ; apply B2 ].
  apply comp_plus.
  apply trans with ((sum M1 + sum M2) · p * q) ; apply B4 || auto.
  apply comp_mult ; apply refl || auto.
  apply trans with (sum (M1 ++ M2)) ; apply sum_app || auto.
  apply eq_list_eq_sum ; auto.
  apply trans with (sum (N1 ++ N2)) ; apply sum_app || auto.
  apply eq_list_eq_sum ; auto.
  apply comp_plus ; apply refl || auto.
  apply trans with (sum M1 · p * q + (sum M2 · p * q + sum N1)) ;
    [ apply B2 | ].
  apply trans with (sum M1 · p * q + (sum N1 + sum M2 · p * q)) ; 
    [ | apply symm ; apply B2 ].
  apply comp_plus ; apply refl || apply B1.
  apply comp_plus.
  apply IHr1 with t ; auto.
  intros u v a Hin Hbisim'.
  apply IHN with a ; auto.
  apply HeqlistN ; apply in_or_app ; auto.
  intros a u Hin ; apply HM.
  apply HeqlistM ; apply in_or_app ; auto.

  (* Congruence application *)
  intros M' N' u Hbisim' Hclos' IHM' IHN'.
  assert (forall (a : A) (u v : V), emb (sum M' · p * q + sum N') -(a)-> u ->
    emb (sum M · p * q + sum N) -(a)-> v -> u <=> v -> teq u v) as Hnext.
  intros a w v H H' Hbisim''.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_plus_fmt in H' ; destruct H' as [ H' | H' ].
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ x [ Heq_x Hstep_x ] ] ; rewrite Heq_x in *.
  apply sum_step in Hstep_x ; apply IHM' in Hstep_x.
  apply step_mult_fmt in H' ; destruct H' as [ H' | H' ].
  destruct H' as [ y [ Heq_y Hstep_y ] ] ; rewrite Heq_y in *.
  apply sum_step in Hstep_y ; apply HM in Hstep_y.
  unfold teq ; apply comp_mult ; apply refl || auto.
  apply IHprov ; auto.
  assert (depth x <= depth p) as Hpx.
  apply depth_pres_plus.
  apply clos_init_cases in Hclos' ; destruct Hclos' as [ H | H ].
  rewrite <- H in * ; exists a ; exists x ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with u ; auto.
  apply clos_trans with x a ; apply clos_refl || auto.
  assert (depth p < depth (p * q)) ; omega || auto.
  simpl ; destruct (depth q) ; auto.
  rewrite succ_max_distr.
  assert (S (depth p) <= max (S (depth p)) (S n)) ; omega || apply le_max_l.
  apply congruence with (p * q) ; auto.
  apply comp_plus_left.
  apply congr_pres_plus with p ; solve [ simpl in * ; tauto ] || auto.
  apply clos_init_cases in Hclos' ; destruct Hclos' as [ H | H ].
  rewrite <- H in * ; exists a ; exists x ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with u ; auto.
  apply clos_trans with x a ; apply clos_refl || auto.
  apply congr_pres_plus with p ; solve [ simpl in * ; tauto ] || auto.
  apply clos_init_cases in Hclos ; destruct Hclos as [ H | H ].
  rewrite <- H in * ; exists a ; exists y ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with t ; auto.
  apply clos_trans with y a ; apply clos_refl || auto.
  destruct H' as [ Hstep Heq ] ; rewrite Heq in *.
  assert (congr p (p * q)) as Hcongr by ( simpl in * ; tauto ).
  apply Hcongr in Hbisim'' ; contradiction || auto.
  apply clos_init_cases in Hclos' ; destruct Hclos' as [ H | H ].
  rewrite <- H in * ; exists a ; exists x ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep' Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with u ; auto.
  apply clos_trans with x a ; apply clos_refl || auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  apply step_mult_fmt in H' ; destruct H' as [ H' | H' ].
  destruct H' as [ y [ Heq' Hstep' ] ] ; rewrite Heq' in *.
  apply sum_step in Hstep' ; apply HM in Hstep'.
  assert (congr p (p * q)) as Hcongr by ( simpl in * ; tauto ).
  apply bisim_symm in Hbisim'' ; apply Hcongr in Hbisim'' ; contradiction || auto.
  apply clos_init_cases in Hclos ; destruct Hclos as [ H | H ].
  rewrite <- H in * ; exists a ; exists y ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep'' Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with t ; auto.
  apply clos_trans with y a ; apply clos_refl || auto.
  destruct H' as [ Hstep' Heq' ] ; rewrite Heq' in *.
  unfold teq ; apply refl.
  apply sum_step in H' ; apply teq_symm ; apply IHN with a ;
    apply bisim_symm || auto ; auto.
  apply IHN' with a ; apply sum_step in H ; auto.

  (* Application of theorem next using the previous assertion *)
  apply next ; apply bisim_fwd in Hbisim'.
  intros a x Hstep ; auto.
  assert (emb (sum M' · p * q + sum N') -(a)-> x) as Hstep_x by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ y [ Hstep_y Hbisim'' ] ].
  exists y ; split ; auto.
  apply Hnext with a ; auto.
  intros a y Hstep ; auto.
  assert (emb (sum M · p * q + sum N) -(a)-> y) as Hstep_y by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ x [ Hstep_x Hbisim'' ] ].
  exists x ; split ; auto.
  apply Hnext with a ; auto.

  (* Solve the r2 case *)
  apply IHr2 with t ; auto.
  intros u v a Hin Hbisim' ; apply IHN with a ; auto.
  apply HeqlistN ; apply in_or_app ; auto.
  intros a u Hin ; apply HM.
  apply HeqlistM ; apply in_or_app ; auto.
Qed.

Lemma complete_split : forall (p q r s : T) (M N : list (A * V)),
  emb (sum M · p * q + sum N) <=> emb r -> nf (p * q) ->
  (forall (u v : V) (a : A), emb q -(a)-> u -> u <=> v -> teq u v) ->
  (forall (x y : T), depth x < depth (p * q) -> emb x <=> emb y -> x == y) ->
  (forall (t u : V) (a : A), In (a, t) N -> t <=> u -> teq t u) ->
  p -->* s -> (forall (a : A) (u : V), In (a, u) M -> emb s -(a)-> u) ->
  (sum M · p * q + sum N) == r.
Proof.
  intros p q r ; revert p q ; induction r ;
    intros p q s M N Hbisim Hnf Hleft_top IHprov IHN Hclos HM.
 
  (* Case for 0 *)
  apply next ; apply bisim_fwd in Hbisim.
  intros a u Hstep ; apply Hbisim in Hstep.
  destruct Hstep as [ v [ H _ ] ] ; inversion H.
  intros a v H ; inversion H.

  (* Case for a \in A *)
  apply next ; apply bisim_fwd in Hbisim.
  intros a' u Hstep ; apply Hbisim in Hstep.
  destruct Hstep as [ v [ Hstep Hbisim' ] ].
  replace a' with a in * by ( inversion Hstep ; auto ).
  replace v with term in * by ( inversion Hstep ; auto ).
  exists term ; split ; auto.
  destruct u as [ | t ] ; unfold teq ; auto.
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  intros a' v Hstep ; assert (emb (act a) -(a')-> v) as Hstep_act by auto.
  apply Hbisim in Hstep ; destruct Hstep as [ u [ Hstep Hbisim' ] ].
  replace a' with a in * by ( inversion Hstep_act ; auto ).
  replace v with term in * by ( inversion Hstep_act ; auto ).
  exists u ; split ; auto.
  destruct u as [ | t ] ; unfold teq ; auto.
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.

  (* Case for r1 + r2 *)
  destruct (double_split (p * q) r1 r2 M N) as 
    [ Mr1 [ Mr2 [ Nr1 [ Nr2 H ] ] ] ] ; auto.
  destruct H as [ HeqM [ HeqN [ Hbisim_r1 Hbisim_r2 ] ] ].
  apply trans with (sum Mr1 · p * q + sum Nr1 + (sum Mr2 · p * q + sum Nr2)).
  apply trans with (sum Mr1 · p * q + sum Nr1 + sum Mr2 · p * q + sum Nr2) ;
    apply B2 || auto.
  apply trans with (sum Mr1 · p * q + sum Mr2 · p * q + sum Nr1 + sum Nr2).
  apply trans with (sum Mr1 · p * q + sum Mr2 · p * q + (sum Nr1 + sum Nr2)) ;
    [ apply comp_plus | apply symm ; apply B2 ].
  apply trans with ((sum Mr1 + sum Mr2) · p * q) ; apply B4 || auto.
  apply comp_mult ; apply refl || auto.
  apply trans with (sum (Mr1 ++ Mr2)) ; apply sum_app || auto.
  apply eq_list_eq_sum ; auto.
  apply trans with (sum (Nr1 ++ Nr2)) ; apply sum_app || auto.
  apply eq_list_eq_sum ; auto.
  apply comp_plus ; apply refl || auto.
  apply trans with (sum Mr1 · p * q + (sum Mr2 · p * q + sum Nr1)) ;
    [ apply B2 | ].
  apply trans with (sum Mr1 · p * q + (sum Nr1 + sum Mr2 · p * q)) ;
    [ | apply symm ; apply B2 ].
  apply comp_plus ; apply refl || apply B1.
  apply comp_plus ; [ apply IHr1 with s | apply IHr2 with s ] ; auto.
  intros t u a Hin Hbisim' ; apply IHN with a ; auto.
  apply HeqN ; apply in_or_app ; auto.
  intros a u Hin ; apply HM ; apply HeqM ; apply in_or_app ; auto.
  intros t u a Hin Hbisim' ; apply IHN with a ; auto.
  apply HeqN ; apply in_or_app ; auto.
  intros a u Hin ; apply HM ; apply HeqM ; apply in_or_app ; auto.

  (* Case for r1 · r2 *)
  apply complete_split_mult with s ; auto.
  intros M' N' u Hbisim' Hclos' HM' IHN'.
  apply IHr2 with u ; auto.

  (* Case for r1 * r2 *)
  apply RSP.
  destruct (double_split (p * q) (r1 · (sum M · p * q + sum N)) r2 M N) as
    [ M1 [ M2 [ N1 [ N2 H ] ] ] ].
  apply RSP_inv_sound in Hbisim ; auto.
  destruct H as [ HMeqlist [ HNeqlist [ Hbisim_left Hbisim_right ] ] ].
  apply trans with (sum M1 · p * q + sum N1 + (sum M2 · p * q + sum N2)).
  apply trans with (sum M1 · p * q + sum N1 + sum M2 · p * q + sum N2) ;
    apply B2 || auto.
  apply trans with (sum M1 · p * q + sum M2 · p * q + sum N1 + sum N2).
  apply trans with (sum M1 · p * q + sum M2 · p * q + (sum N1 + sum N2)) ;
    [ | apply symm ; apply B2 ].
  apply comp_plus.
  apply trans with ((sum M1 + sum M2) · p * q) ; apply B4 || auto.
  apply comp_mult ; apply refl || auto.
  apply trans with (sum (M1 ++ M2)) ; apply sum_app || auto.
  apply eq_list_eq_sum ; auto.
  apply trans with (sum (N1 ++ N2)) ; apply sum_app || auto.
  apply eq_list_eq_sum ; auto.
  apply comp_plus ; apply refl || auto.
  apply trans with (sum M1 · p * q + (sum M2 · p * q + sum N1)) ;
    apply B2 || auto.
  apply trans with (sum M1 · p * q + (sum N1 + sum M2 · p * q)) ;
    [ | apply symm ; apply B2 ].
  apply comp_plus ; apply refl || apply B1.
  apply comp_plus.
  apply complete_split_mult with s ; auto.
  intros t u a Hin Hbisim' ; apply IHN with a ; auto.
  apply HNeqlist ; apply in_or_app ; auto.
  intros a u Hin ; apply HM ; apply HMeqlist ; apply in_or_app ; auto.
  
  (* Congruence application *)
  intros M' N' u Hbisim' Hclos' IHM' IHN'.
  assert (forall (a : A) (u v : V), emb (sum M' · p * q + sum N') -(a)-> u ->
    emb (sum M · p * q + sum N) -(a)-> v -> u <=> v -> teq u v) as Hnext.
  intros a w v H H' Hbisim''.
  apply step_plus_fmt in H ; destruct H as [ H | H ].
  apply step_plus_fmt in H' ; destruct H' as [ H' | H' ].
  apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ x [ Heq_x Hstep_x ] ] ; rewrite Heq_x in *.
  apply sum_step in Hstep_x ; apply IHM' in Hstep_x.
  apply step_mult_fmt in H' ; destruct H' as [ H' | H' ].
  destruct H' as [ y [ Heq_y Hstep_y ] ] ; rewrite Heq_y in *.
  apply sum_step in Hstep_y ; apply HM in Hstep_y.
  unfold teq ; apply comp_mult ; apply refl || auto.
  apply IHprov ; auto.
  assert (depth x <= depth p) as Hpx.
  apply depth_pres_plus.
  apply clos_init_cases in Hclos' ; destruct Hclos' as [ H | H ].
  rewrite <- H in * ; exists a ; exists x ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with u ; auto.
  apply clos_trans with x a ; apply clos_refl || auto.
  assert (depth p < depth (p * q)) ; omega || auto.
  simpl ; destruct (depth q) ; auto.
  rewrite succ_max_distr.
  assert (S (depth p) <= max (S (depth p)) (S n)) ; omega || apply le_max_l.
  apply congruence with (p * q) ; auto.
  apply comp_plus_left.
  apply congr_pres_plus with p ; solve [ simpl in * ; tauto ] || auto.
  apply clos_init_cases in Hclos' ; destruct Hclos' as [ H | H ].
  rewrite <- H in * ; exists a ; exists x ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with u ; auto.
  apply clos_trans with x a ; apply clos_refl || auto.
  apply congr_pres_plus with p ; solve [ simpl in * ; tauto ] || auto.
  apply clos_init_cases in Hclos ; destruct Hclos as [ H | H ].
  rewrite <- H in * ; exists a ; exists y ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with s ; auto.
  apply clos_trans with y a ; apply clos_refl || auto.
  destruct H' as [ Hstep Heq ] ; rewrite Heq in *.
  assert (congr p (p * q)) as Hcongr by ( simpl in * ; tauto ).
  apply Hcongr in Hbisim'' ; contradiction || auto.
  apply clos_init_cases in Hclos' ; destruct Hclos' as [ H | H ].
  rewrite <- H in * ; exists a ; exists x ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep' Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with u ; auto.
  apply clos_trans with x a ; apply clos_refl || auto.
  destruct H as [ Hstep Heq ] ; rewrite Heq in *.
  apply step_mult_fmt in H' ; destruct H' as [ H' | H' ].
  destruct H' as [ y [ Heq' Hstep' ] ] ; rewrite Heq' in *.
  apply sum_step in Hstep' ; apply HM in Hstep'.
  assert (congr p (p * q)) as Hcongr by ( simpl in * ; tauto ).
  apply bisim_symm in Hbisim'' ; apply Hcongr in Hbisim'' ; contradiction || auto.
  apply clos_init_cases in Hclos ; destruct Hclos as [ H | H ].
  rewrite <- H in * ; exists a ; exists y ; split ; apply clos_refl || auto.
  destruct H as [ a' [ p' [ Hstep'' Htr ] ] ].
  exists a' ; exists p' ; split ; auto.
  apply clos_clos with s ; auto.
  apply clos_trans with y a ; apply clos_refl || auto.
  destruct H' as [ Hstep' Heq' ] ; rewrite Heq' in *.
  unfold teq ; apply refl.
  apply sum_step in H' ; apply teq_symm ; apply IHN with a ;
    apply bisim_symm || auto ; auto.
  apply IHN' with a ; apply sum_step in H ; auto.

  (* Application of theorem next using the previous assertion *)
  apply next ; apply bisim_fwd in Hbisim'.
  intros a x Hstep ; auto.
  assert (emb (sum M' · p * q + sum N') -(a)-> x) as Hstep_x by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ y [ Hstep_y Hbisim'' ] ].
  exists y ; split ; auto.
  apply Hnext with a ; auto.
  intros a y Hstep ; auto.
  assert (emb (sum M · p * q + sum N) -(a)-> y) as Hstep_y by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ x [ Hstep_x Hbisim'' ] ].
  exists x ; split ; auto.
  apply Hnext with a ; auto.

  (* Solve the r2-equality *)
  apply IHr2 with s ; auto.
  intros t u a Hin Hbisim'.
  apply IHN with a ; auto.
  apply HNeqlist ; apply in_or_app ; auto.
  intros a u Hin ; apply HM.
  apply HMeqlist ; apply in_or_app ; auto.
Qed.

Lemma complete_star_step_nf : forall (q r s : T) (a : A) (w : V),
  emb (mult' w (q * r)) <=> emb s -> nf (q * r) -> emb q -(a)-> w ->
  (forall (x y : T), depth x < depth (q * r) -> emb x <=> emb y -> x == y) -> 
  (forall (u v : V) (a : A), emb r -(a)-> u -> u <=> v -> teq u v) ->
  (mult' w (q * r)) == s.
Proof.
  intros q r s a w Hbisim Hnf Hstep IHprov Htop ; destruct w as [ | t ] ; simpl.
  apply trans with (q · q * r + r) ; [ apply symm ; apply BKS1 | ].
  destruct (summation r) as [ N [ Hiff_N Heq_N ] ].
  apply trans with (q · q * r + sum N).
  apply comp_plus ; apply refl || apply symm ; auto.
  destruct (summation q) as [ M [ Hiff_M Heq_M ] ].
  apply trans with (sum M · q * r + sum N).
  apply comp_plus ; apply refl || auto.
  apply comp_mult ; apply refl || apply symm ; auto.
  apply complete_split with q ; apply clos_refl || tauto || auto.
  simpl in Hbisim ; apply bisim_trans with (emb (sum M · q * r + r)).
  apply bisim_comp_plus ; apply bisim_refl || apply soundness ; auto.
  apply bisim_trans with (emb (q · q * r + r)).
  apply bisim_comp_plus ; apply bisim_refl || auto.
  apply bisim_comp_mult ; apply bisim_refl || apply soundness ; auto.
  apply bisim_trans with (emb (q * r)) ; apply BKS1_sound || auto.
  intros t u a' Hin Hbisim' ; apply Htop with a' ; auto.
  apply Hiff_N ; auto.
  intros a' u Hin ; apply Hiff_M ; auto.
  destruct (summation t) as [ M [ Hiff_M Heq_M ] ].
  apply trans with (sum M · q * r).
  apply comp_mult ; apply refl || apply symm ; auto.
  apply trans with (sum M · q * r + sum nil) ; [ apply symm ; apply B6 | ].
  apply complete_split with t ; auto.
  simpl ; apply bisim_trans with (emb (sum M · q * r)) ; apply B6_sound || auto.
  simpl in Hbisim ; apply bisim_trans with (emb (t · q * r)) ; auto.
  apply bisim_comp_mult ; apply bisim_refl || apply soundness ; auto.
  intros v u a' Hin ; simpl in Hin ; contradiction.
  apply clos_trans with t a ; apply clos_refl || auto.
  intros a' u Hin ; apply Hiff_M ; auto.
Qed.

Lemma complete_mult_nf : forall (p q r : T), 
  emb (p · r) <=> emb q -> nf (p · r) ->
  (forall (x y : T), depth x < depth (p · r) -> emb x <=> emb y -> x == y) -> 
  (forall (u v : V) (a : A), emb r -(a)-> u -> u <=> v -> teq u v) ->
  (p · r) == q.
Proof.
  intros p q r Hbisim Hnf IHprov Htop.
  assert (forall (u v : V) (a : A),
    emb p -(a)-> u -> emb (mult' u r) <=> v -> teq (emb (mult' u r)) v) as Hnext.
  clear Hbisim ; revert Hnf IHprov Htop ; revert r ; clear q.
  induction p ; intros r Hnf IHprov Htop u v a' Hstep_p Hbisim ;
    solve [ inversion Hstep_p ] || auto.

  (* Case for a \in A *)
  replace u with term in * by ( inversion Hstep_p ; auto ) ; simpl.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  unfold teq ; apply next.
  intros a'' w Hstep_r ; assert (emb r -(a'')-> w) as Hstep by auto.
  simpl in Hbisim ; apply bisim_fwd in Hbisim ; apply Hbisim in Hstep.
  destruct Hstep as [ v [ Hstep_q Hbisim' ] ] ; exists v ; split ; auto.
  apply Htop with a'' ; auto.
  intros a'' v Hstep_q ; assert (emb q -(a'')-> v) as Hstep by auto.
  simpl in Hbisim ; apply bisim_fwd in Hbisim ; apply Hbisim in Hstep.
  destruct Hstep as [ w [ Hstep_r Hbisim' ] ] ; exists w ; split ; auto.
  apply Htop with a'' ; auto.

  (* Case for p1 + p2 *)
  apply step_plus_fmt in Hstep_p ; destruct Hstep_p as [ Hstep_p | Hstep_p ].
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  apply IHp1 with a' ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim' ; apply IHprov ; auto.
  assert (depth (p1 · r) <= depth ((p1 + p2) · r)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || 
    rewrite <- max_assoc ; apply le_max_l.
  apply IHp2 with a' ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim' ; apply IHprov ; auto.
  assert (depth (p2 · r) <= depth ((p1 + p2) · r)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite (max_comm (depth p1)) ; rewrite <- max_assoc ; apply le_max_l.

  (* Case for p1 · p2 *)
  apply step_mult_fmt in Hstep_p ; destruct Hstep_p as [ H | H ].
  destruct H as [ p' [ Heq Hstep_p1 ] ] ; rewrite Heq in *.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  simpl ; unfold teq.
  apply trans with (p' · p2 · r) ; apply B5 || auto.
  assert (teq (emb (mult' (emb p') (p2 · r))) (emb q)) as Hcond.
  apply IHp1 with a' ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim' ; apply IHprov ; auto.
  assert (depth (p1 · p2 · r) <= depth ((p1 · p2) · r)) ; omega || auto.
  simpl ; rewrite <- max_assoc ; auto.
  intros w v a Hstep Hbisim'.
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p'' [ Heq' Hstep_p2 ] ] ; rewrite Heq' in *.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  assert (teq (emb (mult' (emb p'') r)) (emb q')) as Hcond.
  apply IHp2 with a ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth (p2 · r) <= depth ((p1 · p2) · r)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite (max_comm (depth p1)) ; rewrite <- max_assoc ; apply le_max_l.
  simpl in Hcond ; auto.
  destruct H as [ Hstep_p2 Heq' ] ; rewrite Heq' in *.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  apply next ; apply bisim_fwd in Hbisim'.
  intros a'' u' Hstep_r ; assert (emb r -(a'')-> u') as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ v' [ Hstep_q Hbisim'' ] ].
  exists v' ; split ; auto.
  apply Htop with a'' ; auto.
  intros a'' v' Hstep_q ; assert (emb q' -(a'')-> v') as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ u' [ Hstep_r Hbisim'' ] ].
  exists u' ; split ; auto.
  apply Htop with a'' ; auto.
  simpl in Hbisim ; simpl.
  apply bisim_trans with (emb ((p' · p2) · r)) ; auto.
  apply bisim_symm ; apply B5_sound.
  simpl in Hcond ; unfold teq in Hcond ; auto.
  destruct H as [ Hstep_p1 Heq ] ; rewrite Heq in *.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  simpl in Hbisim ; unfold teq ; simpl.
  apply next ; apply bisim_fwd in Hbisim.
  intros a w H ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq' Hstep_p2 ] ] ; rewrite Heq' in *.
  assert (emb p2 -(a)-> emb p') as Hstep by auto.
  assert (emb (p2 · r) -(a)-> emb (p' · r)) as Hstep' by
    ( apply step_mult_left ; auto ).
  apply Hbisim in Hstep' ; destruct Hstep' as [ v [ Hstep_q Hbisim' ] ].
  exists v ; split ; auto.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  assert (teq (emb (mult' (emb p') r)) (emb q')) as Hcond.
  apply IHp2 with a ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth (p2 · r) <= depth ((p1 · p2) · r)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite (max_comm (depth p1)) ; rewrite <- max_assoc ; apply le_max_l.
  simpl in Hcond ; auto.
  destruct H as [ Hstep_p2 Heq' ] ; rewrite Heq' in *.
  assert (emb (p2 · r) -(a)-> emb r) as Hstep by ( apply step_mult_right ; auto ).
  apply Hbisim in Hstep ; destruct Hstep as [ v [ Hstep_q Hbisim' ] ].
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  exists (emb q') ; split ; auto.
  unfold teq ; apply next ; apply bisim_fwd in Hbisim'.
  intros a'' x Hstep_r ; assert (emb r -(a'')-> x) as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ y [ Hstep_q' Hbisim'' ] ].
  exists y ; split ; auto.
  apply Htop with a'' ; auto.
  intros a'' y Hstep_q' ; assert (emb q' -(a'')-> y) as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ x [ Hstep_r Hbisim'' ] ].
  exists x ; split ; auto.
  apply Htop with a'' ; auto.
  intros a v Hstep_q ; assert (emb q -(a)-> v) as Hstep by auto.
  apply Hbisim in Hstep ; destruct Hstep as [ w [ Hstep Hbisim' ] ] ;
    exists w ; split ; auto.
  apply step_mult_fmt in Hstep ; destruct Hstep as [ H | H ].
  destruct H as [ p' [ Heq' Hstep_p2 ] ] ; rewrite Heq' in *.
  assert (teq (emb (mult' (emb p') r)) v) as Hcond.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  apply IHp2 with a ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth (p2 · r) <= depth ((p1 · p2) · r)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  rewrite (max_comm (depth p1)) ; rewrite <- max_assoc ; apply le_max_l.
  simpl in Hcond ; auto.
  destruct H as [ Hstep_p2 Heq' ] ; rewrite Heq' in *.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  unfold teq ; apply next ; apply bisim_fwd in Hbisim'.
  intros a'' x Hstep_r ; assert (emb r -(a'')-> x) as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ y [ Hstep_q' Hbisim'' ] ].
  exists y ; split ; auto.
  apply Htop with a'' ; auto.
  intros a'' y Hstep_q' ; assert (emb q' -(a'')-> y) as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ x [ Hstep_r Hbisim'' ] ].
  exists x ; split ; auto.
  apply Htop with a'' ; auto.

  (* Case for p1 * p2 *)
  apply step_star_fmt in Hstep_p ; destruct Hstep_p as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq Hstep_p1 ] ] ; rewrite Heq in *.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  assert ((mult' (emb p') (p1 * (p2 · r))) == q) as Hcond.
  apply complete_star_step_nf with a' ; solve [ simpl in * ; tauto ] || auto.
  simpl in Hbisim ; simpl.
  apply bisim_trans with (emb ((p' · p1 * p2) · r)) ; auto.
  apply bisim_trans with (emb (p' · p1 * p2 · r)) ;
    [ | apply bisim_symm ; apply B5_sound ].
  apply bisim_comp_mult ; apply bisim_refl || 
    apply bisim_symm ; apply BKS2_sound.
  simpl ; repeat split ; solve [ simpl in * ; tauto ] || auto.
  apply nf_mult_right_compat with (p1 * p2 · r) ;
    solve [ simpl in * ; tauto ] || apply BKS2_sound.
  apply congr_right_compat with (p1 * p2 · r) ;
    solve [ simpl in * ; tauto ] || apply BKS2_sound.
  intros x y Hless Hbisim' ; apply IHprov ; auto.
  assert (depth (p1 * (p2 · r)) <= depth (p1 * p2 · r)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ].
  rewrite max_0_l ; destruct (depth r) as [ | n ] ; apply le_max_l || auto.
  destruct (depth r) as [ | n ] ; simpl ; auto.
  rewrite succ_max_distr ; rewrite succ_max_distr ; apply max_lub.
  rewrite succ_max_distr.
  transitivity (S (max (depth p1) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_l.
  rewrite succ_max_distr ; apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p1) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_r.
  intros w v a Hstep Hbisim' ; apply step_mult_fmt in Hstep.
  destruct Hstep as [ [ p'' [ Heq' Hstep_p2 ] ] | H ] ; [ rewrite Heq' in * | ].
  assert (teq (emb (mult' (emb p'') r)) v) as Hcond.
  apply IHp2 with a ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth (p2 · r) <= depth (p1 * p2 · r)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ].
  rewrite max_0_l ; apply le_max_r.
  apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p1) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_r.
  simpl in Hcond ; auto.
  destruct H as [ Hstep_p2 Heq' ] ; rewrite Heq' in *.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  apply next ; apply bisim_fwd in Hbisim'.
  intros a'' x Hstep_r ; assert (emb r -(a'')-> x) as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ y [ Hstep_q' Hbisim'' ] ].
  exists y ; split ; auto.
  apply Htop with a'' ; auto.
  intros a'' y Hstep_q' ; assert (emb q' -(a'')-> y) as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ x [ Hstep_r Hbisim'' ] ].
  exists x ; split ; auto.
  apply Htop with a'' ; auto.
  simpl ; simpl in Hcond ; unfold teq.
  apply trans with (p' · p1 * (p2 · r)) ; auto.
  apply trans with (p' · p1 * p2 · r) ; apply B5 || auto.
  apply comp_mult ; apply refl || apply BKS2.
  destruct H as [ Heq Hstep_p1 ] ; rewrite Heq in *.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  assert ((mult' term (p1 * (p2 · r))) == q) as Hcond.
  apply complete_star_step_nf with a' ; auto.
  simpl ; simpl in Hbisim.
  apply bisim_trans with (emb (p1 * p2 · r)) ; auto.
  apply bisim_symm ; apply BKS2_sound.
  simpl ; repeat split ; solve [ simpl in * ; tauto ] || auto.
  apply nf_mult_right_compat with (p1 * p2 · r) ;
    solve [ simpl in * ; tauto ] || apply BKS2_sound.
  apply congr_right_compat with (p1 * p2 · r) ;
    solve [ simpl in * ; tauto ] || apply BKS2_sound.
  intros x y Hless Hbisim' ; apply IHprov ; auto.
  assert (depth (p1 * (p2 · r)) <= depth (p1 * p2 · r)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ].
  rewrite max_0_l ; destruct (depth r) as [ | n ] ; apply le_max_l || auto.
  destruct (depth r) as [ | n ] ; simpl ; auto.
  rewrite succ_max_distr ; apply max_lub ; rewrite succ_max_distr.
  transitivity (S (max (depth p1) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_l.
  rewrite succ_max_distr ; apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p1) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_r.
  intros w v a H Hbisim' ; apply step_mult_fmt in H ; destruct H as [ H | H ].
  destruct H as [ p' [ Heq' Hstep_p2 ] ] ; rewrite Heq' in *.
  assert (teq (emb (mult' (emb p') r)) v) as Hcond.
  apply IHp2 with a ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth (p2 · r) <= depth (p1 * p2 · r)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ].
  rewrite max_0_l ; apply le_max_r.
  apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p1) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_r.
  simpl in Hcond ; auto.
  destruct H as [ Hstep_p2 Heq' ] ; rewrite Heq' in *.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  unfold teq ; apply next ; apply bisim_fwd in Hbisim'.
  intros a'' x Hstep_r ; assert (emb r -(a'')-> x) as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ y [ Hstep_q' Hbisim'' ] ].
  exists y ; split ; auto.
  apply Htop with a'' ; auto.
  intros a'' y Hstep_q' ; assert (emb q' -(a'')-> y) as Hstep by auto.
  apply Hbisim' in Hstep ; destruct Hstep as [ x [ Hstep_r Hbisim'' ] ].
  exists x ; split ; auto.
  apply Htop with a'' ; auto.
  unfold teq ; simpl in * ; apply trans with (p1 * (p2 · r)) ; apply BKS2 || auto.
  apply IHp2 with a' ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim' ; apply IHprov ; auto.
  assert (depth (p2 · r) <= depth (p1 * p2 · r)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ].
  rewrite max_0_l ; apply le_max_r.
  apply max_lub ; apply le_max_r || auto.
  transitivity (S (max (depth p1) m)) ; apply le_max_l || auto.
  rewrite succ_max_distr ; apply le_max_r.

  (* Use assertion and Lemma next to prove this lemma *)
  assert (forall (a : A) (u v : V), emb (p · r) -(a)-> u ->
    emb q -(a)-> v -> u <=> v -> teq u v) as Happl.
  intros a u v H Hstep_q Hbisim' ; apply step_mult_fmt in H ;  
    destruct H as [ H | H ].
  destruct H as [ p' [ Heq Hstep_p ] ] ; rewrite Heq in *.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  assert (teq (emb (mult' (emb p') r)) (emb q')) as Hcond.
  apply Hnext with a ; auto.
  simpl in Hcond ; auto.
  destruct H as [ Hstep_p Heq ] ; rewrite Heq in *.
  destruct v as [ | q' ].
  destruct Hbisim' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  apply next ; apply bisim_fwd in Hbisim'.
  intros a' x Hstep_r ; assert (emb r -(a')-> x) as H by auto.
  apply Hbisim' in H ; destruct H as [ y [ Hstep_q' Hbisim'' ] ].
  exists y ; split ; auto.
  apply Htop with a' ; auto.
  intros a' y Hstep_q' ; assert (emb q' -(a')-> y) as H by auto.
  apply Hbisim' in H ; destruct H as [ x [ Hstep_r Hbisim'' ] ].
  exists x ; split ; auto.
  apply Htop with a' ; auto.
  apply next ; apply bisim_fwd in Hbisim.
  intros a u Hstep_pr ; assert (emb (p · r) -(a)-> u) as H by auto.
  apply Hbisim in H ; destruct H as [ v [ Hstep_q Hbisim' ] ].
  exists v ; split ; auto.
  apply Happl with a ; auto.
  intros a v Hstep_q ; assert (emb q -(a)-> v) as H by auto.
  apply Hbisim in H ; destruct H as [ u [ Hstep_pr Hbisim' ] ].
  exists u ; split ; auto.
  apply Happl with a ; auto.
Qed.

Lemma complete_nf : forall (p q : T), emb p <=> emb q -> nf p ->
  (forall (r s : T), depth r < depth p -> emb r <=> emb s -> r == s) -> p == q.
Proof.
  intros p q Hbisim Hnf IHprov.
  assert (forall (u v : V) (a : A), 
    emb p -(a)-> u -> u <=> v -> teq u v) as Hnext.
  clear Hbisim ; revert Hnf IHprov ; clear q.
  induction p ; intros Hnf IHprov u v a' Hstep_p Hbisim ;
    solve [ inversion Hstep_p ] || auto.
  replace u with term in * by ( inversion Hstep_p ; auto ).
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; rewrite H ; auto.

  (* Case for p1 + p2 in asertion *)
  apply step_plus_fmt in Hstep_p ; destruct Hstep_p as [ Hstep_p | Hstep_p ].
  apply IHp1 with a' ; solve [ simpl in * ; tauto ] || auto.
  intros r s Hless Hbisim' ; apply IHprov ; auto.
  assert (depth p1 <= depth (p1 + p2)) by ( simpl ; apply le_max_l ) ; omega.
  apply IHp2 with a' ; solve [ simpl in * ; tauto ] || auto.
  intros r s Hless Hbisim' ; apply IHprov ; auto.
  assert (depth p2 <= depth (p1 + p2)) by ( simpl ; apply le_max_r ) ; omega.

  (* Case for p1 · p2 in assertion *)
  apply step_mult_fmt in Hstep_p ; destruct Hstep_p as [ H | H ].
  destruct H as [ p' [ Heq Hstep_p1 ] ] ; rewrite Heq in *.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  unfold teq ; apply complete_mult_nf ; auto.
  simpl ; split ; solve [ simpl in * ; tauto ] || auto.
  apply nf_mult_pres_step with p1 a' ; solve [ simpl in * ; tauto ] || auto.
  intros x y Hless Hbisim' ; apply IHprov ; auto.
  assert (depth (p' · p2) <= depth (p1 · p2)) ; omega || auto.
  simpl ; apply max_lub ; apply le_max_r || auto.
  transitivity (depth p1) ; apply le_max_l || 
    apply depth_pres_step with a' ; auto.
  intros w v a Hstep Hbisim' ; apply IHp2 with a ;
    solve [ simpl in * ; tauto ] || auto.
  intros r s Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth p2 <= depth (p1 · p2)) ; omega || simpl ; apply le_max_r.
  destruct H as [ Hstep_p1 Heq ] ; rewrite Heq in *.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  apply next ; apply bisim_fwd in Hbisim.
  intros a w Hstep ; assert (emb p2 -(a)-> w) as Hstep_p2 by auto.
  apply Hbisim in Hstep ; destruct Hstep as [ v [ Hstep_q Hbisim' ] ].
  exists v ; split ; auto.
  apply IHp2 with a ; solve [ simpl in * ; tauto ] || auto.
  intros r s Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth p2 <= depth (p1 · p2)) ; omega || simpl ; apply le_max_r.
  intros a v Hstep_q ; assert (emb q -(a)-> v) as Hstep by auto.
  apply Hbisim in Hstep ; destruct Hstep as [ w [ Hstep_p2 Hbisim' ] ].
  exists w ; split ; auto.
  apply IHp2 with a ; solve [ simpl in * ; tauto ] || auto.
  intros r s Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth p2 <= depth (p1 · p2)) ; omega || simpl ; apply le_max_r.

  (* Case for p1 * p2 in assertion *)
  apply step_star_fmt in Hstep_p ; destruct Hstep_p as [ H | [ H | H ] ].
  destruct H as [ p' [ Heq Hstep_p1 ] ] ; rewrite Heq in *.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  unfold teq ; assert (emb (mult' (emb p') (p1 * p2)) <=> emb q) as H by
    ( unfold mult' ; simpl ; auto ).
  apply complete_star_step_nf with (a := a') in H ; auto.
  intros w v a Hstep_p2 Hbisim' ; apply IHp2 with a ; 
    solve [ simpl in * ; tauto ] || auto.
  intros r s Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth p2 <= depth (p1 * p2)) ; omega || auto. 
  simpl ; destruct (depth p2) as [ | m ] ; omega || auto.
  rewrite succ_max_distr ; apply le_max_r.
  destruct H as [ Heq Hstep_p1 ] ; rewrite Heq in *.
  destruct v as [ | q ].
  destruct Hbisim as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (term = term) as H by auto ; apply HinR in H ; inversion H.
  unfold teq ; assert (emb (mult' term (p1 * p2)) <=> emb q) as H by
    ( unfold mult' ; simpl ; auto ).
  apply complete_star_step_nf with (a := a') in H ; auto.
  intros w v a Hstep_p2 Hbisim' ; apply IHp2 with a ; 
    solve [ simpl in * ; tauto ] || auto.
  intros r s Hless Hbisim'' ; apply IHprov ; auto.
  assert (depth p2 <= depth (p1 * p2)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ] ; omega || auto.
  rewrite succ_max_distr ; apply le_max_r.
  apply IHp2 with a' ; solve [ simpl in * ; tauto ] || auto.
  intros r s Hless Hbisim' ; apply IHprov ; auto.
  assert (depth p2 <= depth (p1 * p2)) ; omega || auto.
  simpl ; destruct (depth p2) as [ | m ] ; omega || auto.
  rewrite succ_max_distr ; apply le_max_r.

  (* Use assertion and Lemma next to prove lemma *)
  apply next ; apply bisim_fwd in Hbisim.
  intros a u Hstep_p ; assert (emb p -(a)-> u) as Hstep by auto.
  apply Hbisim in Hstep ; destruct Hstep as [ v [ Hstep_q Hbisim' ] ].
  exists v ; split ; auto.
  apply Hnext with a ; auto.
  intros a v Hstep_q ; assert (emb q -(a)-> v) as Hstep by auto.
  apply Hbisim in Hstep ; destruct Hstep as [ u [ Hstep_p Hbisim' ] ].
  exists u ; split ; auto.
  apply Hnext with a ; auto.
Qed.

Theorem completeness : forall (p q : T), emb p <=> emb q -> p == q.
Proof.
  intro p ; assert (exists (n : nat), n = depth p) as H by eauto.
  destruct H as [ n Heq ] ; revert Heq ; revert p.
  induction n using strong_ind ; intros p Heq q Hbisim.
  destruct (normalization p) as [ r [ Hbisim' [ Hnf Hleq ] ] ].
  apply trans with r ; [ apply symm | ] ; apply complete_nf ; auto.
  apply bisim_symm ; auto.
  intros t u Hleq' Hbisim'' ; apply H with (depth t) ; omega || auto.
  apply bisim_trans with (emb p) ; [ apply bisim_symm | ] ; auto.
  intros t u Hleq' Hbisim'' ; apply H with (depth t) ; omega || auto.
Qed.
