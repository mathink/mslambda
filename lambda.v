(* Map Skelton *)
Require Import
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.ssrbool
Ssreflect.eqtype.

Set Implicit Arguments.
Unset Strict Implicit.

Delimit Scope map with map_scope.
Open Scope map_scope.

  (** 
   ** Define map from map1
       to realize abstraction mechanism
   *)
Inductive map1: Set :=
| binder
| minl (m: map1)
| minr (m: map1)
| mcons (m n: map1).
Notation "1" := binder.

Inductive map: Set :=
| mnull
| mmap (m: map1).
Coercion mmap: map1 >-> map.
Notation "0" := mnull.

(* eqType declaration(s) *)
Fixpoint eq_map1 (x y: map1): bool :=
  match x, y with
    | 1, 1 => true
    | minl m, minl n | minr m, minr n => eq_map1 m n
    | mcons m m', mcons n n' => eq_map1 m n && eq_map1 m' n'
    | _, _ => false
  end.
Functional Scheme eq_map1_ind := Induction for eq_map1 Sort Prop.
Functional Scheme eq_map1_rect := Induction for eq_map1 Sort Type.

Definition eq_map (x y: map): bool :=
  match x, y with
    | mnull, mnull => true
    | mmap m, mmap n => eq_map1 m n
    | _, _ => false
  end.
Functional Scheme eq_map_ind := Induction for eq_map Sort Prop.
Functional Scheme eq_map_rect := Induction for eq_map Sort Type.

Lemma eq_map1P: Equality.axiom eq_map1.
Proof.
  rewrite /Equality.axiom => m n.
  elim/eq_map1_rect: m n /(eq_map1 m n) => m0 n0 /=; try by constructor.
  - by move=> m _ n _ [->|Hneq]; [ left | right; case ].
  - by move=> m _ n _ [->|Hneq]; [ left | right; case ].
  - move=> m m' _ n n' _ [->|Hneq] [->|Hneq'] /=; first (by left);
          by right; case.
Defined.

Canonical map1_eqMixin := EqMixin eq_map1P.
Canonical map1_eqType := Eval hnf in EqType map1 map1_eqMixin.

Lemma eq_map1E: eq_map1 = eq_op.
Proof. by []. Qed.

Lemma eq_minl m n: (minl m == minl n) = (m == n).
Proof. by []. Qed.

Lemma eq_minr m n: (minr m == minr n) = (m == n).
Proof. by []. Qed.

Lemma eq_mcons m m' n n'
: (mcons m n == mcons m' n') = (m == m') && (n == n').
Proof. by []. Qed.

Lemma eq_mapP: Equality.axiom eq_map.
Proof.
  rewrite /Equality.axiom => m n.
  elim/eq_map_rect: m n /(eq_map m n) => m0 n0 /=; try by constructor.
  move=> m _ n _; apply iffP with (m = n); first by apply eq_map1P.
  - by move=> -> //.
  - by case.
Defined.

Canonical map_eqMixin := EqMixin eq_mapP.
Canonical map_eqType := Eval hnf in EqType map map_eqMixin.

Lemma eq_mapE: eq_map = eq_op.
Proof. by []. Qed.

Lemma eq_mmap m n:
  (mmap m == mmap n) = (m == n).
Proof.
    by rewrite inj_eq //=; last move=> x1 x2 [] //=.
Qed.


(* append map *)
Definition mapp (m n: map): map :=
  match m, n with
    | mnull, mnull => mnull
    | mnull, mmap n1 => minr n1
    | mmap m1, mnull => minl m1
    | mmap m1, mmap n1 => mcons m1 n1
  end.
Functional Scheme mapp_ind := Induction for mapp Sort Prop.
Infix "*" := mapp (at level 40, left associativity).

Lemma mapp_injective (m m' n n': map):
  m*n == m'*n' = (m == m') && (n == n').
Proof.
  move: m m' n n' => [| m1] [| m1'] [| n1] [| n1'] //=; try by rewrite andbF.
  rewrite andbT //=.
Qed.

Lemma mappm0l (m1: map1): m1*0 = minl m1.
Proof.
  case: m1 => [] //=; try done.
Qed.    

Lemma mapp0mr (m1: map1): 0*m1 = minr m1.
Proof.
  case: m1 => [] //=; try done.
Qed.    

Lemma mapp_mcons (m1 m2: map1): m1*m2 = mcons m1 m2.
Proof.
  case: m1 => [] //=; try done.
Qed.    


Reserved Notation "m ! n" (at level 70, no associativity).
Inductive orthogonal: map -> map -> Prop :=
| orthm0 (m: map): m!0
| orth0m (n: map): 0!n
| orth_mapp (m n m' n': map): m!n -> m'!n' -> m*m'!n*n'
where "m ! n" := (orthogonal m n).
Notation "m ! n" := (orthogonal m n) (at level 70, no associativity).
Hint Constructors orthogonal.

Lemma orth_symm m n: m!n -> n!m.
Proof.
  elim=> [m'|n'|m1 n1 m2 n2 Hmn1 Hnm1 Hmn2 Hnm2] /=; try by constructor.
Qed.                                                   

Lemma orth1m m: 1!m -> m = 0.
Proof.
  move=> Horth; inversion Horth; try done.
  destruct m0, m'; simpl in *; try discriminate.
Qed.

Lemma orthm1 m: m!1 -> m = 0.
Proof.
  move=> Horth; inversion Horth; try done.
  destruct n, n'; simpl in *; try discriminate.
Qed.

Lemma orthl m n: minl m ! minl n -> m ! n.
Proof.
  rewrite -2!mappm0l => H; inversion H.
  move: H1 => /eqP; move: H0 => /eqP; rewrite -!mappm0l.
    by rewrite !mapp_injective => /andP[/eqP<-_]/andP[/eqP<-_].
Qed.

Lemma orthlc m n n': minl m ! mcons n n' -> m ! n.
Proof.
  rewrite -mappm0l -mapp_mcons => H; inversion H.
  move: H1 => /eqP; move: H0 => /eqP; rewrite -mappm0l -mapp_mcons.
    by rewrite !mapp_injective => /andP[/eqP<-_]/andP[/eqP<-_].
Qed.

Lemma orthcl m m' n: mcons m m' ! minl n -> m ! n.
Proof.
  rewrite -mappm0l -mapp_mcons => H; inversion H.
  move: H1 => /eqP; move: H0 => /eqP; rewrite -mappm0l -mapp_mcons.
    by rewrite !mapp_injective => /andP[/eqP<-_]/andP[/eqP<-_].
Qed.

Lemma orthr m n: minr m ! minr n -> m ! n.
Proof.
  rewrite -2!mapp0mr => H; inversion H.
  move: H1 => /eqP; move: H0 => /eqP; rewrite -!mapp0mr.
    by rewrite !mapp_injective => /andP[_/eqP<-]/andP[_/eqP<-].
Qed.

Lemma orthrc m n n': minr m ! mcons n' n -> m ! n.
Proof.
  rewrite -mapp0mr -mapp_mcons => H; inversion H.
  move: H1 => /eqP; move: H0 => /eqP; rewrite -mapp0mr -mapp_mcons.
    by rewrite !mapp_injective => /andP[_/eqP<-]/andP[_/eqP<-].
Qed.

Lemma orthcr m m' n: mcons m' m ! minr n -> m ! n.
Proof.
  rewrite -mapp0mr -mapp_mcons => H; inversion H.
  move: H1 => /eqP; move: H0 => /eqP; rewrite -mapp0mr -mapp_mcons.
    by rewrite !mapp_injective => /andP[_/eqP<-]/andP[_/eqP<-].
Qed.

Lemma orthccl m m' n n': mcons m m' ! mcons n n' -> m ! n.
Proof.
  rewrite -!mapp_mcons => H; inversion H.
  move: H1 => /eqP; move: H0 => /eqP; rewrite -!mapp_mcons.
  by rewrite !mapp_injective => /andP[/eqP<-_]/andP[/eqP<-_].
Qed.

Lemma orthccr m m' n n': mcons m m' ! mcons n n' -> m' ! n'.
Proof.
  rewrite -!mapp_mcons => H; inversion H.
  move: H1 => /eqP; move: H0 => /eqP; rewrite -!mapp_mcons.
  by rewrite !mapp_injective => /andP[_/eqP<-]/andP[_/eqP<-].
Qed.

Fixpoint orthb1 (m n: map1) :=
  match m, n with
    | mcons m1 _, minl n1
    | minl m1, mcons n1 _
    | minl m1, minl n1 => orthb1 m1 n1

    | mcons _ m2, minr n2
    | minr m2, mcons _ n2
    | minr m2, minr n2 => orthb1 m2 n2

    | mcons m1 m2, mcons n1 n2 => orthb1 m1 n1 && orthb1 m2 n2

    | minl _, minr _ | minr _, minl _ => true
    | _, _ => false
  end.
Functional Scheme orthb1_ind := Induction for orthb1 Sort Prop.
Functional Scheme orthb1_rect := Induction for orthb1 Sort Type.

Lemma orthb1_symm m n: orthb1 m n = orthb1 n m.
Proof.
  elim/orthb1_ind: m n /(orthb1 m n) => m n /=; try by case: n.
    by move=> m1 m2 _ n1 n2 _ -> ->.
Qed.

Definition orthb (m n: map) :=
  match m, n with
    | 0, _ => true
    | _, 0 => true
    | mmap m', mmap n' => orthb1 m' n'
  end.
Functional Scheme orthb_ind := Induction for orthb Sort Prop.
Functional Scheme orthb_rect := Induction for orthb Sort Type.

Lemma orthbm0 m: orthb m 0.
Proof. by case: m. Qed.

Lemma orthb0m m: orthb 0 m.
Proof. by []. Qed.

Lemma orthb_symm m n: orthb m n = orthb n m.
Proof.
  elim/orthb_ind: m n /(orthb m n) => m n //=.
  - by rewrite orthbm0.
  - move=> m' _ n' _; apply orthb1_symm.
Qed.

Lemma orthb1P (m1 n1: map1): reflect (m1!n1) (orthb1 m1 n1).
Proof.
  (* elim/orthb1_ind: m1 n1 /(orthb1 m1 n1). *)
  (* Toplevel input, characters 0-38: *)
  (* > elim/orthb1_ind: m1 n1 /(orthb1 m1 n1). *)
  (* > ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
  (* Anomaly: Uncaught exception Reduction.NotConvertible. Please report. *)
  elim/orthb1_rect: m1 n1 /(orthb1 m1 n1) => m0 n0 //=.
  - move=> _; right; move=> /orth1m H; discriminate.
  - move=> m1 _{m0} _; right; move=> /orth_symm /orth1m; discriminate.
  - move=> m1 _{m0} n1 _{n0} [Hor|Hnor].
    + by left; rewrite -2!mappm0l; apply orth_mapp.
    + by right=> Hor; apply: Hnor; move: Hor; apply orthl.
  - move=> m1 _{m0} n1 _{n0}; left;
             by rewrite -mappm0l -mapp0mr; constructor.
  - move=> m1 _{m0} n1 n2 _{n0} [Hor|Hnor].
    + by left; rewrite -mappm0l -mapp_mcons; apply orth_mapp.
    + by right=> Hor; apply: Hnor; move: Hor; apply orthlc.
  - move=> m1 _{m0} _{n0}; right=> /orthm1 H; discriminate.
  - move=> m1 _{m0} n1 _{n0}; left;
             by rewrite -mappm0l -mapp0mr; constructor.
  - move=> m1 _{m0} n1 _{n0} [Hor|Hnor].
    + by left; rewrite -2!mapp0mr; apply orth_mapp.
    + by right=> Hor; apply: Hnor; move: Hor; apply orthr.
  - move=> m1 _{m0} n1 n2 _{n0} [Hor|Hnor].
    + by left; rewrite -mapp0mr -mapp_mcons; apply orth_mapp.
    + by right=> Hor; apply: Hnor; move: Hor; apply orthrc.
  - move=> m1 m2 _{m0} _{n0}; right=> /orthm1 H; discriminate.
  - move=> m1 m2 _{m0} n1 _{n0} [Hor|Hnor].
    + by left; rewrite -mappm0l -mapp_mcons; apply orth_mapp.
    + by right=> Hor; apply: Hnor; move: Hor; apply orthcl.
  - move=> m1 m2 _{m0} n1 _{n0} [Hor|Hnor].
    + by left; rewrite -mapp0mr -mapp_mcons; apply orth_mapp.
    + by right=> Hor; apply: Hnor; move: Hor; apply orthcr.
  - move=> m1 m2 _{m0} n1 n2 _{n0} [Hor1|Hnor1] /=.
    + move=> [Hor2 | Hnor2].
      * by left; rewrite -!mapp_mcons; apply orth_mapp.
      * right=> Hor; apply: Hnor2; move: Hor; apply orthccr.
    + move=> _; right => Hor; apply Hnor1; move: Hor; apply orthccl.
Qed.
Notation "m1 !1P n1" :=
  (orthb1P m1 n1: reflect (mmap m1!mmap n1) (orthb1 m1 n1))
    (at level 70, no associativity).

Lemma orthbP (m n: map): reflect (m!n) (orthb m n).
Proof.
  elim/orthb_rect: m n /(orthb m n) => m0 n0; try by left.
  by move=> m _ n _; apply orthb1P.
Qed.
Notation "m !P n" := (orthbP m n: reflect (m!n) (orthb m n))
                       (at level 70, no associativity).


(* for interpret *)
Inductive tree: Set :=
| leaf (b: bool)
| node (lt rt: tree).

Fixpoint interpret1 (m1: map1): tree :=
  match m1 with
    | binder => leaf true
    | minl m => node (interpret1 m) (leaf false)
    | minr m => node (leaf false) (interpret1 m)
    | mcons m n => node (interpret1 m) (interpret1 n)
  end.

Fixpoint interpret (m: map): tree :=
  match m with
    | mnull => leaf false
    | mmap m1 => interpret1 m1
  end.

Notation "1" := binder: map_scope.
Notation "0" := mnull: map_scope.
Notation "m * n" := (mapp m n) 
                      (at level 40, left associativity): map_scope.
Notation "m ! n" := (orthogonal m n)
                      (at level 70, no associativity): map_scope.
Open Scope map_scope.
Notation "m1 !1P n1" :=
  (orthb1P m1 n1: reflect (mmap m1!mmap n1) (orthb1 m1 n1))
    (at level 70, no associativity): map_scope.
Notation "m !P n" := (orthbP m n: reflect (m!n) (orthb m n))
                       (at level 70, no associativity): map_scope.


Section Lambda.

  Variable (T: eqType).

  Inductive sexp: Type :=
  | free (x: T)
  | box 
  | app (s t: sexp)
  | abs (m: map)(s: sexp).
  Infix "@" := app (at level 25, left associativity).
  Infix "\" := abs (at level 35, right associativity).

  Fixpoint eq_sexp (s t: sexp): bool :=
    match s, t with
      | free x, free y => x == y
      | box, box => true
      | app s1 s2, app t1 t2 => (eq_sexp s1 t1) && (eq_sexp s2 t2)
      | abs m s', abs n t' => (m == n) && (eq_sexp s' t')
      | _, _ => false
    end.
  Functional Scheme eq_sexp_ind := Induction for eq_sexp Sort Prop.
  Functional Scheme eq_sexp_rect := Induction for eq_sexp Sort Type.

  Lemma eq_sexpP: Equality.axiom eq_sexp.
  Proof.
    rewrite /Equality.axiom => x y.
    elim/eq_sexp_rect: x y /(eq_sexp x y) => x0 y0; try by constructor.
    - by move=> x _ y _; case: (x =P y); [left; subst | by right; case ].
    - move=> x1 x2 _{x0} y1 y2 _{y0} [->|Hneq1] /=.
      + move=> [->|Hneq2]; try by constructor.
        by right=> H; apply Hneq2; inversion H.
      + move=> _.
        by right=> H; apply Hneq1; inversion H.
    - move=> m x _ n y _ [->|Hneq]; rewrite ?andbF ?andbT.
      + case: (m =P n) => [->|Hneq]; try by constructor.
        by right=> H; apply Hneq; inversion H.
      + by right=> H; apply Hneq; inversion H.
  Defined.

  Canonical sexp_eqMixin := EqMixin eq_sexpP.
  Canonical sexp_eqType := Eval hnf in EqType sexp sexp_eqMixin.

  Lemma eq_sexpE: eq_sexp = eq_op.
  Proof. by []. Qed.

  Lemma eq_free x y: (free x == free y) = (x == y).
  Proof. by []. Qed.

  Lemma eq_app s1 s2 t1 t2: (s1@t1 == s2@t2) = (s1 == s2) && (t1 == t2).
  Proof. by []. Qed.

  Lemma eq_abs m n s t: (m\s == n\t) = (m == n) && (s == t).
  Proof. by []. Qed.


  (* freshness judgement *)
  Fixpoint fresh_on (x: T)(M: sexp) :=
    match M with
      | free y => ~~ (x == y)
      | box => true
      | app s t => fresh_on x s && fresh_on x t
      | abs m s => fresh_on x s
    end.

  (* well-formedness of 'sexp' *)
  Reserved Notation "m # s" (at level 70, no associativity).
  Inductive well_formed: map -> sexp -> Prop :=
  | wf_free (x: T): 0#free x
  | wf_0_box: 0#box
  | wf_1_box: 1#box
  | wf_mapp_app (m n: map)(s t: sexp): m#s -> n#t -> m*n#s@t
  | wf_abs (m n: map)(t: sexp): m#t -> n#t -> m!n -> m#(n\t)
  where "m # s" := (well_formed m s).
  Hint Constructors well_formed.

  Fixpoint wfb (m: map)(s: sexp): bool :=
    match m, s with
      | 0, free x => true
      | 0, box => true
      | 1, box => true
      | mcons m1 m2, app s1 s2 => wfb m1 s1 && wfb m2 s2
      | minl m1, app s1 s2 => wfb m1 s1 && wfb 0 s2
      | minr m2, app s1 s2 => wfb 0 s1 && wfb m2 s2
      | 0, app s1 s2 => wfb 0 s1 && wfb 0 s2
      | m, abs n t => wfb m t && wfb n t && orthb m n
      | _, _ => false
    end.
  Functional Scheme wfb_ind := Induction for wfb Sort Prop.
  Functional Scheme wfb_rect := Induction for wfb Sort Type.

  Lemma wf_0 m s: m#s -> 0#s.
  Proof.
    elim=> [x||
           |m' n' s' t' IHms Hs IHnt Ht
           |m' n' t IHmt Hmt IHnt Hnt Horth] //=; try by constructor.
    have: (0*0 = 0); first done; move=> <-.
      by apply wf_mapp_app.
  Qed.
  
  Lemma mapp_00_0: 0*0 = 0. done. Qed.

  Lemma wf0appl s1 s2: 0 # s1 @ s2 -> 0 # s1.
  Proof.
    rewrite -mapp_00_0 => H; inversion H.
    move: H0 => /eqP; rewrite -mapp_00_0.
    rewrite mapp_injective => /andP[Heq/eqP->].
      by move: Heq H3 => /eqP ->.
  Qed.

  Lemma wf0appr s1 s2: 0 # s1 @ s2 -> 0 # s2.
  Proof.
    rewrite -mapp_00_0 => H; inversion H.
    move: H0 => /eqP; rewrite -mapp_00_0.
    rewrite mapp_injective => /andP[/eqP->Heq].
      by move: Heq H4 => /eqP ->.
  Qed.

  Lemma wfabs_inv m n t: m # n \ t -> n # t.
  Proof.
    by move=> H; inversion H.
  Qed.

  Lemma mapp_neq1 m n: m * n != 1.
  Proof.
    elim/mapp_ind: m n /(mapp m n) => m n //=.
  Qed.

  Lemma wfbP m s: reflect (m#s) (wfb m s).
  Proof.
    elim/wfb_rect: m s /(wfb m s) => m0 s0;
      try (by right; move=> H; inversion H);
      try (by move=> *; match goal with |- reflect ?x true => left end).
    - move=> _ s1 s2 _ [Hwf1|Hnwf1] /=.
      + move=> [Hwf2|Hnwf2];
          first by left; rewrite -mapp_00_0; try constructor.
          by right=> H; apply: Hnwf2; move: H; apply wf0appr.
      + move=> _; by right=> H; apply: Hnwf1; move: H; apply wf0appl.
    - move=> -> n t _ /=; rewrite andbT; move=> [Hwf0|Hnwf0] /=.
      + move=> [Hwf|Hnwf] /=; first by left; constructor.
          by right=> H; apply: Hnwf; apply wfabs_inv with 0.
      + by move=> _; right=> H; apply: Hnwf0; inversion H.
    - move=> m _ _{m} s1 s2 _{s0}; right => H; inversion H.
      destruct m, n; discriminate.
    - move=> m -> -> {m0} n s _.
      move=> [Hwf1|Hnwf1]; first rewrite orthb_symm; move=> /=.
      + move=> [Hwf|Hnwf] //=.
        * case: (orthbP n 1) => [Hor|Hnor];
            first by left; apply wf_abs => //; apply orth_symm.
          by right=> H; apply: Hnor; inversion H; subst; apply orth_symm.
        * by right=> H; apply: Hnwf; inversion H; subst.
      + by move=> _; right=> H; apply: Hnwf1; inversion H; subst.
    - move=> m1 _{m0} m _{m1} s1 s2 _.
      case=> [Hwf1|Hnwf1] /=; last (move=> _; right=> H; apply: Hnwf1; inversion H; subst).
      + move=> [Hwf2|Hnwf2] /=; first by left; rewrite -mappm0l; constructor.
        right=> H; apply: Hnwf2; inversion H; subst.
        move: H0 H4; rewrite -mappm0l => /eqP; rewrite mapp_injective.
          by move=>/andP[_/eqP->].
      + move: H0 H3; rewrite -mappm0l => /eqP; rewrite mapp_injective.
          by move=>/andP[/eqP->_].
    - move=> m' ->{m0} m ->{m'} n s _{s0}.
      case=> [Hwfl|Hnwfl]; last by (move=> _; right=> H; apply: Hnwfl; inversion H; subst).
      case=> [Hwf|Hnwf]; first rewrite orthb_symm /=.
      + case: (orthbP n (minl m)) => [Hor|Hnor];
          first by left; apply wf_abs => //; apply orth_symm.
          by right=> H; apply: Hnor; inversion H; subst; apply orth_symm.
      + by right=> H; apply: Hnwf; inversion H; subst.
    - move=> m1 _{m0} m _{m1} s1 s2 _{s0}.
      case=> [Hwf1|Hnwf1] /=; last (move=> _; right=> H; apply: Hnwf1; inversion H; subst).
      + move=> [Hwf2|Hnwf2] /=; first by left; rewrite -mapp0mr; constructor.
        right=> H; apply: Hnwf2; inversion H; subst.
        move: H0 H4; rewrite -mapp0mr => /eqP; rewrite mapp_injective.
          by move=>/andP[_/eqP->].
      + move: H0 H3; rewrite -mapp0mr => /eqP; rewrite mapp_injective.
          by move=>/andP[/eqP->_].
    - move=> m1 ->{m0} m ->{m1} n s _{s0}.
      case=> [Hwfl|Hnwfl]; last by (move=> _; right=> H; apply: Hnwfl; inversion H; subst).
      case=> [Hwf|Hnwf]; first rewrite orthb_symm /=.
      + case: (orthbP n (minr m)) => [Hor|Hnor];
          first by left; apply wf_abs => //; apply orth_symm.
          by right=> H; apply: Hnor; inversion H; subst; apply orth_symm.
      + by right=> H; apply: Hnwf; inversion H; subst.
    - move=> m1 _{m0} m n _{m1} s1 s2 _{s0}.
      case=> [Hwf1|Hnwf1] /=; last (move=> _; right=> H; apply: Hnwf1; inversion H; subst).
      + move=> [Hwf2|Hnwf2] /=; first by left; rewrite -mapp_mcons; constructor.
        right=> H; apply: Hnwf2; inversion H; subst.
        move: H0 H4; rewrite -mapp_mcons => /eqP; rewrite mapp_injective.
          by move=>/andP[_/eqP->].
      + move: H0 H3; rewrite -mapp_mcons => /eqP; rewrite mapp_injective.
          by move=>/andP[/eqP->_].
    - move=> m1 ->{m0} m n ->{m1} n' s _{s0}.
      case=> [Hwfl|Hnwfl]; last by (move=> _; right=> H; apply: Hnwfl; inversion H; subst).
      case=> [Hwf|Hnwf]; first rewrite orthb_symm /=.
      + case: (orthbP n' (mcons m n)) => [Hor|Hnor];
          first by left; apply wf_abs => //; apply orth_symm.
          by right=> H; apply: Hnor; inversion H; subst; apply orth_symm.
      + by right=> H; apply: Hnwf; inversion H; subst.
  Qed.
  Notation "m #P s" := (wfbP m s: reflect (m#s) (wfb m s))
                         (at level 70, no associativity): map_scope.


  (* lambda, subtype of sexp *)
  Inductive isL: sexp -> Prop :=
  | lfree (x: T): isL (free x)
  | lbox: isL box
  | lapp (s t: sexp): isL s -> isL t -> isL (s@t)
  | labs (m: map)(s: sexp): isL s -> m#s -> isL (m\s).
  Hint Constructors isL.

  Fixpoint isLb (s: sexp): bool :=
    match s with
      | free _ | box => true
      | app s1 s2 => isLb s1 && isLb s2
      | abs m s => isLb s && wfb m s
    end.
  Functional Scheme isLb_ind := Induction for isLb Sort Prop.
  Functional Scheme isLb_rect := Induction for isLb Sort Type.

  Lemma isLbP s: reflect (isL s) (isLb s).
  Proof.
    elim/isLb_rect: s /(isLb s) => s0;
      try (by move=> *; match goal with |- reflect ?x true => left end).
    - move=> s1 s2 _{s0} [HL1|HnL1] /=;
        last by move=> _; right=> H; apply: HnL1; inversion H; subst.
        by case=> [HL2|HnL2] /=; first (left; constructor);
             last (right=> H; apply: HnL2; inversion H; subst).
    - move=> m s _{s0} [HL|HnL] /=;
        last by right=> H; apply: HnL; inversion H; subst.
        by case: (m #P s) => [Hwf|Hnwf]; first (left; constructor);
             last (right=> H; apply: Hnwf; inversion H; subst).
  Qed.
  
  Inductive lambda: Type :=
  | Lam (term: sexp): isLb term -> lambda.
  Hint Constructors lambda.
  Definition body: lambda -> sexp :=
    fun M => let (s,_) := M in s.
  Canonical lambda_subType := Eval hnf in [subType for @body].
  Local Coercion body: lambda >-> sexp.

  Lemma isL_wf (s: sexp): isL s -> 0#s.
  Proof.
    elim=> [x||s1 IH1 s2 IH2|m s' IHs] /=; try by constructor.
    move=> HisL Hwf; rewrite -mapp_00_0; apply wf_mapp_app; done.
  Qed.

  Lemma lambda_is_wf (M: lambda): 0#M.
  Proof.
    move: M => [s Hlam] /=.
    move: Hlam => /isLbP; apply isL_wf.
  Qed.

  Lemma wf_sexp_is_lambda (s: sexp): 0#s -> isL s.
  Proof.
    move=> H; apply/isLbP; move: H.
    elim/isLb_ind: s /(isLb s) => s0 //.
    - move=> s1 s2 _ H1 H2 H.
      by move: (H1 (wf0appl H)) (H2 (wf0appr H))=> -> ->.
    - move=> m s _ HL H; apply/andP; split.
      + inversion H; subst.
        by move: (HL H2) => ->.
      + by apply/wfbP; apply wfabs_inv with 0.
  Qed.

  Definition asL (s: sexp): 0#s -> lambda :=
    fun H => Lam (introT (isLbP s) (wf_sexp_is_lambda H)).

End Lambda.

(* lambda is subType of sexp *)

Open Scope map_scope.
Coercion body: lambda >-> sexp.
Infix "@" := app (at level 25, left associativity): map_scope.
Infix "\" := abs (at level 35, right associativity): map_scope.
Notation "m # s" := (well_formed m s)
                      (at level 70, no associativity): map_scope.
Notation "m #P s" := (wfbP m s: reflect (m # s) (wfb m s))
                       (at level 70, no associativity): map_scope.
