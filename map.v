(* Map Skelton *)
Require Import
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.ssrbool
Ssreflect.eqtype.

Set Implicit Arguments.
Unset Strict Implicit.

Delimit Scope map with map_scope.

Module Map.

  Section Definitions.
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
    Local Coercion mmap: map1 >-> map.
    Notation "0" := mnull.

    (* eqType declaration(s) *)
    Fixpoint eq_map1 (x y: map1): bool :=
      match x, y with
        | 1, 1 => true
        | minl m, minl n | minr m, minr n => eq_map1 m n
        | mcons m m', mcons n n' => eq_map1 m n && eq_map1 m' n'
        | _, _ => false
      end.

    Definition eq_map (x y: map): bool :=
      match x, y with
        | mnull, mnull => true
        | mmap m, mmap n => eq_map1 m n
        | _, _ => false
      end.

    Lemma eq_map1P: Equality.axiom eq_map1.
    Proof.
      rewrite /Equality.axiom.
      elim=> [| m IHm | m IHm | m IHm n IHn] //=;
                                             elim=> [| m' IHm'| m' IHm'| m' IHm' n' IHn'] //=;
                                                                                          try by constructor.
      - by move: (IHm m') => [ -> | Hneq] /=; [ left | right; case ].
      - by move: (IHm m') => [ -> | Hneq] /=; [ left | right; case ].
      - move: (IHm m') => [ -> | Hneq] /=; last by right; case.
          by move: (IHn n') => [ -> | Hneq] /=; [ left | right; case ].
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
      rewrite /Equality.axiom.
      move=> [| m]; move=> [| n] //=; try by constructor.
      apply iffP with (m = n); first apply eq_map1P.
      - by move=> -> .
      - by case.
    Defined.
    
    Canonical map_eqMixin := EqMixin eq_mapP.
    Canonical map_eqType := Eval hnf in EqType map map_eqMixin.

    Lemma eq_mapE: eq_map = eq_op.
    Proof. by []. Qed.

    Lemma eq_mmap m n:
      (mmap m == mmap n) = (m == n).
    Proof.
      Set Printing Coercions.
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
    Infix "*" := mapp (at level 40, left associativity).

    Lemma mapp_injective:
      forall (m m' n n': map),
        m*n == m'*n' = (m == m') && (n == n').
    Proof.
      move=> [| m1] [| m1'] [| n1] [| n1'] //=; try by rewrite andbF.
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
    | orth_m_0 (m: map): m!0
    | orth_0_n (n: map): 0!n
    | orth_mapp (m n m' n': map): m!n -> m'!n' -> m*m'!n*n'
    where "m ! n" := (orthogonal m n).
    Notation "m ! n" := (orthogonal m n) (at level 70, no associativity).

    Lemma orth_symm m n: m!n -> n!m.
    Proof.
      elim=> [m'|n'|m1 n1 m2 n2 Hmn1 Hnm1 Hmn2 Hnm2] /=; try by constructor.
    Qed.                                                   

    Lemma orth_1_0 m: 1!m -> m = 0.
    Proof.
      move=> Horth; inversion Horth; try done.
      destruct m0, m'; simpl in *; try discriminate.
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
    
    Lemma orthb1_symm m n: orthb1 m n = orthb1 n m.
    Proof.
      elim: m n => [|m IHm|m IHm|m1 IHm1 m2 IHm2] n /=;
                                                  try by destruct n; simpl.
      - destruct n; simpl; try done.
          by rewrite (IHm1 n1) (IHm2 n2).
    Qed.

    Definition orthb (m n: map) :=
      match m, n with
        | 0, _ => true
        | _, 0 => true
        | mmap m', mmap n' => orthb1 m' n'
      end.
    
    Lemma orthb_symm m n: orthb m n = orthb n m.
    Proof.
      destruct m, n; simpl; try done.
      apply orthb1_symm.
    Qed.

    Lemma orthb1P (m1 n1: map1): reflect (m1!n1) (orthb1 m1 n1).
    Proof.
      elim: m1 n1 => [|m IHm|m IHm|m IHm n IHn] /= n1.
      - right; move=> /orth_1_0 H; discriminate.
      - destruct n1; move=> //=.
        + right; move=> /orth_symm /orth_1_0 H; discriminate.
        + case: (IHm n1) => H.
          * left.
            rewrite -mappm0l -mappm0l; apply orth_mapp; try done.
            apply orth_0_n.
          * right.
            rewrite -mappm0l -mappm0l; move=> H'; inversion H'.
            rewrite -mappm0l in H0.
            rewrite -mappm0l in H1.
            move: H0 H1 => /eqP H0 /eqP H1.
            rewrite mapp_injective in H0.
            rewrite mapp_injective in H1.
            move: H0 H1 =>
            /andP [/eqP H00 /eqP H01] /andP [/eqP H10 /eqP H11].
            subst; done.
        + left.
          rewrite -mappm0l -mapp0mr; apply orth_mapp; by constructor.
        + case: (IHm n1_1) => H.
          * left.
              by rewrite -mappm0l -mapp_mcons; apply orth_mapp;
              try by constructor.
          * right.
            rewrite -mappm0l -mapp_mcons; move=> H'; inversion H'.
            rewrite -mappm0l in H0.
            rewrite -mapp_mcons in H1.
            move: H0 H1 => /eqP H0 /eqP H1.
            rewrite mapp_injective in H0.
            rewrite mapp_injective in H1.
            move: H0 H1 =>
            /andP [/eqP H00 /eqP H01] /andP [/eqP H10 /eqP H11].
            subst; done.
      - destruct n1; move=> //=.
        + right; move=> /orth_symm /orth_1_0 H; discriminate.
        + left.
          rewrite -mappm0l -mapp0mr; apply orth_mapp; by constructor.
        + case: (IHm n1) => H.
          * left.
            rewrite -mapp0mr -mapp0mr; apply orth_mapp; try done.
            apply orth_0_n.
          * right.
            rewrite -mapp0mr -mapp0mr; move=> H'; inversion H'.
            rewrite -mapp0mr in H0.
            rewrite -mapp0mr in H1.
            move: H0 H1 => /eqP H0 /eqP H1.
            rewrite mapp_injective in H0.
            rewrite mapp_injective in H1.
            move: H0 H1 =>
            /andP [/eqP H00 /eqP H01] /andP [/eqP H10 /eqP H11].
            subst; done.
        + case: (IHm n1_2) => H.
          * left.
              by rewrite -mapp0mr -mapp_mcons; apply orth_mapp;
              try by constructor.
          * right.
            rewrite -mapp0mr -mapp_mcons; move=> H'; inversion H'.
            rewrite -mapp0mr in H0.
            rewrite -mapp_mcons in H1.
            move: H0 H1 => /eqP H0 /eqP H1.
            rewrite mapp_injective in H0.
            rewrite mapp_injective in H1.
            move: H0 H1 =>
            /andP [/eqP H00 /eqP H01] /andP [/eqP H10 /eqP H11].
            subst; done.
      - destruct n1; move=> //=.
        + right; move=> /orth_symm /orth_1_0 H; discriminate.
        + case: (IHm n1) => H.
          * left.
            rewrite -mappm0l -mapp_mcons; apply orth_mapp; try done.
            apply orth_m_0.
          * right.
            rewrite -mappm0l -mapp_mcons; move=> H'; inversion H'.
            rewrite -mapp_mcons in H0.
            rewrite -mappm0l in H1.
            move: H0 H1 => /eqP H0 /eqP H1.
            rewrite mapp_injective in H0.
            rewrite mapp_injective in H1.
            move: H0 H1 =>
            /andP [/eqP H00 /eqP H01] /andP [/eqP H10 /eqP H11].
            subst; done.
        + case: (IHn n1) => H.
          * left.
            rewrite -mapp_mcons -mapp0mr; apply orth_mapp; try done.
            apply orth_m_0.
          * right.
            rewrite -mapp_mcons -mapp0mr; move=> H'; inversion H'.
            rewrite -mapp_mcons in H0.
            rewrite -mapp0mr in H1.
            move: H0 H1 => /eqP H0 /eqP H1.
            rewrite mapp_injective in H0.
            rewrite mapp_injective in H1.
            move: H0 H1 =>
            /andP [/eqP H00 /eqP H01] /andP [/eqP H10 /eqP H11].
            subst; done.
        + { case: (IHm n1_1) => Hn11 /=.
            - case: (IHn n1_2) => Hn12 /=.
              + left.
                  by rewrite -mapp_mcons -mapp_mcons; apply orth_mapp;
                  try by constructor.
              + right.
                rewrite -mapp_mcons -mapp_mcons; move=> H; inversion H.
                rewrite -mapp_mcons in H0.
                rewrite -mapp_mcons in H1.
                move: H0 H1 => /eqP H0 /eqP H1.
                rewrite mapp_injective in H0.
                rewrite mapp_injective in H1.
                move: H0 H1 =>
                /andP [/eqP H00 /eqP H01] /andP [/eqP H10 /eqP H11].
                subst; done.
            - right.
              rewrite -mapp_mcons -mapp_mcons; move=> H; inversion H.
              rewrite -mapp_mcons in H0.
              rewrite -mapp_mcons in H1.
              move: H0 H1 => /eqP H0 /eqP H1.
              rewrite mapp_injective in H0.
              rewrite mapp_injective in H1.
              move: H0 H1 =>
              /andP [/eqP H00 /eqP H01] /andP [/eqP H10 /eqP H11].
              subst; done. }
    Qed.
    Notation "m1 !1P n1" :=
      (orthb1P m1 n1: reflect (mmap m1!mmap n1) (orthb1 m1 n1))
        (at level 70, no associativity).

    Lemma orthbP (m n: map): reflect (m!n) (orthb m n).
    Proof.
      case: m => [|m1] /=; first by left; constructor.
      case: n => [|n1] /=; first by left; constructor.
      exact (orthb1P m1 n1).
    Qed.
    Notation "m !P n" := (orthbP m n: reflect (m!n) (orthb m n))
                           (at level 70, no associativity).

  End Definitions.

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

  Module Notations.
    Local Close Scope type_scope.
    Open Scope map_scope.
    Coercion mmap: map1 >-> map.
    Notation "1" := binder: map_scope.
    Notation "0" := mnull: map_scope.
    Notation "m * n" := (mapp m n) 
                          (at level 40, left associativity): map_scope.
    Notation "m ! n" := (orthogonal m n)
                          (at level 70, no associativity).
    Notation "m1 !1P n1" :=
      (orthb1P m1 n1: reflect (mmap m1!mmap n1) (orthb1 m1 n1))
        (at level 70, no associativity): map_scope.
    Notation "m !P n" := (orthbP m n: reflect (m!n) (orthb m n))
                           (at level 70, no associativity): map_scope.
  End Notations.

End Map.
Export Map.Notations.

Module Lambda.

  Section Lambda.

    Import Map Map.Notations.

    Parameter (T: eqType).

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

    Lemma eq_sexpP: Equality.axiom eq_sexp.
    Proof.
      rewrite /Equality.axiom.
      elim=> [x||s1 IHs1 s2 IHs2|m s IHs];
            move=> [y||t1 t2|n t] //=;
        try by constructor.
      - by case: (x =P y); [left; subst | by right; case ].
      - case: (IHs1 t1) => Hst1 /=.
        + case: (IHs2 t2) => Hst2 /=; first by left; subst.
          right; case; done.
        + right; case; done.
      - case: (IHs t) => Hst /=.
        + rewrite andbT Hst; case: (m =P n) => Hmn; first by left; subst.
          by right; case.
        + by rewrite andbF; right; case.
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

    Lemma wf_0 m s: m#s -> 0#s.
    Proof.
      elim=> [x||
             |m' n' s' t' IHms Hs IHnt Ht
             |m' n' t IHmt Hmt IHnt Hnt Horth] //=; try by constructor.
      - have: (0*0 = 0); first done; move=> <-.
          by apply wf_mapp_app.
      - apply wf_abs; try done; by constructor.
    Qed.

    Lemma mapp_00_0: 0*0 = 0. done. Qed.

    Lemma wfbP m s: reflect (m#s) (wfb m s).
    Proof.
      elim: s m => [x||s1 IHs1 s2 IHs2|n s IHs].
      - case=> [|[|m1|m2|m1 m2]] /=;
          try (by right; move=> H; inversion H);
              try by left; constructor.
      - case=> [|[|m1|m2|m1 m2]] /=;
          try (by right; move=> H; inversion H);
              try by left; constructor.
      - { case=> [|[|m1|m2|m1 m2]] /=.
          - case: (IHs1 0) => H1 /=.
            + case: (IHs2 0) => H2 /=.
              * by left; rewrite -mapp_00_0; apply wf_mapp_app.
              * right; rewrite -mapp_00_0; move=> H; inversion H; subst.
                apply H2; move: H6; apply wf_0.
            + right; rewrite -mapp_00_0; move=> H; inversion H; subst.
              apply H1; move: H4; apply wf_0.
          - right; move=> H; inversion H; subst.
            destruct m, n; discriminate.
          - case: (IHs1 m1) => H1 /=.
            + case: (IHs2 0) => H2 /=.
              * by left; rewrite -mappm0l; apply wf_mapp_app.
              * right; rewrite -mappm0l; move=> H; inversion H; subst.
                apply H2; move: H6; apply wf_0.
            + right; rewrite -mappm0l; move=> H; inversion H; subst.
              rewrite -mappm0l in H0.
              move: H0 => /eqP H0; rewrite mapp_injective in H0.
              move: H0 => /andP [/eqP H00 /eqP H01]; subst; done.
          - case: (IHs2 m2) => H2 /=.
            + case: (IHs1 0) => H1 /=.
              * by left; rewrite -mapp0mr; apply wf_mapp_app.
              * right; rewrite -mapp0mr; move=> H; inversion H; subst.
                apply H1; move: H5; apply wf_0.
            + rewrite andbF; right;
              rewrite -mapp0mr; move=> H; inversion H; subst.
              rewrite -mapp0mr in H0.
              move: H0 => /eqP H0; rewrite mapp_injective in H0.
              move: H0 => /andP [/eqP H00 /eqP H01]; subst; done.
          - case: (IHs1 m1) => H1 /=.
            + case: (IHs2 m2) => H2 /=;
                first by left; rewrite -mapp_mcons; apply wf_mapp_app.
              right; rewrite -mapp_mcons; move=> H; inversion H; subst.
              rewrite -mapp_mcons in H0.
              move: H0 => /eqP H0; rewrite mapp_injective in H0.
              move: H0 => /andP [/eqP H00 /eqP H01]; subst; done.
            + right; rewrite -mapp_mcons; move=> H; inversion H; subst.
              rewrite -mapp_mcons in H0.
              move: H0 => /eqP H0; rewrite mapp_injective in H0.
              move: H0 => /andP [/eqP H00 /eqP H01]; subst; done. }
      - case=> [|[|m1|m2|m1 m2]] /=.
        + rewrite andbT.
          case: (IHs n) => Hn.
          * rewrite andbT.
            case: (IHs 0) => H0;
              first by left; apply wf_abs; try constructor.
            right; move=> H; inversion H; subst; done.
          * rewrite andbF; right; move=> H; inversion H; subst; done.
        + case: n => [|[|n1|n2|n1 n2]] /=; try rewrite andbF;
          try (right; move=> H; inversion H; subst;
               inversion H5; subst;
               destruct m, m'; discriminate).
          rewrite andbT.
          case: (IHs 1) => H1 /=;
            last by right; move=> H; inversion H; subst; done.
          case: (IHs 0) => H0;
            first by left; apply wf_abs; try constructor.
          right; move=> H; inversion H; subst; done.
        + case: n => [|[|n1|n2|n1 n2]] /=; try rewrite andbF.
          * rewrite andbT.
            case: (IHs (minl m1)) => H1 /=;
              last by right; move=> H; inversion H; subst; done.
            case: (IHs 0) => H0;
              first by left; apply wf_abs; try constructor.
            right; move=> H; inversion H; subst; done.
          * try (right; move=> H; inversion H; subst;
                 inversion H5; subst;
                 destruct n, n'; discriminate).
          * { case: (m1 !1P n1) => Horth1 /=.
              - rewrite andbT.
                case: (IHs (minl m1)) => Hm1 /=.
                + case: (IHs (minl n1)) => Hn1 /=.
                  * left; apply wf_abs; try done.
                    by rewrite -mappm0l -mappm0l;
                      apply orth_mapp; try constructor.
                  * by right; move=> H; inversion H; subst.
                + by right; move=> H; inversion H; subst.
              - rewrite andbF; right; move=> H; inversion H; subst.
                rewrite -mappm0l -mappm0l in H5.
                by move: H5 => /orthbP /= /orthb1P. }
          * rewrite andbT.
            { case: (IHs (minl m1)) => Hm1 /=.
              - case: (IHs (minr n2)) => Hn2 /=.
                + left; apply wf_abs; try done.
                  by apply /orthbP.
                + by right; move=> H; inversion H; subst.
              - by right; move=> H; inversion H; subst. }
          * { case: (m1 !1P n1) => Horth1 /=.
              - rewrite andbT.
                case: (IHs (minl m1)) => Hm1 /=.
                + case: (IHs (mcons n1 n2)) => Hn /=.
                  * left; apply wf_abs; try done.
                    by rewrite -mapp_mcons -mappm0l;
                      apply orth_mapp; try constructor.
                  * by right; move=> H; inversion H; subst.
                + by right; move=> H; inversion H; subst.
              - rewrite andbF; right; move=> H; inversion H; subst.
                rewrite -mapp_mcons -mappm0l in H5.
                by move: H5 => /orthbP /= /orthb1P. }
        + case: n => [|[|n1|n2|n1 n2]] /=; try rewrite andbF.
          * rewrite andbT.
            case: (IHs (minr m2)) => H2 /=;
              last by right; move=> H; inversion H; subst; done.
            case: (IHs 0) => H0;
              first by left; apply wf_abs; try constructor.
            right; move=> H; inversion H; subst; done.
          * try (right; move=> H; inversion H; subst;
                 inversion H5; subst;
                 destruct n, n'; discriminate).
          * rewrite andbT.
            { case: (IHs (minr m2)) => Hm2 /=.
              - case: (IHs (minl n1)) => Hn1 /=.
                + left; apply wf_abs; try done.
                  by apply /orthbP.
                + by right; move=> H; inversion H; subst.
              - by right; move=> H; inversion H; subst. }
          * { case: (m2 !1P n2) => Horth1 /=.
              - rewrite andbT.
                case: (IHs (minr m2)) => Hm2 /=.
                + case: (IHs (minr n2)) => Hn2 /=.
                  * left; apply wf_abs; try done.
                    by rewrite -mapp0mr -mapp0mr;
                      apply orth_mapp; try constructor.
                  * by right; move=> H; inversion H; subst.
                + by right; move=> H; inversion H; subst.
              - rewrite andbF; right; move=> H; inversion H; subst.
                rewrite -mapp0mr -mapp0mr in H5.
                by move: H5 => /orthbP /= /orthb1P. }
          * { case: (m2 !1P n2) => Horth1 /=.
              - rewrite andbT.
                case: (IHs (minr m2)) => Hm2 /=.
                + case: (IHs (mcons n1 n2)) => Hn /=.
                  * left; apply wf_abs; try done.
                    by rewrite -mapp_mcons -mapp0mr;
                      apply orth_mapp; try constructor.
                  * by right; move=> H; inversion H; subst.
                + by right; move=> H; inversion H; subst.
              - rewrite andbF; right; move=> H; inversion H; subst.
                rewrite -mapp_mcons -mapp0mr in H5.
                by move: H5 => /orthbP /= /orthb1P. }
        + case: n => [|[|n1|n2|n1 n2]] /=; try rewrite andbF.
          * rewrite andbT.
            case: (IHs (mcons m1 m2)) => Hm /=;
              last by right; move=> H; inversion H; subst; done.
            case: (IHs 0) => H0;
              first by left; apply wf_abs; try constructor.
            right; move=> H; inversion H; subst; done.
          * try (right; move=> H; inversion H; subst;
                 inversion H5; subst;
                 destruct n, n'; discriminate).
          * { case: (m1 !1P n1) => Horth1 /=.
              - rewrite andbT.
                case: (IHs (mcons m1 m2)) => Hm /=.
                + case: (IHs (minl n1)) => Hn1 /=.
                  * left; apply wf_abs; try done.
                    by rewrite -mapp_mcons -mappm0l;
                      apply orth_mapp; try constructor.
                  * by right; move=> H; inversion H; subst.
                + by right; move=> H; inversion H; subst.
              - rewrite andbF; right; move=> H; inversion H; subst.
                rewrite -mapp_mcons -mappm0l in H5.
                by move: H5 => /orthbP /= /orthb1P. }
          * { case: (m2 !1P n2) => Horth1 /=.
              - rewrite andbT.
                case: (IHs (mcons m1 m2)) => Hm /=.
                + case: (IHs (minr n2)) => Hn2 /=.
                  * left; apply wf_abs; try done.
                    by rewrite -mapp_mcons -mapp0mr;
                      apply orth_mapp; try constructor.
                  * by right; move=> H; inversion H; subst.
                + by right; move=> H; inversion H; subst.
              - rewrite andbF; right; move=> H; inversion H; subst.
                rewrite -mapp_mcons -mapp0mr in H5.
                by move: H5 => /orthbP /= /orthb1P. }
          * { case: (m1 !1P n1) => Horth1 /=.
              - case: (m2 !1P n2) => Horth2 /=.
                + rewrite andbT.
                  case: (IHs (mcons m1 m2)) => Hm /=.
                  * { case: (IHs (mcons n1 n2)) => Hn /=.
                      - left; apply wf_abs; try done.
                          by rewrite -mapp_mcons -mapp_mcons;
                          apply orth_mapp; try constructor.
                      - by right; move=> H; inversion H; subst. }
                  * by right; move=> H; inversion H; subst.
                + rewrite andbF; right; move=> H; inversion H; subst.
                  rewrite -mapp_mcons -mapp_mcons in H5.
                  by move: H5 => /= /orthbP /= /andP
                       [/orthb1P Ho1 /orthb1P Ho2].
              - rewrite andbF; right; move=> H; inversion H; subst.
                  rewrite -mapp_mcons -mapp_mcons in H5.
                  by move: H5 => /= /orthbP /= /andP
                       [/orthb1P Ho1 /orthb1P Ho2]. }
    Qed.
    Notation "m #P s" := (wfbP m s: reflect (m#s) (wfb m s))
                           (at level 70, no associativity).


    (* lambda, subtype of sexp *)
    Inductive isL: sexp -> Prop :=
    | lfree (x: T): isL (free x)
    | lbox: isL box
    | lapp (s t: sexp): isL s -> isL t -> isL (s@t)
    | labs (m: map)(s: sexp): isL s -> m#s -> isL (m\s).

    Fixpoint isLb (s: sexp): bool :=
      match s with
        | free _ | box => true
        | app s1 s2 => isLb s1 && isLb s2
        | abs m s => isLb s && wfb m s
      end.

    Lemma isLbP s: reflect (isL s) (isLb s).
    Proof.
      elim: s => [x||s1 IH1 s2 IH2|m s IHs] /=.
      - left; by constructor.
      - left; by constructor.
      - case: IH1 => H1 /=.
        + case: IH2 => H2 /=.
          * left; by constructor.
          * by right; move=> H; inversion H; subst.
        + by right; move=> H; inversion H; subst.
      - case: IHs => Hs /=.
        + case: (m #P s) => Hwf /=.
          * left; by constructor.
          * by right; move=> H; inversion H; subst.
        + by right; move=> H; inversion H; subst.
    Qed.
    
    (* lambda is subType of sexp *)
    Structure lambda := Lam { term : sexp; _: isLb term }.
    Canonical lambda_subType := Eval hnf in [subType for term].
    Check lambda.

  End Lambda.

  Module Notations.
    Import Map.Notations.
    Open Scope map_scope.
    Coercion term: lambda >-> sexp.
    Infix "@" := app (at level 25, left associativity): map_scope.
    Infix "\" := abs (at level 35, right associativity): map_scope.
    Notation "m # s" := (well_formed m s)
                          (at level 70, no associativity): map_scope.
    Notation "m #P s" := (wfbP m s: reflect (m # s) (wfb m s))
                           (at level 70, no associativity): map_scope.
  End Notations.
End Lambda.
Export Lambda.Notations.


(* monad for computational context *)
Class Monad (T: Type -> Type) :=
  { emb {X: Type}: X -> T X;
    bind {X Y: Type}(f: X -> T Y): T X -> T Y;
    
    bind_subst:
      forall (X Y: Type)(f g: X -> T Y)(m n: T X),
        m = n -> (forall x, f x = g x) -> bind f m = bind g n;

    emb_bind:
      forall (X Y: Type)(f: X -> T Y)(x: X),
        bind f (emb x) = f x;

    bind_emb:
      forall (X: Type)(m: T X),
        bind emb m = m;

    bind_assoc:
      forall (X Y Z: Type)(f: X -> T Y)(g: Y -> T Z)(m: T X),
        bind g (bind f m) = bind (fun x => bind g (f x)) m
 }.
Notation "m >>= f" := (bind f m) (at level 65, left associativity).
Notation "m >> p" := (bind (fun _ => p) m) (at level 65, left associativity).
Notation "x <- m ; p" := (m >>= fun x => p) (at level 60, right associativity).
Notation "(: x , y :) <- m ; p" := (m >>= fun tup:_*_ => let: (x,y) := tup in p) (at level 60, right associativity).
Notation "'do' m" := m (at level 100, right associativity).
Notation "'mlet' x := m ; p" := (x <- emb m ; p) (at level 60, right associativity).

Class Failable {T}(m: Monad T) :=
  { failure (X: Type): T X;
    failure_propagate:
      forall (X Y: Type)(f: X -> T Y),
        failure X >>= f = failure Y }.

Section Monadic.
  Import Map Lambda.
  Open Scope map_scope.
  Context {F}{monad: Monad F}(failable: Failable monad){T: eqType}.

  Check @map1.
  Program Fixpoint HoleFill (M: lambda)(m: map)(P: lambda): F lambda :=
    let: s := term M in
    match s, m with
      | box, 1 => emb (@Lam P _)
      | box, 0 => emb (@Lam box _)
      | free x, 0 => emb (@Lam (free x) _)
      | _, _ => failure lambda
    end.
          | M@N, 0 =>
            do mlet m := 0;
                        mlet n := 0;
                                 MmP <- HoleFill M m p;
                                 NnP <- HoleFill N n p;
                                 emb (MmP@NnP)
          | M@N, minl m =>
            do mlet n := 0;
                        MmP <- HoleFill M m p;
                        NnP <- HoleFill N n p;
                        emb (MmP@NnP)
          | M@N, minr n =>
            do mlet m := 0;
                        MmP <- HoleFill M m p;
                        NnP <- HoleFill N n p;
                        emb (MmP@NnP)
          | M@N, mcons m n =>
            do MmP <- HoleFill M m p;
              NnP <- HoleFill N n p;
              emb (MmP@NnP)
          | n\N, m =>
            do NmP <- HoleFill N m p;
              emb (n\NmP)
          | _,_ => failure sexp
        end.

      Notation "[ M '_' m { P } ]" := (HoleFill M m P).

      (*      Lemma wf_wf m x: 0#x -> m#x.
      Proof.
        move=> H0x; move: x H0x m.
        elim=> [y||s IHs t IHt|m s IHs] Hwf m'; try constructor. *)

      (* Lemma HoleFill_wf m M N: *)
      (*   (exists x, emb x = HoleFill M m N) -> m#M. *)

      Lemma HoleFill_wf m M N:
        m#M -> 0#N -> exists x, 0#x /\ emb x = HoleFill M m N.
      Proof.
        move=> HmM H0N.
        elim: HmM =>  //= [x||
                          | m1 m2 s t H1 IH1 H2 IH2
                          | m1 m2 s H1 IH1 H2 IH2] /=.
        - exists (free x); split; try by constructor.
        - exists box; split; try by constructor.
        - exists N; split; done.
          move: IH1 IH2 => [x1 [Hx1 Heq1]] [x2 [Hx2 Heq2]] /=.
          exists (x1@x2); split;
          first (rewrite -mapp_00_0; apply wf_mapp_app; done).
          case: m1 H1 Heq1 => /=.
          + case: m2 H2 Heq2 => /=.
            * move=> _ Heq1 _ Heq2.
                by rewrite emb_bind emb_bind
                   -Heq1 -Heq2 emb_bind emb_bind.
            * move=> m' _ Heq1 _ Heq2.
                by rewrite emb_bind -Heq1 -Heq2 emb_bind emb_bind.
          + case: m2 H2 Heq2 => /=.
            * move=> _ Heq1 n' _ Heq2.
                by rewrite emb_bind -Heq1 -Heq2 emb_bind emb_bind.
            * move=> m' _ Heq1 n' _ Heq2.
                by rewrite -Heq1 -Heq2 emb_bind emb_bind.
        - move: IH1 IH2 => [x1 [Hx1 Heq1]] [x2 [Hx2 Heq2]] Horth.
          rewrite -Heq1 emb_bind.
          exists (m2\x1); split; last done.
          apply wf_abs; first done; try by constructor.
          (*   Heq2 : emb x2 = [s _ m2 {N}] means m2#x1 *)

      Fixpoint mapf (x: T)(s: sexp): map :=
        match s with
          | free y => if x == y then 1 else 0
          | box => 0
          | M@N => mapf x M*mapf x N
          | m\M => mapf x M
        end.

      Fixpoint skelf (x: T)(s: sexp): sexp :=
        match s with
          | free y => if x == y then box else free y
          | box => box
          | M@N => skelf x M@skelf x N
          | m\M => m\skelf x M
        end.

      Definition lam (x: T)(M: sexp) := mapf x M\skelf x M.

      Lemma mapp_0 m n: m*n = 0 -> m = 0 /\ n = 0.
      Proof.
        case: m => [|m] /=; case: n => [| n] /=; try done.
      Qed.

      Lemma wf_skelf m x s: m#s -> m#skelf x s.
      Proof.
        elim=> [y|||m1 m2 s1 s2 H1 IH1 H2 IH2|m1 m2 t H1 IH1 H2 IH2 H] /=;
          try by constructor.
        - case: (x == y) => /=; try by constructor.
      Qed.


(*      Lemma orth_mapf m x s: 0#s -> 0!m -> (mapf x s)!m.
        elim: s => [y||s IHs t IHt|n s IHs] /= Hwf Horth;
                  try by constructor.
        - case: (x == y) => /=; try by constructor.
          simpl.
        move=> Horth; move: Horth x s.
        elim=> [m'|n'|m1 n1 m2 n2 H1 IH1 H2 IH2] x s; try by constructor.
      Lemma orth_mapf m x s: 0!m -> mapf x s!m.
      Proof.
        move=> Horth; move: Horth x s.
        elim=> [_|n|m1 n1 m2 n2 H1 IH1 H2 IH2]; try by constructor.
        - case: (x == y) => /=; try by constructor.
      Qed.
       *)

      (*
      Lemma map_skeleton_aux:
        forall x m M,
          m#M ->
          m*mapf x M # skelf x M -> mapf x M # m\skelf x M.
      Proof.
        move=> x m M Hwf.
        elim: Hwf => [y||
                     |m1 m2 s1 s2 H1 IH1 H2 IH2
                     |m1 m2 s H1 IH1 H2 IH2 Horth] /=;
          try by constructor.
        - case: (x == y) => /=; try by constructor.
          + move=> H; inversion H.
          + move=> H; inversion H.
            apply wf_abs; try by constructor.
        - move=> H; apply wf_abs; try by constructor.
        - move=> H; apply wf_abs; try by constructor.
        - move=> H; inversion H; subst.
          move: H3 => /eqP; rewrite mapp_injective;
            move=> -/andP [-/eqP Heq1 -/eqP Heq2]; subst.
          apply wf_abs; try done.
          apply wf_mapp_app; try done.
          + apply wf_mapp_app; try done.


        move=> x m M; simpl; auto.
      Qed.
       *)

      Definition substitute (M: sexp)(x: T)(p: sexp) :=
        HoleFill (skelf x M) (mapf x M) p.

      Lemma substitute_app M N x P:
        substitute (M@N) x P = do MxP <- substitute M x P;
                                  NxP <- substitute N x P;
                                  emb (MxP@NxP).
      Proof.
        rewrite /substitute //=.
        case: (mapf x M) => //=.
        - case: (mapf x N) => //=.
          + by rewrite emb_bind emb_bind.
          + by move=> m; rewrite emb_bind.
        - move=> m.
          case: (mapf x N) => //=.
          + by rewrite emb_bind.
      Qed.

      Lemma substitute_abs m M x P:
        substitute (m\M) x P = do MxP <- substitute M x P;
                                  emb (m\MxP).
      Proof.
        rewrite /substitute //=.
      Qed.


      Lemma fresh_on_skelf x P:
        fresh_on x P -> skelf x P = P.
      Proof.
        elim: P => //= [y|s IHs t IHt| m s IHs] /=.
        - apply ifN_eq.
        - by move=> /andP [Hs Ht]; rewrite (IHs Hs) (IHt Ht).
        - by move=> H; rewrite (IHs H).
      Qed.

      Lemma fresh_on_mapf x P:
        fresh_on x P -> mapf x P = 0.
      Proof.
        elim: P => //= [y|s IHs t IHt] /=.
        - apply ifN_eq.
        - by move=> /andP [Hs Ht]; rewrite (IHs Hs) (IHt Ht).
      Qed.

      Lemma HF_0 P M: emb P = HoleFill P 0 M.
      Proof.
        { elim: P => [x||s IHs t IHt|m s IHs] //=.
          - rewrite emb_bind emb_bind //= -IHs -IHt.
            rewrite emb_bind emb_bind //=.
          - by rewrite -IHs emb_bind. }
      Qed.

      Lemma substitute_lemma x y P M N:
        x <> y -> fresh_on x P ->
        (do MxN <- substitute M x N;
            substitute MxN y P)
        =
        (do MyP <- substitute M y P;
            NyP <- substitute N y P;
            substitute MyP x NyP).
      Proof.
        move=> Hneq Hfresh.
        rewrite /substitute; induction M; move=> //=.
        - case Hxx0: (x == x0) => //=.
          + rewrite emb_bind //=.
            case Hyy0: (y == x0) => //=.
            * move: Hxx0 Hyy0 => /eqP Hxx0 /eqP Hyy0 //=; subst.
                by elim Hneq.
            * by rewrite emb_bind //= Hxx0 //= bind_emb.
          + rewrite emb_bind //=.
            case Hyy0: (y == x0) => //=.
            * rewrite emb_bind //=.
              rewrite (fresh_on_mapf Hfresh)
                      (fresh_on_skelf Hfresh) //=.
              { elim: N => [x1||s IHs t IHt| m s IHs] //=.
                - case Hyx1: (y == x1) => //=.
                  + rewrite emb_bind.
                    apply: (HF_0 P P).
                  + rewrite emb_bind.
                    apply: (HF_0 P _).
                - rewrite emb_bind.
                  apply: (HF_0 P _).
                - destruct (mapf y s); simpl.
                  + destruct (mapf y t); simpl.
                    * rewrite emb_bind emb_bind.
                      by rewrite -(HF_0 _ P) -(HF_0 _ P)
                        emb_bind emb_bind emb_bind -(HF_0 _ _).
                    * rewrite emb_bind -(HF_0 _ _) emb_bind //=.
                      rewrite bind_assoc IHt.
                      apply bind_subst; try done.
                      by move=> x1;
                          rewrite emb_bind -(HF_0 _ _) -(HF_0 _ _).
                  + destruct (mapf y t); simpl.
                    * rewrite emb_bind bind_assoc IHs.
                      apply bind_subst; try done.
                      move=> x1.
                      rewrite bind_assoc -(HF_0 _ _) IHt.
                      apply bind_subst; try done.
                      move=> x2.
                      by rewrite emb_bind -(HF_0 _ _) -(HF_0 _ _).
                    * rewrite bind_assoc IHs.
                      apply bind_subst; try done.
                      move=> x1.
                      rewrite bind_assoc -(HF_0 _ _) IHt.
                      apply bind_subst; try done.
                      move=> x2.
                      by rewrite emb_bind -(HF_0 _ _) -(HF_0 _ _).
                - rewrite bind_assoc IHs.
                  apply bind_subst; try done.
                  move=> x1.
                    by rewrite emb_bind -(HF_0 _ _) -(HF_0 _ _). }
            * rewrite emb_bind //= Hxx0 /=.
              