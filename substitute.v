(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/23 21:0:44> *)
(*
  substitute.v 
  - mathink : Author
 *)

(* Program libraries for [Program] *)
(* Map Skelton *)
Require Import
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.ssrbool
Ssreflect.eqtype.

Set Implicit Arguments.
Unset Strict Implicit.

Require Import MSL.lambda.

Delimit Scope map with map_scope.
Open Scope map_scope.
Unset Strict Implicit.
Import Prenex Implicits.

(* Notations for Maybe *)
Definition bind {X Y: Type}(f: X -> option Y)(m: option X): option Y :=
  if m is Some x then f x else None.
Notation emb := Some.
Notation "m >>= f" := (bind f m) (at level 65, left associativity).
Notation "m >> p" := (bind (fun _ => p) m) (at level 65, left associativity).
Notation "x <- m ; p" := (m >>= fun x => p) (at level 60, right associativity).
Notation "(: x , y :) <- m ; p" := (m >>= fun tup:_*_ => let: (x,y) := tup in p) (at level 60, right associativity).
Notation "'do' m" := m (at level 100, right associativity).
Notation "'mlet' x := m ; p" := (x <- emb m ; p) (at level 60, right associativity).

Section HoleFilling.
  Open Scope map_scope.
  Context {T: eqType}.

  Notation "[=]" := (box T).
  Let sexp := sexp T.
  Let lambda := lambda T.

  Arguments asL {T}(s H): rename.

  Check (fun s (b: is_true (wfb 0 s)) =>(elimT (wfbP 0 s) b)).
  Notation "[ 'L' s | b ]" :=
    (Lam (introT (isLbP s) (elimT (isLbP s) b)))
  (at level 0, format "[ 'L' s | b ]"): map_scope.
  Notation "'L.' s" := (asL s _)
  (at level 0, format "'L.' s"): map_scope.
  Notation "[ 'S' M ]" := (body M)
  (at level 0, format "[ 'S' M ]"): map_scope.
  Notation "'S.' M" := (body M)
  (at level 0, format "'S.' M"): map_scope.
  Definition asL (s: sexp): 0#s -> lambda :=
    fun H => Lam (introT (isLbP s) (wf_sexp_is_lambda H)).

  Fixpoint HF_aux (P: lambda)(m: map)(s: sexp){struct s}: option sexp :=
    match m, s with
      | 1, box => Some S.P
      | 0, box => Some [=]
      | 0, free x => Some (free x)
      | 1, free x => None
      | 0, M@N =>
       match HF_aux P 0 M, HF_aux P 0 N with
         | Some MmP, Some NnP  => Some (MmP@NnP)
         | _, _  => None end
      | minl m, M@N =>
       match HF_aux P m M, HF_aux P 0 N with
         | Some MmP, Some NnP  => Some (MmP@NnP)
         | _, _  => None end
      | minr n, M@N =>
       match HF_aux P 0 M, HF_aux P n N with
         | Some MmP, Some NnP  => Some (MmP@NnP)
         | _, _  => None end
      | mcons m n, M@N =>
       match HF_aux P m M, HF_aux P n N with
         | Some MmP, Some NnP  => Some (MmP@NnP)
         | _, _  => None end
      | m, n\N =>
        if wfb n N && orthb n m then
          if HF_aux P m N is Some NmP then Some (n\NmP) else None
        else None
      |  _,_  => None
    end.

  Functional Scheme HF_aux_ind := Induction for HF_aux Sort Prop.

  Lemma HF_0 M (P: lambda): 0#M -> emb M = HF_aux P 0 M.
  Proof.
    elim: M => [x||M1 IH1 M2 IH2|m M IH] Hwf //=.
    - rewrite -mapp_00_0 in Hwf; inversion Hwf; subst.
      rewrite H; rewrite -mapp_00_0 in H.
      by move: H H2 H3 => /eqP; rewrite mapp_injective;
        move=> /andP [/eqP -> /eqP ->] H1 H2;
          rewrite -(IH1 H1) -(IH2 H2). 2!emb_bind //=.
    - rewrite orthb_symm //= andbT.
      inversion Hwf; subst.
      by move: H3 => /wfbP ->; rewrite -(IH H1).
  Qed.
      
(*   Lemma orth_wf_HF_wf m1 m2 t t1 P: *)
(*     m1!m2 -> m1#t -> emb t1 = HF_aux P m1 t -> m2#t1. *)
(*   Proof. *)
(*     move: m2 t1. *)
(*     pattern (HF_aux P m1 t); apply HF_aux_ind => // m0 s0. *)
(*     - move=> _{m0} x _{s0} m s Hor Hwf [] -> //=. *)
(*       inversion Hor. *)
(*     elim/HF_aux_ind: P t /(HF_aux P m1 t). *)
(* Check HF_aux_ind. *)
(*     elim=> [m|n|m n m' n' Ho IH Ho' IH'] Hwf Heq /=. *)
(*     - elim: t m Hwf Heq => [x||s1 IHs1 s2 IHs2|m s1 IH] /=. *)
(*       + move=> m Hwfm; inversion Hwfm; subst. *)
(*         by move=> Heq; apply emb_mono in Heq; subst. *)
(*       + move=> m Hwfm; inversion Hwfm; subst. *)
(*         * by move=> Heq; apply emb_mono in Heq; subst. *)
(*         * move=> Heq; apply emb_mono in Heq; subst. *)
(*           apply lambda_is_wf. *)
(*       + move=> m Hwfm; inversion Hwfm; subst. *)
(*         destruct m0, n; simpl in *. *)
(*         * rewrite -(HF_0 _ H2) -(HF_0 _ H3) 2!emb_bind; *)
(*           by move=> Heq; apply emb_mono in Heq; move: Heq => ->. *)
(*         * rewrite -(HF_0 _ H2) emb_bind. *)

  Lemma HF_aux_wf s m P:
    m#s -> exists t: sexp, emb t = HF_aux P m s/\isLb t.
  Proof.
    elim=> [y|||m1 m2 s1 s2 H1 IH1 H2 IH2|m1 m2 t H1 IH1 H2 IH2 Horth] .
    - exists (free y); repeat split; constructor.
    - by exists [=]; repeat split; constructor.
    - by exists (S.P); repeat split; try constructor; destruct P.
    - move: IH1 IH2 => [t1 [Heq1 HL1]] [t2 [Heq2 HL2]].
      exists (t1@t2).
      destruct m1, m2; simpl in *;
      (rewrite -Heq1 -Heq2;
       repeat split; try done; last by apply /andP; split).
    - move: IH1 IH2 => [t1 [Heq1 HL1]] [t2 [Heq2 HL2]].
      exists (m2\t1); split.
      + simpl HF_aux.
        rewrite -Heq1 /=.
        case: (m2!P m1) => [Hor|Hnor]; rewrite ?andbT ?andbF.
        * case: (m2#P t) => [Hwf|Hnwf]; rewrite ?andbT.
          clear Heq1 H1 Horth Hor.
          destruct m1; try done.
          destruct m0; try done.
        * destruct m1; try done.
      + apply orth_symm in Horth; contradiction.
    - apply/isLbP; apply labs; first by apply/isLbP.
  (* have: m1!m2 -> m1#t -> emb t1 = HF_aux t m1 P -> m2#t1 *)
      Abort.
  Qed.

  Notation "[ M '_' m { P } ]" := (HF_ M m P).


  Program Fixpoint HoleFill (s: sexp)(m: map)(s: lambda): F lambda :=
    match M , m return F lambda with
      | Lam (free x) _, 0 => emb L.(free x)
      | Lam box _, 1 => emb P
      | Lam box _, 0 => emb L.[]
      | Lam (M@N) H, 0 =>
        do mlet m := 0;
           mlet n := 0;
           MmP <- HoleFill L.M m P;
           NnP <- HoleFill L.N n P;
           emb L.(S.MmP @ S.NnP)
      | _, _ => failure lambda
    end; try by constructor.
    Proof.
      - rewrite -mapp_00_0; apply wf_mapp_app; apply lambda_is_wf.
      - move: H => /isLbP.
        destruct term.
apply lambda_is_wf.

      | M@N, minl m =>
        do mlet n := 0;
           MmP <- HoleFill L.M m P;
           NnP <- HoleFill L.N n P;
           emb L.(S.MmP @ S.NnP)
      | M@N, minr n =>
        do mlet m := 0;
           MmP <- HoleFill M m P;
           NnP <- HoleFill N n P;
           emb (MmP@NnP)
       | M@N, mcons m n =>
         do MmP <- HoleFill M m P;
            NnP <- HoleFill N n P;
            emb (MmP@NnP)
       | n\N, m =>
         do NmP <- HoleFill N m P;
            emb (n\NmP)
      | _, _ => failure lambda
    end).
          | _,_ => failure sexP
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
              