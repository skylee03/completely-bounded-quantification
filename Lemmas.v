Require Export Fsub.Infrastructure.

(* wf_env *)

Lemma wf_env_tailing : forall F E,
  wf_env (F ++ E) ->
  wf_env E.
Proof with auto.
  intros.
  induction F...
  apply IHF.
  inversion H...
Qed.

(* uniq *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof with auto.
  intros; induction H...
Qed.

Hint Extern 1 (uniq ?E) => apply uniq_from_wf_env; auto : core.

(* type *)

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof with eauto.
  intros; induction H...
Qed.

Lemma type_from_wf_typ' : forall E T,
  wf_typ' E T -> type T.
Proof with auto.
  intros.
  induction H...
  apply type_all with (L := L)...
  apply type_from_wf_typ with (E := E)...
Qed.

Hint Extern 1 (type ?T) =>
  match goal with
  | H: wf_typ ?E T |- _ => apply (type_from_wf_typ E); auto
  | H: sub ?E T _ |- _ => apply (type_from_wf_typ' E); auto
  | H: sub ?E _ T |- _ => apply (type_from_wf_typ' E); auto
  end : core.

(* wf_typ <-> wf_typ' *)

Lemma wf_typ'_from_wf_typ : forall E T,
  wf_typ E T ->
  wf_typ' E T.
Proof with eauto.
  intros; induction H...
Qed.

Hint Resolve wf_typ'_from_wf_typ : core.

Hint Extern 1 (wf_typ' ?E ?T) =>
  match goal with
  | H: wf_typ E T |- _ => apply (proj2 (proj2 (wf_typ'_from_wf_typ E T H)))
  end : core.

(* wf_typ *)

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction H; intros; subst...
  pick fresh Y and apply wf_typ_all...
  rewrite_env ((Y ~ T1 ++ G) ++ F ++ E).
  apply H1...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_typ_from_binds : forall X U E,
  wf_env E ->
  binds X U E ->
  wf_typ E U.
Proof with auto.
  intros.
  induction H.
  - inversion H0.
  - analyze_binds H0; rewrite_env (X0 ~ T ++ E);
      apply wf_typ_weaken_head...
Qed.

Lemma wf_typ_subst_tt : forall F Q E Z P T,
  wf_typ (F ++ Z ~ Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tt Z P) F ++ E) ->
  wf_typ (map (subst_tt Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  - destruct (X == Z); subst...
    + rewrite_env (map (subst_tt Z P) F ++ E).
      apply wf_typ_weaken_head; auto.
    + analyze_binds H...
  - pick fresh Y and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tt Z P) (Y ~ T1 ++ F) ++ E).
    apply H0...
Qed.

Lemma wf_typ_from_wf_env : forall F X U E,
  wf_env (F ++ X ~ U ++ E) ->
  wf_typ E U.
Proof with simpl_env; auto.
  intros.
  induction F.
  - inversion H...
  - apply IHF; inversion H...
Qed.

Hint Extern 3 (wf_typ ?E ?T) =>
  match goal with
  | H: wf_typ' E (typ_all T _) |- _ => inversion H; auto
  end : core.

(* wf_typ' *)

Lemma wf_typ'_weakening : forall T E F G,
  wf_typ' (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ' (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction H; intros; subst...
  pick fresh Y and apply wf_typ'_all...
  - apply wf_typ_weakening...
  - rewrite_env ((Y ~ T1 ++ G) ++ F ++ E).
    apply H1...
Qed.

Lemma wf_typ'_weaken_head : forall T E F,
  wf_typ' E T ->
  uniq (F ++ E) ->
  wf_typ' (F ++ E) T.
Proof.
  intros.
  rewrite_env (nil ++ F++ E).
  auto using wf_typ'_weakening.
Qed.

Lemma wf_typ'_subst_tt : forall F Q E Z P T,
  wf_typ' (F ++ Z ~ Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tt Z P) F ++ E) ->
  wf_typ' (map (subst_tt Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  - destruct (X == Z); subst...
    + rewrite_env (map (subst_tt Z P) F ++ E).
      apply wf_typ'_weaken_head...
    + analyze_binds H...
  - pick fresh Y and apply wf_typ'_all...
    + eapply wf_typ_subst_tt...
    + rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tt Z P) (Y ~ T1 ++ F) ++ E).
      apply H1...
Qed.

Lemma wf_typ'_open : forall E U T1 T2,
  wf_env E ->
  wf_typ' E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_typ' E (open_tt T2 U).
Proof with eauto.
  intros.
  inversion H0; subst.
  pick fresh Y.
  rewrite (subst_tt_intro Y)...
  rewrite_env (map (subst_tt Y U) nil ++ E).
  eapply wf_typ'_subst_tt...
Qed.

Hint Extern 3 (wf_typ' ?E ?T) =>
  match goal with
  | H: wf_typ' E (typ_arrow T _) |- _ => inversion H; auto
  | H: wf_typ' E (typ_arrow _ T) |- _ => inversion H; auto
  | H: wf_typ' E (typ_all T _) |- _ => inversion H; auto
  | H: wf_typ' E (typ_all _ T) |- _ => inversion H; auto
  end : core.