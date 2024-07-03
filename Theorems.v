Require Export Fsub.Definitions.

Lemma wf_typ'_from_wf_typ : forall E T,
  wf_typ E T ->
  wf_typ' E T.
Proof.
  intros.
  induction H; eauto.
Qed.

Hint Resolve wf_typ'_from_wf_typ : core.

Hint Extern 1 (wf_typ' ?E ?T) =>
  match goal with
  | H: wf_typ E T |- _ => apply (proj2 (proj2 (wf_typ'_from_wf_typ E T H)))
  end : core.

Lemma wf_typ_from_wf_typ' : forall E (X : atom),
  wf_env E ->
  wf_typ' E X ->
  wf_typ E X.
Proof.
  intros.
  inversion H0; subst; eauto.
Qed.

Hint Resolve wf_typ_from_wf_typ' : core.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: wf_typ' E T |- _ => apply (proj2 (proj2 (wf_typ_from_wf_typ' E T H)))
  end : core.

(* Reflexivity *)

Theorem sub_reflexivity_aux : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T.
Proof.
  intros.
  induction H0; eauto.
  pick fresh Y excluding (L `union` dom E) and apply sub_all; auto.
Qed.

Theorem sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ' E T ->
  sub E T T.
Proof.
  intros.
  induction H0; eauto.
  pick fresh Y excluding (L `union` dom E) and apply sub_all; auto.
  apply sub_reflexivity_aux; auto.
Qed.

(* Transitivity *)

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof.
  intros.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction H; intros; subst; eauto.
  pick fresh Y excluding (L `union` dom E `union` dom F `union` dom G) and apply wf_typ_all; auto.
  rewrite_env ((Y ~ T1 ++ G) ++ F ++ E).
  apply H1; auto.
  simpl_env.
  auto.
Qed.

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

Lemma wf_typ_from_binds_typ : forall X U E,
  wf_env E ->
  binds X U E ->
  wf_typ E U.
Proof.
  intros.
  induction H.
  - inversion H0.
  - analyze_binds H0; rewrite_env (nil ++ X0 ~ T ++ E);
      apply wf_typ_weakening; auto;
      simpl_env;
      apply uniq_from_wf_env; auto.
Qed.

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof.
  intros.
  induction H; eauto.
Qed.

Lemma type_from_wf_typ' : forall E T,
  wf_typ' E T -> type T.
Proof.
  intros.
  induction H; auto.
  apply type_all with (L := L); auto.
  apply type_from_wf_typ with (E := E); auto.
Qed.

Lemma wf_typ'_open : forall E U T1 T2,
  uniq E ->
  wf_typ' E (typ_all T1 T2) ->
  wf_typ' E U ->
  wf_typ' E (open_tt T2 U).
Admitted.

Theorem sub_transitivity :
  forall E, wf_env E ->
  forall Q, wf_typ' E Q ->
  forall S, wf_typ' E S -> sub E S Q ->
  forall T, wf_typ' E T -> sub E Q T ->
  sub E S T.
Proof.
  intros E HwfE Q HwfQ.
  assert (W : type Q).
  {
    apply type_from_wf_typ' with (E := E).
    exact HwfQ.
  }
  generalize dependent E.
  remember Q as Q' in |- *.
  generalize dependent Q'.
  induction W; intros Q' Heq E HwfE HwfQ S HwfS SsubQ.
  (* NTop *)
  - subst; intros T HwfT QsubT.
    inversion QsubT; subst; auto.
  (* NVar *)
  - induction SsubQ; subst; try discriminate; auto.
    intros T HwfT QsubT.
    apply sub_var with (U := U); auto.
    apply IHSsubQ; auto.
    apply wf_typ'_from_wf_typ.
    apply wf_typ_from_binds_typ with (X := X0); auto.
  (* NArrow *)
  - induction SsubQ; subst; try discriminate; intros T HwfT QsubT.
    + inversion QsubT; subst; auto.
      apply sub_var with (U := U); auto.
      apply IHSsubQ; auto.
      apply wf_typ'_from_wf_typ.
      apply wf_typ_from_binds_typ with (X := X); auto.
    + inversion Heq; inversion QsubT; subst; auto.
      apply sub_arrow; auto.
      * apply IHW1 with (Q' := T1); auto.
        -- inversion HwfQ; auto.
        -- inversion HwfT; auto.
        -- inversion HwfS; auto.
      * apply IHW2 with (Q' := T2); auto.
        -- inversion HwfQ; auto.
        -- inversion HwfS; auto.
        -- inversion HwfT; auto.
  (* NAll *)
  - induction SsubQ; subst; try discriminate; intros T HwfT QsubT.
    + inversion QsubT; subst; auto.
      apply sub_var with (U := U); auto.
      apply IHSsubQ; auto.
      apply wf_typ'_from_wf_typ.
      apply wf_typ_from_binds_typ with (X := X); auto.
    + inversion Heq; inversion QsubT; subst; auto.
      pick fresh Y excluding (L `union` dom E) and apply sub_all.
      * apply IHW with (Q' := T1); auto.
        -- inversion HwfQ; auto.
        -- inversion HwfT; auto.
        -- inversion HwfS; auto.
      * apply H0 with (X := Y) (Q' := open_tt T2 Y); auto.
        -- apply wf_env_sub; auto.
           inversion HwfT; auto.
        -- apply wf_typ'_open with (T1 := T1).
           ++ apply uniq_from_wf_env; auto.
              apply wf_env_sub; auto.
              inversion HwfT; auto.
           ++ apply wf_typ'_all with (L := dom (Y ~ T4 ++ E)).
              ** rewrite_env (nil ++ Y ~ T4 ++ E).
                 apply wf_typ_weakening; simpl_env.
                 --- inversion HwfQ; auto.
                 --- apply uniq_from_wf_env.
                     apply wf_env_sub; auto.
                     inversion HwfT; auto.
              ** admit.
           ++ apply wf_typ'_var with (U := T4); auto.
        -- apply wf_typ'_open with (T1 := S1).
           ++ apply uniq_from_wf_env; auto.
              apply wf_env_sub; auto.
              inversion HwfT; auto.
           ++ apply wf_typ'_all with (L := dom (Y ~ T4 ++ E)).
              ** rewrite_env (nil ++ Y ~ T4 ++ E).
                 apply wf_typ_weakening; simpl_env.
                 --- inversion HwfS; auto.
                 --- apply uniq_from_wf_env.
                     apply wf_env_sub; auto.
                     inversion HwfT; auto.
              ** intros. admit.
           ++ apply wf_typ'_var with (U := T4); auto.
        -- admit.
        -- apply wf_typ'_open with (T1 := T4).
           ++ apply uniq_from_wf_env; auto.
              apply wf_env_sub; auto.
              inversion HwfT; auto.
           ++ apply wf_typ'_all with (L := dom (Y ~ T4 ++ E)).
              ** rewrite_env (nil ++ Y ~ T4 ++ E).
                 apply wf_typ_weakening; simpl_env.
                 --- inversion HwfT; auto.
                 --- apply uniq_from_wf_env.
                     apply wf_env_sub; auto.
                     inversion HwfT; auto.
              ** intros. admit.
           ++ apply wf_typ'_var with (U := T4); auto.
        -- admit.
Admitted.
