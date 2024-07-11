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

Lemma wf_typ'_weakening : forall T E F G,
  wf_typ' (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ' (G ++ F ++ E) T.
Proof.
  intros.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction H; intros; subst; eauto.
  pick fresh Y excluding (L `union` dom E `union` dom F `union` dom G) and apply wf_typ'_all; auto.
  - apply wf_typ_weakening; auto.
  - rewrite_env ((Y ~ T1 ++ G) ++ F ++ E).
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

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_all T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  end.

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else T
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tt Z U T2)
  end.

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...
  - destruct (k === n)... simpl. destruct (X == X)...
  - destruct (a == X)... contradict Fr; fsetdec.
Qed.

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  - destruct (j === n)... destruct (i === n)...
Qed.

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  - unfold open_tt in *.
    pick fresh X.
    apply (open_tt_rec_type_aux T2 0 (typ_fvar X))...
Qed.

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  - destruct (k === n); subst...
  - destruct (a == X); subst... apply open_tt_rec_type...
Qed.

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma wf_typ_subst_tt : forall F Q E Z P T,
  wf_typ (F ++ Z ~ Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tt Z P) F ++ E) ->
  wf_typ (map (subst_tt Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto using type_from_wf_typ'.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  - destruct (X == Z); subst...
    + rewrite_env (nil ++ map (subst_tt Z P) F ++ E).
      apply wf_typ_weakening; auto.
    + analyze_binds H...
  - pick fresh Y excluding (L `union` singleton Z `union` dom E `union` dom F) and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tt Z P) (Y ~ T1 ++ F) ++ E).
    apply H0...
Qed.


Lemma wf_typ'_subst_tt : forall F Q E Z P T,
  wf_typ' (F ++ Z ~ Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tt Z P) F ++ E) ->
  wf_typ' (map (subst_tt Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto using type_from_wf_typ'.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  - destruct (X == Z); subst...
    + rewrite_env (nil ++ map (subst_tt Z P) F ++ E).
      apply wf_typ'_weakening; auto.
    + analyze_binds H...
  - pick fresh Y excluding (L `union` singleton Z `union` dom E `union` dom F) and apply wf_typ'_all...
    + eapply wf_typ_subst_tt; eauto.
    + rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tt Z P) (Y ~ T1 ++ F) ++ E).
      apply H1...
Qed.

Lemma wf_typ'_open : forall E U T1 T2,
  wf_env E ->
  wf_typ' E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_typ' E (open_tt T2 U).
Proof.
  intros.
  inversion H0; subst.
  pick fresh Y for (L `union` fv_tt T2).
  rewrite (subst_tt_intro Y); auto.
  rewrite_env (map (subst_tt Y U) nil ++ E).
  eapply wf_typ'_subst_tt; eauto.
  simpl_env.
  apply uniq_from_wf_env; auto.
Qed.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  (forall E S T, wf_env E -> wf_typ' E Q -> wf_typ' E S -> sub E S Q -> wf_typ' E T -> sub E Q T -> sub E S T) ->
  sub (F ++ Z ~ Q ++ E) S T ->
  sub E P Q ->
  sub (F ++ Z ~ P ++ E) S T.
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
      pick fresh Y excluding (L `union` dom E `union` fv_tt T4 `union` L0 `union` L1) and apply sub_all.
      * apply IHW with (Q' := T1); auto.
        -- inversion HwfQ; auto.
        -- inversion HwfT; auto.
        -- inversion HwfS; auto.
      * apply H0 with (X := Y) (Q' := open_tt T2 Y); auto.
        -- apply wf_env_sub; auto.
           inversion HwfT; auto.
        -- apply wf_typ'_open with (T1 := T1) (U := Y); auto.
           ++ inversion HwfT; auto.
           ++ rewrite_env (nil ++ Y ~ T4 ++ E).
              apply wf_typ'_weakening; auto.
              simpl_env.
              apply uniq_from_wf_env.
              apply wf_env_sub; auto.
              inversion HwfT; auto.
           ++ apply wf_typ_var with (U := T4); auto.
        -- apply wf_typ'_open with (T1 := S1) (U := Y); auto.
           ++ inversion HwfT; auto.
           ++ rewrite_env (nil ++ Y ~ T4 ++ E).
              apply wf_typ'_weakening; auto.
              simpl_env.
              apply uniq_from_wf_env.
              apply wf_env_sub; auto.
              inversion HwfT; auto.
           ++ apply wf_typ_var with (U := T4); auto.
        -- rewrite_env (nil ++ Y ~ T4 ++ E).
           apply sub_narrowing_aux with (Q := T1); eauto.
        -- apply wf_typ'_open with (T1 := T4) (U := Y); auto.
           ++ inversion HwfT; auto.
           ++ rewrite_env (nil ++ Y ~ T4 ++ E).
              apply wf_typ'_weakening; auto.
              simpl_env.
              apply uniq_from_wf_env.
              apply wf_env_sub; auto.
              inversion HwfT; auto.
           ++ apply wf_typ_var with (U := T4); auto.
Qed.
