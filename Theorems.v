Require Export Fsub.Lemmas.

(* Reflexivity *)

Theorem sub_reflexivity_aux : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T.
Proof with eauto.
  intros.
  induction H0...
  pick fresh Y and apply sub_all...
Qed.

Theorem sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ' E T ->
  sub E T T.
Proof with eauto.
  intros.
  induction H0...
  pick fresh Y and apply sub_all...
  apply sub_reflexivity_aux...
Qed.

(* Transitivity *)

Lemma sub_weakening : forall E F G S T,
  wf_env (G ++ E) ->
  wf_typ' (G ++ E) S -> wf_typ' (G ++ E) T ->
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T.
Proof with simpl_env; eauto using wf_typ_weakening, wf_typ'_weaken_head, uniq_from_wf_env.
  intros E F G S T HwfGE HwfGES HwfGET SsubT HwfGFE.
  remember (G ++ E) as H.
  generalize dependent G.
  induction SsubT; intros G Heq HwfGFE; subst...
  - apply sub_var with (U := U)...
    apply IHSsubT...
    apply wf_typ'_from_wf_typ.
    apply wf_typ_from_binds with (X := X)...
  - pick fresh Y and apply sub_all.
    + apply IHSsubT...
    + rewrite_env ((Y ~ T1 ++ G) ++ F ++ E).
      apply H0; try eapply wf_typ'_open...
Qed.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  wf_env (F ++ Z ~ Q ++ E) -> wf_env (F ++ Z ~ P ++ E) ->
  wf_typ' (F ++ Z ~ Q ++ E) S -> wf_typ' (F ++ Z ~ Q ++ E) T ->
  wf_typ' (F ++ Z ~ P ++ E) S -> wf_typ' (F ++ Z ~ P ++ E) T ->
  (forall E S T, wf_env E -> wf_typ' E Q -> wf_typ' E S -> wf_typ' E T -> sub E S Q -> sub E Q T -> sub E S T) ->
  sub (F ++ Z ~ Q ++ E) S T ->
  sub E P Q ->
  sub (F ++ Z ~ P ++ E) S T.
Proof with simpl_env; eauto using wf_typ'_weaken_head.
  intros Q F E Z P S T HwfEq HwfEp HwfEqS HwfEqT HwfEpS HwfEpT Htrans SsubT PsubQ.
  remember (F ++ Z ~ Q ++ E) as G.
  generalize dependent F.
  induction SsubT; auto; intros F Heq HwfEp HwfEpS HwfEpT; subst.
  (* NVar *)
  - destruct (X == Z); subst.
    + apply sub_var with (U := P)...
      apply Htrans...
      (* wf_typ' E Q *)
      * rewrite_env ((F ++ Z ~ P) ++ E).
        apply wf_typ'_weaken_head...
        apply wf_typ'_from_wf_typ.
        apply wf_typ_from_wf_env with (F := F) (X := Z)...
      (* wf_typ' E S *)
      * rewrite_env ((F ++ Z ~ P) ++ E).
        apply wf_typ'_weaken_head...
        apply wf_typ'_from_wf_typ.
        apply wf_typ_from_wf_env with (F := F) (X := Z)...
      (* sub E S Q *)
      * rewrite_env (nil ++ (F ++ Z ~ P) ++ E).
        apply sub_weakening...
        -- apply wf_env_tailing with (F := F ++ Z ~ P)...
        -- apply wf_typ'_from_wf_typ.
           apply wf_typ_from_wf_env with (F := F) (X := Z)...
        -- apply wf_typ'_from_wf_typ.
           apply wf_typ_from_wf_env with (F := F) (X := Z)...
      (* sub E Q T *)
      * analyze_binds_uniq H.
        apply IHSsubT...
        -- apply wf_typ'_from_wf_typ.
           apply wf_typ_from_binds with (X := Z)...
        -- rewrite_env ((F ++ Z ~ P) ++ E).
           apply wf_typ'_weaken_head...
           apply wf_typ'_from_wf_typ.
           apply wf_typ_from_wf_env with (F := F) (X := Z)...
    + apply sub_var with (U := U)...
      analyze_binds H; apply IHSsubT; eauto;
        apply wf_typ'_from_wf_typ;
        eapply wf_typ_from_binds...
  (* NAll *)
  - pick fresh Y and apply sub_all...
    rewrite_env ((Y ~ T1 ++ F) ++ Z ~ P ++ E).
    apply H0; try eapply wf_typ'_open...
Qed.

Theorem sub_transitivity :
  forall E, wf_env E ->
  forall Q, wf_typ' E Q ->
  forall S, wf_typ' E S -> sub E S Q ->
  forall T, wf_typ' E T -> sub E Q T ->
  sub E S T.
Proof with simpl_env; eauto using wf_typ'_weaken_head.
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
    inversion QsubT; subst...
  (* NVar *)
  - induction SsubQ; subst; try discriminate...
    intros T HwfT QsubT.
    apply sub_var with (U := U)...
    apply IHSsubQ...
    apply wf_typ'_from_wf_typ.
    apply wf_typ_from_binds with (X := X0)...
  (* NArrow *)
  - induction SsubQ; subst; try discriminate; intros T HwfT QsubT.
    + inversion QsubT; subst...
      apply sub_var with (U := U)...
      apply IHSsubQ...
      apply wf_typ'_from_wf_typ.
      apply wf_typ_from_binds with (X := X)...
    + inversion Heq; inversion QsubT; subst...
  (* NAll *)
  - induction SsubQ; subst; try discriminate; intros T HwfT QsubT.
    + inversion QsubT; subst...
      apply sub_var with (U := U)...
      apply IHSsubQ...
      apply wf_typ'_from_wf_typ.
      apply wf_typ_from_binds with (X := X)...
    + inversion Heq; inversion QsubT; subst...
      pick fresh Y and apply sub_all.
      * apply IHW with (Q' := T1)...
      * apply H0 with (X := Y) (Q' := open_tt T2 Y); eauto;
          try eapply wf_typ'_open...
        rewrite_env (nil ++ Y ~ T4 ++ E);
          apply sub_narrowing_aux with (Q := T1); eauto;
          try eapply wf_typ'_open...
Qed.