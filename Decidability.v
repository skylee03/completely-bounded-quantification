Require Export Fsub.Theorems.
Require Import Lia.
Require Import Coq.Program.Equality.

Definition aenv := list (atom * nat).
Definition nenv := list (nat * nat).

Fixpoint find (n : nat) (E : nenv) :=
  match E with
  | (k, v) :: E' => if n == k then Some v else find n E'
  | nil => None
  end.

Fixpoint findX (x : atom) (E : aenv) :=
  match E with
  | (k, v) :: E' => if x == k then Some v else findX x E'
  | nil => None
  end.

Fixpoint size (E : aenv) (F : nenv) (n : nat) (T : typ) {struct T} : nat :=
  match T with
  | typ_top => 1
  | typ_bvar J => match find (n - J) F with
                  | Some n => n
                  | None => 1
                  end
  | typ_fvar X => match findX X E with
                  | Some n => n
                  | None => 1
                  end
  | typ_arrow T1 T2 => size E F n T1 + size E F n T2
  | typ_all T1 T2 => let s1 := size E F n T1 in s1 + size E (S n ~ s1 ++ F) (S n) T2
  end.

Fixpoint depth (E : aenv) (F : nenv) (n : nat) (T : typ) {struct T} : nat :=
  match T with
  | typ_top => 0
  | typ_bvar J => match find (n - J) F with
                  | Some n => n
                  | None => 0
                  end
  | typ_fvar X => match findX X E with
                  | Some n => n
                  | None => 0
                  end
  | typ_arrow T1 T2 => (depth E F n T1) + (depth E F n T2)
  | typ_all T1 T2 => let d1 := depth E F n T1 in d1 + (depth E (S n ~ S d1 ++ F) (S n) T2)
  end.

Fixpoint mk_aenv (E : env) : aenv :=
  match E with
  | nil => nil
  | (X, U)::E' => let G := mk_aenv E' in
                  (X, size G nil 0 U) :: G
  end.

Fixpoint mk_aenv_depth (E : env) : aenv :=
  match E with
  | nil => nil
  | (X, U)::E' => let G := mk_aenv_depth E' in
                  (X, S (depth G nil 0 U)) :: G
  end.

Definition complexity (E : env) (S T : typ) : nat :=
  let E' := mk_aenv E in
  size E' nil 0 S + size E' nil 0 T.

Definition complexity_depth (E : env) (S T : typ) : nat :=
  let E' := mk_aenv_depth E in
  depth E' nil 0 S + depth E' nil 0 T.


Lemma find_in : forall (E1 E2 : nenv) k,
  find 0 (E1 ++ E2) = None ->
  find 0 (E1 ++ 0 ~ k ++ E2) = Some k.
Proof with auto.
  induction E1; intros...
  destruct a.
  destruct n; simpl in *...
  inversion H.
Qed.

Lemma find_notin : forall (E1 E2 : nenv) k (n : nat),
  find (S n) (E1 ++ 0 ~ k ++ E2) = find (S n) (E1 ++ E2).
Proof with auto.
  induction E1; intros...
  destruct a.
  simpl.
  destruct (S n == n0)...
  simpl_env...
Qed.

Inductive wfc : typ -> nat -> Prop :=
  | wfc_top : forall k,
      wfc typ_top k
  | wfc_fvar : forall X k,
      wfc (typ_fvar X) k
  | wfc_bvar : forall b k,
      b <= k -> (* <= k bvar *)
      wfc (typ_bvar b) k
  | wfc_arrow : forall T1 T2 k,
      wfc T1 k ->
      wfc T2 k ->
      wfc (typ_arrow T1 T2) k
  | wfc_all : forall T1 T2 k,
      wfc T1 k ->
      wfc T2 (S k) ->
      wfc (typ_all T1 T2) k
.

Inductive wfd : typ -> nat -> Prop :=
  | wfd_top : forall k,
      wfd typ_top k
  | wfd_fvar : forall X k,
      wfd (typ_fvar X) k
  | wfd_bvar : forall b k,
      b < k -> (* < k bvar *)
      wfd (typ_bvar b) k
  | wfd_arrow : forall T1 T2 k,
      wfd T1 k ->
      wfd T2 k ->
      wfd (typ_arrow T1 T2) k
  | wfd_all : forall T1 T2 k,
      wfd T1 k ->
      wfd T2 (S k) ->
      wfd (typ_all T1 T2) k
.

Inductive wfe : nenv -> nat -> Prop :=
  | wfe_empty :
      wfe nil 0
  | wfe_sub : forall b E k,
      wfe E k ->
      find (S k) E = None ->
      wfe (S k ~ b ++ E) (S k)
.

Hint Constructors wfc wfd wfe : core.

Fixpoint minusk (E : nenv) (k : nat) : nenv :=
  match E with
  | nil => nil
  | (a, b) :: E' => (a - k, b) :: (minusk E' k)
  end.

Fixpoint maxfst (E : nenv) : nat :=
  match E with
  | nil => 0
  | (a, _) :: E' => max a (maxfst E')
  end.

Lemma wfe_maxfst : forall E k,
  wfe E k ->
  maxfst E <= k.
Proof with auto.
  induction 1...
  simpl...
  destruct (maxfst E)...
  lia.
Qed.

Lemma maxfst_find_none : forall E k,
  maxfst E <= k ->
  find (S k) E = None.
Proof with auto.
  induction E; intros...
  destruct a.
  simpl in *.
  destruct (S k == n); try lia.
  apply IHE.
  lia.
Qed.

Lemma wfe_find_none : forall k E,
  wfe E k ->
  find (S k) E = None.
Proof with auto.
  intros.
  apply maxfst_find_none.
  apply wfe_maxfst...
Qed.

Lemma wfe_S_n : forall E n k,
  wfe E n ->
  wfe (S n ~ k ++ E) (S n).
Proof with auto.
  induction E; intros...
  constructor...
  apply wfe_find_none...
Qed.

Fixpoint addone (E : nenv) : nenv :=
  match E with
  | nil => nil
  | (a, b) :: E' => (S a, b) :: (addone E')
  end.

Lemma find_add_eq : forall E k,
  find k E = find (S k) (addone E).
Proof with auto.
  induction E; intros...
  destruct a.
  simpl.
  destruct (k == n); destruct (S k == S n)...
  - destruct n1...
  - destruct n1...
Qed.

Lemma find_add : forall E k b,
  k >= b ->
  find (k - b) E = find (S k - b) (addone E).
Proof with auto using find_add_eq.
  induction E; intros...
  rewrite Nat.sub_succ_l...
Qed.

Lemma size_add : forall E n A G,
  wfc A n ->
  size G E n A = size G (addone E) (S n) A.
Proof with auto.
  intros.
  generalize dependent E.
  induction H; intros; simpl...
  - rewrite find_add...
  - f_equal...
    rewrite <- IHwfc1.
    replace ((S (S k), size G E k T1) :: addone E) with (addone ((S k, size G E k T1) :: E))...
Qed.

Fixpoint close_tt_rec (K : nat) (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then typ_bvar K else typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (close_tt_rec K Z T1) (close_tt_rec K Z T2)
  | typ_all T1 T2 => typ_all (close_tt_rec K Z T1) (close_tt_rec (S K) Z T2)
  end.

Definition close_tt T X := close_tt_rec 0 X T.

Lemma close_wfc : forall A X,
  wfc A 0 ->
  wfc (close_tt A X) 0.
Proof with auto.
  unfold close_tt.
  intro.
  generalize 0.
  induction A; intros; simpl...
  - destruct (a == X)...
  - inversion H; subst...
  - inversion H; subst...
Qed.

Lemma wfc_add_one : forall A k,
  wfc A k -> wfc A (S k).
Proof with auto.
  intros.
  induction H...
Qed.

Lemma close_wfd : forall A X,
  wfd A 0 ->
  wfd (close_tt A X) 1.
Proof with auto.
  unfold close_tt.
  intro.
  generalize 0.
  induction A; intros; simpl...
  - inversion H; subst...
  - destruct (a == X)...
  - inversion H; subst...
  - inversion H; subst...
Qed.

Lemma close_open_reverse_rec : forall T X,
  (X `notin` fv_tt T) ->
  forall k,
  T = close_tt_rec k X (open_tt_rec k (typ_fvar X) T).
Proof with auto.
  induction T; intros; simpl in *...
  - destruct (k == n); simpl...
    destruct (X == X); subst...
    destruct n0...
  - destruct (a == X); simpl...
    apply notin_singleton_1 in H.
    destruct H...
  - f_equal...
  - f_equal...
Qed.

Lemma close_open_reverse : forall T X,
  (X `notin` fv_tt T) ->
  T = close_tt (open_tt T X) X.
Proof with auto.
  intros.
  apply close_open_reverse_rec...
Qed.

Lemma close_type_wfc : forall A,
  type A ->
  wfc A 0.
Proof with auto.
  intros.
  induction H; intros...
  constructor...
  apply wfc_add_one.
  pick_fresh X.
  eapply close_wfc in H1...
  rewrite <- close_open_reverse in H1...
Qed.

Lemma close_type_wfd : forall A,
  type A ->
  wfd A 0.
Proof with auto.
  intros.
  induction H; intros...
  constructor...
  pick_fresh X.
  eapply close_wfd in H1...
  rewrite <- close_open_reverse in H1...
Qed.

Lemma type_open_tt_wfc : forall T X,
  X `notin` fv_tt T ->
  type (open_tt T X) ->
  wfc T 0.
Proof with auto.
  intros.
  apply close_type_wfc in H0.
  apply close_wfc with (X:=X) in H0...
  rewrite <- close_open_reverse in H0... 
Qed.

Lemma wfe_find_in : forall E k,
    wfe E k ->
    forall q n, 0 < n -> 
    q < n ->
    find n E = find (n - q) (minusk E q).
Proof with auto.
  intros E k H.
  induction H; intros...
  remember (n - q).
  assert (minusk (S k ~ b ++ E) q = (S k - q) ~ b ++ (minusk E q)) as W by (simpl;auto).
  rewrite W.
  remember (S k - q).
  simpl...
  destruct (n == S k); destruct (n0 == n1); subst; try lia...
Qed.

Lemma size_wfd_drop : forall E n b q G, 
    wfe E n -> q < n - b ->
    size G E n b = size G (minusk E q) (n - q) b.
Proof with auto.
  induction E; intros...
  inversion H; subst.
  replace (minusk ((S k, b0) :: E) q) with ((S k - q, b0) :: (minusk E q)) by auto.
  remember (S k - q).
  remember (S k).
  simpl.
  destruct (n - b == n); destruct (n0 - b == n0); try lia; subst...
  replace (S k - q - b) with (S k - b - q) by lia.
  rewrite <- wfe_find_in with (k := k); try lia...
Qed.

Lemma size_wfd_wfe : forall A k n E q G,
  wfd A k -> wfe E n -> k <= n - q -> q <= n ->
  size G E n A = size G (minusk E q) (n - q) A.
Proof with auto using wfe_S_n.
  intros.
  generalize dependent E.
  generalize dependent n.
  generalize dependent q.
  induction H; intros; try solve [simpl in *; auto]...
  - apply size_wfd_drop...
    lia.
  - simpl.
    f_equal.
    rewrite <- IHwfd1...
    rewrite <- IHwfd1...
    replace (S (n - q)) with (S n - q) by lia.
    replace (((S n - q, size G E n T1) :: minusk E q)) with (minusk ((S n, size G E n T1)::E) q) by auto.
    rewrite <- IHwfd2; try lia...
    apply wfe_sub...
    apply wfe_find_none...
Qed.

Lemma find_former : forall E1 E2 k,
  (exists p, In (k, p) E1) ->
  find k E1 = find k (E1 ++ E2).
Proof with auto.
  induction E1; intros.
  - inversion H.
    inversion H0.
  - destruct a.
    destruct H.
    destruct (k == n); subst.
    + simpl.
      destruct (n == n)...
      destruct n1...
    + simpl.
      destruct (k == n)...
      apply in_inv in H.
      destruct H.
      inversion H; subst.
      destruct n1...
      apply IHE1.
      exists x...
Qed.

Lemma minus_in_for_size : forall E (n k : nat),
  (forall q, exists p, q < n -> In (n - q, p) E) ->
  (forall q, exists p, q < S n -> In (S n - q, p) ((S n, k) :: E)).
Proof with auto.
  intros.
  destruct n.
  - destruct q.
    + exists k.
      intros.
      simpl...
    + exists 0.
      intros.
      lia.
  - destruct q.
    exists k.
    intros; simpl...
    destruct H with (q := q).
    exists x.
    intros.
    replace (S (S n) - S q) with (S n - q) by lia.
    apply in_cons.
    apply H0.
    lia.
Qed.    

Lemma size_close_env_aux : forall G A k,
  wfd A k -> forall E1 E2,
  (forall q, exists p, q < k -> In (k - q, p) E1) -> 
  size G (E1 ++ E2) k A = size G E1 k A.
Proof with eauto.
  intros G A k H.
  induction H; intros; try solve [simpl in *; auto]...
  - simpl.
    assert (find (k - b) E1 = find (k - b) (E1 ++ E2)).
    {
      rewrite find_former with (E2 := E2)...
      destruct H0 with (q := b)...
    }
    rewrite H1...
  - simpl.
    f_equal...
    rewrite IHwfd1...
    remember (size G E1 k T1).
    rewrite_env (((S k, n) :: E1) ++ E2).
    rewrite IHwfd2...
    intros.
    apply minus_in_for_size...
Qed.

Lemma size_close_env: forall A E G,
  type A-> 
  size G E 0 A = size G nil 0 A.
Proof with eauto.
  intros.
  rewrite_env (nil ++ E).
  rewrite_env (nil ++ nil : nenv).
  apply size_close_env_aux...
  - apply close_type_wfd...
  - intros.
    exists 0.
    intros.
    lia.
Qed.

Lemma size_local_close: forall B E n G,
  type B -> wfe E n ->
  size G E n B = size G nil 0 B.
Proof with auto.
  intros.
  rewrite size_wfd_wfe with (k := 0) (q := n)...
  - replace (n - n) with 0 by lia.
    rewrite size_close_env...
  - apply close_type_wfd...
  - lia.
Qed.

Lemma size_close : forall B a G E n,
    type B ->
    wfe E n ->
    size G E n B = size G (S n ~ a ++ E) (S n) B.
Proof with auto.
  intros.
  rewrite size_local_close...
  remember (size G nil 0 B).
  rewrite size_local_close...
  apply wfe_S_n...
Qed.

Lemma findX_extend : forall Q G E X T n,
  wfd Q n ->
  X `notin` fv_tt Q ->
  wfe E n ->
  size (mk_aenv G) E n Q = 
  size (mk_aenv (X ~ T ++ G)) E n Q.
Proof with auto.
  intros.
  generalize dependent E.
  induction H; try solve [simpl in *; intros; auto]; intros; simpl in *...
  - destruct (X0 == X); subst...
    f_equal.
    exfalso.
    apply H0.
    simpl...
  - f_equal.
    rewrite <- IHwfd1...
    rewrite <- IHwfd1...
    rewrite <- IHwfd2...
    constructor...
    apply wfe_find_none...
Qed.

Lemma findX_extend_depth : forall Q G E X T n,
  wfd Q n ->
  X `notin` fv_tt Q ->
  wfe E n ->
  depth (mk_aenv_depth G) E n Q = 
  depth (mk_aenv_depth (X ~ T ++ G)) E n Q.
Proof with auto.
  intros.
  generalize dependent E.
  induction H; try solve [simpl in *; intros; auto]; intros; simpl in *...
  - destruct (X0 == X); subst...
    f_equal.
    exfalso.
    apply H0.
    simpl...
  - f_equal.
    rewrite <- IHwfd1...
    rewrite <- IHwfd1...
    rewrite <- IHwfd2...
    constructor...
    apply wfe_find_none...
Qed.

Lemma findX_extend_spec : forall Q E X T,
  type Q ->
  X `notin` fv_tt Q ->
  size (mk_aenv E) nil 0 Q = 
  size (mk_aenv (X ~ T ++ E)) nil 0 Q.
Proof with auto.
  intros.
  apply findX_extend...
  apply close_type_wfd...
Qed.

Lemma findX_extend_spec_depth : forall Q E X T,
  type Q ->
  X `notin` fv_tt Q ->
  depth (mk_aenv_depth E) nil 0 Q = 
  depth (mk_aenv_depth (X ~ T ++ E)) nil 0 Q.
Proof with auto.
  intros.
  apply findX_extend_depth...
  apply close_type_wfd...
Qed.

Fixpoint fv_env (E:env) : atoms :=
  match E with
  | nil => {}
  | (x, y)::E' => (fv_tt y) `union` (fv_env E')
  end.

Lemma fv_open_tt_notin_inv: forall T S (X:atom),
  X `notin` fv_tt T ->
  fv_tt (open_tt T X) [<=] add X S ->
  fv_tt T [<=] S.
Proof with auto .
  intro T.
  unfold open_tt in *.
  generalize 0.
  induction T; intros; try fsetdec; simpl in *.
  - apply KeySetProperties.union_subset_3.
    + apply IHT1 with (n := n) (X := X)...
      fsetdec.
    + apply IHT2 with (n := n) (X := X)...
      fsetdec.
  - apply KeySetProperties.union_subset_3.
    + apply IHT1 with (n := n) (X := X)...
      fsetdec.
    + apply IHT2 with (n := Datatypes.S n) (X := X)...
      fsetdec.
Qed.

Lemma wf_typ_imply_dom: forall E A,
  wf_typ E A ->
  fv_tt A [<=] dom E.
Proof with auto.
  intros.
  induction H.
  - unfold "[<=]".
    intros.
    apply KeySetFacts.singleton_iff in H0.
    subst.
    apply binds_In with (a := U)...
  - apply KeySetProperties.union_subset_3...
  - simpl.
    pick fresh X.
    apply KeySetProperties.union_subset_3...
    apply fv_open_tt_notin_inv with (X := X)...
Qed.

Lemma wf_typ'_imply_dom: forall E A,
  wf_typ' E A ->
  fv_tt A [<=] dom E.
Proof with auto.
  intros.
  induction H.
  - fsetdec.
  - unfold "[<=]".
    intros.
    apply KeySetFacts.singleton_iff in H0.
    subst.
    apply binds_In with (a := U)...
  - apply KeySetProperties.union_subset_3...
  - simpl.
    pick fresh X.
    apply KeySetProperties.union_subset_3.
    + apply wf_typ_imply_dom...
    + apply fv_open_tt_notin_inv with (X := X)...
Qed.

Lemma fv_env_ls_dom: forall E,
  wf_env E ->
  fv_env E [<=] dom E.
Proof with auto.
  induction E; intros; simpl in *...
  - fsetdec.
  - dependent destruction H.
    apply KeySetProperties.subset_add_2...
    apply AtomSetProperties.union_subset_3...
    apply wf_typ'_imply_dom...
Qed.

Lemma notin_from_wf_env: forall E1 X T E2,
  wf_env (E1 ++ X ~ T ++ E2) ->
  X `notin` fv_tt T `union` dom E2 `union` dom E1 `union` fv_env E2.
Proof with auto.
  induction E1; intros; dependent destruction H; subst...
  - assert (wf_typ' E2 T)...
    apply fv_env_ls_dom in H.
    apply wf_typ'_imply_dom in H2.
    fsetdec.
  - apply IHE1 in H...
Qed.

Lemma notin_fv_tt_fv_env: forall E T X Y,
  binds Y T E ->
  X `notin` fv_env E ->
  X `notin` fv_tt T.
Proof with auto.
  induction E; intros...
  simpl in *.
  destruct a.
  analyze_binds H.
  apply IHE with (Y := Y)...
Qed.

Lemma findX_sem : forall E X Q,
  wf_env E ->
  binds X Q E ->
  findX X (mk_aenv E) = Some (size (mk_aenv E) nil 0 Q).
Proof with auto.
  induction E; intros.
  - inversion H0.
  - destruct H0.
    + destruct a.
      inversion H0; subst.
      simpl.
      rewrite eq_dec_refl.
      f_equal.
      rewrite_alist (mk_aenv (X ~ Q ++ E)).
      apply findX_extend_spec...
      * inversion H...
      * rewrite_env (nil ++ X ~ Q ++ E) in H.
        apply notin_from_wf_env in H...
    + destruct a.
      simpl.
      destruct (X == a); subst.
      * inversion H; subst.
        exfalso.
        apply H6.
        apply in_split in H0 as [E1 [E2 H1]].
        rewrite H1.
        rewrite dom_app.
        simpl...
      * rewrite IHE with (Q := Q); try inversion H; subst...
        rewrite_alist (mk_aenv (a ~ t ++ E)).
        f_equal.
        apply findX_extend_spec...
        -- inversion H; subst.
           apply in_split in H0 as [? [? ?]]; subst.
           apply type_from_wf_typ with (E := x ++ (X, Q) :: x0).
           apply wf_typ_from_binds with (X := X)...
        -- rewrite_env (nil ++ a ~ t ++ E) in H.
           apply notin_from_wf_env in H.
           assert (binds X Q E) by auto.
           apply notin_fv_tt_fv_env with (E := E) (Y := X)...
Qed.

Lemma findX_sem_depth : forall E X Q,
  wf_env E ->
  binds X Q E ->
  findX X (mk_aenv_depth E) = Some (S (depth (mk_aenv_depth E) nil 0 Q)).
Proof with auto.
  induction E; intros.
  - inversion H0.
  - destruct H0.
    + destruct a.
      inversion H0; subst.
      simpl.
      rewrite eq_dec_refl.
      f_equal.
      rewrite_alist (mk_aenv_depth (X ~ Q ++ E)).
      f_equal.
      apply findX_extend_spec_depth...
      * inversion H...
      * rewrite_env (nil ++ X ~ Q ++ E) in H.
        apply notin_from_wf_env in H...
    + destruct a.
      simpl.
      destruct (X == a); subst.
      * inversion H; subst.
        exfalso.
        apply H6.
        apply in_split in H0 as [E1 [E2 H1]].
        rewrite H1.
        rewrite dom_app.
        simpl...
      * rewrite IHE with (Q := Q); try inversion H; subst...
        rewrite_alist (mk_aenv_depth (a ~ t ++ E)).
        f_equal.
        f_equal.
        apply findX_extend_spec_depth...
        -- inversion H; subst.
           apply in_split in H0 as [? [? ?]]; subst.
           apply type_from_wf_typ with (E := x ++ (X, Q) :: x0).
           apply wf_typ_from_binds with (X := X)...
        -- rewrite_env (nil ++ a ~ t ++ E) in H.
           apply notin_from_wf_env in H.
           assert (binds X Q E) by auto.
           apply notin_fv_tt_fv_env with (E := E) (Y := X)...
Qed.

Ltac solve_right_dec := right; intro v; inversion v; auto.

Lemma EqDec_eq : forall (A B: typ),
  {A = B} + {A <> B}.
Proof with auto.
  intros.
  decide equality.
  decide equality.
Qed.

Lemma size_find_in: forall (E1 E2 : nenv) k,
  find 0 (E1 ++ E2) = None ->
  find 0 (E1 ++ (0, k) :: E2) = Some k.
Proof with auto.
  induction E1...
  intros.
  destruct a.
  simpl in *.
  destruct n; simpl in *...
  inversion H.
Qed.

Lemma neq_minus: forall k n,
  n <= k ->
  n <> k ->
  exists q, k - n = S q.
Proof with auto.
  induction k;intros...
  inversion H...
  destruct H0...
  induction n...
  exists k...
  destruct IHk with (n:=n)...
  lia.
  exists x...
Qed.

Lemma size_find_notin: forall (E1 E2 : nenv) k (n : nat),
  find (S n) (E1 ++ (0, k) :: E2) = find (S n) (E1++E2).
Proof with auto.
  induction E1;intros...
  - destruct a...
    simpl...
    destruct (S n == n0)...
Qed.

Definition zero := 0.

Lemma size_fvar: forall A G E1 E2 X B,
  wfc A 0 ->
  X `notin` fv_tt A ->
  wf_env (X ~ B ++ G) ->
  find zero (E1 ++ E2) = None ->
  type B ->
  wfe (E1 ++ E2) 0 ->
  size (mk_aenv (X ~ B ++ G)) (E1 ++ E2) 0 (open_tt A X) =
  size (mk_aenv G) (E1 ++ [(zero, size (mk_aenv G) (E1 ++ E2) 0 B)] ++ E2) 0 A.
Proof with auto.
  intro A.
  unfold open_tt.
  generalize 0.
  unfold zero.
  induction A; intros...
  - destruct (n0 == n); subst.
    + assert (open_tt_rec n X n = X) as Q.
      {
        simpl.
        destruct (n == n)...
        destruct n0...
      }
      rewrite Q.
      simpl.
      destruct (X == X).
      * rewrite Nat.sub_diag.
        rewrite size_find_in...
        rewrite <- size_local_close with (E := E1 ++ E2) (n := n)...
      * exfalso...
    + assert (open_tt_rec n0 X n = n) as Q.
      {
        simpl.
        destruct (n0 == n)...
        destruct e.
        exfalso...
      }
      rewrite Q.
      simpl.
      dependent destruction H.
      apply neq_minus in H...
      destruct H.
      rewrite H.
      erewrite <- size_find_notin...
  - simpl.
    destruct (a == X)...
    subst X.
    exfalso.
    apply H0.
    simpl...
  - simpl in *.
    dependent destruction H.
    rewrite IHA1...
  - simpl in *.
    dependent destruction H.
    rewrite IHA1...
    f_equal.
    remember (size (mk_aenv G) (E1 ++ (0, size (mk_aenv G) (E1 ++ E2) k B) :: E2) k A1) as K.
    rewrite_env ((S k ~ K ++ E1) ++ E2).
    rewrite IHA2...
    + rewrite_env (S k ~ K ++ E1 ++ E2).
      rewrite <- size_close...
    + constructor...
      apply wfe_find_none...
Qed.

Lemma size_fvar_spec : forall G A X B,
  wfc A 0 ->
  X `notin` fv_tt A ->
  wf_env (X ~ B ++ G) ->
  type B ->
  size (mk_aenv (X ~ B ++ G)) nil 0 (open_tt A X) =
  size (mk_aenv G) (1 ~ size (mk_aenv G) nil 0 B) 1 A.
Proof with auto.
  intros.
  rewrite_env ((nil : nenv) ++ nil).
  rewrite size_fvar...
  simpl.
  rewrite size_add...
Qed.

Lemma depth_fvar: forall A G E1 E2 X B,
  wfc A 0 ->
  X `notin` fv_tt A ->
  wf_env (X ~ B ++ G) ->
  find zero (E1 ++ E2) = None ->
  type B ->
  wfe (E1 ++ E2) 0 ->
  depth (mk_aenv_depth (X ~ B ++ G)) (E1 ++ E2) 0 (open_tt A X) =
  depth (mk_aenv_depth G) (E1 ++ [(zero, depth (mk_aenv_depth G) (E1 ++ E2) 0 B)] ++ E2) 0 A.
Admitted.

Lemma depth_fvar_spec : forall G A X B,
  wfc A 0 ->
  X `notin` fv_tt A ->
  wf_env (X ~ B ++ G) ->
  type B ->
  depth (mk_aenv_depth (X ~ B ++ G)) nil 0 (open_tt A X) =
  depth (mk_aenv_depth G) (1 ~ S (depth (mk_aenv_depth G) nil 0 B)) 1 A.
Admitted.

Lemma binds_positive : forall E X U,
  wf_env E ->
  binds X U E ->
  0 < size (mk_aenv E) nil 0 U.
Admitted.

Lemma size_positive_aux : forall E T,
  wf_env E -> wf_typ E T ->
  0 < size (mk_aenv E) nil 0 T.
Proof with auto.
  intros.
  induction H0; simpl...
  + rewrite findX_sem with (Q := U)...
    apply binds_positive with (X := X)...
  + specialize (IHwf_typ1 H).
    specialize (IHwf_typ2 H).
    lia.
  + specialize (IHwf_typ H).
    lia.
Qed.

Lemma size_positive : forall E T,
  wf_env E -> wf_typ' E T ->
  0 < size (mk_aenv E) nil 0 T.
Proof with auto.
  intros.
  induction H0; simpl...
  + rewrite findX_sem with (Q := U)...
    apply binds_positive with (X := X)...
  + specialize (IHwf_typ'1 H).
    specialize (IHwf_typ'2 H).
    lia.
  + enough (0 < size (mk_aenv E) nil 0 T1) by lia.
    apply size_positive_aux...
Qed.

Lemma sub_replacing : forall E2 A B U X Y,
  sub (X ~ U ++ E2) (open_tt A X) (open_tt B X) ->
  X `notin` fv_tt A `union` fv_tt B `union` {{Y}} ->
  wf_env (Y ~ U ++ E2) ->
  sub (Y ~ U ++ E2) (open_tt A Y) (open_tt B Y).
Admitted.

Theorem theorem2 : forall E S T,
  wf_env E -> wf_typ E S -> wf_typ E T ->
  sub E T S ->
  size (mk_aenv E) nil 0 T = size (mk_aenv E) nil 0 S.
Proof with auto.
  intros.
  induction H2.
  (* NTop *)
  - inversion H0.
  (* NRefl *)
  - reflexivity.
  (* NVar *)
  - rewrite <- IHsub...
    + unfold size at 1.
      rewrite findX_sem with (Q := U)...
    + apply wf_typ_from_binds with (X := X)...
  (* NArrow *)
  - simpl.
    rewrite IHsub1...
    + rewrite IHsub2...
      * inversion H0...
      * inversion H1...
    + inversion H1...
    + inversion H0...
  (* NAll *)
  - simpl.
    rewrite <- IHsub...
    + f_equal.
      simpl_alist.
      pick fresh Y.
      repeat rewrite <- size_fvar_spec with (X := Y)...
      * apply H4...
        -- apply wf_env_sub...
           inversion H0...
        -- apply wf_typ_open with (T1 := T1).
           ++ apply wf_env_sub...
              inversion H0...
           ++ apply wf_typ_weaken_head...
           ++ apply wf_typ_var with (U := T1)...
        -- apply wf_typ_open with (T1 := S1).
           ++ apply wf_env_sub...
              inversion H0...
           ++ apply wf_typ_weaken_head...
           ++ apply wf_typ_var with (U := T1)...
      * inversion H0.
        pick fresh Z.
        apply type_open_tt_wfc with (X := Z)...
        apply type_from_wf_typ with (E := Z ~ T1 ++ E)...
      * apply wf_env_sub...
        inversion H0...
      * inversion H0...
      * inversion H1.
        pick fresh Z.
        apply type_open_tt_wfc with (X := Z)...
        apply type_from_wf_typ with (E := Z ~ S1 ++ E)...
      * apply wf_env_sub...
        inversion H0...
      * inversion H0...
    + inversion H1...
    + inversion H0...
Qed.

Lemma subtyping_dec : forall k E S T,
  wf_env E -> wf_typ' E S -> wf_typ' E T ->
  complexity E S T + complexity_depth E S T < k ->
  sub E S T \/ ~ sub E S T.
Proof with auto.
  unfold complexity.
  (* unfold complexity_depth. *)
  induction k; try lia.
  induction S.
  (* typ_top *)
  - induction T; try solve [solve_right_dec]...
  (* typ_bvar *)
  - induction T; try solve [solve_right_dec]...
  (* typ_fvar *)
  - intros.
    inversion H0; subst.
    unfold complexity_depth in H2.
    simpl in H2.
    rewrite findX_sem with (Q := U) in H2...
    rewrite findX_sem_depth with (Q := U) in H2...
    simpl in H2.
    rewrite <- plus_n_Sm in H2.
    rewrite <- Nat.succ_lt_mono in H2.
    assert (sub E U T \/ ~ sub E U T).
    {
      apply IHk...
      apply wf_typ'_from_wf_typ.
      apply wf_typ_from_binds with (X := a)...
    }
    destruct H3.
    + left.
      apply sub_var with (U := U)...
    + destruct (EqDec_eq a T); subst...
      solve_right_dec; subst...
      assert (U = U0).
      {
        apply binds_unique with (x := a) (E := E)...
      }
      subst.
      contradiction.
  (* typ_arrow *)
  - unfold complexity_depth in *.
    intros.
    induction T; intros; try solve [solve_right_dec]...
    simpl in H2.
    assert (0 < size (mk_aenv E) nil 0 S1) by auto using size_positive.
    assert (0 < size (mk_aenv E) nil 0 S2) by auto using size_positive.
    assert (0 < size (mk_aenv E) nil 0 T1) by auto using size_positive.
    assert (0 < size (mk_aenv E) nil 0 T2) by auto using size_positive.
    destruct IHk with (S := T1) (T := S1) (E := E); try solve [lia | solve_right_dec]...
    destruct IHk with (S := S2) (T := T2) (E := E); try solve [lia | solve_right_dec]...
  (* typ_all *)
  - intros.
    induction T; try solve [solve_right_dec]...
    simpl in H2.
    assert (type S1).
    {
      inversion H0...
    }
    assert (type T1).
    {
      inversion H1...
    }
    assert (wfc S2 0).
    {
      inversion H0; subst...
      pick fresh X.
      apply type_open_tt_wfc with (X := X)...
      apply type_from_wf_typ' with (E := X ~ S1 ++ E)...
    }
    assert (wfc T2 0).
    {
      inversion H1; subst...
      pick fresh X.
      apply type_open_tt_wfc with (X := X)...
      apply type_from_wf_typ' with (E := X ~ T1 ++ E)...
    }
    assert (0 < size (mk_aenv E) (1 ~ size (mk_aenv E) nil 0 S1) 1 S2).
    {
      inversion H0; subst...
      pick fresh X.
      rewrite <- size_fvar_spec with (X := X)...
      apply size_positive...
    }
    assert (0 < size (mk_aenv E) (1 ~ size (mk_aenv E) nil 0 T1) 1 T2).
    {
      inversion H1; subst...
      pick fresh X.
      rewrite <- size_fvar_spec with (X := X)...
      apply size_positive...
    }
    destruct (IHk E T1 S1); try solve [lia | solve_right_dec]...
    {
      revert H2.
      unfold complexity_depth.
      simpl.
      simpl_env.
      lia.
    }
    pick fresh X1.
    assert (uniq (X1 ~ T1 ++ E))...
    assert (wf_typ' (X1 ~ T1 ++ E) (open_tt S2 X1)).
    {
      apply wf_typ'_open with (T1 := S1)...
      - apply wf_typ'_weaken_head...
      - apply wf_typ_var with (U := T1)...
    }
    assert (wf_typ' (X1 ~ T1 ++ E) (open_tt T2 X1)).
    {
      apply wf_typ'_open with (T1 := T1)...
      - apply wf_typ'_weaken_head...
      - apply wf_typ_var with (U := T1)...
    }
    specialize (IHk (X1 ~ T1 ++ E) (open_tt S2 X1) (open_tt T2 X1)).
    simpl_env in H2.
    rewrite <- size_fvar_spec with (X := X1) in H2...
    rewrite <- size_fvar_spec with (X := X1) in H2...
    destruct IHk...
    + assert (0 < size (mk_aenv E) nil 0 S1) by auto using size_positive.
      assert (0 < size (mk_aenv E) nil 0 T1) by auto using size_positive.
      revert H2.
      rewrite Nat.lt_succ_r.
      apply Nat.lt_le_trans.
      enough (size (mk_aenv (X1 ~ T1 ++ E)) nil 0 (open_tt S2 X1) + complexity_depth (X1 ~ T1 ++ E) (open_tt S2 X1) (open_tt T2 X1) < size (mk_aenv E) nil 0 S1 + size (mk_aenv (X1 ~ S1 ++ E)) nil 0 (open_tt S2 X1) + (size (mk_aenv E) nil 0 T1) + complexity_depth E (typ_all S1 S2) (typ_all T1 T2)) by lia.
      assert (size (mk_aenv (X1 ~ T1 ++ E)) nil 0 (open_tt S2 X1) = size (mk_aenv (X1 ~ S1 ++ E)) nil 0 (open_tt S2 X1)).
      {
        simpl.
        f_equal.
        f_equal.
        f_equal.
        rewrite theorem2 with (S := S1) (T := T1)...
      }
      enough (complexity_depth (X1 ~ T1 ++ E) (open_tt S2 X1) (open_tt T2 X1) <= complexity_depth E (typ_all S1 S2) (typ_all T1 T2)) by lia.
      unfold complexity_depth. 
      simpl_env.
      simpl.
      simpl_env.
      repeat rewrite <- depth_fvar_spec with (X := X1)...
      simpl.
      simpl_env.
      enough (depth (X1 ~ S (depth (mk_aenv_depth E) nil 0 T1) ++ mk_aenv_depth E) nil 0 (open_tt S2 X1) <= depth (X1 ~ S (depth (mk_aenv_depth E) nil 0 S1) ++ mk_aenv_depth E) nil 0 (open_tt S2 X1)) by lia.
      admit.
    + left.
      apply sub_all with (L := (singleton X1) `union` (union (fv_tt S1) (union (fv_tt S2) (union (fv_tt T1) (union (fv_tt T2) (dom E))))))...
      intros.
      apply sub_replacing with (X := X1)...
    + solve_right_dec; subst.
      apply H13.
      pick_fresh X2.
      apply sub_replacing with (X := X2)...
Qed.

Theorem decidability : forall E S T,
  wf_env E -> wf_typ' E S -> wf_typ' E T ->
  sub E S T \/ ~ sub E S T.
Proof with auto.
  intros.
  eapply subtyping_dec...
Qed.