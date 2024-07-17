Require Export Metalib.Metatheory.

Inductive typ : Set :=
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
.

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => if K == J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all T1 T2)
.

Notation env := (list (atom * typ)).

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_var : forall U E X,
      binds X U E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X, X `notin` L -> wf_typ (X ~ T1 ++ E) (open_tt T2 X)) ->
      wf_typ E (typ_all T1 T2)
.

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env nil
  | wf_env_sub : forall E X T,
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env (X ~ T ++ E)
.

Inductive wf_typ' : env -> typ -> Prop :=
  | wf_typ'_top : forall E,
      wf_typ' E typ_top
  | wf_typ'_var : forall U E X,
      binds X U E ->
      wf_typ' E (typ_fvar X)
  | wf_typ'_arrow : forall E T1 T2,
      wf_typ' E T1 ->
      wf_typ' E T2 ->
      wf_typ' E (typ_arrow T1 T2)
  | wf_typ'_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X, X `notin` L -> wf_typ' (X ~ T1 ++ E) (open_tt T2 X)) ->
      wf_typ' E (typ_all T1 T2)
.

Inductive sub : env -> typ -> typ -> Prop :=
  (* NTop *)
  | sub_top : forall E S,
      sub E S typ_top
  (* NRefl *)
  | sub_refl : forall E X,
      sub E (typ_fvar X) (typ_fvar X)
  (* NVar *)
  | sub_var : forall U E T X,
      binds X U E ->
      sub E U T ->
      sub E (typ_fvar X) T
  (* NArrow *)
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  (* NAll *)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X, X `notin` L -> sub (X ~ T1 ++ E) (open_tt S2 X) (open_tt T2 X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2)
.

#[export] Hint Constructors type wf_typ wf_typ' wf_env : core.
#[export] Hint Resolve sub_top sub_refl sub_var sub_arrow sub_all : core.