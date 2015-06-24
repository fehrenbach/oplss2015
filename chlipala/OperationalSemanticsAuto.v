Require Import Coq.Unicode.Utf8 String.

Set Implicit Arguments.


Inductive star A (R : A -> A -> Prop) : A -> A -> Prop :=
| StarRefl : forall x,
  star R x x
| StarStep : forall x1 x2 x3,
  R x1 x2
  -> star R x2 x3
  -> star R x1 x3.

Hint Constructors star.

Theorem star_trans : forall A (R : A -> A -> Prop) x1 x2 x3,
  star R x1 x2
  -> star R x2 x3
  -> star R x1 x3.
Proof.
  induction 1; eauto.
Qed.


Inductive exp : Set :=
| Var : string -> exp
| Abs : string -> exp -> exp
| App : exp -> exp -> exp.

Fixpoint subst (rep : exp) (x : string) (e : exp) : exp :=
  match e with
  | Var y => if string_dec y x then rep else Var y
  | Abs y e1 => Abs y (if string_dec y x then e1 else subst rep x e1)
  | App e1 e2 => App (subst rep x e1) (subst rep x e2)
  end.

(** * Big-step semantics *)

Inductive bigStep : exp -> exp -> Prop :=
| BigAbs : forall x e,
  bigStep (Abs x e) (Abs x e)
| BigApp : forall e1 x e1' e2 v2 v,
  bigStep e1 (Abs x e1')
  -> bigStep e2 v2
  -> bigStep (subst v2 x e1') v
  -> bigStep (App e1 e2) v.

Inductive value : exp -> Prop :=
| Value : forall x e, value (Abs x e).

Hint Constructors value bigStep.

Theorem bigStep_value : forall e v,
  bigStep e v
  -> value v.
Proof.
  induction 1; auto.
Qed.


(** * Small-step semantics *)

Inductive smallStep : exp -> exp -> Prop :=
| SmallBeta : forall x e1 v,
  value v
  -> smallStep (App (Abs x e1) v) (subst v x e1)
| SmallApp1 : forall e1 e1' e2,
   smallStep e1 e1'
   -> smallStep (App e1 e2) (App e1' e2)
| SmallApp2 : forall e1 e2 e2',
   value e1
   -> smallStep e2 e2'
   -> smallStep (App e1 e2) (App e1 e2').

Hint Constructors smallStep.

(** * Small-step semantics with evaluation contexts *)

Inductive context : Set :=
| Hole : context
| App1 : context -> exp -> context
| App2 : exp -> context -> context.

Inductive plug : context -> exp -> exp -> Prop :=
| PlugHole : forall e,
  plug Hole e e
| PlugApp1 : forall c e1 e2 e,
  plug c e1 e
  -> plug (App1 c e2) e1 (App e e2)
| PlugApp2 : forall c e1 e2 e,
  value e1
  -> plug c e2 e
  -> plug (App2 e1 c) e2 (App e1 e).

Inductive contextStep : exp -> exp -> Prop :=
| ContextBeta : forall c x e v e1 e2,
  value v
  -> plug c (App (Abs x e) v) e1
  -> plug c (subst v x e) e2
  -> contextStep e1 e2.

Hint Constructors plug contextStep.

Ltac inv H := inversion H; clear H; subst.

Ltac t1 :=
  match goal with
  | [ H : bigStep _ _ |- _ ] =>
    inv H;
      try match goal with
          | [ H : value (App _ _) |- _ ] => inversion H
          end; []
  | [ H : smallStep (App _ _) _ |- _ ] => inv H
  | [ H : value _ |- _ ] => inv H
  | [ H : plug _ _ _ |- _ ] => inv H; []
  | [ H : contextStep _ _ |- _ ] => inv H
  end.

Ltac t := intros; repeat t1; eauto.

Lemma smallStep_bigStep' : forall e1 e2,
  smallStep e1 e2
  -> forall v, bigStep e2 v
    -> bigStep e1 v.
Proof.
  induction 1; t.
Qed.

Hint Resolve smallStep_bigStep'.

Theorem smallStep_bigStep : forall e v,
  star smallStep e v
  -> value v
  -> bigStep e v.
Proof.
  induction 1; t.
Qed.

Lemma star_App1 : forall e1 e1' e2,
  star smallStep e1 e1'
  -> star smallStep (App e1 e2) (App e1' e2).
Proof.
  induction 1; t.
Qed.

Lemma star_App2 : forall e1 e2 e2',
  value e1
  -> star smallStep e2 e2'
  -> star smallStep (App e1 e2) (App e1 e2').
Proof.
  induction 2; t.
Qed.

Hint Resolve bigStep_value star_App1 star_App2.

Theorem bigStep_smallStep : forall e v,
  bigStep e v
  -> star smallStep e v.
Proof.
  induction 1; t; eauto 8 using star_trans.
Qed.

Theorem smallStep_contextStep : forall e1 e2,
  smallStep e1 e2
  -> contextStep e1 e2.
Proof.
  induction 1; t.
Qed.

Lemma plug_smallStep : forall c e1 e1',
  plug c e1 e1'
  -> forall e2 e2', plug c e2 e2'
  -> smallStep e1 e2
  -> smallStep e1' e2'.
Proof.
  induction 1; t.
Qed.

Hint Resolve plug_smallStep.

Theorem contextStep_smallStep : forall e1 e2,
  contextStep e1 e2
  -> smallStep e1 e2.
Proof.
  t.
Qed.
