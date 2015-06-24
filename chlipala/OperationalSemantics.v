Require Import Coq.Unicode.Utf8 String.

Open Scope string_scope.

Set Implicit Arguments.


(** Today's topic: formal semantics for high-level programming languages *)


(** * Preliminaries: general transitive-reflexive closure of a binary relation *)

(** A rather higher-order construction: this relation is parameterized on not just the type of "states" [A] but also on the relation [R] whose closure we are taking. *)
Inductive star A (R : A -> A -> Prop) : A -> A -> Prop :=
| StarRefl : forall x,
  star R x x
| StarStep : forall x1 x2 x3,
  R x1 x2
  -> star R x2 x3
  -> star R x1 x3.

(** It's transitive. *)
Theorem star_trans : forall A (R : A -> A -> Prop) x1 x2 x3,
  star R x1 x2
  -> star R x2 x3
  -> star R x1 x3.
Proof.
  induction 1; intros.

  assumption.

  econstructor.
  eassumption.
  apply IHstar.
  assumption.
Qed.


(** * Lambda terms again *)

(** Here's the syntax we saw on the first day. *)
Inductive exp : Set :=
| Var : string -> exp
| Abs : string -> exp -> exp
| App : exp -> exp -> exp.

(** We saw this substitution function on the first day. *)
Fixpoint subst (rep : exp) (x : string) (e : exp) : exp :=
  match e with
  | Var y => if string_dec y x then rep else Var y
  | Abs y e1 => Abs y (if string_dec y x then e1 else subst rep x e1)
  | App e1 e2 => App (subst rep x e1) (subst rep x e2)
  end.

(** Here are a few example terms. *)
Definition identity := Abs "x" (Var "x").
(** \x. x *)

Definition identity2 := App identity identity.
(** (\x. x) (\x. x) *)

Definition identity4 := App identity2 identity2.
(** ((\x. x) (\x. x)) ((\x. x) (\x. x)) *)


(** * Big-step semantics *)

(** This is the most straightforward way to give semantics to lambda terms:
  * We evaluate any closed term into a value (that is, an [Abs]). *)
Inductive bigStep : exp -> exp -> Prop :=
| BigAbs : forall x e,
  bigStep (Abs x e) (Abs x e)
| BigApp : forall e1 x e1' e2 v2 v,
  bigStep e1 (Abs x e1')
  -> bigStep e2 v2
  -> bigStep (subst v2 x e1') v
  -> bigStep (App e1 e2) v.

(** Note that we omit a [Var] case, since variable terms can't be *closed*. *)

(** An example of evaluating a term, the tedious way *)
Theorem bigStep_identity4 : bigStep identity4 identity.
Proof.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  simpl.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  simpl.
  econstructor.
  simpl.
  econstructor.
Qed.

(** Which terms are values, that is, final results of execution? *)
Inductive value : exp -> Prop :=
| Value : forall x e, value (Abs x e).
(** We're cheating a bit here, *assuming* that the term is also closed. *)

(** Actually, let's prove that [bigStep] only produces values. *)
Theorem bigStep_value : forall e v,
  bigStep e v
  -> value v.
Proof.
  induction 1.

  econstructor.

  assumption.
Qed.


(** * Small-step semantics *)

(** For languages with non-terminating programs, or for other reasons, it
  * can be convenient to define semantics in a more fine-grained way.
  * Here's a *call-by-value* small-step semantics. *)

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

(** Our example evaluation repeated with small steps.
  * We get the same result as last time.  What a coincidence!  Or is it...? *)
Theorem smallStep_identity4 : star smallStep identity4 identity.
Proof.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  simpl.
  econstructor.
  apply SmallApp2.
  econstructor.
  econstructor.
  econstructor.
  simpl.
  econstructor.
  econstructor.
  econstructor.
  simpl.
  econstructor.
Qed.

(** Let's *prove* that these semantics coincide. *)

(** First, we can "compose" a small step with a big step. *)
Lemma smallStep_bigStep' : forall e1 e2,
  smallStep e1 e2
  -> forall v, bigStep e2 v
    -> bigStep e1 v.
Proof.
  induction 1; intros.

  destruct H.
  econstructor.
  constructor.
  constructor.
  assumption.

  inversion H0; subst.
  econstructor.
  apply IHsmallStep.
  eassumption.
  eassumption.
  assumption.

  inversion H1; subst.
  econstructor.
  eassumption.
  apply IHsmallStep.
  eassumption.
  assumption.
Qed.

(** That's the key result for showing that small-stepping to a value implies big-stepping. *)
Theorem smallStep_bigStep : forall e v,
  star smallStep e v
  -> value v
  -> bigStep e v.
Proof.
  induction 1; intros.

  destruct H.
  constructor.

  eapply smallStep_bigStep'.
  eassumption.
  apply IHstar.
  assumption.
Qed.

(** The other direction of the equivalence also requires a particular sort of lemma.  This time, we show that the small-step rules may be lifted to multi-small-step rules. *)

Lemma star_App1 : forall e1 e1' e2,
  star smallStep e1 e1'
  -> star smallStep (App e1 e2) (App e1' e2).
Proof.
  induction 1.

  constructor.

  econstructor.
  apply SmallApp1.
  eassumption.
  assumption.
Qed.

Lemma star_App2 : forall e1 e2 e2',
  value e1
  -> star smallStep e2 e2'
  -> star smallStep (App e1 e2) (App e1 e2').
Proof.
  induction 2.

  constructor.

  econstructor.
  apply SmallApp2.
  assumption.
  eassumption.
  assumption.
Qed.

(** Finally, we show the inclusion. *)

Theorem bigStep_smallStep : forall e v,
  bigStep e v
  -> star smallStep e v.
Proof.
  induction 1.

  constructor.

  eapply star_trans.
  apply star_App1.
  eassumption.
  eapply star_trans.
  eapply star_App2.
  constructor.
  eassumption.
  econstructor.
  econstructor.
  eapply bigStep_value.
  eassumption.
  assumption.
Qed.


(** * Small-step semantics with evaluation contexts *)

(** As languages get more complex, we value notational shorthands that cut out the boilerplate of a semantics.  *Evaluation*contexts* are one such popular shorthand, which starts to pay off a tiny bit for lambda calculus, and which pays off even more for some extensions we'll consider later. *)

(** Main idea: a context is a *term with a hole in it*. *)
Inductive context : Set :=
| Hole : context
| App1 : context -> exp -> context
| App2 : exp -> context -> context.

(** The plug relation indicates how to plug a term into the hole, intuitively enough. *)
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
(** Subtle point: the [value] hypothesis right above enforces a well-formedness condition on contexts that may actually be plugged.  We don't allow skipping over a lefthand subterm of an application when that term has evaluation work left to do.  This condition is the essence of *call-by-value* instead of other evaluation strategies.  Details are largely beyond the scope of these lectures. *)

(** Now the one small-step evaluation rule is surprisingly simple: find a beta redex (anonymous function applied to a value) and reduce it. *)
Inductive contextStep : exp -> exp -> Prop :=
| ContextBeta : forall c x e v e1 e2,
  value v
  -> plug c (App (Abs x e) v) e1
  -> plug c (subst v x e) e2
  -> contextStep e1 e2.

(** We can move directly to establishing inclusion from basic small steps to contextual small steps. *)

Theorem smallStep_contextStep : forall e1 e2,
  smallStep e1 e2
  -> contextStep e1 e2.
Proof.
  induction 1.

  eapply ContextBeta with (c := Hole).
  (** The [with] clause here allows us to specify some of the rule's free variables manually. *)
  eassumption.
  econstructor.
  econstructor.

  destruct IHsmallStep.
  eapply ContextBeta with (c := App1 c e2).
  eassumption.
  econstructor.
  eassumption.
  econstructor.
  assumption.

  destruct IHsmallStep.
  eapply ContextBeta with (c := App2 e1 c).
  eassumption.
  econstructor.
  eassumption.
  eassumption.
  eapply PlugApp2.
  assumption.
  assumption.
Qed.

(** The other direction of the inclusion calls for a lemma: a small-step transition can be "lifted" to apply inside a context. *)
Lemma plug_smallStep : forall c e1 e1',
  plug c e1 e1'
  -> forall e2 e2', plug c e2 e2'
  -> smallStep e1 e2
  -> smallStep e1' e2'.
Proof.
  induction 1; inversion 1; intros; subst.

  assumption.

  econstructor.
  eapply IHplug.
  eassumption.
  assumption.

  econstructor.
  assumption.
  eapply IHplug.
  eassumption.
  assumption.
Qed.

(** Now the inclusion is almost trivial. *)
Theorem contextStep_smallStep : forall e1 e2,
  contextStep e1 e2
  -> smallStep e1 e2.
Proof.
  destruct 1.

  eapply plug_smallStep.
  eassumption.
  eassumption.
  constructor.
  assumption.
Qed.


(** * A simple application: verifying a trivial "optimization" *)

(** We contract every beta redex appearing literally in a term, not under a binder. *)
Fixpoint doSomeBeta (e : exp) : exp :=
  match e with
  | App (Abs x1 e1) (Abs x2 e2) => subst (Abs x2 e2) x1 e1
  | Var x => Var x
  | Abs x e1 => Abs x e1
  | App e1 e2 => App (doSomeBeta e1) (doSomeBeta e2)
  end.

(** This funky transformation preserves big-step behavior. *)
Theorem doSomeBeta_bigStep : forall e v,
  bigStep e v
  -> bigStep (doSomeBeta e) v.
Proof.
  induction 1; simpl.

  constructor.

  destruct e1; simpl in *.

  inversion H.

  inversion H; subst.

  destruct e2; simpl in *.

  inversion H0.

  inversion H0; subst.
  assumption.

  econstructor.
  eassumption.
  eassumption.
  assumption.

  econstructor.
  eassumption.
  eassumption.
  assumption.
Qed.

(** Note that this theorem says nothing about the effect of [doSomeBeta] on *non-terminating* programs.  Handling that case, too, is a bit trickier, and we won't attempt it now. *)
