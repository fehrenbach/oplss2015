Require Import Coq.Unicode.Utf8 Arith String Omega.

Inductive exp : Set :=
| Var : string -> exp
| Constant : nat -> exp
| Plus : exp -> exp -> exp
| Times : exp -> exp -> exp.

(* $$\mathsf{eval} : \mathsf{exp} \to (\mathsf{string} \to \mathsf{nat}) \to \mathsf{nat}$$ *)
Fixpoint eval (e : exp) (env : string -> nat) : nat :=
  match e with
    | Var x => env x
    | Constant n => n
    | Plus e1 e2 => eval e1 env + eval e2 env
    | Times e1 e2 => eval e1 env * eval e2 env
  end.

(* $$\mathsf{optimize} : \mathsf{exp} \to \mathsf{exp}$$ *)
Fixpoint optimize (e : exp) : exp :=
  match e with
    | Constant n => Constant n
    | Var x => Var x
    | Plus (Constant 0) e => optimize e
    | Plus e1 e2 => Plus (optimize e1) (optimize e2)
    | Times e1 e2 => Times (optimize e1) (optimize e2)
  end.

  
Theorem opt_sound : forall e env, eval e env = eval (optimize e) env.
Proof.
  intros.
  induction e.

  simpl.
  congruence.

  simpl.
  congruence.

  destruct e1.
  simpl.
  rewrite IHe2.
  congruence.

  simpl.
  destruct n.
  simpl.
  rewrite IHe2.
  congruence.

  simpl.
  rewrite IHe2.
  congruence.

  simpl in *.
  rewrite IHe1, IHe2.
  congruence.

  simpl in *.
  rewrite IHe1, IHe2.
  congruence.

  simpl.
  rewrite IHe1, IHe2.
  congruence.
Qed.

