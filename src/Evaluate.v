Require Import FunctionNinjas.All.
Require Import Io.All.
Require Import Monad.All.

Import C.Notations.
Local Open Scope type.

(** Evaluate the commands of a computation. *)
Fixpoint command {E1 E2 : Effect.t} {A : Type}
  (eval : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c))
  (x : C.t E1 A) : C.t E2 A :=
  match x with
  | C.Ret _ x => C.Ret _ x
  | C.Call c => eval c
  | C.Let _ _ x f => C.Let _ _ (command eval x) (fun x => command eval (f x))
  | C.Join _ _ x y => C.Join _ _ (command eval x) (command eval y)
  | C.Choose _ x y => C.Choose _ (command eval x) (command eval y)
  end.

Fixpoint exception {E1 E2 : Effect.t} {Exc A : Type}
  (eval : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c + Exc))
  (eval_join : Exc -> Exc -> Exc) (x : C.t E1 A) : C.t E2 (A + Exc) :=
  match x with
  | C.Ret _ x => ret @@ inl x
  | C.Call c => eval c
  | C.Let _ _ x f =>
    let! x := exception eval eval_join x in
    match x with
    | inl x => exception eval eval_join (f x)
    | inr exc => ret @@ inr exc
    end
  | C.Join _ _ x y =>
    let! xy := join (exception eval eval_join x) (exception eval eval_join y) in
    match xy with
    | (inl x, inl y) => ret @@ inl (x, y)
    | (inr exc, inl _) | (inl _, inr exc) => ret @@ inr exc
    | (inr exc_x, inr exc_y) => ret @@ inr (eval_join exc_x exc_y)
    end
  | C.Choose _ x y =>
    choose (exception eval eval_join x) (exception eval eval_join y)
  end.

Module EvalMonad.
  Record t (E : Effect.t) (M : Type -> Type) := New {
    command : forall (c : Effect.command E), M (Effect.answer E c);
    join : forall A B, M A -> M B -> M (A * B);
    choose : forall A, M A -> M A -> M A }.
  Arguments command {E M} _ _.
  Arguments join {E M} _ {A B} _ _.
  Arguments choose {E M} _ {A} _ _.
End EvalMonad.

Fixpoint monad {E : Effect.t} {A : Type} {M : Type -> Type} (m : Monad.t M)
  (eval : EvalMonad.t E M) (x : C.t E A) : M A :=
  match x with
  | C.Ret _ x => Monad.ret m x
  | C.Call c => EvalMonad.command eval c
  | C.Let _ _ x f =>
    Monad.bind m (monad m eval x) (fun x =>
    monad m eval (f x))
  | C.Join _ _ x y => EvalMonad.join eval (monad m eval x) (monad m eval y)
  | C.Choose _ x y => EvalMonad.choose eval (monad m eval x) (monad m eval y)
  end.

Module Run.
  Fixpoint command {E1 E2 : Effect.t} {A : Type}
    {eval : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c)}
    (run : forall c (a : Effect.answer E1 c), Run.t (eval c) a)
    {x : C.t E1 A} {v : A} (r : Run.t x v) : Run.t (command eval x) v.
    destruct r; simpl.
    - apply Run.Ret.
    - apply run.
    - eapply Run.Let. apply (command _ _ _ _ run _ _ r1).
      apply (command _ _ _ _ run _ _ r2).
    - apply ChooseLeft.
      apply (command _ _ _ _ run _ _ r).
    - apply ChooseRight.
      apply (command _ _ _ _ run _ _ r).
    - apply Run.Join.
      + apply (command _ _ _ _ run _ _ r1).
      + apply (command _ _ _ _ run _ _ r2).
  Defined.

  Fixpoint exception {E1 E2 : Effect.t} {Exc A : Type}
    {eval : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c + Exc)}
    {eval_join : Exc -> Exc -> Exc}
    (run : forall c (a : Effect.answer E1 c), Run.t (eval c) (inl a))
    {x : C.t E1 A} {v : A} (r : Run.t x v)
    : Run.t (exception eval eval_join x) (inl v).
    destruct r; simpl.
    - apply Run.Ret.
    - apply run.
    - eapply Run.Let. apply (exception _ _ _ _ _ _ run _ _ r1).
      apply (exception _ _ _ _ _ _ run _ _ r2).
    - apply Run.ChooseLeft.
      apply (exception _ _ _ _ _ _ run _ _ r).
    - apply Run.ChooseRight.
      apply (exception _ _ _ _ _ _ run _ _ r).
    - eapply Run.Let.
      + eapply Run.Join.
        * apply (exception _ _ _ _ _ _ run _ _ r1).
        * apply (exception _ _ _ _ _ _ run _ _ r2).
      + apply Run.Ret.
  Defined.
End Run.
