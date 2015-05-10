Require Import FunctionNinjas.All.
Require Import Io.All.

Import C.Notations.

(** Evaluate the commands of a computation. *)
Fixpoint command {E1 E2 : Effect.t} {A : Type}
  (run : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c))
  (x : C.t E1 A) : C.t E2 A :=
  match x with
  | C.Ret _ x => C.Ret _ x
  | C.Call c => run c
  | C.Let _ _ x f => C.Let _ _ (command run x) (fun x => command run (f x))
  | C.Join _ _ x y => C.Join _ _ (command run x) (command run y)
  | C.Choose _ x y => C.Choose _ (command run x) (command run y)
  end.

Fixpoint exception {E1 E2 : Effect.t} {Exc A : Type}
  (run : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c + Exc))
  (run_join : Exc -> Exc -> Exc) (x : C.t E1 A) : C.t E2 (A + Exc) :=
  match x with
  | C.Ret _ x => ret @@ inl x
  | C.Call c => run c
  | C.Let _ _ x f =>
    let! x := exception run run_join x in
    match x with
    | inl x => exception run run_join (f x)
    | inr exc => ret @@ inr exc
    end
  | C.Join _ _ x y =>
    let! xy := join (exception run run_join x) (exception run run_join y) in
    match xy with
    | (inl x, inl y) => ret @@ inl (x, y)
    | (inr exc, inl _) | (inl _, inr exc) => ret @@ inr exc
    | (inr exc_x, inr exc_y) => ret @@ inr (run_join exc_x exc_y)
    end
  | C.Choose _ x y =>
    choose (exception run run_join x) (exception run run_join y)
  end.
