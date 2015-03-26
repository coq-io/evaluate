Require Import FunctionNinjas.All.
Require Import Io.All.

Import C.Notations.

(** Run the commands of a computation. *)
Fixpoint lift {E1 E2 : Effect.t} {A : Type}
  (run : forall (c : Effect.command E1), C.t E2 (Effect.answer E1 c))
  (x : C.t E1 A) : C.t E2 A :=
  match x with
  | C.Ret _ x => C.Ret _ x
  | C.Call c => run c
  | C.Let _ _ x f => C.Let _ _ (lift run x) (fun x => lift run (f x))
  | C.Join _ _ x y => C.Join _ _ (lift run x) (lift run y)
  | C.First _ _ x y => C.First _ _ (lift run x) (lift run y)
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
  | C.First _ _ x y =>
    let! xy := first (exception run run_join x) (exception run run_join y) in
    match xy with
    | inl (inl x) => ret @@ inl @@ inl x
    | inr (inl y) => ret @@ inl @@ inr y
    | inl (inr exc) | inr (inr exc) => ret @@ inr exc
    end
  end.
