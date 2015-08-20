Add Rec ML Path "../".
Add LoadPath "../src" as Pwilke.

Require Import Pwilke.

Inductive P : nat -> Prop :=
| P0 : P O
| PS: forall n, P (S n)
| PS2: forall n, P (S n).

Goal
P O -> P 1 -> P 2 -> exists n, P n .
Proof.
  intros.
  eexists.
  AppHyps.
  AppCons.

  Restart.

  intros.
  refine (ex_intro _ (S _) _).
  AppHyps.
  AppCons.
Abort.