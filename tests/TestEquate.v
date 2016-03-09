Require Import Equate.
Require Import ZArith.
Open Scope Z_scope.

Require Import Psatz.

Goal forall (a b c d e f g : Z),
    (a * b) * (d + e * b - b * g * f) = f * b - e * c -> False.
Proof.
  intros.
  factor b H. lia.
Abort.

Definition align := 
fun n amount : Z => (n + amount - 1) / amount * amount.


Ltac elim_div :=
  unfold Zdiv, Zmod in *;
  repeat
    match goal with
      |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      |  |-  context[ Zdiv_eucl ?X ?Y ] =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
    end; unfold Remainder.


Lemma two_power_nat_O : two_power_nat O = 1.
Proof. reflexivity. Qed.

Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
Proof.
  induction n. rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. omega.
Qed.


Lemma two_power_nat_two_p:
  forall x, two_power_nat x = two_p (Z_of_nat x).
Proof.
  induction x. auto. 
  rewrite two_power_nat_S. rewrite inj_S. rewrite two_p_S. omega. omega.
Qed.


Lemma align_le_two_p:
  forall al al' (AlGt: (al <= al')%nat) x,
    (* (al' <= 12)%nat -> *)
    align (align x (two_power_nat al)) (two_power_nat al') = align x (two_power_nat al').
Proof.
  intros.
  unfold align.
  elim_div.
  generalize (two_power_nat_pos al) (two_power_nat_pos al'). intuition.
  assert (EQ: two_power_nat al' = two_power_nat al * two_power_nat (al' - al)).
  rewrite ! two_power_nat_two_p. rewrite <- two_p_is_exp; try lia.
  f_equal. lia.
  generalize (two_power_nat_pos (al' - al)).
  rewrite EQ in *. clear EQ.
  generalize dependent (two_power_nat (al' - al)). intros.

  factor z5 H3. ring_simplify. lia.
  
  equate x H1. lia. clear H1. subst.
  equate z0 H3. lia. clear H3. subst.
  equate z4 H2. lia. clear H2. subst.
  
  generalize dependent (two_power_nat al). intros.
  f_equal.
  remember (z1 - z5 * z3 - 1) as V1.
  assert (V1 = 0 \/ V1 < 0 \/ V1 > 0) by lia.
  intuition ; try nia.  
Qed.