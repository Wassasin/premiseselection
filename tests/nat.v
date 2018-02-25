Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition nat_id := fun x : nat => x.

Fixpoint plus (n m : nat) : nat :=
match n with
| O => m
| S p => S (plus p m)
end.

Lemma plus_0_r: forall x, plus x O = x.
Proof.
intro x.
apply eq_sym.
induction x.
unfold plus.
apply eq_refl.
unfold plus.
apply f_equal.
exact IHx.
Qed.