Require Export P01.



(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)

(** Successor of a natural number: *)

Print c_nat.

Definition c_succ (n : c_nat) : c_nat  :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example c_succ_1 : c_succ c_zero = c_one.
Proof. reflexivity. Qed.

Example c_succ_2 : c_succ c_one = c_two.
Proof. reflexivity. Qed.

Example c_succ_3 : c_succ c_two = c_three.
Proof. reflexivity. Qed.
