Require Export P02.



(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] transformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | AId x              => AId x
  | ANum n             => ANum n
  | APlus (ANum 0) e2  => optimize_0plus e2
  | APlus e1 e2        => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2       => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2        => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: forall st a,
  aeval st (optimize_0plus a) = aeval st a.
Proof.
  intros st a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  - (* APlus *)
    destruct a1;
      try (simpl; simpl in IHa1; rewrite IHa1;rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n; simpl; rewrite IHa2; reflexivity.
    + (* a1 = AId i *) simpl. rewrite IHa2. reflexivity.
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BEq a1 a2   => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2   => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1     => BNot (optimize_0plus_b b1)
  | BAnd b1 b2  => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Example optimize_0plus_b_example1:
  optimize_0plus_b (BEq 
     (AMult (APlus (ANum 0) (APlus (ANum 0) (ANum 3)))
            (AMinus (ANum 5) (APlus (ANum 0) (ANum 1))))
     (APlus (ANum 2)
            (APlus (ANum 0)
                   (APlus (ANum 0) (ANum 1)))))
  = (BEq (AMult (ANum 3) (AMinus (ANum 5) (ANum 1)))
         (APlus (ANum 2) (ANum 1))).
Proof. reflexivity. Qed.  

Theorem optimize_0plus_b_sound : forall st b,
  beval st (optimize_0plus_b b) = beval st b.
Proof.
  intros st b.
  induction b;
    try (simpl; repeat rewrite optimize_0plus_sound; reflexivity);
    try reflexivity.
  - (* BNot *) simpl. rewrite IHb. reflexivity.
  - (* BAnd *) simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.