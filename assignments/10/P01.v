Require Export D.



(** **** Exercise: 3 stars (eval__multistep)  *)
(** The key idea behind the proof comes from the following picture:
       P t1 t2 ==>            (by ST_Plus1) 
       P t1' t2 ==>           (by ST_Plus1)  
       P t1'' t2 ==>          (by ST_Plus1) 
       ...                
       P (C n1) t2 ==>        (by ST_Plus2)
       P (C n1) t2' ==>       (by ST_Plus2)
       P (C n1) t2'' ==>      (by ST_Plus2)
       ...                
       P (C n1) (C n2) ==>    (by ST_PlusConstConst)
       C (n1 + n2)              
    That is, the multistep reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_Plus1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_Plus2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PlusConstConst] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

(** To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of [==>*]: that it is reflexive, transitive, and
    includes [==>]. *)

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.  Qed.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 ==>* t1' ->
     P t1 t2 ==>* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
    - (* multi_refl *) apply multi_refl.
    - (* multi_step *) apply multi_step with (P y t2).
        apply ST_Plus1. apply H.
        apply IHmulti.  Qed.

Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
  intros t1 t2 t2' Ht1 H. induction H.
  - apply multi_refl.
  - apply multi_step with (P t1 y).
    inversion Ht1. apply ST_Plus2. assumption. assumption. 
Qed.

Theorem eval__multistep : forall t n,
  t \\ n -> t ==>* C n.
Proof.
  intros t n H. induction H.
  - apply multi_refl.
  - apply multistep_congr_1 with (t1 := t1) (t1' := C n1) (t2 := t2) in IHeval1.
    apply multistep_congr_2 with (t1 := C n1) (t2 := t2) (t2' := C n2) in IHeval2.
    apply multi_trans with (x := P t1 t2) (y := P (C n1) t2) (z := P (C n1) (C n2))in IHeval1.
    apply multi_trans with (x := P t1 t2) (y := P (C n1) (C n2)) (z := C (n1 + n2)).
    assumption.  apply multi_R. constructor. assumption. constructor.
Qed.

