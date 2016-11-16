Require Export P08.



(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
   we distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As often happens, this
   apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof. intros.
  induction l as [|h t IH].
  - simpl in H. destruct H.
  - simpl in H. inversion H as [HL| HR].
    + exists [], t. simpl. rewrite HL. reflexivity.
    + apply IH in HR. inversion HR as [l3 H2]. inversion H2 as[l4 H3].
      exists (h::l3), l4. rewrite H3. simpl. reflexivity.
Qed.

Lemma alc : forall (X:Type) (x:X) (l1 l2 : list X),
  length (l1 ++ x :: l2) = S (length(l1 ++ l2)).
Proof. intros. induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

(*
Inductive repeats {X:Type} : list X -> Prop :=
| rp_base: forall x l, In x l -> repeats (x::l)
| rp_next: forall x l, repeats l -> repeats (x::l)
.
*)

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Lemma leSS : forall a b, 
  S a <= b -> a <= b.
Proof.
   intros. generalize dependent b. induction a.
        - intros. apply le_0_n.
        - intros. destruct b. inversion H. apply le_S_n in H.
          apply IHa in H. apply le_n_S. apply H.
Qed.

Lemma Inor : forall (X: Type) (l1 l2 : list X) (x : X),
  In x (l1++l2) <-> In x l1 \/ In x l2.
Proof. intros. induction l1.
  - simpl. split. 
    + intros. right. apply H.
    + intros H. inversion H. inversion H0. apply H0.
  - simpl. split.
    + intros [HL | HR]. 
      ++ left. left. apply HL.
      ++ apply or_assoc. right. apply IHl1 in HR. apply HR.
    + intros [HL | HR].
      ++ inversion HL. 
        +++ left. apply H.
        +++ right. apply or_introl with (B:= In x l2) in H.
            apply IHl1 in H. apply H.
      ++ right. apply or_intror with (A:= In x l1) in HR.
         apply IHl1 in HR. apply HR.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
   { unfold excluded_middle. intros. inversion H1. }
   { intros. unfold excluded_middle in H. 
     destruct H with (P:= In x l1').
     - apply rp_base in H2. apply H2.
     - simpl in H0. assert (x = x) as eq. { reflexivity. }
        apply or_introl with (B:= In x l1') in eq. apply H0 in eq.
        apply in_split in eq.
        inversion eq as [l1 [l3 H3]].
        apply IHl1' with (l2:=l1++l3) in H as H4.
        + apply rp_next with (x0:=x) in H4. apply H4.
        + intros. destruct H with (P:=x=x0).
          ++ rewrite H5 in H2. unfold not in H2. 
              apply H2 in H4. destruct H4.
          ++ apply or_intror with (A:=x=x0) in H4.
              apply H0 in H4. rewrite H3 in H4. 
              apply Inor in H4. inversion H4.
            +++ apply or_introl with (B:= In x0 l3) in H6.
                apply Inor in H6. apply H6.
            +++ simpl in H6. inversion H6.
              ++++ rewrite H7 in H5. destruct H5. reflexivity.
              ++++ apply or_intror with (A:= In x0 l1) in H7.
                    apply Inor in H7. apply H7.
        + inversion H1.
          ++ rewrite H3. rewrite alc. unfold lt. apply le_n.
          ++ unfold lt. rewrite H3 in H5. rewrite alc in H5.
              apply leSS in H5. apply H5. }

Qed. 



