Require Export P04.


Lemma IFB_split: forall P Q b c1 c2,
    {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} ->
    {{fun st => P st /\ (beval st b = true)}} c1 {{Q}} /\
{{fun st => P st /\ (beval st b = false)}} c2 {{Q}}.
Proof.
  intros P Q b c1 c2 HIf. split.
  - unfold hoare_triple in *. intros st st' Hst [HP HB].
    remember (HIf st st') as H. apply H.
    apply E_IfTrue; assumption. assumption.
  - unfold hoare_triple in *. intros st st' Hst [HP HB].
    remember (HIf st st') as H. apply H.
    apply E_IfFalse; assumption. assumption.
Qed.

Theorem hoare_if_weakest : forall P1 P2 Q b c1 c2, 
  is_wp P1 c1 Q ->
  is_wp P2 c2 Q ->
  is_wp (fun st => (beval st b = true -> P1 st) /\ (beval st b = false -> P2 st)) 
        (IFB b THEN c1 ELSE c2 FI) Q.
Proof.
  unfold is_wp. intros P1 P2 Q b c1 c2.
  intros [H1 C1] [H2 C2]. split.
  - apply hoare_if_wp; assumption.
  - unfold assert_implies in *.

    intros P' H. apply IFB_split in H. inversion H as [HT HF]. 
    intros st HP. split; intros HB.
    + apply (C1 (fun st : state => P' st /\ beval st b = true)).
      assumption. eauto.
    + apply C2 with (P':=(fun st: state => P' st /\ beval st b = false)); eauto.
Qed.
