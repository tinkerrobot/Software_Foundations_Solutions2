Require Export P04.

Lemma IFB_split: forall P Q b c1 c2,
    {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} ->
    {{fun st => P st /\ (beval st b = true)}} c1 {{Q}} /\
    {{fun st => P st /\ (beval st b = false)}} c2 {{Q}}.
Proof.
  intros.
  split.
  - unfold hoare_triple.
    intros st st' HC [HP HB].
    unfold hoare_triple in H.
    apply H with (st := st) (st' := st'); try assumption.
    apply E_IfTrue; assumption.
  - intros st st' HC [HP HB].
    eauto.
    unfold hoare_triple in H.
    apply H with (st := st) (st' := st'); try assumption.
    apply E_IfFalse; assumption.
Qed.

Theorem hoare_if_weakest : forall P1 P2 Q b c1 c2, 
  is_wp P1 c1 Q ->
  is_wp P2 c2 Q ->
  is_wp (fun st => (beval st b = true -> P1 st) /\ (beval st b = false -> P2 st)) 
        (IFB b THEN c1 ELSE c2 FI) Q.
Proof.
  unfold is_wp, "->>".
  intros P1 P2 Q b c1 c2 [H1 W1] [H2 W2].
  split.
  - unfold hoare_triple.
    intros st st' H [C1 C2].
    inversion H.
    + inversion H8; subst; eauto.
    + inversion H8; subst; eauto.
  - intros P' P'H st H.
    apply IFB_split in P'H as [PH1 PH2].
    split.
    + intros. eapply W1. eapply PH1. simpl. split. assumption. assumption.
    + intros. eapply W2. eapply PH2. simpl. split. assumption. assumption.
Qed.