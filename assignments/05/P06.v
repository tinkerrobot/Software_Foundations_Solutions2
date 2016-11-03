Require Export P05.



Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - (* -> *) intros H. destruct H as [X' H]. destruct H as [HP | HQ].
    + left. exists X'. apply HP.
    + right. exists X'. apply HQ.      
  - (* <- *) intros H. destruct H as [HP | HQ].
    + destruct HP as [X' HP]. exists X'. left. apply HP.
    + destruct HQ as [X' HQ]. exists X'. right. apply HQ.
Qed.

