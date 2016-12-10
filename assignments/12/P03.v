Require Export P02.



(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Definition halve : tm :=
  tfix (tabs Halve (TArrow TNat TNat) (tabs X TNat 
    (tif0 (tvar X)
      (tnat 0)
      (tif0 (tpred (tvar X))
        (tnat 0)
        (tsucc (tapp (tvar Halve) (tpred (tpred (tvar X)))))
      )
    )
  )).

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  unfold halve; eauto 10.
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  unfold halve; normalize.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  unfold halve; normalize.
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
  intros n. induction n.
  - simpl. unfold halve. normalize.
  - eapply multi_step. eapply ST_AppFix; eauto.
    eapply multi_step. eapply ST_App1; eauto.
    eapply multi_step. simpl. eapply ST_AppAbs; eauto.
    eapply multi_step. simpl. eapply ST_If0Nonzero.
    eapply multi_step. eapply ST_If01; eauto. simpl. rewrite <- plus_n_Sm.
    eapply multi_step. eapply ST_If0Nonzero.
    eapply multi_step. eapply ST_Succ1. eapply ST_App2; eauto.
    eapply multi_step. eapply ST_Succ1. eapply ST_App2; eauto.
    simpl.
    assert (forall t1 t2, t1 ==>* t2 -> tsucc t1 ==>* tsucc t2).
    { intros t1 t2 H. induction H; eauto. }
    apply H in IHn. eapply multi_trans. unfold halve in IHn. apply IHn.
    eapply multi_step. eauto. apply multi_refl.
    
  
Qed.

