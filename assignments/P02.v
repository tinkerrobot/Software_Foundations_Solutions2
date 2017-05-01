Require Export P01.



(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if_wp]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  eapply hoare_if_wp.
Qed.

Theorem hoare_if_wp : forall (P1 P2 Q : Assertion) (b : bexp) (c1 c2 : com),
    {{P1}} c1 {{Q}} ->
    {{P2}} c2 {{Q}} ->
    {{fun st : state => (beval st b = true -> P1 st) /\ (beval st b = false -> P2 st)}}
      IFB b THEN c1 ELSE c2 FI {{Q}}

 Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.