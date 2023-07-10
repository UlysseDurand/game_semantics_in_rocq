Require Import jeu.
Require Import jeuthese.
Require Import interactions.
Require Import strategy.
Require Import residu.
Require Import Coq.Program.Equality.
Require Import residustrat.



(**
On va composer des stratégies, on peut soit composer
- Une stratégie O avec une stratégie O (on obtient une stratégie O)
- Une stratégie O avec une stratégie P (on obtient une stratégie P)
- Une stratégie P avec une stratégie O (on obtient une stratégie P)
 *)

(**
* Définiton du parallèle de deux stratégies
 *)

Inductive parallele_stratOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) (u:@OOO_int J G H) :=
  | respecte_stratsOO :
      sigma.(SO) (restriction_lm_OOO u) ->
      tau.(SO) (restriction_mr_OOO u) ->
        parallele_stratOO sigma tau u.

Inductive parallele_stratPO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2P J G) (tau : @strategy2O G H) (u:@POP_int J G H) :=
  | respecte_stratsPO :
      sigma.(SP) (restriction_lm_POP u) ->
      tau.(SO) (restriction_mr_POP u) ->
        parallele_stratPO sigma tau u.

Inductive parallele_stratOP `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2P G H) (u:@OPP_int J G H) :=
  | respecte_stratsOP :
      sigma.(SO) (restriction_lm_OPP u) ->
      tau.(SP) (restriction_mr_OPP u) ->
        parallele_stratOP sigma tau u.



(**
* Définition de la composition de deux stratégies
 *)

Inductive partiecomposeOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) :
  (@O_play2 J H) -> Prop :=
  | restr_temoinsOO :
      forall (u:@OOO_int J G H),
      parallele_stratOO sigma tau u ->
        partiecomposeOO sigma tau (restriction_lr_OOO u).

Inductive partiecomposePO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2P J G) (tau : @strategy2O G H) :
  (@P_play2 J H) -> Prop :=
  | restr_temoinsPO :
      forall (u:@POP_int J G H),
      parallele_stratPO sigma tau u ->
        partiecomposePO sigma tau (restriction_lr_POP u).

Inductive partiecomposeOP `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2P G H) :
  (@P_play2 J H) -> Prop :=
  | restr_temoinsOP :
      forall (u:@OPP_int J G H),
      parallele_stratOP sigma tau u ->
        partiecomposeOP sigma tau (restriction_lr_OPP u).



(**
Prouvons que la propriété d'être dans sigma parallele tau
est stable par préfixeOOO.
 *)
Check OOO_induc.

Lemma prefixOOO_restriction_lm `{J:Game} `{G:Game} `{H:Game}:
  forall (u v:@OOO_int J G H),
  prefixOOO u v -> prefixO2 (restriction_lm_OOO u) (restriction_lm_OOO v).
Proof.
  revert J G H.
  apply prefixOOO_induc with
    (fun J G H u v e => prefixO2 (restriction_lm_OPP u) (restriction_lm_OPP v))
    (fun J G H u v e => prefixP2 (restriction_lm_POP u) (restriction_lm_POP v));
  intros J G H; intros;simpl;try constructor;auto.
Qed.

Lemma prefixOOO_restriction_mr `{J:Game} `{G:Game} `{H:Game}:
  forall (u v:@OOO_int J G H),
  prefixOOO u v -> prefixO2 (restriction_mr_OOO u) (restriction_mr_OOO v).
Proof.
  revert J G H.
  apply prefixOOO_induc with
    (fun J G H u v e => prefixP2 (restriction_mr_OPP u) (restriction_mr_OPP v))
    (fun J G H u v e => prefixO2 (restriction_mr_POP u) (restriction_mr_POP v));
  intros J G H; intros;simpl;try constructor;auto.
Qed.

Lemma prefixOPP_restriction_lm `{J:Game} `{G:Game} `{H:Game}:
  forall (u v:@OPP_int J G H),
  prefixOPP u v -> prefixO2 (restriction_lm_OPP u) (restriction_lm_OPP v).
Proof.
  revert J G H.
  apply prefixOPP_induc with
    (fun J G H u v e => prefixO2 (restriction_lm_OOO u) (restriction_lm_OOO v))
    (fun J G H u v e => prefixP2 (restriction_lm_POP u) (restriction_lm_POP v));
  intros J G H; intros;simpl;try constructor;auto.
Qed.

Lemma prefixOPP_restriction_mr `{J:Game} `{G:Game} `{H:Game}:
  forall (u v:@OPP_int J G H),
  prefixOPP u v -> prefixP2 (restriction_mr_OPP u) (restriction_mr_OPP v).
Proof.
  revert J G H.
  apply prefixOPP_induc with
    (fun J G H u v e => prefixO2 (restriction_mr_OOO u) (restriction_mr_OOO v))
    (fun J G H u v e => prefixO2 (restriction_mr_POP u) (restriction_mr_POP v));
    intros J G H; intros;simpl;try constructor;auto.
Qed.

Lemma prefixPOP_restriction_lm `{J:Game} `{G:Game} `{H:Game}:
  forall (u v:@POP_int J G H),
  prefixPOP u v -> prefixP2 (restriction_lm_POP u) (restriction_lm_POP v).
Proof.
  revert J G H.
  apply prefixPOP_induc with
    (fun J G H u v e => prefixO2 (restriction_lm_OOO u) (restriction_lm_OOO v))
    (fun J G H u v e => prefixO2 (restriction_lm_OPP u) (restriction_lm_OPP v));
  intros J G H; intros;simpl;try constructor;auto.
Qed.
Lemma prefixPOP_restriction_mr `{J:Game} `{G:Game} `{H:Game}:
  forall (u v:@POP_int J G H),
  prefixPOP u v -> prefixO2 (restriction_mr_POP u) (restriction_mr_POP v).
Proof.
  revert J G H.
  apply prefixPOP_induc with
    (fun J G H u v e => prefixO2 (restriction_mr_OOO u) (restriction_mr_OOO v))
    (fun J G H u v e => prefixP2 (restriction_mr_OPP u) (restriction_mr_OPP v));
    intros J G H; intros;simpl;try constructor;auto.
Qed.


Lemma prefixe_donc_paralleleOO `{J:Game} `{G:Game} `{H:Game} :
    forall (u:@OOO_int J G H) (v:@OOO_int J G H)
      (sigma:@strategy2O J G) (tau:@strategy2O G H),
    (parallele_stratOO sigma tau) u ->
    prefixOOO v u ->
      (parallele_stratOO sigma tau) v.
Proof.
  apply (OOO_induc
    (fun J0 G0 H0 u =>
      forall (v:@OOO_int J0 G0 H0)
        (sigma:@strategy2O J0 G0) (tau: @strategy2O G0 H0),
        (parallele_stratOO sigma tau) u ->
        prefixOOO v u ->
          (parallele_stratOO sigma tau) v
    )
    (fun J0 G0 H0 u =>
      forall (v:@OPP_int J0 G0 H0)
        (sigma:@strategy2O J0 G0) (tau: @strategy2P G0 H0),
        (parallele_stratOP sigma tau) u ->
        prefixOPP v u ->
          (parallele_stratOP sigma tau) v
    )
    (fun J0 G0 H0 u =>
      forall (v:@POP_int J0 G0 H0)
        (sigma:@strategy2P J0 G0) (tau: @strategy2O G0 H0),
        (parallele_stratPO sigma tau) u ->
        prefixPOP v u ->
          (parallele_stratPO sigma tau) v
    )
  ).

  - intros J0 G0 H0 v sigma tau nilparall vprefnil.
    induction v; [assumption| inversion vprefnil|inversion vprefnil].
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    induction consas_parall. eapply respecte_stratsOO.
    + eapply SO_closed;[apply s0|]. now apply prefixOOO_restriction_lm.
    + eapply SO_closed;[apply s1|]. now apply prefixOOO_restriction_mr.
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    induction consas_parall;eapply respecte_stratsOO.
    + eapply SO_closed;[apply s0|]. now apply prefixOOO_restriction_lm.
    + eapply SO_closed;[apply s1|]. now apply prefixOOO_restriction_mr.
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    induction consas_parall;eapply respecte_stratsOP.
    + eapply SO_closed;[apply s0|]. now apply prefixOPP_restriction_lm.
    + eapply SP_closed;[apply s1|]. now apply prefixOPP_restriction_mr.
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    induction consas_parall;eapply respecte_stratsOP.
    + eapply SO_closed;[apply s0|]. now apply prefixOPP_restriction_lm.
    + eapply SP_closed;[apply s1|]. now apply prefixOPP_restriction_mr.
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    induction consas_parall;eapply respecte_stratsPO.
    + eapply SP_closed;[apply s0|]. now apply prefixPOP_restriction_lm.
    + eapply SO_closed;[apply s1|]. now apply prefixPOP_restriction_mr.
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    induction consas_parall;eapply respecte_stratsPO.
    + eapply SP_closed;[apply s0|]. now apply prefixPOP_restriction_lm.
    + eapply SO_closed;[apply s1|]. now apply prefixPOP_restriction_mr.
Qed.




Set Keep Proof Equalities.

Ltac inv_with_eq:=
  match goal with
  | [H: existT ?P ?a ?m = existT ?P ?a ?n |- _ ] =>
      apply Eqdep.EqdepTheory.inj_pair2 in H;subst
  end.

Lemma compose_prefix_closed `{J:Game} `{G:Game} `{H:Game} :
      forall (u:@OOO_int J G H) (s1:@O_play2 J H) s2,
      prefixO2 s1 s2 ->
      s2 = restriction_lr_OOO u ->
        exists v, ((restriction_lr_OOO v) = s1) /\ (prefixOOO v u).
Proof.
  intros u s1 s2 s1prefs2.
  apply (prefixO2_induc
  (
    fun J H s1 s2 s1prefs2 => forall G u,
    s2=restriction_lr_OOO u ->
      exists (v:@OOO_int J G H), (restriction_lr_OOO v = s1) /\ (prefixOOO v u)
  )
  (
    fun J H s1 s2 s1prefs2 => forall G,
    (forall u, s2 = restriction_lr_OPP u ->
     exists (v:@OPP_int J G H), (restriction_lr_OPP v = s1) /\ (prefixOPP v u))
  /\ (forall u,  s2 = restriction_lr_POP u ->
      exists (v:@POP_int J G H), (restriction_lr_POP v = s1) /\ (prefixPOP v u)
  )))
  ;
    intros;try split;intros; try (specialize (H0 G1); destruct H0 as (HI1,HI2)).
  - exists nilOOO;split;auto.
      
  (* Une version un peu dépliée, mais tout est dans la tactique inv_with_eq définie plus 
       ainsi que l'utilisation de l'option Set Keep Proof Equalities. *)
  - assert (Hu:exists u', s' = restriction_lr_POP u' /\ u0 = consOOO_A a m n u').
    +  destruct u0;simpl in H1;inversion H1;subst;
         repeat inv_with_eq;
         try (eexists; split; reflexivity). 
    + destruct Hu as (u',(s2'eq,u'eq)). destruct H1.
      destruct (HI2 u' s2'eq) as (v',(v'H1,v'H2)).
      exists (consOOO_A a m n v').
      split.
      * simpl. f_equal. apply v'H1.
      * simpl. rewrite u'eq. apply prefOOO_A. exact v'H2.

  (* Une version plus efficace, sans le assert mais qui fait pareil. *)        
  - destruct u0;simpl in H1;inversion H1;subst.
    repeat inv_with_eq.
    destruct (HI1 o eq_refl) as (v',(v'H1,v'H2)).
    exists (consOOO_C c m0 n0 v').
    split;simpl;[now rewrite v'H1| now constructor].
    
  - admit.
  - admit.
    
  - assert (exists u',  u0 = consOPP_C a m p u'). 
    admit. (* Mais c'est pas très vrai, ça peut être en profondeur... *)
    destruct H2 as (u',Hu');subst.
    simpl in H1. inversion H1.
     destruct (H0  _ u') as (v,(Hv,Pv));trivial;
     inv_with_eq;trivial.
    exists (consOPP_C a m p v);
      split;simpl;[reflexivity| now constructor].
  - admit.
  - exact s1prefs2.
Admitted.



Lemma prefix_closedOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) :
    forall s1 s2, (partiecomposeOO sigma tau) s2 -> prefixO2 s1 s2 ->
      (partiecomposeOO sigma tau) s1.
Proof.
  intros s1 s2 (u,u_parall) s1prefs2.
  assert (exists v : OOO_int, restriction_lr_OOO v = s1 /\ prefixOOO v u).
  apply (@compose_prefix_closed J G H u s1 (restriction_lr_OOO u) s1prefs2).
  reflexivity.
  destruct H0 as (v,(restrvs1,prefvu)).
  rewrite <- restrvs1.
  exact (restr_temoinsOO sigma tau v (prefixe_donc_paralleleOO u v sigma tau u_parall prefvu)).
Qed.

Lemma coherentOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) s s' :
  partiecomposeOO sigma tau s ->
  partiecomposeOO sigma tau s' ->
  coherentO2 s s'.
Admitted.


Program Definition composeOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) :
  (@strategy2O J H) :=
  @Build_strategy2O
    J
    H
    (partiecomposeOO sigma tau)
    (prefix_closedOO sigma tau)
    (@coherentOO J G H sigma tau).
