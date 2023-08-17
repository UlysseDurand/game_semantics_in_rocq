Require Import jeu.
Require Import jeuthese.
Require Import interactions.
Require Import strategy.
Require Import residu.
Require Import Coq.Program.Equality.
Require Import residustrat.

Inductive ens_copycat `{J:Game} : (@O_play2 J J) -> Prop :=
  | truc1 : forall a m n s,
      ens_copycat (consO_r a m n (consO_l a m n s)).
  | truc2 : forall a m n s,
      ens_copycat (consO_)
