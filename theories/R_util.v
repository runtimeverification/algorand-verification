From mathcomp.ssreflect
Require Import all_ssreflect.

From Coq
Require Import Reals.Reals.

From Algorand
Require Import boolp Rstruct fmap_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma Rle_pos_r : forall x y p,
    (x <= y -> x <= y + pos p)%R.
Proof.
  intros x y p Hxy.
  apply Rle_trans with (y + 0)%R.
  rewrite Rplus_0_r;assumption.
  clear x Hxy.
  apply Rplus_le_compat_l, Rlt_le, cond_pos.
Qed.
