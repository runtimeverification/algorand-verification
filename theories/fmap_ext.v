
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.

From mathcomp.finmap Require Import order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.
Open Scope fset_scope.

Section CheckAllFmap.

Variable (V : Type).

Variable (I : choiceType).

Variable P : pred V.

Variable f : {fmap I -> V}.

Definition allf :=
 \big[andb/true]_(i <- domf f) (if f.[? i] is Some v then P v else true).

Lemma allfP : reflect (forall (i : I) (h : i \in domf f), P f.[h]) allf.
Proof.
apply: (iffP idP); last first.
- rewrite /allf.
  elim/big_ind: _ => //; last first.
  * move => i Ht Hi.
    case Hf: (i \in domf f); last by rewrite not_fnd // Hf.
    rewrite (in_fnd Hf).
    exact: Hi.
  * move => x y Hx Hy Hp.
    apply/andP.
    split.
    + exact: Hx.
    + exact: Hy.
- move => Hb i Hi.
  case Hp: (P _) => //.
  have Hip: f.[? i] = Some f.[Hi] by apply: in_fnd.
  move: Hb.
  set B : pred I := fun j => j == i.
  rewrite /allf (big_fsetID _ B) /=.
  move/andP => [Ha Hb].
  move: Ha.
  rewrite /B /=.
  suff Hsuff: [fset x | x in domf f & x == i] = [fset i].
    rewrite Hsuff.
    rewrite big_seq_fset1.
    by rewrite (in_fnd Hi) Hp.
  apply/fsetP => x.
  rewrite inE in_fsetE /= inE.
  apply/idP/idP; first by move/andP; case.
  by move/eqP =>->; rewrite Hi; apply/andP.
Qed.

Variable upd : I -> V -> V.

Definition updf :=
  \big[(@catf _ _)/f]_(i <- domf f)
   (if f.[? i] is Some v then [fmap].[i <- upd i v] else [fmap]).

Definition updf' :=
  \big[(@catf _ _)/[fmap]]_(i <- domf f)
   (if f.[? i] is Some v then [fmap].[i <- upd i v] else [fmap]).

(*
Definition updf :=
  \big[(@catf _ _)/f]_(i <- domf f)
   (if f.[? i] is Some v then [fmap].[i <- upd i v] else [fmap]).
*)

Lemma updf_domf : domf f = domf updf.
Proof.
rewrite /updf.
elim/big_rec: _ => //.
move => i x Hd Hf.
case Hi: (i \in domf f).
  rewrite (in_fnd Hi) domf_cat -Hf /=.
  by rewrite -fsetUA fset0U mem_fset1U.
move/negP/idP: Hi => Hi.
by rewrite not_fnd // cat0f.
Qed.

Variable s : {fset I}.

Definition updf'' :=
  \big[(@catf _ _)/f]_(i <- s)
   (if f.[? i] is Some v then [fmap].[i <- upd i v] else [fmap]).

(*
Lemma updf''_update :
  forall g (i : I) (h : i \in s),
    i \in domf updf -> updf.[? i] = Some (upd i f.[h]).
Proof.
rewrite /updf.
elim/big_rec: _.
*)

(*
Lemma updf_update :
  forall (i : I) (h : i \in domf f),
    i \in domf updf -> updf.[? i] = Some (upd i f.[h]).
Proof.
move => i h.
rewrite /updf.
elim/big_rec: _.
*)

Lemma updf'_update :
  forall (i : I) (h : i \in domf f),
    i \in domf updf' -> updf'.[? i] = Some (upd i f.[h]).
Proof.
rewrite /updf'.
elim/big_rec: _.
  move => i h.
  by rewrite /= in_fset0.
move => i x Ht IH i0 h.
case Hi: (i0 == i).
  move/eqP: Hi =><-.
  rewrite (in_fnd h) => Hi.
  rewrite /= fsetU0 in Hi.   
  rewrite catf_setl.
  case: ifP => Hx'.
    rewrite cat0f.
    exact: IH.
  rewrite cat0f.
    move/negP/negP: Hx' => Hx'.
    rewrite in_fnd.
      rewrite dom_setf in_fsetU.
      apply/orP.
      left.
      by rewrite in_fset1.
    move => h'.
    by rewrite getf_set.
have IH' := IH _ h.
move/eqP: Hi => Hi.
case Hii: (i \in domf f). 
  rewrite (in_fnd Hii).
  rewrite [domf _]/=.
  rewrite {1}fsetU0.
  rewrite in_fsetU.
  case/orP.
    rewrite in_fsetD.
    move/andP => [H1 H2].
    move: H2 Hi.
    rewrite in_fset1.
    by move/eqP.
 move => Hi0.
 have IH'' := IH' Hi0.
 rewrite -IH''.
 rewrite fnd_cat.
 case: ifP => //.
 by rewrite Hi0.
move/negP/negP: Hii => Hii.
by rewrite (not_fnd Hii) cat0f.
Qed.

Lemma updf'_domf : forall i, i \in domf updf' -> i \in domf f.
Proof.
rewrite /updf'.
elim/big_rec: _ => //.
move => i x Ht IH i0.
case Hi0: (i == i0).
  move/eqP: Hi0 =>->.
  rewrite mem_catf.
  case/orP; last by exact: IH.
  case Hi0: (i0 \in domf f) => //.
  move/negP/negP: Hi0 => Hi0.
  by rewrite (not_fnd Hi0).
rewrite mem_catf.
case/orP; last by exact: IH.
case Hi: (i \in domf f).
  rewrite (in_fnd Hi) mem_setf /= inE.
  move/eqP => Hii.
  move: Hi0.
  by rewrite Hii.
move/negP/negP: Hi => Hi.
by rewrite (not_fnd Hi).
Qed.

(*
Lemma updf'_domf : domf f = domf updf'.
Proof.
rewrite /updf'.
elim/big_ind: _ => //.
move => i x Hd Hf.
case Hi: (i \in domf f).
  rewrite (in_fnd Hi) domf_cat -Hf /=.
  by rewrite -fsetUA fset0U mem_fset1U.
move/negP/idP: Hi => Hi.
by rewrite not_fnd // cat0f.
Qed.
*)
    
End CheckAllFmap.
