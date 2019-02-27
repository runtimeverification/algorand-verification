From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.
Open Scope fset_scope.

Section CheckAllFmap.

Variable (R : Type).

Variable (I : choiceType).

Variable P : pred R.

Variable f : {fmap I -> R}.

Lemma allfmapP :
  reflect
    (forall (i : I) (h : i \in domf f), P f.[h])
    (\big[andb/true]_(i <- domf f) (if f.[? i] is Some v then P v else true)).
Proof.
apply: (iffP idP); last first.
- elim/big_ind: _ => //; last first.
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
  rewrite (big_fsetID _ B) /=.
  move/andP => [Ha Hb].
  move: Ha.
  rewrite /B /=.
  suff Hsuff: [fset x | x in domf f & x == i] = [fset i].
    rewrite Hsuff.
    rewrite big_seq_fset1.
    by rewrite (in_fnd Hi) Hp.
  apply/fsetP.
  move => x.
  rewrite inE.
  rewrite in_fsetE /=.
  rewrite inE.
  apply/idP/idP.
  * by move/andP; case.
  * move/eqP =>->.
    rewrite Hi.
    by apply/andP.
Qed.

End CheckAllFmap.
