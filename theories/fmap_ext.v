From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.finmap Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fmap_scope.
Open Scope fset_scope.

(** * General utility lemmas for finite maps *)

Section CheckAllFmap.

Variables (V : Type) (I : choiceType).

Variable P : pred V.

Variable f : {fmap I -> V}.

Section AllFs.

Variable s : {fset I}.

(** Check the predicate [P] on given domain elements in the map [f]. *)
Definition allfs :=
 \big[andb/true]_(i <- s) (if f.[? i] is Some v then P v else true).

Lemma allfsP : reflect (forall (i : I) (h : i \in domf f), i \in s -> P f.[h]) allfs.
Proof.
apply: (iffP idP); last first.
  rewrite /allfs big_seq.
  elim/big_ind: _ => //; last first.
    move => i Hs Hi.
    case Hf: (i \in domf f); last by rewrite not_fnd // Hf.
    rewrite (in_fnd Hf).
    exact: Hi.
  move => x y Hx Hy Hp.
  by apply/andP; split; [apply Hx|apply Hy].
move => Hb i Hi Hs.
case Hp: (P _) => //.
have Hip: f.[? i] = Some f.[Hi] by apply: in_fnd.
move: Hb.
set B : pred I := fun j => j == i.
rewrite /allfs (big_fsetID _ B) /=.
move/andP => [Ha Hb].
move: Ha.
rewrite /B /=.
suff Hsuff: [fset x | x in s & x == i] = [fset i].
  by rewrite Hsuff big_seq_fset1 (in_fnd Hi) Hp.
apply/fsetP => x.
rewrite inE in_fsetE /= inE.
apply/idP/idP; first by move/andP; case.
by move/eqP =>->; rewrite Hs; apply/andP.
Qed.

End AllFs.

Definition allf := allfs (domf f).

Lemma allfP : reflect (forall (i : I) (h : i \in domf f), P f.[h]) allf.
Proof.
apply: (iffP idP); last by move => Hf; apply/allfsP.
by move/allfsP => Hf i h; apply: Hf.
Qed.

End CheckAllFmap.

Section UpdateAllFmap.

Variables (V : Type) (I : choiceType).

Variable P : pred V.

Variable f : {fmap I -> V}.

Variable s : {fset I}.

(** Update function parameter for individual values. *)
Variable upd : I -> V -> V.

(** Update values for given elements in map domain. *)
Definition updf' :=
  \big[(@catf _ _)/[fmap]]_(i <- s)
   (if f.[? i] is Some v then [fmap].[i <- upd i v] else [fmap]).

Lemma updf'_update : forall (i : I) (h : i \in domf f),
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

Lemma updf'_s : forall i, i \in domf updf' -> i \in s.
Proof.
rewrite /updf'.
have ->: (\big[catf (V:=V)/[fmap]]_(i0 <- s) match f.[? i0] with | Some v => [fmap].[i0 <- upd i0 v] | None => [fmap] end) =
(\big[catf (V:=V)/[fmap]]_(i0 <- s | i0 \in s) match f.[? i0] with | Some v => [fmap].[i0 <- upd i0 v] | None => [fmap] end).
  by rewrite big_seq.
elim/big_rec: _ => //.
move => i x Ht IH i0.
case Hi0: (i0 \in domf x); first by move => Hi0'; apply: IH.
move/negP/negP: Hi0 => Hi0.
case Hi: (i \in domf f).
  rewrite (in_fnd Hi) /=.
  rewrite fsetU0 /=.
  rewrite in_fsetU.
  case/orP; last by move => Hi0'; case/negP: Hi0.
  rewrite in_fsetD.
  move/andP => [Ha Ha'].
  move: Ha'.
  rewrite in_fset1.
  by move/eqP =>->.
move/negP/negP: Hi => Hi.
rewrite (not_fnd Hi).
rewrite mem_catf.
case/orP => //.
move => Hi0'.
exact: IH.
Qed.

(** Update given domain elements while retaining original mapping for other elements. *)
Definition updf := f + updf'.

Lemma domf_s_updf' : forall i, i \in domf f -> (i \in enum_fset s) = (i \in domf updf').
Proof.
rewrite /updf'.
have Hs := fset_uniq s.
rewrite unlock.
elim: (enum_fset s) Hs => //=.
move => a l IH.
move/andP => [Ha Hu].
move/IH: Hu => {IH} IH.
move => i Hi.
rewrite in_cons in_fsetU.
apply/idP/idP; first case/orP.
- move => Haa.
  move: Hi; move/eqP: Haa=>-> => Hi.
  rewrite -IH //.
  rewrite (in_fnd Hi).
  apply/orP; left.
  rewrite in_fsetD.
  apply/andP; split; last by rewrite /= fsetU0 in_fset1.
  move: Ha.
  by rewrite IH.
- move => Hf.
  apply/orP; right.
  by rewrite -IH.
- case/orP; last first.
    rewrite -IH //.
    by move =>->; rewrite orbT.
  rewrite in_fsetD.
  rewrite -IH //.
  move/andP => [Hd Hf].
  case Hia: (i == a); first by rewrite orbC orbT.
  move/negP: Hia; case.
  move: Hf.
  case Haa: (a \in domf f); first by rewrite (in_fnd Haa) /= fsetU0 in_fset1.
  move/negP/negP: Haa => Haa.
  by rewrite (not_fnd Haa).
Qed.

Lemma updf_update : forall (i : I) (h : i \in domf f),
  i \in s -> updf.[? i] = Some (upd i f.[h]).
Proof.
move => i h Hi.
rewrite /updf fnd_cat.
case: ifP; first by move => Hi'; apply: updf'_update.
move/negP; case.
by rewrite -domf_s_updf'.
Qed.

Lemma updf_update' : forall (i : I) (h : i \in domf f),
  i \notin s -> updf.[? i] = Some f.[h].
Proof.
move => i h Hi.
rewrite /updf.
rewrite fnd_cat.
case: ifP; first by move/updf'_s; move/negP: Hi.
move/negP/negP.
rewrite -domf_s_updf' // => Hs.
by rewrite in_fnd.
Qed.

Lemma updf_domf : domf f = domf updf.
Proof.
apply/fsetP => x; apply/idP/idP.
  move => Hx.
  rewrite /updf domf_cat in_fsetU.
  by apply/orP; left.
rewrite /updf domf_cat in_fsetU; case/orP => Hx //.
exact: updf'_domf.
Qed.
    
End UpdateAllFmap.

Section SetFs.

Variables (K : choiceType) (V : eqType).

Variable (default : K -> V).

Definition setfs_fmap (fm : {fmap K -> V}) (k : K) (v : V) : {fmap K -> V} :=
if v == default k then if k \in fm then fm.[~ k] else fm
else fm.[k <- v].

Lemma setfs_not_default_remove (fs: {fsfun K -> V for default}) (k : K) (v : V) :
 [forall k0, (setfs_fmap (fmap_of_fsfun fs) k v) k0 != default (fsval k0)].
Proof.
case: fs => fs /=.
move/forallP => Hx.
apply/forallP.
rewrite /= /setfs_fmap.
case Heq: (v == default k).
  move/eqP: Heq => Heq.
  case Hif: (k \in fs) => //.
  case => k' Hk.
  move: (Hk) => Hk'.
  simpl in Hk.
  rewrite mem_remf1 in Hk.
  move/andP: Hk => [Hkk' Hk].
  apply/eqP.
  have Hxx := (Hx (FSetSub Hk)).
  rewrite /= in Hxx.
  rewrite [default _]/= => Hd.
  case/eqP: Hxx.
  rewrite -Hd.
  suff Hsuff: Some fs.[Hk] = Some (fs.[~ k] [` Hk']) by case: Hsuff.
  by rewrite -2!in_fnd fnd_rem1 Hkk'.
move/eqP: Heq => Heq x.
rewrite ffunE.
apply/eqP => Heqx.
move: Heqx.
case Heqk: (eqtype.val x == k); first by move/eqP: Heqk =>->.
move/eqP => /= Heqx.
move/eqP: Heqk => Heqk.
move: x Heqx Heqk => /=.
case => /= k0.
rewrite in_fsetU in_fset1.
case/orP; first by move/eqP.
move => Hk0 /eqP => Heqv Heqk.
have Hxx := (Hx (FSetSub Hk0)).
case/eqP: Hxx.
rewrite /= -Heqv /odflt /= /oapp.
by rewrite (in_fnd Hk0).
Qed.

Definition setfs (fs: {fsfun K -> V for default}) (k : K) (v : V) : {fsfun K -> V for default} :=
@Fsfun K V default (setfs_fmap (fmap_of_fsfun fs) k v) (setfs_not_default_remove _ _ _).

Local Arguments Fsfun : clear implicits.

Lemma getfs_set (fs: {fsfun K -> V for default}) (k : K) (v : V) :
 setfs fs k v k = v.
Proof.
case: fs => fm /=; rewrite /setfs /= => i.
move: (setfs_not_default_remove _ _ _) => /=.
rewrite /setfs_fmap /=.
case Heq: (v == default k); first case Hk: (k \in fm).
- move => Hkk.
  move/eqP: Heq =>->.
  rewrite /fun_of_fsfun /fmap_of_fsfun /=.
  rewrite /odflt /oapp /= not_fnd //=.
  rewrite inE /=.
  rewrite in_fsetE /= inE.
  apply/negP => Hmem.
  move/andP: Hmem => [Hmem Hmemk].
  move: Hmemk.
  rewrite in_fsetD inE /=.
  move/andP => [Heqk Hdomf].
  by move/eqP: Heqk.
- move => Hkk.
  move/eqP: Heq =>->.
  rewrite /fun_of_fsfun /fmap_of_fsfun /=.
  rewrite /odflt /oapp /= not_fnd //=.
  by rewrite Hk.
- move => Hkk.
  rewrite /fun_of_fsfun.
  rewrite in_fnd /=.
    rewrite inE /=.
    apply/orP.
    left.
    by rewrite in_fset1.
  move => Hk.
  rewrite ffunE /=.
  case Heqk: (k == k) => //.
  by move/eqP: Heqk.
Qed.

Lemma setfs_get (fs: {fsfun K -> V for default}) (k : K) :
 setfs fs k (fs k) = fs.
Proof.
case: fs => fm Hfm.
apply/fsfunP => k0.
rewrite /setfs /= /setfs_fmap /=.
rewrite /fun_of_fsfun /=.
rewrite /odflt /= /oapp.
case Hkk: (k \in fm).
  rewrite (in_fnd Hkk).
  move/forallP: Hfm => Hx.
  move: (Hx (FSetSub Hkk)) => {Hx}.
  rewrite /=.
  case Heqd: (_ == _) => // _.
  case Hk0: (k0 \in fm).
    rewrite fnd_set.
    rewrite (in_fnd Hk0).
    case Hkk0: (k0 == k) => //.
    move/eqP: Hkk0 => Hkk0.
    move => {Heqd}.
    move: (Hkk) (Hk0).
    rewrite Hkk0.
    exact: eq_getf.
  rewrite fnd_set.
  case Heqk: (_ == _) => //.
  move/eqP: Heqk (Hkk) (Hk0) => Heqk {Heqd}.
  by rewrite -Heqk Hk0 in Hkk.
move/negP/negP: Hkk => Hkk.
rewrite (not_fnd Hkk).
case Hd: (_ == _) => //.
by move/eqP: Hd.
Qed.

Lemma setfsNK (fs: {fsfun K -> V for default}) (k k' : K) (v : V) :
 setfs fs k v k' = if k' == k then v else fs k'.
Proof.
case Hk: (k' == k); first by move/eqP: Hk =>->; rewrite getfs_set.
case: fs => fm /=; rewrite /setfs /= => i.
move: (setfs_not_default_remove _ _ _) => /=.
rewrite /setfs_fmap /=.
case Heq: (v == default k); first case Hkk: (k \in fm).
- move => Hk0.
  rewrite /fun_of_fsfun /fmap_of_fsfun /=.
  case Hkk': (k' \in fm).
    rewrite (in_fnd Hkk') /=.
    rewrite in_fnd /=; first by rewrite inE /= inE in_fsetD1 Hkk' Hk.
    move => Hkk''.
    set fm' := [ffun x => _].
    suff Hsuff: Some fm'.[Hkk''] = Some (fm.[Hkk']) by case: Hsuff.
    by rewrite -2!in_fnd fnd_rem1 Hk.
  move/negP/negP: Hkk' => Hkk'.
  rewrite (not_fnd Hkk') /=.
  rewrite not_fnd //.
  rewrite /finmap_of_finfun /= inE /=.
  rewrite in_fsetE /= inE in_fsetD1 /=.
  apply/andP => Hk'.
  move: Hk' => [Hk1 Hk2].
  move: Hk2.
  move/andP => [Heqk Hdk].
  by rewrite Hdk in Hkk'.
- by move => Hkk'.
- move => Hkk'.
  rewrite /fun_of_fsfun /fmap_of_fsfun /=.
  case Hk': (k' \in fm).
    rewrite (in_fnd Hk') /=.
    rewrite in_fnd /=; first by rewrite in_fset1U Hk' Hk.
    move => Hk'0.
    by rewrite ffunE /= Hk (in_fnd Hk').
  move/negP/negP: Hk' => Hk'.
  rewrite (not_fnd Hk') /=.
  rewrite not_fnd //=.
  by rewrite inE /= in_fset1U /= Hk Hk'.
Qed.

End SetFs.
