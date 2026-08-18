From ltl Require Import ltl ltl_fixpoints ltl_now.

Section ltl_adequacy.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.
  Notation tProp := (tProp S L Rel).

  Import tProp.

  Lemma ltl_adequate (P Q : tProp) :
    (P ⊢ Q)%I ≡ (∀ tr, P tr → Q tr).
  Proof.
    split.
    - intros. apply H. done.
    - intros. done.
  Qed.

  Lemma ltl_next_adequate (P : tProp) tr :
    (○ P)%I tr ≡ P (wf_tail tr).
  Proof. rewrite ltl_next_unseal. done. Qed.

  Lemma ltl_next_iter_adequate n (P : tProp) tr :
    (○^n P)%I tr ≡ P (wf_after n tr).
  Proof.
    revert tr P. induction n; intros tr P.
    { simpl. rewrite wf_after_0. done. }
    simpl. replace (Datatypes.S n) with (n + 1) by lia.
    rewrite wf_after_sum.
    rewrite ltl_next_adequate. rewrite -IHn. done.
  Qed.

  Lemma ltl_always_adequate (P : tProp) tr :
    (□ P)%I tr ≡ ∀ n, P (wf_after n tr).
  Proof.
    rewrite bi_intuitionistically_unseal'. rewrite ltl_always_unseal.
    rewrite /ltl_always_def. unseal.
    split.
    - intros.
      specialize (H n). simpl in *.
      revert P tr H.
      induction n; intros P tr H.
      { simpl in *. rewrite wf_after_0. done. }
      simpl in *. rewrite ltl_next_adequate in H.
      apply IHn in H.
      (* rewrite -wf_after_sum in H. *)
      replace (Datatypes.S n) with (n + 1) by lia.
      rewrite wf_after_sum. done.
    - intros H n.
      specialize (H n).
      revert tr P H.
      induction n; intros tr P H.
      { simpl in *. rewrite wf_after_0 in H. done. }
      apply ltl_next_iter_S.
      apply IHn.
      rewrite ltl_next_adequate.
      replace (Datatypes.S n) with (1 + n) in H by lia.
      rewrite wf_after_sum in H. done.
  Qed.

  Lemma ltl_eventually_next_equiv (P : tProp) :
    (◊ P)%I ≡ (∃ n : nat, ltl_next_iter n P)%I.
  Proof.
    iSplit.
    - iApply ltl_eventually_ind.
      { iIntros "HP". iExists 0. done. }
      iIntros "[HP IH]".
      rewrite ltl_next_exists.
      iDestruct "IH" as (n) "IH".
      iExists (Datatypes.S n).
      simpl.
      iIntros "!>".
      done.
    - iDestruct 1 as (x) "H".
      iInduction x as [|n Hn].
      { iModIntro. done. }
      iApply ltl_next_eventually.
      simpl. iModIntro.
      by iApply "Hn".
  Qed.

  (* TODO: Clean up this proof *)
  Lemma ltl_eventually_adequate_1 (P : tProp) tr :
    (∃ n, P (wf_after n tr)) → (◊ P)%I tr.
  Proof. 
    intros H.
    apply ltl_eventually_next_equiv.
    destruct H as [n Hn].
    unseal. exists n.
    revert tr P Hn.
    induction n; intros tr P Hn.
    { rewrite wf_after_0 in Hn. simpl. done. }
    apply ltl_next_iter_S. apply IHn.
    rewrite ltl_next_adequate.
    replace (Datatypes.S n) with (1+n) in Hn by lia.
    rewrite wf_after_sum in Hn. done.
  Qed.

  Lemma ltl_eventually_adequate_2 (P : tProp) :
    (◊ P)%I ⊢ ∃ n : nat, ltl_next_iter n P.
  Proof.
    iApply ltl_eventually_ind.
    { iIntros "HP". iExists 0. done. }
    iIntros "[HP IH]".
    rewrite ltl_next_exists.
    iDestruct "IH" as (n) "IH".
    iExists (Datatypes.S n).
    simpl.
    iIntros "!>".
    done.
  Qed.

  Lemma ltl_eventually_adequate (P : tProp) tr :
    (◊ P)%I tr ≡ ∃ n, P (wf_after n tr).
  Proof.
    split; [|apply ltl_eventually_adequate_1].
    intros.
    apply ltl_eventually_adequate_2 in H.
    revert H. unseal. intros H. destruct H as [n Hn].
    revert tr Hn.
    induction n; intros tr Hn.
    { exists 0. by rewrite wf_after_0. }
    simpl in *.
    rewrite ltl_next_adequate in Hn.
    apply IHn in Hn.
    destruct Hn as [m Hn].
    exists (Datatypes.S m).
    replace (Datatypes.S m) with (m + 1) by lia.
    rewrite wf_after_sum. done.
  Qed.

  Lemma ltl_now_adequate P (tr : wf_trace S L Rel) :
    (↓ P)%I tr ≡ P $ head_trace (tr_car tr).
  Proof.
    rewrite ltl_now_unseal. split.
    - intros. simplify_eq; done.
    - intros. destruct tr as [[[]|]]; done.
  Qed.

  Lemma ltl_now_f_adequate {A} f (x : A) (tr : wf_trace S L Rel) :
    (↓fs f x)%I tr ≡ (f <$> (fst <$> head_trace (tr_car tr)) = Some x).
  Proof.
    rewrite ltl_now_adequate.
    split.
    - intros. destruct tr as [[[]|]]; simpl in *; simplify_eq; try eauto; try done.
    - intros. destruct tr as [[[]|]]; inversion H; simplify_eq; try eauto; try done.
  Qed.

  Lemma ltl_now_label_f_adequate {A} f (x : A) (tr : wf_trace S L Rel) :
    (↓fl f x)%I tr ≡ (f <$> mjoin (snd <$> head_trace (tr_car tr)) = Some x).
  Proof.
    rewrite ltl_now_adequate.
    split.
    - intros. destruct tr as [[[]|]]; simpl in *; simplify_eq; try eauto; try done.
    - intros. destruct tr as [[[]|]]; inversion H; simplify_eq; try eauto; try done.
  Qed.

End ltl_adequacy.

Ltac adequacy_unseal_core := 
  try rewrite !ltl_impl_unseal /ltl_impl_def;
  try rewrite !ltl_and_unseal /ltl_and_def;
  try rewrite !ltl_always_adequate;
  try rewrite ltl_next_unseal /ltl_next_def;
  try setoid_rewrite ltl_eventually_adequate;
  try setoid_rewrite ltl_now_f_adequate;
  try setoid_rewrite ltl_now_label_f_adequate;
  try setoid_rewrite ltl_now_adequate.

Ltac adequacy_unseal :=
  rewrite ltl_adequate; adequacy_unseal_core.

Ltac adequacy_unseal_goal :=
  rewrite ltl_adequate; try (intros ?tr); adequacy_unseal_core.
