From ltl Require Import trace ltl ltl_fixpoints ltl_now.

Section ltl_adequacy.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.
  Notation tProp' := tProp.
  Notation tProp := (tProp S L Rel).

  Import tProp.

  Lemma ltl_adequate (P Q : tProp) :
    (P ⊢ Q)%I ≡ (∀ tr, trace_maximal Rel tr → P tr → Q tr).
  Proof.
    split.
    - intros ???. apply H. done.
    - intros. done.
  Qed.

  Lemma ltl_next_adequate (P : tProp) tr :
    (○ P)%I tr ≡ P (tail_trace tr).
  Proof. rewrite ltl_next_unseal. done. Qed.

  Lemma trace_tail_after (tr : trace S L) :
    tail_trace tr = after 1 tr.
  Proof. done. Qed.
  
  Lemma trace_tail_after_comm n (tr : trace S L) :
    tail_trace (after n tr) = after n (tail_trace tr).
  Proof. rewrite trace_tail_after after_sum_comm. done. Qed.

  Lemma ltl_next_iter_adequate n (P : tProp) tr :
    (○^n P)%I tr ≡ P (after n tr).
  Proof.
    revert tr P. induction n; intros tr P.
    { simpl. done. }
    replace (Datatypes.S n) with (1 + n) by lia.
    simpl.
    rewrite trace_tail_after.
    rewrite after_sum_comm.
    rewrite ltl_next_adequate. 
    rewrite IHn.
    done.
  Qed.

  Lemma ltl_always_equiv (P : tProp) :
    (□ P)%I ≡ (∀ n, ○^n P)%I.
  Proof. apply ltl_always_unseal'. Qed.

  Lemma ltl_always_adequate (P : tProp) tr :
    (□ P)%I tr ≡ (∀ n, P (after n tr)).
  Proof.
    rewrite bi_intuitionistically_unseal'. rewrite ltl_always_unseal.
    rewrite /ltl_always_def. unseal.
    split.
    - intros H n.
      specialize (H n). simpl in *.
      revert P tr H.
      induction n; intros P tr H.
      { simpl in *. done. }
      simpl in *. rewrite ltl_next_adequate in H.
      apply IHn in H.
      replace (Datatypes.S n) with (n + 1) by lia.
      rewrite trace_tail_after_comm. done.
    - intros H n.
      specialize (H n).
      revert tr P H.
      induction n; intros tr P H.
      { simpl in *. done. }
      apply ltl_next_iter_adequate. done.
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
  Lemma ltl_eventually_adequate_1 (P : tProp) tr (Hwf : trace_maximal Rel tr) :
    (∃ n, P (after n tr)) → (◊ P)%I tr.
  Proof.
    intros H.
    apply ltl_eventually_next_equiv; [done|].
    destruct H as [n Hn].
    unseal. exists n.
    revert tr P Hn Hwf.
    induction n; intros tr P Hn Hwf.
    { simpl. done. }
    apply ltl_next_iter_S; [done|].
    apply IHn; [|done].
    rewrite ltl_next_adequate.
    replace (Datatypes.S n) with (1+n) in Hn by lia.
    rewrite after_sum in Hn. done.
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

  Lemma ltl_eventually_adequate (P : tProp) tr (Hwf : trace_maximal Rel tr):
    (◊ P)%I tr ≡ ∃ n, P (after n tr).
  Proof.
    split; [|by apply ltl_eventually_adequate_1].
    intros.
    apply ltl_eventually_adequate_2 in H; [|done].
    revert H. unseal. intros H. destruct H as [n Hn].
    revert tr Hn Hwf.
    induction n; intros tr Hn Hwf.
    { exists 0. done. }
    simpl in *.
    rewrite ltl_next_adequate in Hn.
    apply IHn in Hn; [|by apply wf_after_tail_wf].
    destruct Hn as [m Hn].
    exists (Datatypes.S m).
    replace (Datatypes.S m) with (m + 1) by lia.
    rewrite after_sum. done.
  Qed.

  Lemma ltl_now_adequate P (tr : trace S L) :
    ((↓ P)%I:tProp) tr ≡ P $ head_trace tr.
  Proof.
    rewrite ltl_now_unseal. split.
    - intros. simplify_eq; done.
    - intros. destruct tr as [[]|]; done.
  Qed.

  Lemma ltl_now_f_adequate {A} f (x : A) (tr : trace S L) :
    ((↓fs f x)%I:tProp) tr ≡ (f <$> (fst <$> head_trace tr) = Some x).
  Proof.
    rewrite ltl_now_adequate.
    split.
    - intros. destruct tr as [[]|]; simpl in *; simplify_eq; try eauto; try done.
    - intros. destruct tr as [[]|]; inversion H; simplify_eq; try eauto; try done.
  Qed.

  Lemma ltl_now_label_f_adequate {A} f (x : A) (tr : trace S L) :
    ((↓fl f x)%I:tProp) tr ≡ (f <$> mjoin (snd <$> head_trace tr) = Some x).
  Proof.
    rewrite ltl_now_adequate.
    split.
    - intros. destruct tr as [[]|]; simpl in *; simplify_eq; try eauto; try done.
    - intros. destruct tr as [[]|]; inversion H; simplify_eq; try eauto; try done.
  Qed.

End ltl_adequacy.

Import tProp.

Tactic Notation "adequacy_unseal" := 
  try rewrite !ltl_impl_unseal /ltl_impl_def;
  try rewrite !ltl_and_unseal /ltl_and_def;
  try setoid_rewrite ltl_always_equiv;
  try setoid_rewrite ltl_eventually_next_equiv;
  try rewrite !ltl_forall_unseal /ltl_forall_def;
  try rewrite !ltl_exist_unseal /ltl_exist_def;
  try rewrite ltl_adequate;
  try setoid_rewrite ltl_next_adequate;
  try setoid_rewrite ltl_next_iter_adequate;
  try setoid_rewrite ltl_now_f_adequate;
  try setoid_rewrite ltl_now_label_f_adequate;
  try setoid_rewrite ltl_now_adequate.
