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

  Lemma ltl_adequate_equiv (P Q : tProp) :
    (P ≡ Q) ≡ (∀ tr, P tr ≡ Q tr).
  Proof.
    split.
    - intros. apply H.
    - intros. constructor. intros. apply H.
  Qed.

  Lemma ltl_next_adequate (P : tProp) tr :
    (○ P)%I tr ≡ P (wf_tail tr).
  Proof. rewrite ltl_next_unseal. done. Qed.

  Lemma ltl_next_iter_adequate n (P : tProp) tr :
    (○^n P)%I tr ≡ P (wf_after n tr).
  Proof.
    revert tr P. induction n; intros tr P.
    { simpl. done. }
    replace (Datatypes.S n) with (n + 1) by lia.
    rewrite wf_after_sum.
    simpl.
    rewrite -IHn.
    replace (n + 1) with (Datatypes.S n) by lia.
    simpl. rewrite ltl_next_adequate. done.
  Qed.

  Lemma ltl_now_adequate P (tr : wf_trace S L Rel) :
    (↓ P)%I tr ≡ P $ wf_head tr.
  Proof.
    rewrite ltl_now_unseal. split.
    - intros. simplify_eq; done.
    - intros. destruct tr as [[[]|]]; done.
  Qed.

  Lemma ltl_now_f_adequate {A} f (x : A) (tr : wf_trace S L Rel) :
    (↓fs f x)%I tr ≡ (f <$> (fst <$> wf_head tr) = Some x).
  Proof.
    rewrite ltl_now_adequate.
    split.
    - intros. destruct tr as [[[]|]]; simpl in *; simplify_eq; try eauto; try done.
    - intros. destruct tr as [[[]|]]; inversion H; simplify_eq; try eauto; try done.
  Qed.

  Lemma ltl_now_label_f_adequate {A} f (x : A) (tr : wf_trace S L Rel) :
    (↓fl f x)%I tr ≡ (f <$> mjoin (snd <$> wf_head tr) = Some x).
  Proof.
    rewrite ltl_now_adequate.
    split.
    - intros. destruct tr as [[[]|]]; simpl in *; simplify_eq; try eauto; try done.
    - intros. destruct tr as [[[]|]]; inversion H; simplify_eq; try eauto; try done.
  Qed.

  Lemma ltl_always_next_equiv (P : tProp) :
    (□ P)%I ≡ (∀ n, ○^n P)%I.
  Proof. by rewrite bi_intuitionistically_unseal ltl_always_unseal. Qed. 
  
  Lemma ltl_always_adequate (P : tProp) tr :
    (□ P)%I tr ≡ ∀ n, P (wf_after n tr).
  Proof.
    etrans; [apply ltl_adequate_equiv; apply ltl_always_next_equiv|].
    setoid_rewrite <-ltl_next_iter_adequate.
    rewrite ltl_forall_unseal.
    done.
  Qed.

  Lemma ltl_eventually_next_equiv (P : tProp) :
    (◊ P)%I ≡ (∃ n : nat, ltl_next_iter n P)%I.
  Proof.
    iSplit.
    - iApply ltl_eventually_ind.
      { iIntros "HP". by iExists 0. }
      iIntros "[_ IH]".
      rewrite ltl_next_exists.
      iDestruct "IH" as (n) "IH".
      by iExists (Datatypes.S n).
    - iDestruct 1 as (n) "H".
      iInduction n as [|n Hn].
      { by iModIntro. }
      iApply ltl_next_eventually.
      simpl. iModIntro.
      by iApply "Hn".
  Qed.

  Lemma ltl_eventually_adequate (P : tProp) tr :
    (◊ P)%I tr ≡ ∃ n, P (wf_after n tr).
  Proof.
    etrans; [apply ltl_adequate_equiv; apply ltl_eventually_next_equiv|].
    setoid_rewrite <-ltl_next_iter_adequate.
    rewrite ltl_exist_unseal.
    done.
  Qed.

End ltl_adequacy.

Import tProp.

(* TODO: Unhack this *)
Ltac adequacy_unseal_core := 
  repeat (
      first
        [rewrite !ltl_impl_unseal /ltl_impl_def |
          rewrite !ltl_and_unseal /ltl_and_def |
          setoid_rewrite ltl_always_adequate |
          rewrite ltl_next_unseal /ltl_next_def |
          setoid_rewrite ltl_eventually_adequate |
          rewrite ltl_forall_unseal /ltl_forall_def |
          rewrite ltl_exist_unseal /ltl_exist_def |
          setoid_rewrite ltl_now_f_adequate |
          setoid_rewrite ltl_now_label_f_adequate |
          setoid_rewrite ltl_now_adequate]).

Ltac adequacy_unseal :=
  rewrite ltl_adequate; adequacy_unseal_core.

Ltac adequacy_unseal_goal :=
  rewrite ltl_adequate; try (intros ?tr); adequacy_unseal_core.
