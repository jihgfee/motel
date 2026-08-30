From Stdlib.Logic Require Import ClassicalFacts.
From ltl Require Import ltl ltl_fixpoints ltl_now ltl_adequacy.

Axiom excluded_middle : ∀ P, P ∨ ¬ P.

Axiom choice :
  ∀ A B (R : A → B → Prop), (∀ x, ∃ y, R x y) → {f : A → B | ∀ x, R x (f x)}.

Definition epsilon {A : Type} {P : A → Prop} (Hex : ∃ x, P x) : A :=
  proj1_sig (choice unit A (λ _ x, P x) (λ _, Hex)) tt.

Lemma make_decision P : Decision P.
Proof.
  assert (∃ x : Decision P, True) as Hdecex.
  { destruct (excluded_middle P) as [HP|HnP].
    - exists (left HP); done.
    - exists (right HnP); done. }
  apply epsilon in Hdecex; done.
Qed.

Section classical.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Import tProp.

  Lemma ltl_excluded_middle (P : tProp) :
    ⊢ P ∨ ¬ P.
  Proof.
    econstructor. intros.
    pose proof (excluded_middle (P tr)).
    unseal. done.
  Qed.

  Lemma ltl_until_not_until (P Q : tProp) :
    P ∪ Q ⊢ (P ∧ ¬ Q) ∪ Q.
  Proof.
    iDestruct (ltl_excluded_middle Q) as "[HQ|HQ]".
    { iIntros "H".
      iEval (rewrite ltl_until_unfold).
      iLeft. done. }
    iIntros "H". iRevert "HQ".
    iApply (ltl_until_ind_strong with "[] H").
    iIntros "!> [HQ|(HP&HPQ&IH)] HQ'".
    { by rewrite -ltl_until_intro_now. }
    iEval (rewrite ltl_until_unfold).
    iRight.
    iFrame "HP". iFrame.
    iModIntro.
    iDestruct (ltl_excluded_middle Q) as "[HQ|HQ]".
    { iEval (rewrite ltl_until_unfold). iLeft. done. }
    by iApply "IH".
  Qed.

  Lemma ltl_neg_neg (P : tProp) :
    ¬ ¬ P ⊢ P.
  Proof.
    iIntros "HP".
    iPoseProof (ltl_excluded_middle P) as "[$|HP']".
    iExFalso. iApply "HP". done.
  Qed.

  Lemma ltl_always_not_eventually_not (P : tProp) :
    (□ P)%I ≡ (¬ (◊ (¬ P)))%I.
  Proof.
    iSplit.
    - iIntros "#HP HP'".
      iMod "HP'".
      iApply "HP'". done.
    - iIntros "HP".
      rewrite ltl_not_eventually_always_not.
      iDestruct "HP" as "#HP".
      iModIntro.
      by iApply ltl_neg_neg.
  Qed.

  Lemma ltl_eventually_not_always_not (P : tProp) :
    (◊ P)%I ≡ (¬ (□ (¬ P)))%I.
  Proof.
    iSplit.
    - rewrite ltl_always_unseal'.
      rewrite !ltl_eventually_next_equiv.
      iIntros "[%n HP]".
      iIntros "HP'". iSpecialize ("HP'" $! n).
      rewrite -ltl_iter_next_not. iApply "HP'". done.
    - iIntros "HP".      
      rewrite -ltl_not_eventually_always_not.
      by iApply ltl_neg_neg.
  Qed.

  Lemma ltl_terminates_dec :
    ⊢@{tProp} ◊ ↯ ∨ ∞.
  Proof.
    iDestruct (ltl_excluded_middle (◊ ↯))%I as "[?|?]"; [by iLeft|].
    iRight. rewrite ltl_not_eventually_always_not. done.
  Qed.

  Lemma inf_live_strong b :
    (∀ s b' s', Rel s b' s' → ∃ s', Rel s b s') →
    ∞ ⊢@{tProp} (□ ◊ is_live b)%I.
  Proof.
    iIntros (Hrel) "#H !>".
    rewrite /ltl_terminated. rewrite ltl_now_not.
    iDestruct (ltl_st with "H") as (s) "Hs".
    { intros. destruct osl; done. }
    iModIntro.
    iAssert (⌜∃ b s', Rel s b s'⌝)%I as %(?&?&?).
    { assert (reducible Rel s ∨ ¬ reducible Rel s) as [(?&?&Hred)|Hred];
        [|iPureIntro; eexists _,_; eauto|].
      { apply excluded_middle. }
      iDestruct (trace_terminates with "Hs") as "Hs"; [done|].
      iExFalso.
      rewrite -ltl_false_next. iModIntro.
      iCombine "Hs H" as "Hs".
      iDestruct (ltl_now_pure with "Hs") as %[??].
      destruct x as [[]|]; simpl in *; try naive_solver; destruct H; simplify_eq. }
    iApply (ltl_now_mono with "Hs").
    intros. simpl.
    destruct osl as [[]|]; simpl in *; simplify_eq; [|naive_solver].
    eapply Hrel.
    apply H.
  Qed.

End classical.
