From motel Require Import ltl ltl_fixpoints ltl_now ltl_adequacy.

Import tProp.

Section examples.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Lemma propositional_primer (P Q R : tProp) : ⊢ (P → Q) → (Q → R) → P → R.
  Proof. iIntros "HPQ HQR HP". iDestruct ("HPQ" with "HP") as "HQ". iApply "HQR". done. Qed.

  Lemma globally_primer (P Q : tProp) : ⊢ □ (P → Q) → □ P → Q → □ Q.
  Proof. iIntros "#HPQ #HP HQ". iModIntro. iApply "HPQ". done. Qed.

  Lemma next_primer (P Q R : tProp) : ⊢ □ ○ (P → Q) → ○ P → Q → ○ R → ○ Q.
  Proof. iIntros "#HPQ HP HQ HR". iModIntro. iApply "HPQ". done. Qed.

  Lemma eventually_primer (P Q : tProp) : ⊢ □ (P → ○ ◊ Q) → ◊ P →  ○ ◊ Q.
  Proof. iIntros "#HPQ HP". iMod "HP". iApply "HPQ". done. Qed.

  Lemma eventually_primer' (P Q R : tProp) : ⊢ □ (P → □ ◊ Q) → ◊ P → ◊ R →  □ ◊ Q.
  Proof. iIntros "#HPQ HP HR". iMod "HP". iApply "HPQ". done. Qed.

  Lemma eventually_primer'' (P1 P2 Q1 Q2 : tProp) :
    (□ (P1 → □ P2)) ∧ (□ (Q1 → □ Q2)) ⊢ ◊ P1 → ◊ Q1 → ◊ □ (P2 ∧ Q2).
  Proof.
    iIntros "[#HP' #HQ'] HP HQ".
    iCombine "HP HQ" as "[HPQ|HPQ]".
    - iMod "HPQ" as "[HP HQ]". iDestruct ("HP'" with "HP") as "#HP''".
      iMod "HQ". iDestruct ("HQ'" with "HQ") as "#HQ''".
      iModIntro. iModIntro. iFrame "#".
    - iMod "HPQ" as "[HP HQ]". iDestruct ("HQ'" with "HQ") as "#HQ''".
      iMod "HP". iDestruct ("HP'" with "HP") as "#HP''".
      iModIntro. iModIntro. iFrame "#".
  Qed.

  Lemma until_primer (P Q R : tProp) :
    ⊢ □ (R → P ∪ Q) → (○ P ∪ ○ R) → ◊ ○ R → ○ (P ∪ Q).
  Proof. iIntros "#HPQ HP HR". iMod "HP". iModIntro. iApply "HPQ". done. Qed.

  Lemma until_primer' (P P' Q R : tProp) :
    ⊢ □ (R → P' ∪ Q) → □ (P → P') → (○ P ∪ ○ R) → ◊ ○ R → ○ (P' ∪ Q).
  Proof.
    iIntros "#HPQ #HP' HP HR".
    iDestruct (ltl_until_mono_strong _ (○ P') _ (○ R) with "[] [] HP") as "HP".
    { iIntros "!>HP!>". by iApply "HP'". }
    { eauto. }
    iMod "HP". iModIntro. by iApply "HPQ".
  Qed.

  Lemma induction_example (P Q : tProp) :
    ⊢ □ P → ◊ Q → P ∪ Q.
  Proof.
    iIntros "#HP HQ".
    iApply (ltl_eventually_ind_strong with "[] HQ").
    iIntros "!> [HQ|[H IH]]".
    { iModIntro. iFrame. }
    iEval (rewrite ltl_until_unfold).
    iRight. iFrame "#". iModIntro. done.
  Qed.

  Lemma induction_example' (P Q R : tProp) :
    ⊢  □ (P → ○ Q) → □ (Q → ○ P) → ◊ R → P → (P ∨ Q) ∪ R.
  Proof.
    iIntros "#HPQ #HQP HR HP".
    iAssert (P ∨ Q)%I with "[$HP]" as "HP".
    iRevert "HP".
    iApply (ltl_eventually_ind_strong with "[] HR").
    iIntros "!> [HQ|[H IH]] HP".
    { iModIntro. iFrame. }
    iEval (rewrite ltl_until_unfold).
    iRight. iSplit; [done|].
    iDestruct "HP" as "[HP|HQ]".
    - iDestruct ("HPQ" with "HP") as "HQ". iModIntro. iApply "IH". iRight. done.
    - iDestruct ("HQP" with "HQ") as "HP". iModIntro. iApply "IH". iLeft. done.
  Qed.

  Lemma running_example (P Q : tProp) : ⊢ □ (P → ○ ◊ Q) → ◊ P → ○ ◊ Q.
  Proof. iIntros "#HPQ HP". iMod "HP". by iApply "HPQ". Qed.

  Lemma running_example' (P Q R : tProp) :
    ⊢ □ (P → ○ ◊ Q) → □ (Q → ○ ◊ R) → ◊ P → ○ ○ ◊ R.
  Proof.
    iIntros "#HPQ #HQR HP". iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
    iModIntro. iMod "HQ". by iApply "HQR".
  Qed.

  Lemma ltl_always_eventually_intro (P Q : tProp) :
    (P ⊢ ○◊ (P ∧ Q)) → (P ⊢ □◊ Q).
  Proof.
    iIntros (HPQ) "HP".
    iAssert (□ ◊ (P ∧ Q))%I with "[-]" as "[_ $]".
    iApply (ltl_always_intro with "[] [HP]"); last first.
    { iDestruct (HPQ with "HP") as "HP". by rewrite ltl_next_eventually. }
    iIntros "!> [HP _]". iMod "HP". by iApply HPQ.
  Qed.

  Lemma ltl_always_eventually_intro_strong (P : tProp) :
    □ (P → ○◊ P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iApply (ltl_always_intro with "[] [HP2]"); last first.
    { by iApply ltl_eventually_intro_now. }
    iIntros "!> HP". iApply ltl_eventually_next_comm.
    iMod "HP". iDestruct ("HP1" with "HP") as "HP". by iModIntro.
  Qed.

  Lemma always_eventually_example (P Q : tProp) :
    □ P ∧ ◊ (P → ○ ◊ Q) ⊢ ◊ Q.
  Proof.
    iIntros "[#HP HPQ]".
    iMod "HPQ" as "HPQ".
    iApply ltl_next_eventually.
    by iApply ("HPQ" with "HP").
  Qed.

  Lemma every_other_example (P : tProp) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iAssert (□ (P ∨ (○P)))%I with "[HP1 HP2]" as "#H".
    { iApply (ltl_always_intro with "[] [HP2]"); last first.
      { by iLeft. }
      iIntros "!> [HP|HP]".
      + iDestruct ("HP1" with "HP") as "HP".
        iIntros "!>". by iRight.
      + iIntros "!>". by iLeft. }
    iIntros "!>".
    iDestruct "H" as "[H|H]".
    - by iApply ltl_eventually_intro_now.
    - iApply ltl_next_eventually.
      iIntros "!>".
      by iApply ltl_eventually_intro_now.
  Qed.

  Lemma every_other_example_alt (P : tProp) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iApply ltl_always_eventually_intro_strong. iFrame.
    iIntros "!> HP".
    iDestruct ("HP1" with "HP") as "HP".
    iIntros "!>". by iApply ltl_eventually_intro_next.
  Qed.

  Lemma advanced_example (P Q R : tProp) :
    ○ P ∧ □ ○ (P → □ Q) ∧ ◊ ○ (Q → R) ⊢ ○ ◊ R.
  Proof.
    iIntros "(HP & #HPQ & HQR)".
    iModIntro.
    iDestruct ("HPQ" with "HP") as "#HQ".
    iMod "HQR".
    iDestruct ("HQR" with "HQ") as "HR".
    by iModIntro.
  Qed.

  Lemma quantifier_example (P Q R : nat → tProp) :
    ○ (∃ n, P n) ∧ □ ○ (∀ n, P n → ∃ m, □ Q m) ∧
    ◊ ○ (∀ m, Q m → ∃ k, R k) ⊢ ○ ◊ ∃ k, R k.
  Proof.
    iIntros "(HP & #HPQ & HQR)".
    iModIntro. iDestruct "HP" as (n) "HP".
    iDestruct ("HPQ" with "HP") as (m) "#HQ".
    iMod "HQR". iModIntro. by iApply "HQR".
  Qed.

End examples.
