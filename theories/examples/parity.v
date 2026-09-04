From ltl Require Import ltl ltl_fixpoints ltl_now ltl_adequacy classical.

Import tProp.

Section parity.

  Inductive L :=
  | a
  | b.

  Inductive Q :=
  | q0
  | q1.

  Definition Ω (s:Q) : nat :=
    match s with
    | q0 => 1
    | q1 => 2
    end.

  Inductive M :=
  | s0
  | s1
  | s2.

  Inductive RQ : Q → L → Q → Prop :=
  | q0_a : RQ q0 a q1
  | q0_b : RQ q0 b q0
  | q1_a : RQ q1 a q0
  | q1_b : RQ q1 b q1.

  Inductive RM : M → L → M → Prop :=
  | s0_a : RM s0 a s1
  | s1_a : RM s1 a s2
  | s1_b : RM s1 b s0
  | s2_b : RM s2 b s1.

  Inductive R : (Q*M) → L → (Q*M) → Prop :=
  | R_step q q' l s s' : RQ q l q' → RM s l s' → R (q,s) l (q',s').

  Notation tProp := (tProp (Q*M) L R).

  Lemma q0_step:
    ↓fs fst q0 ⊢@{tProp}
    (↓l a ∧ ○ ↓fs fst q1) ∨
    (↓l b ∧ ○ ↓fs fst q0).
  Proof.
    iIntros "Hs".
    iDestruct (ltl_now_prod_fst with "Hs") as (m) "Hs".
    iDestruct (trace_steps with "Hs") as "Hs".
    { destruct m.
      - eexists a, _; repeat constructor.
      - eexists a, _; repeat constructor.
      - eexists b, _; repeat constructor. }
    iDestruct "Hs" as (l s' Hrel) "[Hl Hs]".
    inversion Hrel. simplify_eq.
    inversion H1; simplify_eq.
    - iLeft. iFrame. iModIntro. iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver.
    - iRight. iFrame. iModIntro. iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver.
  Qed.

  Lemma q1_step :
    ↓fs fst q1 ⊢@{tProp}
    (↓l a ∧ ○ ↓fs fst q0) ∨
    (↓l b ∧ ○ ↓fs fst q1).
  Proof.
    iIntros "Hs".
    iDestruct (ltl_now_prod_fst with "Hs") as (m) "Hs".
    iDestruct (trace_steps with "Hs") as "Hs".
    { destruct m.
      - eexists a, _; repeat constructor.
      - eexists a, _; repeat constructor.
      - eexists b, _; repeat constructor. }
    iDestruct "Hs" as (l s' Hrel) "[Hl Hs]".
    inversion Hrel. simplify_eq.
    inversion H1; simplify_eq.
    - iLeft. iFrame. iModIntro. iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver.
    - iRight. iFrame. iModIntro. iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver.
  Qed.

  Lemma s0_step :
    ↓fs snd s0 ⊢@{tProp}
    ↓l a ∧ ○ ↓fs snd s1.
  Proof.
    iIntros "Hs".
    iDestruct (ltl_now_prod_snd with "Hs") as (q) "Hs".
    iDestruct (trace_steps with "Hs") as "Hs".
    { destruct q.
      - eexists a, _; repeat constructor.
      - eexists a, _; repeat constructor. }
    iDestruct "Hs" as (l s' Hrel) "[Hl Hs]".
    inversion Hrel. simplify_eq.
    inversion H4; simplify_eq.
    iFrame. iModIntro. iApply (ltl_now_mono with "Hs").
    intros [[]|]; naive_solver.
  Qed.

  Lemma s1_step :
    ↓fs snd s1 ⊢@{tProp}
    (↓l a ∧ ○ ↓fs snd s2) ∨
    (↓l b ∧ ○ ↓fs snd s0).
  Proof.
    iIntros "Hs".
    iDestruct (ltl_now_prod_snd with "Hs") as (q) "Hs".
    iDestruct (trace_steps with "Hs") as "Hs".
    { destruct q.
      - eexists a, _; repeat constructor.
      - eexists a, _; repeat constructor. }
    iDestruct "Hs" as (l s' Hrel) "[Hl Hs]".
    inversion Hrel. simplify_eq.
    inversion H4; simplify_eq.
    - iLeft. iFrame. iModIntro. iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver.
    - iRight. iFrame. iModIntro. iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver.
  Qed.

  Lemma s2_step :
    ↓fs snd s2 ⊢@{tProp}
    (↓l b ∧ ○ ↓fs snd s1).
  Proof.
    iIntros "Hs".
    iDestruct (ltl_now_prod_snd with "Hs") as (q) "Hs".
    iDestruct (trace_steps with "Hs") as "Hs".
    { destruct q.
      - eexists b, _; repeat constructor.
      - eexists b, _; repeat constructor. }
    iDestruct "Hs" as (l s' Hrel) "[Hl Hs]".
    inversion Hrel. simplify_eq.
    inversion H4; simplify_eq.
    iFrame. iModIntro. iApply (ltl_now_mono with "Hs").
    intros [[]|]; naive_solver.
  Qed.

  Lemma q0_s0_step :
    ↓s (q0,s0) ⊢@{tProp}
    (↓l a ∧ ○ ↓s (q1,s1)).
  Proof.
    iIntros "Hs".
    iDestruct (ltl_dup with "Hs") as "[Hq Hs]".
    iDestruct (q0_step with "[Hq]") as "Hq".
    { iApply (ltl_now_mono with "Hq").
      intros [[]|]; naive_solver. }
    iDestruct (s0_step with "[Hs]") as "Hs".
    { iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver. }
    iDestruct "Hs" as "[Hl' Hs]".
    iDestruct "Hq" as "[[_ Hq]|[Hl _]]".
    - iFrame. iModIntro. iCombine "Hq Hs" as "Hs". iFrame.
    - iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq. simplify_eq.
  Qed.

  Lemma q0_s1_step :
    ↓s (q0,s1) ⊢@{tProp}
    (↓l a ∧ ○ ↓s (q1,s2)) ∨
    (↓l b ∧ ○ ↓s (q0,s0)).
  Proof.
    iIntros "Hs".
    iDestruct (ltl_dup with "Hs") as "[Hq Hs]".
    iDestruct (q0_step with "[Hq]") as "Hq".
    { iApply (ltl_now_mono with "Hq").
      intros [[]|]; naive_solver. }
    iDestruct (s1_step with "[Hs]") as "Hs".
    { iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver. }
    iDestruct "Hq" as "[[Hlq Hq]|[Hlq Hq]]";
      iDestruct "Hs" as "[[Hls Hs]|[Hls Hs]]".
    - iLeft. iFrame. iModIntro. iCombine "Hq Hs" as "Hs". iFrame.
    - iDestruct (ltl_now_lbl_agree with "Hlq Hls") as %Heq. simplify_eq.
    - iDestruct (ltl_now_lbl_agree with "Hlq Hls") as %Heq. simplify_eq.
    - iRight. iFrame. iModIntro. iCombine "Hq Hs" as "Hs". iFrame.
  Qed.

  Lemma q0_s2_step :
    ↓s (q0,s2) ⊢@{tProp}
    (↓l b ∧ ○ ↓s (q0,s1)).
  Proof.
    iIntros "Hs".
    iDestruct (ltl_dup with "Hs") as "[Hq Hs]".
    iDestruct (q0_step with "[Hq]") as "Hq".
    { iApply (ltl_now_mono with "Hq").
      intros [[]|]; naive_solver. }
    iDestruct (s2_step with "[Hs]") as "Hs".
    { iApply (ltl_now_mono with "Hs").
      intros [[]|]; naive_solver. }
    iDestruct "Hq" as "[[Hlq Hq]|[Hlq Hq]]";
      iDestruct "Hs" as "[Hls Hs]".
    - iDestruct (ltl_now_lbl_agree with "Hlq Hls") as %Heq. simplify_eq.
    - iFrame. iModIntro. iCombine "Hq Hs" as "Hs". iFrame.
  Qed.

  Lemma ltl_eventually_pure (P : Prop) :
    ⌜P⌝ ⊣⊢@{tProp} ◊ ⌜P⌝.
  Proof.
    iSplit.
    - iIntros (HP) "!>". iPureIntro. done.
    - iApply ltl_eventually_ind; [done|].
      iIntros "[_ HP]". by iApply ltl_next_pure.
  Qed.

  Lemma state_preserved (s:Q * M) :
    ↓s s ⊢@{tProp} ○ ∃ s', ↓s s'.
  Proof.
    destruct s as [[] m]; iIntros "Hs".
    - iDestruct (q0_step with "[Hs]") as "Hs".
      { iApply (ltl_now_mono with "Hs").
        intros [[]|]=> /= ?; by simplify_eq. }
      iDestruct "Hs" as "[[_ Hs]|[_ Hs]]"; iModIntro;
        iDestruct (ltl_now_prod_fst with "Hs") as (m') "Hs";        
        iExists _; done.
    - iDestruct (q1_step with "[Hs]") as "Hs".
      { iApply (ltl_now_mono with "Hs").
        intros [[]|]=> /= ?; by simplify_eq. }
      iDestruct "Hs" as "[[_ Hs]|[_ Hs]]"; iModIntro;
        iDestruct (ltl_now_prod_fst with "Hs") as (m') "Hs";        
        iExists _; done.
  Qed.

  Lemma eventually_parity_2 (s:Q * M) :
    ↓s s ⊢@{tProp} ◊ ↓fs (Ω ∘ fst) 2.
  Proof.
    iIntros "Hs".
    destruct s as [[] m]; last first.
    { iModIntro. iApply (ltl_now_mono with "Hs").
      intros [[]|] =>/= ?; by simplify_eq. }
    destruct m.
    - iDestruct (q0_s0_step with "Hs") as "[_ Hs]".
      rewrite -ltl_next_eventually. iModIntro.
      iModIntro. iApply (ltl_now_mono with "Hs").
      intros [[]|] =>/= ?; by simplify_eq.
    - iDestruct (q0_s1_step with "Hs") as "[[_ Hs]|[_ Hs]]".
      + rewrite -ltl_next_eventually. iModIntro.
        iModIntro. iApply (ltl_now_mono with "Hs").
        intros [[]|] =>/= ?; by simplify_eq.
      + rewrite -ltl_next_eventually. iModIntro.
        iDestruct (q0_s0_step with "Hs") as "[_ Hs]".
        rewrite -ltl_next_eventually. iModIntro.
        iModIntro. iApply (ltl_now_mono with "Hs").
        intros [[]|] =>/= ?; by simplify_eq.
    - iDestruct (q0_s2_step with "Hs") as "[_ Hs]".
      rewrite -ltl_next_eventually. iModIntro.
      iDestruct (q0_s1_step with "Hs") as "[[_ Hs]|[_ Hs]]".
      + rewrite -ltl_next_eventually. iModIntro.
        iModIntro. iApply (ltl_now_mono with "Hs").
        intros [[]|] =>/= ?; by simplify_eq.
      + rewrite -ltl_next_eventually. iModIntro.
        iDestruct (q0_s0_step with "Hs") as "[_ Hs]".
        rewrite -ltl_next_eventually. iModIntro.
        iModIntro. iApply (ltl_now_mono with "Hs").
        intros [[]|] =>/= ?; by simplify_eq.
  Qed.
      
  Theorem parity_theorem :
    ↓s (q0,s0) ⊢@{tProp} ∃ x, ⌜Nat.even x⌝ ∧ (□ ◊ ↓fs (Ω ∘ fst) x) ∧
                              ∀ y, (□ ◊ (↓fs (Ω ∘ fst) y)) → ⌜y <= x⌝.
  Proof.
    iIntros "Hs".
    iExists 2.
    iSplit; [done|].
    iSplit.
    - iDestruct (ltl_st with "Hs") as "Hs".
      { intros [|]; naive_solver. }
      iDestruct (ltl_eventually_intro_now with "Hs") as "Hs".
      iApply (ltl_always_coind with "[] Hs").
      { iIntros "!> Hs".
        iSplit.
        { iMod "Hs" as (s) "Hs".
          by iApply eventually_parity_2. }
        rewrite ltl_always_eventually_idemp.
        rewrite -{2}ltl_eventually_idemp.
        rewrite -ltl_until_or.
        rewrite -ltl_eventually_next_comm.
        iMod "Hs".
        iApply ltl_eventually_intro_now.
        iDestruct "Hs" as (s) "Hs".
        iDestruct (state_preserved with "Hs") as "Hs".
        iModIntro. iLeft. iModIntro.
        done. }
    - iIntros (y) "#H".
      iApply ltl_eventually_pure. iMod "H". iModIntro.
      iDestruct (ltl_now_pure with "H") as %[[[[q s] l]|] H]; [|done].
      simpl in *.
      iPureIntro.
      destruct q; simpl in *; lia.
  Qed.
        
End parity.
