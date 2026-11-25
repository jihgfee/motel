From motel Require Import ltl ltl_fixpoints ltl_now ltl_classical.

Module yes_no_example.

  Definition state : Set := nat * bool.
  Definition label : Set := bool.
  Inductive steps : state → label → state → Prop :=
  | step_succ i b : i > 0 → steps (i,b) b (i-1,negb b)
  | step_fail i b : i > 0 → steps (i,b) (negb b) (i,b).

  Notation tProp := (tProp state label steps).

  Lemma inf_live b :
    ∞ ⊢@{tProp} □ is_live b.
  Proof.
    iApply inf_live_strong.
    intros. inversion H; [destruct b'|destruct b0]; destruct b; simplify_eq; eexists _; econstructor; lia.
  Qed.

  Axiom fair : ∀ (b:bool),
    ⊢ (□ ◊ is_live b) → ◊ ↓l b : tProp.

  Lemma step_b b i :
    ↓s (S i,b) ⊢ ↓l b ∧ ○ ↓s (S i - 1,negb b) ∨ ↓l (negb b) ∧ ○ (↓s (S i,b)) : tProp.
  Proof.
    iIntros "H".
    iDestruct (trace_steps with "H") as (l s' Hsteps') "[Hl Hs]";
      [by eexists _, _; constructor; lia|].
    inversion Hsteps'; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma step_b_label b i :
    ↓s (S i,b) ∧ ↓l b ⊢  ○ ↓s (S i - 1, negb b): tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as (s' Hsteps') "Hs".
    inversion Hsteps'; simplify_eq; [done|]. by destruct b.
  Qed.

  Theorem eventually_terminates (n:nat) :
    ↓fs fst n ⊢@{tProp} ◊ ↯.
  Proof.
    rewrite (ltl_eventually_intro_now (↓fs fst n)).
    iInduction n as [|n IHn].
    { iIntros ">Hs".
      iDestruct (ltl_now_prod_fst with "Hs") as (b) "Hs".
      iDestruct (trace_terminates with "Hs") as "Hs".
      { intros H. inversion H as (?&?&?). inversion H0; lia. }
      rewrite -ltl_next_eventually. iModIntro. iModIntro. done. }
    iIntros ">Hs".
    iDestruct (ltl_now_prod_fst with "Hs") as (b) "Hs".
    iDestruct ltl_terminates_dec as "[$|#H]".
    iApply "IHn". iClear "IHn".
    iDestruct (inf_live b with "H") as "#Hlive".
    iDestruct (fair with "[Hlive]") as "-#Hsched".
    { by iIntros "!>!>". } 
    iRevert "Hs".
    iApply (ltl_eventually_ind_strong with "[] Hsched").
    iIntros "!> [Hl|[_ IH]] Hs".
    { iDestruct (step_b_label with "[$Hs $Hl]") as "H'".
      iEval (rewrite -ltl_next_eventually). iModIntro. iModIntro.
      iApply ltl_now_prod_fst. iExists _.
      replace (S n - 1) with n by lia. done. }
    iDestruct (step_b with "Hs") as "[[Hl Hs]|[Hl Hs]]".
    - iEval (rewrite -ltl_next_eventually). iModIntro. iModIntro.
      iApply ltl_now_prod_fst. iExists _.
      replace (S n - 1) with n by lia. done.
    - iEval (rewrite -ltl_next_eventually). iModIntro.
      by iApply "IH".
  Qed.

End yes_no_example.
