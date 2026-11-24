From motel Require Import ltl ltl_fixpoints ltl_now.

Import tProp.

Section fair_sched.

  Definition state := nat.
  Context (label : Set).
  Context (f : nat → label).

  Inductive steps : state → label → state → Prop :=
  | my_step_succ i : steps i (f i) (i+1)
  | my_step_fail i j : f i ≠ j → steps i j i.

  Notation tProp := (tProp state label steps).

  Axiom fair : ∀ i, ⊢ ◊ ↓l i : tProp.

  Lemma step i :
    ↓s i ⊢ ∃ l, ↓l l ∧
                ((⌜f i = l⌝ ∧ ○ ↓s (i+1)) ∨
                (⌜f i ≠ l⌝ ∧ ○ (↓s i))) : tProp.
  Proof.
    iIntros "H".
    iDestruct (trace_steps with "H") as (l s' Hsteps') "[Hl Hs]";
      [by eexists _, _; constructor|].
    inversion Hsteps'; simplify_eq.
    - iExists (f i). iFrame. iLeft. iFrame. done. 
    - iExists l. iFrame. iRight. iFrame. done.
  Qed.

  Lemma step_succ_alt i :
    ↓s i ∧ ↓l (f i) ⊢ ○ ↓s (i+1) : tProp.
  Proof.
    iIntros "Hsl".
    iDestruct (trace_steps_label with "Hsl") as (s Hsteps) "Hs".
    by inversion Hsteps; simplify_eq.
  Qed.

  Lemma step_succ i :
    ↓s i ∧ ↓l (f i) ⊢ ○ ↓s (i+1) : tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (step with "Hs") as (l) "[Hl' [[-> Hs]|[%Hneq Hs]]]".
    - iFrame.
    - iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq. subst. done.
  Qed.

  Lemma eventually_step i :
    ↓s i ⊢ ◊ (↓s i ∧ ↓l (f i)) : tProp.
  Proof.
    iDestruct (fair (f i)) as "-#Hl".
    iApply (ltl_eventually_ind_strong with "[] Hl").
    iIntros "!> [Hl|[_ IH]] Hs".
    { iModIntro. iFrame. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (step with "Hs'") as (l) "[Hl [[-> Hs']|[Hl' Hs']]]".
    { iModIntro. iFrame. }
    iEval (rewrite -ltl_next_eventually). iModIntro.
    iApply "IH". iFrame.
  Qed.

  Lemma eventually_incr i :
    ↓s i ⊢ ◊ ↓s (i+1) : tProp.
  Proof.
    iIntros "Hs".
    iMod (eventually_step with "Hs") as "Hsl".
    iDestruct (step_succ with "Hsl") as "Hs".
    iApply ltl_next_eventually.
    iModIntro. iModIntro. iApply "Hs".
  Qed.

  Lemma eventually_n n :
    ↓s 0 ⊢ ◊ ↓s n : tProp.
  Proof.
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. }
    iInduction j as [|j IHj] forall (n i H1 H2).
    { simplify_eq. rewrite right_id. iIntros "H".
      by iApply ltl_eventually_intro_now. }
    iIntros "Hs".
    iDestruct (eventually_incr with "Hs") as "H'".
    iApply (ltl_eventually_ind_strong with "[] H'").
    iIntros "!> [H|(H3&H2)]".
    { iApply "IHj".
      { instantiate (1:=i+1). rewrite -H1. iPureIntro. lia. }
      { iPureIntro. lia. }
      done. }
    by iApply ltl_next_eventually.
  Qed.

End fair_sched.

Module sequential.

  Lemma eventually_n_coin n :
    ↓s 0 ⊢ ◊ ↓s n : tProp nat () (steps () (λ _, ())).
  Proof. apply eventually_n. Qed.

End sequential.

Module fair_coin.

  Lemma eventually_n_coin n :
    ↓s 0 ⊢ ◊ ↓s n : tProp nat bool (steps bool Nat.even).
  Proof. apply eventually_n. Qed.

End fair_coin.

Module fair_inf.

  Lemma eventually_n_inf n :
    ↓s 0 ⊢ ◊ ↓s n : tProp nat nat (steps nat id).
  Proof. apply eventually_n. Qed.

End fair_inf.
