From motel Require Import ltl ltl_fixpoints ltl_now ltl_adequacy.

Module fair_coin_example.

  Definition state := bool.
  Definition label := bool.

  Inductive steps : state → label → state → Prop :=
    | steps_succ b : steps b b (negb b)
    | steps_fail b : steps b (negb b) b.

  Notation tProp := (tProp state label steps).

  Lemma step b : 
    ↓s b ⊢
    (↓l b ∧ ○ ↓s (negb b)) ∨
      (↓l (negb b) ∧ ○ ↓s b) : tProp.
  Proof.
    iIntros "Hs".
    iDestruct (trace_steps with "Hs")
      as (l s' Hrel) "[Hl Hs']".
    { eexists _, _. constructor. }
    inversion Hrel; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma step_succ b :
    ↓s b ∧ ↓l b ⊢ ○ ↓s (negb b) : tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (step with "Hs") as "[[_ $]|(Hl'&Hs)]".
    iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq.
    by destruct b.
  Qed.

  Lemma eventual_step b :
    □ (∀ b, ◊ ↓l b) ∧ ↓s b ⊢ ◊ (↓s b ∧ ↓l b) : tProp.
  Proof.
    iIntros "[#Hfair Hs]". iRevert "Hs".
    iDestruct ("Hfair" $! b) as "-#Hl".
    iApply (ltl_eventually_ind_strong with "[] Hl").
    iIntros "!> [Hl|[Hl IH]] Hs".
    { iModIntro. iFrame. }
    iDestruct (bi_dup with "Hs") as "[Hs Hs']".
    iDestruct (step with "Hs'") as "[[Hl' Hs']|[Hl' Hs']]".
    { iModIntro. iFrame. }
    iEval (rewrite -ltl_next_eventually). iModIntro.
    iApply "IH". iFrame.
  Qed.

  Lemma eventual_flip b :
    □ (∀ b, ◊ ↓l b) ∧ ◊ ↓s b ⊢ ○ ◊ ↓s (negb b) : tProp.
  Proof.
    iIntros "[#Hfair Hs]".
    iMod "Hs".
    iDestruct (eventual_step with "[$Hfair $Hs]") as ">[Hs Hl]".
    iDestruct (step_succ with "[$Hs $Hl]") as "Hs".
    iModIntro. iModIntro. iApply "Hs".
  Qed.

  (* Restating above lemma to more easily apply adequacy. *)
  Theorem theorem :
    □ (∀ b, ◊ ↓l b) ⊢ ◊ ↓s true → ○ ◊ ↓s false : tProp.
  Proof.
    iIntros "#Hfair". iIntros "H".
    iApply (eventual_flip with "[$Hfair $H]").
  Qed.

  Theorem theorem_meta
    (tr : wf_trace state label steps) :
    (∀ n b, ∃ m, mjoin (snd <$> (wf_head (wf_after m (wf_after n tr)))) = Some b) →
    (∃ n, (fst <$> wf_head (wf_after n tr)) = Some true) →
    ∃ n, fst <$> wf_head (wf_after n (wf_tail tr)) = Some false.
  Proof.
    pose proof theorem.
    revert H.
    adequacy_unseal.
    setoid_rewrite option_fmap_id.
    naive_solver.
  Qed.

End fair_coin_example.

Module fair_coin_increment_example.

  Definition state : Set := nat.
  Definition label : Set := bool.
  Inductive steps : state → label → state → Prop :=
  | my_step_succ i : steps i (Nat.even i) (i+1)
  | my_step_fail i : steps i (negb (Nat.even i)) i.

  Notation tProp := (tProp state label steps).

  Axiom fair : ∀ (b:bool), ⊢ ◊ ↓l b : tProp.

  Lemma step i :
    ↓s i ⊢ ↓l (Nat.even i) ∧ ○ ↓s (i+1) ∨ ↓l (negb (Nat.even i)) ∧ ○ (↓s i) : tProp.
  Proof.
    iIntros "H".
    iDestruct (trace_steps with "H") as (l s Hsteps) "[Hl Hs]".
    { by eexists _, _; constructor. }
    inversion Hsteps; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma step_succ_alt i :
    ↓s i ∧ ↓l (Nat.even i) ⊢ ○ ↓s (i+1) : tProp.
  Proof.
    iIntros "Hsl".
    iDestruct (trace_steps_label with "Hsl") as (s Hsteps) "Hs".
    inversion Hsteps; simplify_eq.
    - done.
    - by destruct (Nat.even s).
  Qed.

  Lemma step_succ i :
    ↓s i ∧ ↓l (Nat.even i) ⊢ ○ ↓s (i+1) : tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (step with "Hs") as "[[Hl' Hs]|[Hl' Hs]]".
    - iFrame.
    - iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq. by destruct (Nat.even i).
  Qed.

  Lemma eventually_step i :
    ↓s i ⊢ ◊ (↓s i ∧ ↓l (Nat.even i)) : tProp.
  Proof.
    iDestruct (fair (Nat.even i)) as "-#Hl".
    iApply (ltl_eventually_ind_strong with "[] Hl").
    iIntros "!> [Hl|[Hl IH]] Hs".
    { iModIntro. iFrame. }
    iDestruct (bi_dup with "Hs") as "[Hs Hs']".
    iDestruct (step with "Hs'") as "[[Hl' Hs']|[Hl' Hs']]".
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

  Theorem eventually_n_meta
    (tr : wf_trace state label steps) i :
    fst <$> wf_head tr = Some 0 →
    ∃ n, fst <$> (wf_head (wf_after n tr)) = Some i.
  Proof.
    pose proof (eventually_n i).
    revert H. adequacy_unseal. setoid_rewrite option_fmap_id. naive_solver.
  Qed.

End fair_coin_increment_example.
