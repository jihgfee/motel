From ltl Require Import ltl ltl_fixpoints ltl_now classical ltl_adequacy.

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

  Lemma running_example_extended (P Q R : tProp) :
    ⊢ □ (P → ○ ◊ Q) → □ (Q → ○ ◊ R) → ◊ P → ○ ○ ◊ R.
  Proof.
    iIntros "#HPQ #HQR HP". iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
    iModIntro. iMod "HQ". by iApply "HQR".
  Qed.

  Lemma ltl_always_introI (P : tProp) :
     ⊢ P → (□ (P → (○ P))) → □ P.
  Proof. iIntros "HP #HQ". iApply (ltl_always_intro with "HQ HP"). Qed.

  Lemma foo (P Q : tProp) :
    (P ⊢ ○◊ (P ∧ Q)) → (P ⊢ □◊ Q).
  Proof.
    iIntros (HPQ) "HP".
    iAssert (□ ◊ (P ∧ Q))%I with "[-]" as "[_ $]".
    iApply (ltl_always_introI with "[HP]").
    { iDestruct (HPQ with "HP") as "HP".
      by rewrite ltl_next_eventually. }
    iIntros "!> [HP _]".
    rewrite -ltl_eventually_next_comm.
    iMod "HP".
    rewrite ltl_eventually_next_comm. by iApply HPQ.
  Qed.

  Lemma bar (P Q : tProp) :
    □ P ∧ ◊ (P → ○ ◊ Q) ⊢ ◊ Q.
  Proof.
    iIntros "[#HP HPQ]".
    iMod "HPQ" as "HPQ".
    iApply ltl_next_eventually.
    by iApply ("HPQ" with "HP").
  Qed.

  Lemma baz (P Q : tProp) :
    (□ (P ∧ Q)) ∧ ○ P ∧ Q ⊢ □ Q.
  Proof. iIntros "[[#HP #HQ] [HP' HQ']]". iIntros "!>". by iApply "HQ". Qed.

  Lemma motivating_example (P : tProp) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iAssert (□ (P ∨ (○P)))%I with "[HP1 HP2]" as "#H".
    { iApply (ltl_always_introI with "[HP2]").
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

  Lemma ltl_always_eventually_intro (P : tProp) :
    □ (P → ○◊ P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iApply (ltl_always_introI with "[HP2]").
    { by iApply ltl_eventually_intro_now. }
    iIntros "!> HP". iApply ltl_eventually_next_comm.
    iMod "HP".
    iDestruct ("HP1" with "HP") as "HP".
    by iApply ltl_eventually_next_comm.
  Qed.

  Lemma running_example_alt (P : tProp) :
    □ (P → ○○P) ∧ P ⊢ □ ◊ P.
  Proof.
    iIntros "[#HP1 HP2]".
    iApply ltl_always_eventually_intro. iFrame.
    iIntros "!> HP".
    iDestruct ("HP1" with "HP") as "HP".
    iIntros "!>".
    iApply ltl_eventually_intro_next.
    done.
  Qed.

  Lemma ltl_until_example (P Q : tProp) :
    P ∪ Q ∧ (¬ □ P) ⊢ ◊ Q.
  Proof. rewrite -ltl_until_eventually. apply bi.and_elim_l. Qed.

  Lemma bar' (P Q R : Prop) :
    P ∧ (P -> Q) -> Q.
  Proof.
    intros [HP HPQ].
    apply HPQ.
    apply HP.
  Qed.

  Lemma bar'' (P Q R : tProp) :
    P ∧ (P → ◊ Q) ⊢ ◊ Q.
  Proof.
    iIntros "[HP HPQ]".
    iDestruct ("HPQ" with "HP") as "HQ".
    iApply "HQ".
  Qed.

  Lemma foo' (P Q R : tProp) :
    ○ P ∧ □ ○ (P → □ Q) ∧ ◊ ○ (Q → R) ⊢ ○ ◊ R.
  Proof.
    iIntros "(HP & #HPQ & HQR)".
    iModIntro.
    iDestruct ("HPQ" with "HP") as "#HQ".
    iMod "HQR".
    iDestruct ("HQR" with "HQ") as "HR".
    by iModIntro.
  Qed.

  Lemma foo'' (P Q R : nat → tProp) :
    ○ (∃ n, P n) ∧ □ ○ (∀ n, P n → ∃ m, □ Q m) ∧
    ◊ ○ (∀ m, Q m → ∃ k, R k) ⊢ ○ ◊ ∃ k, R k.
  Proof.
    iIntros "(HP & #HPQ & HQR)".
    iModIntro. iDestruct "HP" as (n) "HP".
    iDestruct ("HPQ" with "HP") as (m) "#HQ".
    iMod "HQR". iModIntro. by iApply "HQR".
  Qed.

End examples.


Section demo_ex.

  Definition demo_state := bool.
  Definition demo_label := bool.

  Inductive demo_steps : demo_state → demo_label → demo_state → Prop :=
    | demo_steps_succ b : demo_steps b b (negb b)
    | demo_steps_fail b : demo_steps b (negb b) b.

  Notation tProp := (tProp demo_state demo_label demo_steps).

  Lemma demo_step :
    ∀ b, ↓s b ⊢
         (↓l b ∧ ○ ↓s (negb b)) ∨
         (↓l (negb b) ∧ ○ ↓s b) : tProp.
  Proof.
    iIntros (i) "Hs".
    iDestruct (trace_steps with "Hs")
      as (l s' Hrel) "[Hl Hs']".
    { eexists _, _. constructor. }
    inversion Hrel; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma demo_step_succ :
    ∀ b, (↓s b ∧ ↓l b)%I ⊢ ○ ↓s (negb b) : tProp.
  Proof.
    iIntros (b) "[Hs Hl]".
    iDestruct (demo_step with "Hs") as "[[_ $]|(Hl'&Hs)]".
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
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (demo_step with "Hs") as "[[Hl' Hs]|[Hl' Hs]]".
    { iModIntro. iFrame. }
    iEval (rewrite -ltl_next_eventually). iModIntro.
    iApply "IH". iFrame.
  Qed.

  Lemma eventual_response b :
    □ (∀ b, ◊ ↓l b) ⊢ ↓s b → ○ ◊ ↓s (negb b) : tProp.
  Proof.
    iIntros "#Hfair Hs".
    iDestruct (eventual_step with "[$Hfair $Hs]") as "Hsl".
    iMod "Hsl" as "[Hs Hl]".
    iDestruct (demo_step_succ with "[$Hs $Hl]") as "Hs".
    iModIntro. iModIntro. done.
  Qed.

  Theorem demo_theorem :
    □ (∀ b, ◊ ↓l b) ⊢ ◊ ↓s true → ○ ◊ ↓s false : tProp.
  Proof.
    iIntros "#Hfair".
    iApply eventually_primer.
    iApply (eventual_response with "Hfair").
  Qed.

  Theorem demo_theorem_meta
    (tr : wf_trace demo_state demo_label demo_steps) :
    (∀ n b, ∃ m, mjoin (snd <$> (wf_head (wf_after m (wf_after n tr)))) = Some b) →
    (∃ n, (fst <$> wf_head (wf_after n tr)) = Some true) →
    ∃ n, fst <$> wf_head (wf_after n (wf_tail tr)) = Some false.
  Proof.
    pose proof demo_theorem.
    revert H.
    adequacy_unseal.
    setoid_rewrite option_fmap_id.
    naive_solver.
  Qed.

End demo_ex.

Section simple_ex.
  Definition state := nat.
  Definition label := unit.
  Inductive steps : state → label → state → Prop :=
    | my_step i : steps i () (i+1).

  Notation tProp := (tProp state label steps).

  Lemma step : ⊢ ∀ i, ↓s i → ○ ↓s (i+1) : tProp.
  Proof.
    iIntros (i) "H".
    iDestruct (trace_steps_det with "H") as "[Hl Hs]".
    { intros. by inversion H; inversion H0; simplify_eq. }
    { econstructor. }
    done.
  Qed.

  Lemma eventually_n (n:nat) : ↓s 0 ⊢ ◊ ↓s n : tProp.
  Proof.
    iDestruct step as "Hstep".
    assert (∃ i j, i = 0 ∧ n = i+j) as (i&j&Heq&H1).
    { eexists 0, n. lia. }
    rewrite -{2}Heq. clear Heq.
    iInduction j as [|j IH] forall (i H1).
    { simplify_eq. rewrite right_id. iIntros "Hs". iModIntro. iApply "Hs". }
    iIntros "Hs".
    iDestruct (step with "Hs") as "Hs".
    iApply ltl_next_eventually. iModIntro.
    iApply ("IH" with "[] Hs").
    iPureIntro. lia.
  Qed.

End simple_ex.

Section advanced_ex.

  Definition state' : Set := nat * bool.
  Definition label' : Set := bool.
  Inductive steps' : state' → label' → state' → Prop :=
  | my_step_succ i b : steps' (i,b) b (i+1,negb b)
  | my_step_fail i b : steps' (i,b) (negb b) (i,b).

  Notation tProp := (tProp state' label' steps').

  Axiom advanced_fair : ∀ (b:bool), ⊢ ◊ ↓l b : tProp.

  Lemma step_b b i :
    ↓s (i,b) ⊢ ↓l b ∧ ○ ↓s (i+1,negb b) ∨ ↓l (negb b) ∧ ○ (↓s (i,b)) : tProp.
  Proof.
    iIntros "H".
    iDestruct (trace_steps with "H") as (l s' Hsteps') "[Hl Hs]";
      [by eexists _, _; constructor|].
    inversion Hsteps'; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma eventually_incr i b :
    ↓s (i,b) ⊢ ◊ ↓s (i+1,negb b) : tProp.
  Proof.
    iIntros "Hs".
    iAssert (↓s (i,b) ∪ ↓s (i+1,negb b))%I with "[Hs]" as "H"; last first.
    { by iApply (ltl_until_mono_strong with "[] [] H"); eauto. }
    iRevert "Hs".
    iDestruct (advanced_fair b) as "-#Hfair".
    iApply (ltl_eventually_ind_strong with "[] Hfair").
    iIntros "!> [Hl|H]".
    { iIntros "Hs".
      iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
      iDestruct (step_b with "Hs") as "[Hs|Hs]"; last first.
      { iDestruct "Hs" as "[Hs Hs'']".
        iDestruct (ltl_now_false with "Hl Hs") as "[]".
        destruct b; intros [[[] []]|] HP HQ; by naive_solver. }
      iDestruct "Hs" as "[_ Hs'']".
      iApply ltl_until_intro_next. iFrame.
      iModIntro. iApply ltl_until_intro_now. done. }
    iDestruct "H" as "[Hl IH]".
    iIntros "Hs".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs2]".
    iDestruct (step_b with "Hs") as "[[Hl' Hs']|[Hl' Hs']]".
    { iApply ltl_until_intro_next. iFrame. iModIntro.
      iApply ltl_until_intro_now. by iApply (ltl_now_mono with "Hs'"). }
    iApply ltl_until_intro_next. iFrame. iModIntro. by iApply "IH".
  Qed.

  Lemma eventually_n' n :
    ↓fs fst 0 ⊢ ◊ ↓fs fst n : tProp.
  Proof.
    assert (∃ i j, i = 0 ∧ n-j = i ∧ n >= j) as (i&j&<-&H1&H2).
    { eexists _, n. split; [done|]. lia. }
    iInduction j as [|j IHj] forall (n i H1 H2).
    { simplify_eq. rewrite right_id. iIntros "H".
      by iApply ltl_eventually_intro_now. }
    iIntros "Hi".
    iDestruct (ltl_now_prod_fst with "Hi") as (b) "Hs".
    iDestruct (eventually_incr with "Hs") as "H'".
    iApply (ltl_eventually_ind_strong with "[] H'").
    iIntros "!> [H|(H3&H2)]".
    { iApply "IHj".
      { instantiate (1:=i+1). rewrite -H1. iPureIntro. lia. }
      { iPureIntro. lia. }
      iDestruct "H" as "[$ _]". }
    by iApply ltl_next_eventually.
  Qed.

  Theorem eventually_n_meta'
    (tr : wf_trace state' label' steps') i :
    fst <$> (fst <$> wf_head tr) = Some 0 →
    ∃ n, fst <$> (fst <$> wf_head (wf_after n tr)) = Some i.
  Proof.
    pose proof (eventually_n' i).
    revert H. adequacy_unseal. naive_solver.
  Qed.

End advanced_ex.

Section yes_no_ex.

  Definition yn_state : Set := nat * bool.
  Definition yn_label : Set := bool.
  Inductive yn_steps : yn_state → yn_label → yn_state → Prop :=
  | yn_step_succ i b : i > 0 → yn_steps (i,b) b (i-1,negb b)
  | yn_step_fail i b : i > 0 → yn_steps (i,b) (negb b) (i,b).

  Notation tProp := (tProp yn_state yn_label yn_steps).

  Lemma yn_inf_live b :
    ∞ ⊢@{tProp} □ ◊ is_live b.
  Proof.
    iApply inf_live_strong.
    intros. inversion H; [destruct b'|destruct b0]; destruct b; simplify_eq; eexists _; econstructor; lia.
  Qed.

  Axiom yn_fair : ∀ (b:bool),
    ⊢ (□ ◊ is_live b) → ◊ ↓l b : tProp.

  Lemma yn_step_b b i :
    ↓s (S i,b) ⊢ ↓l b ∧ ○ ↓s (S i - 1,negb b) ∨ ↓l (negb b) ∧ ○ (↓s (S i,b)) : tProp.
  Proof.
    iIntros "H".
    iDestruct (trace_steps with "H") as (l s' Hsteps') "[Hl Hs]";
      [by eexists _, _; constructor; lia|].
    inversion Hsteps'; simplify_eq.
    - iLeft. iFrame.
    - iRight. iFrame.
  Qed.

  Lemma yn_step_b_label b i :
    ↓s (S i,b) ∧ ↓l b ⊢  ○ ↓s (S i - 1, negb b): tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as (s' Hsteps') "Hs";
      [by eexists _, _; constructor; lia|].
    inversion Hsteps'; simplify_eq.
    - done.
    - by destruct b.
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
    iDestruct (yn_inf_live b with "H") as "#Hlive".
    iDestruct (yn_fair with "Hlive") as "-#Hsched".
    iRevert "Hs".
    iApply (ltl_eventually_ind_strong with "[] Hsched").
    iIntros "!> [Hl|[_ IH]] Hs".
    { iDestruct (yn_step_b_label with "[$Hs $Hl]") as "H'".
      iEval (rewrite -ltl_next_eventually). iModIntro. iModIntro.
      iApply ltl_now_prod_fst. iExists _.
      replace (S n - 1) with n by lia. done. }
    iDestruct (yn_step_b with "Hs") as "[[Hl Hs]|[Hl Hs]]".
    - iEval (rewrite -ltl_next_eventually). iModIntro. iModIntro.
      iApply ltl_now_prod_fst. iExists _.
      replace (S n - 1) with n by lia. done.
    - iEval (rewrite -ltl_next_eventually). iModIntro.
      by iApply "IH".
  Qed.

End yes_no_ex.
