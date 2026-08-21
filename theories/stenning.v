From ltl Require Import ltl ltl_fixpoints ltl_now ltl_adequacy classical.

Import tProp.

Section stenning_ex.

  Inductive actor := A | B.

  Inductive stenning_A_state := ASending | AReceiving.
  Inductive stenning_B_state := BSending | BReceiving.
  Definition stenning_state : Set := (stenning_A_state * nat) * (stenning_B_state * nat).

  Definition Message : Set := actor * nat * actor.
  Inductive stenning_action : Set := Send (m:Message) | Recv (b:actor) (o:option Message).
  Definition stenning_label : Set := actor * stenning_action.

  Definition mAB n : Message := (A, n, B).
  Definition mBA n : Message := (B, n, A).

  Inductive stenning_trans : stenning_state → stenning_label → stenning_state → Prop :=
  | A_Send n stB :
    stenning_trans
      ((ASending, n), stB)
      (A, Send $ mAB n)
      ((AReceiving, n), stB)
  | A_RecvFail n stB omsg :
    omsg ≠ Some $ mBA n →
    stenning_trans
      ((AReceiving, n), stB)
      (A, Recv A omsg)
      ((ASending, n), stB)
  | A_RecvSucc n stB omsg :
    omsg = Some $ mBA n →
    stenning_trans
      ((AReceiving, n), stB)
      (A, Recv A omsg)
      ((ASending, (S n)), stB)
  | B_Send stA n :
    stenning_trans
      (stA, (BSending, n))
      (B, Send (mBA (n)))
      (stA, (BReceiving, n))
  | B_RecvFailEmpty stA n omsg :
    omsg = None →
    stenning_trans
      (stA, (BReceiving, n))
      (B, Recv B omsg)
      (stA, (BReceiving, n))
  | B_RecvFail stA n m omsg :
    omsg = Some $ m →
    m ≠ mAB (S n) →
    stenning_trans
      (stA, (BReceiving, n))
      (B, Recv B omsg)
      (stA, (BSending, n))
  | B_RecvSucc stA n omsg :
    omsg = Some $ mAB (S n) →
    stenning_trans
      (stA, (BReceiving, n))
      (B, Recv B omsg)
      (stA, (BSending, (S n)))
  .

  Notation tProp := (tProp stenning_state stenning_label stenning_trans).

  Instance stenning_state_inhabited : Inhabited stenning_state := populate ((ASending, 0), (BSending, 0)).
  Instance stenning_label_inhabited : Inhabited stenning_label := populate (A, Recv A None).

  Lemma stenning_reducible s : reducible stenning_trans s.
  Proof.
    destruct s as [[[] i] [[] j]].
    - eexists _, _. econstructor.
    - eexists _, _. econstructor.
    - eexists (_,Recv _ None),_. econstructor. eauto.
    - eexists (_,Recv _ None),_. econstructor. eauto.
  Qed.

  Definition ltl_now_state_A st : tProp := ↓fs fst st.
  Notation "↓sA st" := (ltl_now_state_A st) (at level 20, right associativity) : bi_scope.

  Definition ltl_now_state_B st : tProp := ↓fs snd st.
  Notation "↓sB st" := (ltl_now_state_B st) (at level 20, right associativity) : bi_scope.

  Definition ltl_now_label_label lbl : tProp := ↓fl fst lbl.
  Notation "↓ll lbl" := (ltl_now_label_label lbl) (at level 20, right associativity) : bi_scope.

  Axiom fair_sched : ∀ (b:actor), ⊢ (◊ ↓ll b) : tProp.

  Axiom fair_net :
    ∀ (A:actor) (Φ: nat → Prop) (B:actor),
    ⊢ (□ ◊ ∃ (m:nat), ⌜Φ m⌝ ∧ ↓l (A, Send (A, m, B))) →
      (□ ◊ ∃ om, ↓l (B, Recv B om)) →
      ◊ ∃ (m:nat), ⌜Φ m⌝ ∧ ↓l (B, Recv B (Some (A, m, B))) : tProp.

  Axiom stenning_safety_inv :
    ⊢ ∃ i stA stB, ↓sA (stA,S i) ∧ (↓sB (stB,S i) ∨ ↓sB (stB,i)).

  Lemma stenning_A : (∃ s, ↓s s) ∨ (∃ l, ↓l l) ⊢ ∃ stA, ↓sA stA : tProp.
  Proof.
    iDestruct 1 as "[[% H]|[% H]]".
    - destruct s. iDestruct "H" as "[$ _]".
    - iDestruct (ltl_st with "H") as ([]) "H".
      { intros [[]|]; naive_solver. }
      iDestruct "H" as "[$ _]".
  Qed.

  Lemma stenning_B : (∃ s, ↓s s) ∨ (∃ l, ↓l l) ⊢ ∃ stB, ↓sB stB : tProp.
  Proof.
    iDestruct 1 as "[[% H]|[% H]]".
    - destruct s. iDestruct "H" as "[_ $]".
    - iDestruct (ltl_st with "H") as ([]) "H".
      { intros [[]|]; naive_solver. }
      iDestruct "H" as "[_ $]".
  Qed.

  Lemma stenning_st_lbl s : ↓s s ⊢ ∃ l, ↓l l : tProp.
  Proof.
    iIntros "Hs".
    iDestruct (trace_steps with "Hs") as (l s' Hrel) "[Hl Hs']".
    { apply stenning_reducible. }
    iFrame.
  Qed.

  Lemma stenning_A_or_B : (∃ s, ↓s s) ∨ (∃ l, ↓l l) ⊢ ↓ll A ∨ ↓ll B.
  Proof.
    iDestruct 1 as "[[% H]|[% H]]".
    - iDestruct (stenning_st_lbl with "H") as (l) "H".
      iDestruct (ltl_lbl with "H") as ([]) "H".
      { intros [[?[]]|] H; try naive_solver. }
      iDestruct "H" as "[? ?]"; iFrame.
      destruct a; iFrame.
    - iDestruct (ltl_lbl with "H") as ([]) "H".
      { intros [[?[]]|] H; try naive_solver. }
      iDestruct "H" as "[? ?]"; iFrame.
      destruct a; iFrame.
  Qed.

  Lemma stenning_infinite s : ↓s s ⊢ ∞ : tProp.
  Proof. apply ltl_reducible_infinite. apply stenning_reducible. Qed.

  Lemma ltl_now_A_agree x y : ⊢ ↓sA x → ↓sA y → ⌜x = y⌝.
  Proof.
    rewrite !/ltl_now_state_A (ltl_now_prod_fst x) (ltl_now_prod_fst y).
    iDestruct 1 as (?) "H1". iDestruct 1 as (?) "H2".
    iDestruct (ltl_now_state_agree with "H1 H2") as %Heq. by simplify_eq.
  Qed.

  Lemma ltl_now_B_agree x y : ⊢ ↓sB x → ↓sB y → ⌜x = y⌝.
  Proof.
    rewrite !/ltl_now_state_B (ltl_now_prod_snd x) (ltl_now_prod_snd y).
    iDestruct 1 as (?) "H1". iDestruct 1 as (?) "H2".
    iDestruct (ltl_now_state_agree with "H1 H2") as %Heq. by simplify_eq.
  Qed.

  Lemma stenning_ASending_A i :
    ↓sA (ASending,i) ∧ ↓ll A ⊢ ↓l (A, Send (mAB i)) ∧ ○ ↓sA (AReceiving,i) : tProp.
  Proof.
    iIntros "[Hs HA]".
    iDestruct (ltl_now_prod_fst with "Hs") as (stB) "Hs".
    iDestruct (ltl_now_label_prod_fst with "HA") as (l) "HA".
    iDestruct (ltl_dup with "HA") as "[HA HA']".
    iDestruct (trace_steps_label with "[Hs HA]") as  (s' Hsteps') "Hs'".
    { eexists _,_. econstructor. }
    { iFrame. }
    inversion Hsteps'; simplify_eq.
    iFrame. iModIntro.
    iApply ltl_now_prod_fst.
    iExists _. done.
  Qed.

  Lemma stenning_AReceiving_A i :
    ↓sA (AReceiving, i) ∧ ↓ll A ⊢
    ∃ omsg,
      (⌜omsg ≠ Some $ mBA i⌝ ∧ ↓l (A, Recv A omsg) ∧ ○ ↓sA (ASending, i)) ∨
      (⌜omsg = Some $ mBA i⌝ ∧ ↓l (A, Recv A omsg) ∧ ○ ↓sA (ASending, S i)).
  Proof.
    iIntros "[Hs HA]".
    iDestruct (ltl_now_prod_fst with "Hs") as (stB) "Hs".
    iDestruct (ltl_now_label_prod_fst with "HA") as (l) "HA".
    iDestruct (ltl_dup with "HA") as "[HA HA']".
    iDestruct (trace_steps_label with "[$Hs $HA]") as  (s' Hsteps') "Hs'".
    { eexists (_,Recv _ None),_. econstructor. eauto. }
    inversion Hsteps'; simplify_eq.
    - iExists omsg. iLeft. iFrame. iSplit; [eauto|]. iModIntro.
      iApply ltl_now_prod_fst. iExists _. iFrame.
    - iExists (Some (mBA i)). iRight. iFrame. iSplit; [eauto|]. iModIntro.
      iApply ltl_now_prod_fst. iExists _. iFrame.
  Qed.

  Lemma stenning_A_B stA :
    ↓sA stA ∧ ↓ll B ⊢ ○ ↓sA stA.
  Proof.
    iIntros "[Hs HA]".
    iDestruct (ltl_now_prod_fst with "Hs") as (stB) "Hs".
    iDestruct (ltl_now_label_prod_fst with "HA") as (l) "HA".
    iDestruct (ltl_dup with "HA") as "[HA HA']".
    iDestruct (trace_steps_label with "[$Hs $HA]") as  (s' Hsteps') "Hs'".
    { apply stenning_reducible. }
    inversion Hsteps'; simplify_eq;
      iModIntro; iApply ltl_now_prod_fst; iExists _; iFrame.
  Qed.

  Lemma stenning_BReceiving_B i :
    ↓sB (BReceiving,i) ∧ ↓ll B ⊢
    ∃ omsg,
      (⌜omsg = None⌝ ∧ ↓l (B,Recv B omsg) ∧ ○ ↓sB (BReceiving, i)) ∨
      (∃ m, ⌜omsg = Some m⌝ ∧ ⌜m ≠ mAB (S i)⌝ ∧ ↓l (B,Recv B omsg) ∧ ○ ↓sB (BSending, i)) ∨
      (⌜omsg = Some $ mAB (S i)⌝ ∧ ↓l (B,Recv B omsg) ∧ ○ ↓sB (BSending, S i)).
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (ltl_now_prod_snd with "Hs") as (stA) "Hs".
    iDestruct (ltl_now_label_prod_fst with "Hl") as (l) "Hl".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as  (s' Hsteps') "Hs'".
    { apply stenning_reducible. }
    inversion Hsteps'; simplify_eq.
    - iExists None. iLeft. iFrame. iSplit; [eauto|]. iModIntro.
      iApply ltl_now_prod_snd. iExists _. iFrame.
    - iExists _. iRight. iLeft. iExists _. iFrame. iSplit; [eauto|]. iSplit; [eauto|].
      iModIntro. iApply ltl_now_prod_snd. iExists _. iFrame.
    - iExists _. iRight. iRight. iFrame. iSplit; [eauto|]. iModIntro.
      iApply ltl_now_prod_snd. iExists _. iFrame.
  Qed.

  Lemma stenning_BSending_B i :
    ↓sB (BSending,i) ∧ ↓ll B ⊢ ↓l (B, Send (mBA i)) ∧ ○ ↓sB (BReceiving,i) : tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (ltl_now_prod_snd with "Hs") as (stA) "Hs".
    iDestruct (ltl_now_label_prod_fst with "Hl") as (l) "Hl".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as  (s' Hsteps') "Hs'".
    { apply stenning_reducible. }
    inversion Hsteps'; simplify_eq.
    iFrame. iModIntro. iApply ltl_now_prod_snd. iExists _. iFrame.
  Qed.

  Lemma stenning_B_A stB :
    ↓sB stB ∧ ↓ll A ⊢ ○ ↓sB stB.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (ltl_now_prod_snd with "Hs") as (stA) "Hs".
    iDestruct (ltl_now_label_prod_fst with "Hl") as (l) "Hl".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as  (s' Hsteps') "Hs'".
    { apply stenning_reducible. }
    inversion Hsteps'; simplify_eq;
      iModIntro; iApply ltl_now_prod_snd; iExists _; iFrame.
  Qed.

  (* Actual lemmas *)

  Lemma stenning_disjoint_A stA :
    ↓sA stA ⊢ ◊ (↓sA stA ∧ ↓ll A).
  Proof.
    iDestruct (fair_sched A) as "Hl".
    iApply (ltl_eventually_ind_strong with "[] Hl").
    iIntros "!> [H|[H IH]] Hs".
    { iModIntro. iFrame. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct (ltl_now_prod_fst with "Hs'") as (?) "Hs'". iExists _. iFrame. }
    { iModIntro. iFrame. }
    iDestruct (stenning_A_B with "[$Hs $HB]") as "Hs".
    iEval (rewrite -ltl_next_eventually). iModIntro.
    by iApply "IH".
  Qed.

  Lemma stenning_disjoint_B stB :
    ↓sB stB ⊢ ◊ (↓sB stB ∧ ↓ll B).
  Proof.
    iDestruct (fair_sched B) as "Hl".
    iApply (ltl_eventually_ind_strong with "[] Hl").
    iIntros "!> [H|[H IH]] Hs".
    { iModIntro. iFrame. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct (ltl_now_prod_snd with "Hs'") as (?) "Hs'". iExists _. iFrame. }
    - iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
      iEval (rewrite -ltl_next_eventually). iModIntro. by iApply "IH".
    - iModIntro. iFrame.
  Qed.

  Lemma stenning_A_send i :
    ↓sA ((ASending, i)) ⊢ ◊ (↓sA ((ASending, i)) ∧ ↓l (A, Send (mAB i))) : tProp.
  Proof.
    iIntros "Hs".
    iDestruct (fair_sched A) as "H".
    iRevert "Hs".
    iApply (ltl_eventually_ind_strong with "[] H").
    iIntros "!> [H1|H2]".
    { iIntros "H'". iDestruct "H1" as "HA".
      iDestruct (ltl_dup with "H'") as "[H' H'']".
      iDestruct (stenning_ASending_A with "[$H' $HA]") as "[Hs Hl]".
      iModIntro. iFrame. }
    iDestruct "H2" as "[H1 H2]".
    iIntros "H'".
    iDestruct (ltl_dup with "H'") as "[H' H'']".
    iDestruct (ltl_dup with "H''") as "[H'' H''']".
    iDestruct (stenning_A_or_B with "[H''']") as "[HA|HB]".
    { iLeft. iDestruct (ltl_now_prod_fst with "H'''") as (?) "H'". iExists _.  iFrame. }
    { iDestruct (stenning_ASending_A with "[$H' $HA]") as "[Hs Hl]".
      iModIntro. iFrame. }
    iDestruct (stenning_A_B with "[$H' $HB]") as "Hs".
    iEval (rewrite -ltl_next_eventually).
    iModIntro.
    by iApply ("H2").
  Qed.

  Lemma stenning_A_advance i :
    ↓sA (AReceiving, i) ∧ ↓l (A, Recv A (Some $ mBA i)) ⊢ ○ ↓sA (ASending, S i) : tProp.
  Proof.
    iIntros "[Hs Hl]".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (stenning_AReceiving_A with "[$Hs Hl]") as (m) "[H|H]".
    { iApply ltl_now_label_prod_fst. by iExists _. }
    { iDestruct "H" as (Heq) "[Hl Hs]".
      iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'. simplify_eq. }
    iDestruct "H" as (->) "[Hl Hs]".
    iFrame.
  Qed.

  Lemma stenning_A_eventually_advance i :
    ↓sA (ASending, i) ∧ ◊ ↓l (A, Recv A (Some $ mBA i)) ⊢ ◊ ↓sA (ASending, S i) : tProp.
  Proof.
    assert (∃ stA, ASending = stA) as [stA Heq].
    { eauto. }
    rewrite {1}Heq. clear Heq.
    iIntros "[Hs Hl]". iRevert (stA) "Hs".
    iApply (ltl_eventually_ind_strong with "[] Hl").
    iIntros "!> [Hl|H]"; iIntros (stA) "Hs".
    { destruct stA.
      - rewrite -ltl_eventually_next.
        iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
        iDestruct (stenning_ASending_A with "[$Hs Hl]") as "[Hl Hs]".
        { iApply ltl_now_label_prod_fst. by iExists _. }
        iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'. simplify_eq.
      - rewrite -ltl_next_eventually. iDestruct (stenning_A_advance with "[$Hl $Hs]") as "Hs".
        iModIntro. iMod (stenning_disjoint_A with "Hs") as "[Hs Hl]".
        iModIntro. iFrame. }
    iDestruct "H" as "[H' IH]".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct (ltl_now_prod_fst with "Hs'") as (?) "Hs'". iFrame. }
    2: { iDestruct (stenning_A_B with "[$Hs $HB]") as "Hs".
      iEval (rewrite -ltl_next_eventually).
      iModIntro. by iApply "IH". }
    destruct stA.
    - iDestruct (stenning_ASending_A with "[$Hs $HA]") as "[Hl Hs]".
      iEval (rewrite -ltl_next_eventually).
      iModIntro.
      by iApply "IH".
    - iDestruct (stenning_AReceiving_A with "[$Hs $HA]")
        as (m) "[[%Hm [Hl Hs]]|[%Hm [Hl Hs]]]".
      + iEval (rewrite -ltl_next_eventually).
        iModIntro.
        iDestruct ("IH" with "Hs") as ">Hs".
        iModIntro. done.
      + iEval (rewrite -ltl_next_eventually).
        iModIntro. iModIntro. done.
  Qed.

  Lemma stenning_A_always_send i :
    (□ (¬ ↓sA (ASending, S i))) ∧
    ↓sA (ASending, i) ⊢ □ ◊ (↓sA (ASending, i) ∧ ↓l (A, Send (mAB i))) : tProp.
  Proof.
    iIntros "[#Hm Hs]".
    iMod (stenning_A_send with "Hs") as "[Hs Hl]".
    iApply (ltl_always_intro with "[] [Hs Hl]"); last first.
    { iModIntro. iFrame. }
    iIntros "!> >[Hs Hl]".
    iDestruct (stenning_ASending_A with "[$Hs Hl]") as "[Hl' Hs]".
    { iApply ltl_now_label_prod_fst. by iExists _. }
    iModIntro.
    iDestruct (stenning_disjoint_A with "Hs") as ">[Hs Hl]".
    iDestruct (stenning_AReceiving_A with "[$Hs $Hl]") as (m') "[(%Hm&Hl'&Hs)|(%Hm&Hl'&Hs)]".
    { rewrite -ltl_next_eventually. iModIntro. by iApply stenning_A_send. }
    subst.
    rewrite -ltl_next_eventually.
    iModIntro. iExFalso.
    iApply "Hm". done.
  Qed.

  Lemma stenning_A_try_recv i :
    ↓sA (ASending, i) ⊢
    ◊ ∃ om : option Message, ↓sA ((AReceiving, i)) ∧ ↓l (A, Recv A om)
    : tProp.
  Proof.
    iIntros "Hs".
    iDestruct (stenning_A_send with "Hs") as ">[Hs Hl]".
    iDestruct (stenning_ASending_A with "[$Hs Hl]") as "[Hl Hs]".
    { iApply ltl_now_label_prod_fst. by iExists _. }
    iEval (rewrite -ltl_next_eventually). iModIntro.
    iDestruct (fair_sched A) as "H".
    iRevert "Hs".
    iApply (ltl_eventually_ind_strong with "[] H").
    iIntros "!> [Hl|[_ IH]] Hs".
    { iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
      iDestruct (stenning_AReceiving_A with "[$Hs $Hl]") as (m) "[(?&?&?)|(?&?&?)]".
      - iModIntro. iExists m. iFrame.
      - iModIntro. iExists m. iFrame. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct (ltl_now_prod_fst with "Hs'") as (?) "Hs'". iFrame. }
    - iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
      iDestruct (stenning_AReceiving_A with "[$Hs $HA]") as (m) "[(?&?&?)|(?&?&?)]".
      + iModIntro. iExists m. iFrame.
      + iModIntro. iExists m. iFrame.
    - iDestruct (stenning_A_B with "[$Hs $HB]") as "H'".
      iEval (rewrite -ltl_next_eventually). iModIntro. by iApply "IH".
  Qed.

  Lemma stenning_A_always_try_recv i :
    (□ (¬ ↓sA (ASending, S i))) ∧ ↓sA (ASending, i)
    ⊢ □ ◊ ∃ om : option Message, ↓sA ((AReceiving, i)) ∧ ↓l (A, Recv A om)
    : tProp.
  Proof.
    iIntros "[#Hm Hs]".
    iMod (stenning_A_try_recv with "Hs") as "[%m [Hs Hl]]".
    iApply (ltl_always_intro with "[] [Hs Hl]"); last first.
    { iModIntro. iFrame. }
    iIntros "!> >[%m' [Hs Hl]]".
    iDestruct (stenning_AReceiving_A with "[$Hs Hl]") as (m'') "[H1|H2]".
    { iApply ltl_now_label_prod_fst. by iExists _. }
    - iDestruct "H1" as (?) "[Hl Hs]".
      iModIntro.
      iMod (stenning_A_try_recv with "Hs") as "[%m''' [Hs Hl]]".
      iExists _. iFrame.
    - iDestruct "H2" as (->) "[Hl Hs]".
      iModIntro. iExFalso. iApply "Hm". done.
  Qed.

  (* OBS: Hypothesis for this lemma is only needed for [stenning_B] *)
  Lemma stenning_B_always_try_recv :
    (□ ◊ ∃ l, ↓l l) ⊢ □ ◊ ∃ m, ↓l (B, Recv B m) : tProp.
  Proof.
    iIntros "#Hl !>". iMod "Hl".
    iDestruct (stenning_B with "[$Hl]") as (stB) "Hs".
    iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
    destruct stB as [[|] i].
    - iDestruct (stenning_BSending_B with "[$Hs $Hl]") as "[Hl Hs]".
      iEval (rewrite -ltl_next_eventually). iModIntro.
      iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
      iDestruct (stenning_BReceiving_B with "[$Hs $Hl]")
        as (m) "[(?&?&?)|[(%m'&?&?&?&?)|(?&?&?)]]".
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
    - iDestruct (stenning_BReceiving_B with "[$Hs $Hl]")
        as (m) "[(?&?&?)|[(%m'&?&?&?&?)|(?&?&?)]]".
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
      + iEval (rewrite -ltl_eventually_intro_now). iExists m. iFrame.
  Qed.

  Lemma stenning_B_recv i :
    □ ◊ ↓l (A, Send (mAB i)) ⊢ ◊ ↓l (B, Recv B $ Some (mAB i)) : tProp.
  Proof.
    iIntros "#H".
    iDestruct (stenning_B_always_try_recv with "[H]") as "#HB".
    { iModIntro. iMod "H". iModIntro. iExists _. iFrame. }
    iDestruct (fair_net _ (λ m, m = i) with "[H] HB") as "H'".
    { iModIntro. iMod "H". iModIntro. iExists i. iFrame. eauto. }
    iMod "H'" as (m ->) "H''".
    iModIntro. done.
  Qed.

  Lemma stenning_B_send i :
    ⊢
    □ (∃ stA, ↓sA (stA,i)) →
    □ ◊ ↓l (B, Recv B $ Some (mAB i)) →
    □ ◊ ↓l (B, Send (mBA i))
    : tProp.
  Proof.
    iIntros "#Hst #Hrecv". iModIntro.
    iAssert (∃ stA : stenning_A_state, ↓sA (stA, i))%I as "Hst'"; [by done|].
    iDestruct "Hst'" as (stA) "Hst'".
    iDestruct (stenning_safety_inv) as (j stA' stB) "[HstA HstB]".
    iDestruct (ltl_now_A_agree with "Hst' HstA") as %Heq.
    simplify_eq. iClear "Hst' HstA".
    iDestruct "HstB" as "[Hs|Hs]".
    - iDestruct (ltl_until_not_until with "Hrecv") as "Hrecv'".
      rewrite left_id.
      iRevert "Hs". iRevert (stB).
      iApply (ltl_until_ind_strong with "[] Hrecv'").
      iIntros "!> [Hl|(Hl&H&IH)]"; iIntros (stB) "Hs".
      { destruct stB.
        { iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
          iDestruct (stenning_BSending_B with "[$Hs $Hl]") as "[Hl Hs]".
          iModIntro. done. }
        iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
        iDestruct (stenning_BReceiving_B with "[$Hs Hl]") as "H".
        { iApply ltl_now_label_prod_fst. by iExists _. }
        iDestruct "H" as (m) "[H|[H|H]]".
        + iDestruct "H" as (->) "[Hl Hs]".
          iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq.
          simplify_eq.
        + iDestruct "H" as (m' ->) "[%Heq [Hl Hs]]".
          iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'.
          simplify_eq.
          iEval (rewrite -ltl_next_eventually). iModIntro.
          iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
          iDestruct (stenning_BSending_B with "[$Hs $Hl]") as "[Hl Hs]".
          iModIntro. done.
        + iDestruct "H" as (->) "[Hl Hs]".
          iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'.
          simplify_eq. lia. }
      destruct stB.
      + iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
        { iLeft. iDestruct (ltl_now_prod_snd with "Hs'") as (?) "Hs'". iFrame. }
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BSending_B with "[$Hs $HB]") as "[Hl' Hs]".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
      + iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
        { iLeft. iDestruct (ltl_now_prod_snd with "Hs'") as (?) "Hs'". iFrame. }
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BReceiving_B with "[$Hs $HB]") as (m) "[Hs|[Hs|Hs]]".
          -- iDestruct "Hs" as "(?&?&Hs)".
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             by iApply "IH".
          -- iDestruct "Hs" as (m') "(?&?&?&Hs)".
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             by iApply "IH".
          -- iDestruct "Hs" as (->) "(?&Hs)".
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             iDestruct "Hst" as (?) "Hst".
             iDestruct (stenning_safety_inv) as (i stA'' stB') "[HstA HstB]".
             iDestruct "HstB" as "[H1|H2]".
             ++ iDestruct (ltl_now_A_agree with "Hst HstA") as %Heq.
                simplify_eq.
                iDestruct (ltl_now_B_agree with "Hs H1") as %Heq.
                simplify_eq.
                lia.
             ++ iDestruct (ltl_now_A_agree with "Hst HstA") as %Heq.
                simplify_eq.
                iDestruct (ltl_now_B_agree with "Hs H2") as %Heq.
                simplify_eq.
                lia.
    - iDestruct (ltl_until_not_until with "Hrecv") as "Hrecv'".
      rewrite left_id.
      iRevert "Hs". iRevert (stB).
      iApply (ltl_until_ind_strong with "[] Hrecv'").
      iIntros "!> [Hl|(Hl&H&IH)]"; iIntros (stB) "Hs".
      { destruct stB.
        - iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
          iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
          iDestruct (stenning_BSending_B with "[$Hs Hl]") as "[Hl Hs]".
          { iApply ltl_now_label_prod_fst. by iExists _. }
          iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq.
          simplify_eq.
        - iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
          iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
          iDestruct (stenning_BReceiving_B with "[$Hs Hl]") as "H".
          { iApply ltl_now_label_prod_fst. by iExists _. }
          iDestruct "H" as (m) "[H|[H|H]]".
          + iDestruct "H" as (->) "[Hl Hs]".
            iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq.
            simplify_eq.
          + iDestruct "H" as (m' ->) "[%Heq [Hl Hs]]".
            iDestruct (ltl_now_lbl_agree with "Hl Hl'") as %Heq'.
            simplify_eq.
          + iDestruct "H" as (->) "[Hl Hs]".
            iEval (rewrite -ltl_next_eventually). iModIntro.
            iDestruct (stenning_disjoint_B with "Hs") as ">[Hs Hl]".
            iDestruct (stenning_BSending_B with "[$Hs $Hl]") as "[Hl Hs]".
            iModIntro. done. }
      destruct stB.
      + iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
        { iLeft. iDestruct (ltl_now_prod_snd with "Hs'") as (?) "Hs'". iFrame. }
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BSending_B with "[$Hs $HB]") as "[Hl' Hs]".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
      + iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
        { iLeft. iDestruct (ltl_now_prod_snd with "Hs'") as (?) "Hs'". iFrame. }
        * iDestruct (stenning_B_A with "[$Hs $HA]") as "Hs".
          iEval (rewrite -ltl_next_eventually).
          iModIntro.
          by iApply "IH".
        * iDestruct (stenning_BReceiving_B with "[$Hs $HB]") as (m) "[Hs|[Hs|Hs]]".
          -- iDestruct "Hs" as "(?&?&Hs)".
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             by iApply "IH".
          -- iDestruct "Hs" as (m') "(?&?&?&Hs)".
             iEval (rewrite -ltl_next_eventually).
             iModIntro.
             by iApply "IH".
          -- iDestruct "Hs" as(->)  "(?&Hs)".
             iExFalso. iApply "Hl". done.
  Qed.

  Lemma stenning_A_preserved i :
    ⊢ □ (¬ ↓sA (ASending, S i)) → ↓sA (ASending, i) → □ ∃ stA', ↓sA (stA', i).
  Proof.
    iIntros "#Hm Hs".
    iApply ltl_always_intro; last first.
    { iExists _. done. }
    iIntros "!> [%stA' Hs]".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (stenning_A_or_B with "[Hs']") as "[HA|HB]".
    { iLeft. iDestruct (ltl_now_prod_fst with "Hs'") as (?) "Hs'". iFrame. }
    2: { iDestruct (stenning_A_B with "[$Hs $HB]") as "H".
      iModIntro. iExists _. iFrame. }
    destruct stA'.
    - iDestruct (stenning_ASending_A with "[$Hs $HA]") as "[Hl Hs]".
      iModIntro. iExists _. done.
    - iDestruct (stenning_AReceiving_A with "[$Hs $HA]") as (m) "[H|H]".
      + iDestruct "H" as "(?&?&?)". iModIntro. iFrame.
      + iDestruct "H" as "(?&?&?)".
        iModIntro. iExFalso. iApply "Hm". done.
  Qed.

  Lemma stenning_A_advances i :
    ↓sA ((ASending, i)) ⊢ ◊ ↓sA ((ASending, S i)) : tProp.
  Proof.
    iIntros "HA".
    iAssert (◊ ↓sA (ASending, S i) ∨ □ (¬ ↓sA (ASending, S i)))%I as "[$|#Hm]".
    { iDestruct (ltl_excluded_middle (◊ ↓sA (ASending, S i))) as "[H|H]".
      { by iLeft. }
      iRight. by iApply ltl_not_eventually_always_not. }
    iDestruct (ltl_dup with "HA") as "[HA1 HA2]".
    iDestruct (ltl_dup with "HA2") as "[HA2 HA3]".
    iDestruct (fair_net _ (λ m, m = i) A with "[HA1] [HA2]") as "Hfair"; last first.
    { iApply (stenning_A_eventually_advance with "[$HA3 Hfair]").
      iMod "Hfair". iModIntro. iDestruct "Hfair" as (m ->) "Hfair". done. }
    { iDestruct (stenning_A_always_try_recv with "[$Hm $HA2]") as "#H".
      iIntros "!>". iMod "H" as (m) "[_ H]". iModIntro. eauto. }
    { iDestruct (stenning_A_always_send with "[$Hm $HA1]") as "#H".
      iDestruct (stenning_B_recv with "[H]") as "H'".
      { iModIntro. iMod "H". iModIntro. iDestruct "H" as "[_ $]". }
      iDestruct (stenning_B_send with "[Hm HA1] H'") as "#H''".
      { by iApply stenning_A_preserved. }
      iIntros "!>". iMod "H''". iModIntro. iFrame. done. }
  Qed.

  Theorem stenning_live i :
    ↓sA (ASending, 0) ⊢ ◊ (↓sA (ASending, i)) : tProp.
  Proof.
    iIntros "H".
    iDestruct (stenning_A_send with "H") as ">[Hs Hl]".
    iStopProof.
    induction i.
    { rewrite -ltl_eventually_intro_now. iIntros "[$ _]". }
    iIntros "[Hs Hl]".
    iDestruct (IHi with "[$Hs $Hl]") as ">Hs".
    iDestruct (stenning_A_advances with "Hs") as ">Hs".
    iModIntro.
    iFrame.
  Qed.

  Theorem stenning_live_label i :
    ↓sA (ASending, 0) ⊢ ◊ (↓l (A, Send (mAB i))) : tProp.
  Proof.
    iIntros "H".
    iDestruct (stenning_live i with "H") as ">H".
    iDestruct (stenning_A_send with "H") as ">[_ Hl]".
    iModIntro. done.
  Qed.

  Theorem stenning_live_meta
    (tr : wf_trace stenning_state stenning_label stenning_trans) i :
    fst <$> (fst <$> wf_head tr) = Some ((ASending, 0)) →
    ∃ n, fst <$> (fst <$> wf_head (wf_after n tr)) = Some (ASending, i).
  Proof.
    pose proof (stenning_live i).
    revert H. adequacy_unseal.
    naive_solver.
  Qed.

  Theorem stenning_live_label_meta
    (tr : wf_trace stenning_state stenning_label stenning_trans) i :
    fst <$> (fst <$> wf_head tr) = Some ((ASending, 0)) →
    ∃ n, mjoin (snd <$> wf_head (wf_after n tr)) = Some (A, Send (mAB i)).
  Proof.
    pose proof (stenning_live_label i).
    revert H. adequacy_unseal. 
    intros. setoid_rewrite option_fmap_id in H.
    naive_solver.
  Qed.

End stenning_ex.
