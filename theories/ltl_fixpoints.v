(* From iris.proofmode Require Import coq_tactics reduction spec_patterns. *)
From iris.proofmode Require Import modality_instances.
From iris.bi Require Export fixpoint_mono.
From ltl Require Export ltl.

Section ltl_until.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  (* Until *)
  Definition ltl_until_F (P Q : tProp) : (() → tProp) → (() → tProp) :=
    (λ (X : unit → tProp) _, Q ∨ (P ∧ ○ (X ())))%I.

  Instance ltl_until_F_mono P Q : BiMonoPred (ltl_until_F P Q).
  Proof.
    constructor.
    - intros. iIntros "#H" (x) "HF".
      rewrite /ltl_until_F.
      iDestruct "HF" as "[HQ|[HP HF]]"; [by iLeft|].
      iRight. iFrame.
      iModIntro. by iApply "H".
    - intros. apply _.
  Qed.

  Definition ltl_until_def (P Q : tProp) : tProp :=
    bi_least_fixpoint (ltl_until_F P Q)%I ().
  Definition ltl_until_aux : seal (@ltl_until_def).
  Proof. by eexists. Qed.
  Definition ltl_until := unseal ltl_until_aux.
  Definition ltl_until_unseal :
    @ltl_until = @ltl_until_def := seal_eq ltl_until_aux.

  Notation "P ∪ Q" := (ltl_until P Q%I) : bi_scope.
  Notation "◊ P" := (ltl_until True P%I) (at level 20, right associativity) : bi_scope.

  Lemma ltl_until_unfold (P Q : tProp) :
    (P ∪ Q)%I ≡ (Q ∨ P ∧ ○ (P ∪ Q))%I.
  Proof. rewrite ltl_until_unseal. by rewrite /ltl_until_def {1}least_fixpoint_unfold. Qed.

  Lemma ltl_until_intro (P Q : tProp) :
    Q ∨ P ∧ ○ (P ∪ Q) ⊢ P ∪ Q.
  Proof. rewrite {2}ltl_until_unfold. done. Qed.

  Lemma ltl_until_ind_strong (P Q R : tProp) :
    □ (Q ∨ (P ∧ ○ (P ∪ Q) ∧ ○ R) → R) ⊢
    P ∪ Q → R.
  Proof.
    iIntros "#IH HPQ".
    rewrite ltl_until_unseal.
    iApply (least_fixpoint_ind with "[] HPQ").
    iIntros "!>" (?) "[Q|[HP HR]]".
    { iApply "IH". by eauto. }
    iApply "IH". iRight. iFrame.
    iSplit.
    - iModIntro. iDestruct "HR" as "[_ $]".
    - iModIntro. iDestruct "HR" as "[$ _]".
  Qed.

  Lemma ltl_until_ind (P Q R : tProp) :
    (Q ∨ (P ∧ ○ (P ∪ Q) ∧ ○ R) ⊢ R) →
    (P ∪ Q ⊢ R).
  Proof. intros IH. iApply ltl_until_ind_strong. iIntros "!> H". iApply IH. done. Qed.

  Lemma ltl_until_intro_now (P Q : tProp) :
    Q ⊢ P ∪ Q.
  Proof. rewrite -ltl_until_intro. apply bi.or_intro_l. Qed.

  Lemma ltl_until_intro_next (P Q : tProp) :
    P ∧ ○ (P ∪ Q) ⊢ P ∪ Q.
  Proof. rewrite -{2}ltl_until_intro. apply bi.or_intro_r. Qed.

  Lemma ltl_until_mono_strong P1 P2 Q1 Q2 :
    □ (P1 → P2) ⊢ □ (Q1 → Q2) →
    P1 ∪ Q1 → P2 ∪ Q2.
  Proof.
    iIntros "#HP #HQ HPQ".
    iApply (ltl_until_ind_strong with "[] HPQ").
    iModIntro.
    iDestruct 1 as "[H|H]".
    { rewrite ltl_until_unfold. iLeft. by iApply "HQ". }
    iEval (rewrite ltl_until_unfold). iRight.
    iDestruct "H" as "[H IH]".
    iSplit.
    - by iApply "HP".
    - iDestruct "IH" as "[_ $]".
  Qed.

  Lemma ltl_until_mono P1 P2 Q1 Q2 :
    (P1 ⊢ P2) → (Q1 ⊢ Q2) →
    P1 ∪ Q1 ⊢ P2 ∪ Q2.
  Proof.
    intros HP HQ.
    iApply ltl_until_mono_strong.
    iApply HP.
    iApply HQ.
  Qed.

  Lemma ltl_until_and (P Q1 Q2 : tProp) :
    (P ∪ (Q1 ∧ Q2)) ⊢ (P ∪ Q1) ∧ (P ∪ Q2).
  Proof.
    rewrite ltl_until_unfold.
    iIntros "[H|H]".
    { iDestruct "H" as "[H1 H2]".
      rewrite (ltl_until_unfold _ Q1).
      rewrite (ltl_until_unfold _ Q2).
      iSplit; by iLeft. }
    iSplit.
    - iEval (rewrite ltl_until_unfold).
      iRight. iDestruct "H" as "[$ H]".
      iModIntro. iApply (ltl_until_mono_strong with "[] [] H").
      + eauto.
      + iIntros "!>[$ _]".
    - iEval (rewrite ltl_until_unfold).
      iRight. iDestruct "H" as "[$ H]".
      iModIntro. iApply (ltl_until_mono_strong with "[] [] H").
      + eauto.
      + iIntros "!>[_ $]".
  Qed.

  Lemma ltl_until_always_combine (P Q R : tProp) :
    (□ P ∧ Q ∪ R) ⊢ (((Q ∧ □ P) ∪ (R ∧ □ P))).
  Proof.
    iIntros "[#HP HQ]".
    iApply (ltl_until_ind_strong with "[] HQ").
    iIntros "!> [HQ|H]".
    { iApply ltl_until_intro_now. iFrame "#∗". }
    iEval (rewrite -ltl_until_intro_next).
    iDestruct "H" as "[$ H]".
    iSplit; [done|].
    iModIntro.
    iDestruct "H" as "[_ $]".
  Qed.

  Lemma ltl_until_next_comm (P Q : tProp) :
    (○ P ∪ ○ Q) ⊣⊢ ○ (P ∪ Q).
  Proof.
    iSplit.
    - iApply ltl_until_ind_strong.
      iIntros "!>H".
      iDestruct "H" as "[HQ|H]".
      + iModIntro. rewrite ltl_until_unfold. by iLeft.
      + iModIntro. iEval (rewrite ltl_until_unfold). iRight.
        iDestruct "H" as "[$ [HP HQ]]". iModIntro. done.
    - iIntros "H".
      iEval (rewrite ltl_until_unfold).
      rewrite ltl_next_and.
      iEval (rewrite (ltl_next_or Q)).
      iModIntro.
      iApply (ltl_until_ind_strong with "[] H").
      iIntros "!>H".
      iDestruct "H" as "[H|H]".
      { iLeft. done. }
      iRight.
      iDestruct "H" as "[$ [_ H]]".
      rewrite {2}ltl_until_unfold.
      rewrite ltl_next_and ltl_next_or.
      iModIntro.
      iDestruct "H" as "[H|H]".
      { iLeft. done. }
      iRight.
      done.
  Qed.

  Lemma ltl_until_idemp (P Q : tProp) :
    (P ∪ (P ∪ Q)) ⊣⊢ (P ∪ Q).
  Proof.
    iSplit.
    - iApply ltl_until_ind_strong.
      iIntros "!> [H|(?&?&?)]".
      { done. }
      iEval (rewrite ltl_until_unfold). iRight. iFrame.
    - iApply ltl_until_ind_strong.
      iIntros "!> [H|(?&?&?)]".
      { rewrite ltl_until_unfold. iLeft. rewrite ltl_until_unfold. iLeft. done. }
      iEval (rewrite ltl_until_unfold). iRight. iFrame.
  Qed.

  Lemma ltl_until_and_r' (P1 P2 Q1 Q2 : tProp) :
    P1 ∪ Q1 ∧ P2 ∪ Q2 ⊢ (P1 ∧ P2) ∪ ((Q1 ∧ P2 ∪ Q2) ∨ (P1 ∪ Q1 ∧ Q2)).
  Proof.
    iIntros "[H1 H2]".
    iRevert "H2".
    iApply (ltl_until_ind_strong with "[] H1").
    iIntros "!> H1 H2".
    rewrite {3}(ltl_until_unfold P2 Q2).
    iDestruct "H1" as "[HQ1|(HP1&HPQ1&IH)]".
    { iDestruct "H2" as "[HQ2|[HP2 HPQ2]]".
      { iEval (rewrite ltl_until_unfold). iLeft.
        iEval (rewrite ltl_until_unfold). iFrame. }
      { iEval (rewrite ltl_until_unfold). iLeft. iLeft. iFrame.
        iEval (rewrite ltl_until_unfold). iRight. iFrame. }
    }
    iDestruct "H2" as "[HQ2|[HP2 HPQ2]]".
    { iEval (rewrite ltl_until_unfold). iLeft.
      iEval (rewrite ltl_until_unfold). iRight.
      iEval (rewrite ltl_until_unfold). iFrame. iRight. iFrame. }
    iEval (rewrite ltl_until_unfold). iRight.
    iFrame. iModIntro.
    by iApply "IH".
  Qed.

  Lemma ltl_until_or (P Q1 Q2 : tProp) :
    P ∪ (Q1 ∨ Q2) ⊢ P ∪ Q1 ∨ P ∪ Q2.
  Proof.
    iApply ltl_until_ind_strong.
    iIntros "!> [HQ|HP]".
    { iDestruct "HQ" as "[HQ1|HQ2]".
      - iLeft. by rewrite -ltl_until_intro_now.
      - iRight. by rewrite -ltl_until_intro_now.
    }
    iDestruct "HP" as "(HP&HPQ&IH)".
    rewrite -!ltl_until_next_comm.
    rewrite {1}(ltl_next_or_2 (P ∪ Q1)).
    iDestruct "IH" as "[IH|IH]".
    - iLeft. iEval (rewrite ltl_until_unfold).
      iRight. iFrame.
    - iRight. iEval (rewrite ltl_until_unfold).
      iRight. iFrame.
  Qed.

  Lemma ltl_until_and_r (P1 P2 Q1 Q2 : tProp) :
    P1 ∪ Q1 ∧ P2 ∪ Q2 ⊢ ((P1 ∧ P2) ∪ (Q1 ∧ (P2 ∪ Q2))) ∨ ((P1 ∧ P2) ∪ (P1 ∪ Q1 ∧ Q2)).
  Proof. rewrite -ltl_until_or. apply ltl_until_and_r'. Qed.

  Global Instance ltl_until_proper : Proper ((≡) ==> (≡) ==> (≡)) (ltl_until).
  Proof.
    constructor.
    intros. split.
    - apply ltl_until_mono; [by rewrite H|by rewrite H0].
    - apply ltl_until_mono; [by rewrite H|by rewrite H0].
  Qed.
  Global Instance ltl_until_mono' :
    Proper ((⊢) ==> (⊢) ==> (⊢)) (ltl_until).
  Proof.
    constructor.
    intros ?. apply ltl_until_mono; [by rewrite H|by rewrite H0].
  Qed.
  Global Instance ltl_until_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (ltl_until).
  Proof.
    constructor.
    intros ?. apply ltl_until_mono; [by rewrite H|by rewrite H0].
  Qed.

  Global Instance ltl_until_combine (P1 P2 Q1 Q2 : tProp) :
    CombineSepAs (P1 ∪ Q1) (P2 ∪ Q2)
      (((P1 ∧ P2) ∪ (Q1 ∧ (P2 ∪ Q2))) ∨ ((P1 ∧ P2) ∪ (P1 ∪ Q1 ∧ Q2))) | 1.
  Proof. rewrite /CombineSepAs. apply ltl_until_and_r. Qed.

  Lemma ltl_eventually_intro (P : tProp) :
    P ∨ ○ ◊ P ⊢ ◊ P.
  Proof.
    rewrite -{2}(ltl_until_intro True P).
    iIntros "[HP|HP]".
    { by iLeft. }
    iRight. by iFrame.
  Qed.

  Lemma ltl_eventually_intro_now (P : tProp) :
    P ⊢ ◊ P.
  Proof. rewrite -ltl_until_intro. apply bi.or_intro_l. Qed.

  Lemma ltl_eventually_intro_next (P : tProp) :
    (○ P) ⊢ (◊ P).
  Proof. rewrite -ltl_eventually_intro.
         etrans; [|apply bi.or_intro_r]. apply ltl_next_mono.
         apply ltl_eventually_intro_now.
  Qed.

  Lemma ltl_eventually_mono_strong (P Q : tProp) :
    □ (P → Q) ⊢ ◊P → ◊Q.
  Proof. by iApply ltl_until_mono_strong. Qed.

  Lemma ltl_eventually_mono (P Q : tProp) :
    (P ⊢ Q) → (◊P) ⊢ (◊Q).
  Proof. by apply ltl_until_mono. Qed.

  Lemma ltl_eventually_and (P Q : tProp) :
    (◊ (P ∧ Q)) ⊢ (◊ P) ∧ (◊ Q).
  Proof. by rewrite -ltl_until_and. Qed.

  Lemma ltl_eventually_next_comm (P : tProp) :
    (◊ ○ P) ⊣⊢ (○ ◊ P).
  Proof.
    rewrite -ltl_until_next_comm.
    apply bi.equiv_entails_2.
    - apply ltl_until_mono; [|done]. by apply ltl_next_emp.
    - apply ltl_until_mono; [|done]. eauto.
  Qed.

  Lemma ltl_eventually_idemp (P : tProp) :
    (◊◊P) ⊣⊢ (◊P).
  Proof. apply ltl_until_idemp. Qed.

  Lemma ltl_eventually_next (P : tProp) :
    (◊ ○ P) ⊢ (◊ P).
  Proof.
    rewrite <-(ltl_eventually_idemp P).
    apply ltl_eventually_mono.
    apply ltl_eventually_intro_next.
  Qed.

  Lemma ltl_next_eventually (P : tProp) :
    (○ ◊ P) ⊢ (◊ P).
  Proof. rewrite -{2}ltl_eventually_next ltl_eventually_next_comm. done. Qed.

  Lemma ltl_until_eventually_equiv (P : tProp) :
    (True ∪ P) ⊣⊢ (◊ P).
  Proof. done. Qed.

  Lemma ltl_until_eventually (P Q : tProp) :
    (P ∪ Q) ⊢ (◊ Q).
  Proof. apply ltl_until_mono; by eauto. Qed.

  Lemma ltl_eventually_ind_strong (P Q : tProp) :
    (□ (P ∨ ○ ◊ P ∧ ○ Q → Q)) ⊢ ◊ P → Q.
  Proof.
    iIntros "#H". iApply ltl_until_ind_strong.
    iModIntro. iIntros "[HP|HP]".
    { iApply "H". iLeft. done. }
    iApply "H". iRight. iDestruct "HP" as "[_ $]".
  Qed.

  Lemma ltl_eventually_ind (P Q : tProp) :
    (P ⊢ Q) →
    ((○ ◊ P) ∧ ○ Q ⊢ Q) →
    ◊ P ⊢ Q.
  Proof.
    intros H1 H2.
    iApply ltl_eventually_ind_strong.
    iDestruct H1 as "#H1".
    iDestruct H2 as "#H2".
    iModIntro. iIntros "[HP|HP]"; [by iApply "H1"|by iApply "H2"].
  Qed.

  Lemma ltl_always_eventually (P : tProp) :
    □ P ⊢ ◊ P.
  Proof. rewrite -ltl_eventually_intro_now. eauto. Qed.

  Lemma ltl_eventually_always_combine (P Q : tProp) :
    (□ P ∧ ◊Q) ⊢ (◊ (Q ∧ □ P)).
  Proof.
    iIntros "[#HP HQ]".
    iApply (ltl_eventually_ind_strong with "[] HQ").
    iIntros "!> [HQ|H]".
    { iApply ltl_eventually_intro_now. iFrame "#∗". }
    iEval (rewrite -ltl_eventually_idemp).
    iEval (rewrite -ltl_eventually_intro_next).
    iModIntro.
    iDestruct "H" as "[_ $]".
  Qed.

  Lemma ltl_not_eventually_always_not (P : tProp) :
    ¬ ◊ P ⊢ □ (¬ P).
  Proof.
    iIntros "H".
    iAssert (□ ((¬ ◊ P) ∧ (¬ P)))%I with "[H]" as "#[H1 H2]"; last first.
    { iApply ltl_always_intro; last first.
      { done. }
      iIntros "!> H !>". iFrame "#". }
    iApply ltl_always_intro; last first.
    { iSplit.
      - done.
      - iIntros "HP". iApply "H". rewrite -ltl_eventually_intro_now. done. }
    iIntros "!> [H1 H2]".
    rewrite -ltl_next_and.
    iSplit.
    - rewrite -ltl_next_not. iIntros "H". iApply "H1". rewrite ltl_next_eventually. done.
    - rewrite -ltl_next_not. iIntros "H". iApply "H1". rewrite -ltl_next_eventually. iModIntro. rewrite -ltl_eventually_intro_now. done.
  Qed.

  Global Instance into_and_eventually (P Q1 Q2 : tProp) :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (◊ P)%I (◊ Q1)%I (◊ Q2)%I.
  Proof.
    rewrite /IntoAnd. simpl.
    intros HPQ.
    rewrite -ltl_eventually_and.
    by eapply ltl_eventually_mono.
  Qed.

  Global Instance into_sep_eventually (P Q1 Q2 : tProp) :
    IntoSep P Q1 Q2 →
    IntoSep (◊ P)%I (◊ Q1)%I (◊ Q2)%I.
  Proof.
    rewrite /IntoSep.
    simpl.
    rewrite !bi_sep_and.
    intros HPQ.
    rewrite -ltl_eventually_and.
    by eapply ltl_eventually_mono.
  Qed.

  Global Instance into_next_eventually (P Q : tProp) :
    IntoNext false P Q →
    IntoNext false (◊ P) (◊ Q).
  Proof.
    rewrite /IntoNext. intros HPQ.
    rewrite -ltl_eventually_next_comm.
    eapply ltl_eventually_mono.
    specialize HPQ. simpl in HPQ.
    done.
  Qed.

  Lemma ltl_eventually_and_r (P Q : tProp) :
    ◊ P ∧ ◊ Q ⊢ ◊ (P ∧ ◊ Q) ∨ ◊ (◊ P ∧ Q).
  Proof. by rewrite ltl_until_and_r right_id. Qed.

  Global Instance ltl_eventually_combine (P Q : tProp) :
    CombineSepAs (◊ P) (◊ Q) (◊ (P ∧ ◊ Q) ∨ ◊ (◊ P ∧ Q)) | 0.
  Proof. rewrite /CombineSepAs. apply ltl_eventually_and_r. Qed.

  Class IntoUntil (P Q R : tProp) :=
    into_until : P ⊢ Q ∪ R.

  Class FromUntil (P Q R : tProp) :=
    from_until : P ∪ Q ⊢ R.

  Class EquivUntil (P Q R : tProp) :=
    equiv_until : P ≡ (Q ∪ R)%I.

  Global Instance ltl_from_into_until_equiv P Q R :
    IntoUntil P Q R →
    FromUntil Q R P →
    EquivUntil P Q R | 10.
  Proof.
    rewrite /IntoUntil /FromUntil /EquivUntil.
    intros H1 H2.
    iSplit.
    - rewrite H1. eauto.
    - rewrite H2. eauto. 
  Qed.

  Global Instance into_until_refl (P Q : tProp) :
    IntoUntil (P ∪ Q) P Q | 0.
  Proof. done. Qed.

  Global Instance from_until_refl (P Q : tProp) :
    FromUntil P Q (P ∪ Q) | 0.
  Proof. done. Qed.

  (* Global Instance EquivUntil_refl (P Q : tProp) : *)
  (*   EquivUntil (P ∪ Q) P Q | 0. *)
  (* Proof. done. Qed. *)

  Global Instance into_until_next (P Q R : tProp) :
    IntoUntil P Q R →
    IntoUntil (○ P) (○ Q) (○ R) | 2.
  Proof.
    intros. rewrite /IntoUntil. rewrite ltl_until_next_comm. by rewrite H.
  Qed.

  Global Instance from_until_next (P Q R : tProp) :
    FromUntil P Q R →
    FromUntil (○ P) (○ Q) (○ R) | 2.
  Proof.
    intros. rewrite /FromUntil. rewrite ltl_until_next_comm. by rewrite H.
  Qed.

  (* Global Instance EquivUntil_next (P Q R : tProp) : *)
  (*   EquivUntil P Q R → *)
  (*   EquivUntil (○ P) (○ Q) (○ R) | 2. *)
  (* Proof. *)
  (*   intros. rewrite /EquivUntil. rewrite ltl_until_next_comm. by rewrite H. *)
  (* Qed. *)

  (* Rename to into_eventually? *)
  Global Instance into_until_next' (P Q : tProp) :
    IntoUntil P True Q →
    IntoUntil (○ P) True (○ Q) | 1.
  Proof.
    intros. rewrite /IntoUntil.
    rewrite ltl_eventually_next_comm. rewrite H. done.
  Qed.

  Global Instance from_until_next' (P Q : tProp) :
    FromUntil True P Q →
    FromUntil True (○ P) (○ Q) | 1.
  Proof.
    intros. rewrite /FromUntil.
    rewrite ltl_eventually_next_comm. rewrite H. done.
  Qed.

  Global Instance elim_modal_until p P Q Q' R R' :
    IntoUntil R' P Q' →
    FromUntil P Q R →
    ElimModal True p false modality_persistently R' Q' R (P ∪ Q) | 2.
  Proof.
    intros HP HP'.
    rewrite /ElimModal.
    iIntros "_ [HP' HP]".
    destruct p; simpl.
    - rewrite HP -HP'.
      iDestruct "HP'" as "#HP'".
      iDestruct "HP" as "#HP".
      iEval (rewrite -ltl_until_idemp).
      by iApply (ltl_until_mono_strong P P Q'); [eauto| |done].
    - rewrite HP -HP'.
      iDestruct "HP" as "#HP".
      iEval (rewrite -ltl_until_idemp).
      by iApply (ltl_until_mono_strong P P Q'); [eauto| |done].
  Qed.

  Global Instance elim_modal_until_strong p P P' Q R R' :
    EquivUntil P Q R →
    EquivUntil P' Q R' →
    ElimModal True p false modality_persistently P' R' P P | 1.
  Proof.
    intros HP HP'.
    rewrite /ElimModal.
    iIntros "_ [HP' HP]".
    destruct p; simpl.
    - rewrite HP HP'.
      iDestruct "HP'" as "#HP'".
      iDestruct "HP" as "#HP".
      iEval (rewrite -ltl_until_idemp).
      by iApply (ltl_until_mono_strong Q Q R'); [eauto| |done].
    - rewrite HP HP'.
      iDestruct "HP" as "#HP".
      iEval (rewrite -ltl_until_idemp).
      by iApply (ltl_until_mono_strong Q Q R'); [eauto| |done].
  Qed.

  Global Instance from_exist_until {A} P Q (Φ : A → tProp) :
    FromExist Q Φ → Inhabited A → FromExist (P ∪ Q) (λ a, (Φ a))%I.
  Proof.
    rewrite /FromExist=> HP ?. rewrite -ltl_until_intro.
    rewrite -bi.or_intro_l. done.
  Qed.

  Lemma ltl_always_until_idemp (P Q : tProp) :
    (□ (P ∪ Q))%I ≡ (P ∪ (□ (P ∪ Q)))%I.
  Proof.
    iSplit.
    { iIntros "H". iEval (rewrite -ltl_until_intro_now). done. }
    iApply ltl_until_ind_strong.
    iIntros "!> [H|(HP&H&IH)]".
    { done. }
    rewrite -ltl_always_next_comm.
    iDestruct "IH" as "#IH".
    iApply ltl_always_intro.
    { iDestruct "IH" as "#IH". iModIntro. eauto. }
    iEval (rewrite -ltl_until_intro_next).
    iFrame. done.
  Qed.

  Lemma ltl_always_eventually_idemp (P : tProp) :
    (□ ◊ P)%I ≡ (◊ □ ◊ P)%I.
  Proof. apply ltl_always_until_idemp. Qed.

  (* OBS: This is necessary to iMod with goals such as [□ ◊ P] *)
  Global Instance from_until_always' (P Q R : tProp) :
    EquivUntil P Q R →
    EquivUntil (□ P) Q (□ P) | 1.
  Proof.
    intros. rewrite /EquivUntil. rewrite H. apply ltl_always_until_idemp.
  Qed.

  Global Instance into_wand_until q R (P Q1 Q2 : tProp) :
    IntoWand true false R Q1 Q2 →
    IntoWand true q R (P ∪ Q1) (P ∪ Q2) | 10.
  Proof.
    rewrite /IntoWand /= => HR.
    iIntros "#HR". destruct q.
    - simpl. iIntros "#H". iApply (ltl_until_mono_strong with "[] [] H").
      + eauto.
      + iIntros "!> HQ". by iApply HR.
    - simpl. iIntros "H". iApply (ltl_until_mono_strong with "[] [] H").
      + eauto.
      + iIntros "!>". by iApply HR.
  Qed.

  Lemma ltl_false_eventually :
    ◊ False ⊢ False.
  Proof.
    iApply ltl_eventually_ind; [done|].
    rewrite ltl_false_next. iDestruct 1 as "[_ $]".
  Qed.

  Global Instance from_modal_until (P Q : tProp) :
    @FromModal ltlI ltlI _ True%type modality_id (P ∪ Q) (P ∪ Q) (Q) | 2.
  Proof. intros _. apply ltl_until_intro_now. Qed.

  Global Instance from_next_until (P Q : tProp) : FromNext (P ∪ Q) ((○ P) ∪ (○ Q)) | 2.
  Proof. rewrite /FromNext. by rewrite ltl_until_next_comm. Qed.

  Global Instance from_next_eventually (P : tProp) : FromNext (◊ P) (◊ ○ P).
  Proof. rewrite /FromNext. by rewrite ltl_eventually_next_comm. Qed.

End ltl_until.

Global Notation "P ∪ Q" := (ltl_until P Q%I) : bi_scope.
Global Notation "◊ P" := (ltl_until True P%I) (at level 20, right associativity) : bi_scope.
