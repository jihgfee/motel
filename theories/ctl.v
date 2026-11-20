From ltl Require Import ltl ltl_fixpoints.

Import tProp.

Section ctl_definitions.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Definition ltl_forall_path_def (P : tProp) : tProp :=
    λ tr, ∀ (tr' : wf_trace S L Rel), wf_head tr' = wf_head tr → P tr'.
  Definition ltl_forall_path_aux : seal (@ltl_forall_path_def).
  Proof. by eexists. Qed.
  Definition ltl_forall_path := unseal ltl_forall_path_aux.
  Definition ltl_forall_path_unseal :
    @ltl_forall_path = @ltl_forall_path_def := seal_eq ltl_forall_path_aux.

  Definition ltl_exists_path_def (P : tProp) : tProp :=
    λ tr, ∃ (tr' : wf_trace S L Rel), wf_head tr' = wf_head tr ∧ P tr'.
  Definition ltl_exists_path_aux : seal (@ltl_exists_path_def).
  Proof. by eexists. Qed.
  Definition ltl_exists_path := unseal ltl_exists_path_aux.
  Definition ltl_exists_path_unseal :
    @ltl_exists_path = @ltl_exists_path_def := seal_eq ltl_exists_path_aux.

End ctl_definitions.

Notation "∀∀ P" :=
  (ltl_forall_path P%I) 
  (at level 200)
    : bi_scope.
Notation "∃∃ P" :=
  (ltl_exists_path P%I)
  (at level 200)
    : bi_scope.

Section ctl_lemmas.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).
  
  Lemma ltl_forall_path_mono (P Q : tProp) :
    (P ⊢ Q) →
    (∀∀ P) ⊢@{tProp} ∀∀ Q.
  Proof.
    intros HPQ.
    rewrite ltl_forall_path_unseal /ltl_forall_path_def.
    constructor.
    intros. simpl.
    specialize (H tr').
    apply HPQ. apply H. apply H0.
  Qed.

  Lemma ltl_exists_path_mono (P Q : tProp) :
    (P ⊢ Q) →
    (∃∃ P) ⊢@{tProp} ∃∃ Q.
  Proof.
    intros HPQ.
    rewrite ltl_exists_path_unseal /ltl_exists_path_def.
    constructor.
    intros. simpl.
    destruct H as (tr'&Heq&HP).
    exists tr'. split; [done|].
    by apply HPQ.
  Qed.

  (* TODO: Can we derive this internally? *)
  Lemma ltl_exists_path_mono_strong (P Q : tProp) :
    ⊢ (∀∀ (P → Q)) → (∃∃ P) → (∃∃ Q).
  Proof.    
    constructor.
    rewrite ltl_forall_path_unseal /ltl_forall_path_def.
    rewrite ltl_exists_path_unseal /ltl_exists_path_def.
    unseal. 
    intros tr _ HPQ [tr' [Htr HP]].
    apply HPQ in HP; [|done].
    eexists _. eauto.
  Qed.

  Lemma ltl_forall_path_taut :
    ⊢@{tProp} ∀∀ True.
  Proof.
    constructor. intros.
    rewrite ltl_forall_path_unseal /ltl_forall_path_def.
    intros. unseal. done.
  Qed.

  Lemma ltl_forall_path_idemp (P : tProp) :
    (∀∀ P) ⊢ ∀∀ ∀∀ P.
  Proof.
    constructor.
    rewrite ltl_forall_path_unseal /ltl_forall_path_def.
    intros. apply H. rewrite H1. done.
  Qed.

  Lemma ltl_forall_path_elim (P : tProp) :
    (∀∀ P) ⊢ P.
  Proof.
    constructor.
    rewrite ltl_forall_path_unseal /ltl_forall_path_def.
    intros. apply H. done.
  Qed.

  Lemma ltl_forall_path_and (P Q : tProp) :
    (∀∀ P) ∧ (∀∀ Q) ⊣⊢@{tProp} ∀∀ (P ∧ Q).
  Proof.
    constructor. intros.
    rewrite ltl_forall_path_unseal /ltl_forall_path_def.
    intros. unseal. 
    split.
    - intros. destruct H as [H1 H2]. split.
      + by apply H1.
      + by apply H2.
    - intros. split.
      + intros. by apply H.
      + intros. by apply H.
  Qed.

  Lemma ltl_exists_path_taut :
    ⊢@{tProp} ∃∃ True.
  Proof.
    constructor. intros.
    rewrite ltl_exists_path_unseal /ltl_exists_path_def.
    intros. unseal. exists tr. done.
  Qed.

  Lemma ltl_forall_exists_path (P : tProp) :
    (∀∀ P) ⊢@{tProp} ∃∃ P.
  Proof.
    constructor.
    rewrite ltl_forall_path_unseal /ltl_forall_path_def.
    rewrite ltl_exists_path_unseal /ltl_exists_path_def.
    intros.
    specialize (H tr). exists tr. split; [done|].
    by apply H.
  Qed.

End ctl_lemmas.

Section ctl_proofmode.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Class IntoForallPath (p:bool) (P Q : tProp) :=
    into_forall_path : □?p P ⊢ ∀∀ Q.
  Global Arguments IntoForallPath _ _%I _%I : simpl never.
  Global Arguments into_forall_path _ _%I _%I {_}.
  Global Hint Mode IntoForallPath ! ! - : typeclass_instances.

  Global Instance into_forall_path_forall_path p P :
    IntoForallPath p (∀∀ P) P.
  Proof.
    rewrite /IntoForallPath.
    destruct p; simpl; by iIntros "HP".
  Qed.

  Class FromForallPath (P Q : tProp) :=
    from_forall_path : (∀∀ P) ⊢ Q.
  Global Arguments FromForallPath _%I _%I : simpl never.
  Global Arguments from_forall_path _%I _%I {_}.
  Global Hint Mode FromForallPath - ! : typeclass_instances.

  Global Instance from_forall_path_forall_path (P : tProp) :
    FromForallPath P (∀∀ P) | 1.
  Proof. done. Qed.
  
  Lemma modality_forall_path_mixin : modality_mixin ltl_forall_path
    (MIEnvClear)
    (MIEnvTransform (IntoForallPath false)).
  Proof.
    split; simpl; eauto.
    - intros. apply ltl_forall_path_taut.
    - by apply ltl_forall_path_mono.
    - iIntros (P Q) "[HP HQ]". iApply ltl_forall_path_and. by iSplit.
  Qed.
  Definition modality_forall_path := Modality ltl_forall_path modality_forall_path_mixin.
  Global Instance from_modal_forall_path (P Q : tProp) :
    FromForallPath P Q → FromModal True modality_forall_path Q Q P | 1.
  Proof. rewrite /FromModal /=. done. Qed.

  Global Instance elim_modal_forall_path p P P' Q :
    IntoForallPath p P P' →
    ElimModal True p false modality_id P P' Q Q.
  Proof.
    intros HP.
    rewrite /ElimModal.
    iIntros "_ [HP' HP]".
    destruct p; simpl.
    - rewrite /IntoForallPath in HP.
      simpl in *. rewrite HP.
      iApply "HP". by iApply ltl_forall_path_elim.
    - rewrite /IntoForallPath in HP.
      simpl in *. rewrite HP.
      iApply "HP". by iApply ltl_forall_path_elim.
  Qed.

  Class IntoExistsPath (p:bool) (P Q : tProp) :=
    into_exists_path : □?p P ⊢ ∃∃ Q.
  Global Arguments IntoExistsPath _ _%I _%I : simpl never.
  Global Arguments into_exists_path _ _%I _%I {_}.
  Global Hint Mode IntoExistsPath ! ! - : typeclass_instances.

  Global Instance into_exists_path_exists_path p P :
    IntoExistsPath p (∃∃ P) P.
  Proof.
    rewrite /IntoExistsPath.
    destruct p; simpl; by iIntros "HP".
  Qed.

  Class FromExistsPath (P Q : tProp) :=
    from_exists_path : (∃∃ P) ⊢ Q.
  Global Arguments FromExistsPath _%I _%I : simpl never.
  Global Arguments from_exists_path _%I _%I {_}.
  Global Hint Mode FromExistsPath - ! : typeclass_instances.

  Global Instance from_exists_path_exists_path (P : tProp) :
    FromExistsPath P (∃∃ P).
  Proof. done. Qed.

  Global Instance elim_modal_exists_path p P P' Q Q' :
    IntoExistsPath p P P' →
    FromExistsPath Q' Q →
    ElimModal True p false modality_forall_path P P' Q Q'.
  Proof.
    intros HP HQ.
    rewrite /ElimModal.
    iIntros "_ [HP' HP]".
    destruct p; simpl.
    - rewrite /IntoExistsPath in HP.
      rewrite /FromExistsPath in HQ.
      iApply HQ.
      simpl in *. rewrite HP.
      iApply (ltl_exists_path_mono_strong with "HP HP'").
    - rewrite /IntoExistsPath in HP.
      rewrite /FromExistsPath in HQ.
      iApply HQ.
      simpl in *. rewrite HP.
      iApply (ltl_exists_path_mono_strong with "HP HP'").
  Qed.

End ctl_proofmode.

Section ctl_test.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Lemma ltl_forall_path_test (P Q : tProp) :
    (∀∀ P → Q) ∧ (∀∀ P) ⊢ ∀∀ Q.
  Proof. iIntros "[HPQ HP]". iModIntro. by iApply "HPQ". Qed.

  Lemma ltl_exists_path_test (P Q : tProp) :
    (∀∀ P → Q) ∧ (∃∃ P) ⊢ ∃∃ Q.
  Proof. iIntros "[HPQ HP]". iMod "HP". by iApply "HPQ". Qed.

End ctl_test.

(*
TODO:
- Better handling of ∀∀, so that it sticks around during [iModIntro] and can be eliminated using [iMod].
- Better support alongside MoSeL □. Might want a new □ that is for all paths,
  alongside current □, which corresponds to ltl G.
*)
