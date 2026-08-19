From ltl Require Export trace.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export proofmode.

Definition tProp S L R := wf_trace S L R → Prop.

Bind Scope bi_scope with tProp.
Bind Scope bi_scope with trace.

Section tProp.
  Context {S L : Type}.
  Context {R : S → L → S → Prop}.
  Notation tProp := (@tProp S L R).

  Inductive tProp_equiv' (P Q : tProp) : Prop :=
    { tProp_in_equiv : ∀ tr, P tr ↔ Q tr }.
  Local Instance tProp_equiv : Equiv tProp := tProp_equiv'.
  Local Instance heapProp_equivalence : Equivalence (≡@{tProp}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure tPropO := discreteO tProp.
End tProp.

Section ltl_constructors.
  Context {S L : Type}.
  Context {R : S → L → S → Prop}.
  Notation tProp := (tProp S L R).
  Implicit Type P Q : tProp.

  Inductive ltl_entails (P Q : tProp) : Prop :=
    { ltl_in_entails : ∀ tr, P tr → Q tr }.

  (* Primitive operators *)
  Definition ltl_pure_def (P : Prop) : tProp :=
    λ tr, P.
  Definition ltl_pure_aux : seal (@ltl_pure_def).
  Proof. by eexists. Qed.
  Definition ltl_pure := unseal ltl_pure_aux.
  Definition ltl_pure_unseal :
    @ltl_pure = @ltl_pure_def := seal_eq ltl_pure_aux.

  Definition ltl_or_def (P Q : tProp) : tProp :=
    λ tr, P tr ∨ Q tr.
  Definition ltl_or_aux : seal (@ltl_or_def).
  Proof. by eexists. Qed.
  Definition ltl_or := unseal ltl_or_aux.
  Definition ltl_or_unseal :
    @ltl_or = @ltl_or_def := seal_eq ltl_or_aux.

  Definition ltl_and_def (P Q : tProp) : tProp :=
    λ tr, P tr ∧ Q tr.
  Definition ltl_and_aux : seal (@ltl_and_def).
  Proof. by eexists. Qed.
  Definition ltl_and := unseal ltl_and_aux.
  Definition ltl_and_unseal :
    @ltl_and = @ltl_and_def := seal_eq ltl_and_aux.

  Definition ltl_impl_def (P Q : tProp) : tProp :=
    λ tr, P tr → Q tr.
  Definition ltl_impl_aux : seal (@ltl_impl_def).
  Proof. by eexists. Qed.
  Definition ltl_impl := unseal ltl_impl_aux.
  Definition ltl_impl_unseal :
    @ltl_impl = @ltl_impl_def := seal_eq ltl_impl_aux.

  Definition ltl_forall_def {A} (Ψ : A → tProp) : tProp :=
    λ tr, ∀ (x:A), Ψ x tr.
  Definition ltl_forall_aux : seal (@ltl_forall_def).
  Proof. by eexists. Qed.
  Definition ltl_forall {A} := unseal ltl_forall_aux A.
  Definition ltl_forall_unseal :
    @ltl_forall = @ltl_forall_def := seal_eq ltl_forall_aux.

  Definition ltl_exist_def {A} (Ψ : A → tProp) : tProp :=
    λ tr, ∃ (x:A), Ψ x tr.
  Definition ltl_exist_aux : seal (@ltl_exist_def).
  Proof. by eexists. Qed.
  Definition ltl_exist {A} := unseal ltl_exist_aux A.
  Definition ltl_exist_unseal :
    @ltl_exist = @ltl_exist_def := seal_eq ltl_exist_aux.

End ltl_constructors.

Module ltl_primitive.

Section primitive.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).
  Implicit Type P Q : tProp.

  Definition ltl_unseal :=
    (@ltl_pure_unseal S L Rel, @ltl_and_unseal S L Rel, @ltl_or_unseal S L Rel,
       @ltl_impl_unseal S L Rel, @ltl_forall_unseal S L Rel, @ltl_exist_unseal S L Rel).

  Ltac unseal := rewrite !ltl_unseal /=.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (ltl_entails P Q).
  Notation "'True'" := (ltl_pure True) : bi_scope.
  Notation "'False'" := (ltl_pure False) : bi_scope.
  Notation "'⌜' φ '⌝'" := (ltl_pure φ%type%stdpp) : bi_scope.
  Infix "∧" := ltl_and : bi_scope.
  Infix "∨" := ltl_or : bi_scope.
  Infix "→" := ltl_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (ltl_forall (λ x, .. (ltl_forall (λ y, P%I)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (ltl_exist (λ x, .. (ltl_exist (λ y, P%I)) ..)) : bi_scope.

  (** Below there follow the primitive laws for [ltl]. There are no derived laws
  in this file. *)

  (** Entailment *)
  Global Instance entails_po : PreOrder (@ltl_entails S L Rel).
  Proof.
    split.
    - intros P; by split=> i.
    - intros P Q Q' HP HQ.
      split=> ? ?. by apply HQ, HP.
  Qed.
  Lemma entails_anti_symm : AntiSymm (≡) (@ltl_entails S L Rel).
  Proof. intros P Q HPQ HQP; split=> n. by split; [apply HPQ|apply HQP]. Qed.
  Lemma equiv_entails (P Q : tProp) : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof.
    split.
    - intros HPQ; split; split=> i; apply HPQ.
    - intros [??]. by apply entails_anti_symm.
  Qed.

  (** Non-expansiveness and setoid morphisms *)
  Lemma pure_ne n : Proper (iff ==> dist n) (@ltl_pure S L Rel).
  Proof. intros φ1 φ2 Hφ. by unseal. Qed.
  Lemma and_ne : NonExpansive2 (@ltl_and S L Rel).
  Proof.
    intros n P P' HP Q Q' HQ; unseal; split=> ?.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  Qed.
  Lemma or_ne : NonExpansive2 (@ltl_or S L Rel).
  Proof.
    intros n P P' HP Q Q' HQ; split=> ?.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  Qed.
  Lemma impl_ne : NonExpansive2 (@ltl_impl S L Rel).
  Proof.
    intros n P P' HP Q Q' HQ; split=> ?.
    unseal; split; intros HPQ ?; apply HQ, HPQ, HP; auto with lia.
  Qed.
  Lemma forall_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@ltl_forall S L Rel A).
  Proof.
     by intros Ψ1 Ψ2 HΨ; unseal; split=> x; split; intros HP a; apply HΨ.
  Qed.
  Lemma exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@ltl_exist S L Rel A).
  Proof.
    intros Ψ1 Ψ2 HΨ.
    unseal; split=> ?; split; intros [a ?]; exists a; by apply HΨ.
  Qed.

  (** Introduction and elimination rules *)
  Lemma pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝.
  Proof. intros ?. unseal; by split. Qed.
  Lemma pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P.
  Proof. unseal=> HP; split=> n ?. by apply HP. Qed.
  Lemma pure_forall_2 {A} (φ : A → Prop) :
    ((∀ a, ⌜ φ a ⌝):tProp) ⊢ ⌜ ∀ a, φ a ⌝.
  Proof. by unseal. Qed.

  Lemma and_elim_l P Q : P ∧ Q ⊢ P.
  Proof. unseal; by split=> n [??]. Qed.
  Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
  Proof. unseal; by split=> n [??]. Qed.
  Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
  Proof.
    intros HQ HR; unseal; split=> n ?.
    split.
    - by apply HQ.
    - by apply HR.
  Qed.

  Lemma or_intro_l P Q : P ⊢ P ∨ Q.
  Proof. unseal; split=> n ?; left; auto. Qed.
  Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
  Proof. unseal; split=> n ?; right; auto. Qed.
  Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
  Proof.
    intros HP HQ. unseal; split=> n [?|?].
    - by apply HP.
    - by apply HQ.
  Qed.

  Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
  Proof.
    unseal=> HQ; split=> ???.
    apply HQ. by split.
  Qed.
  Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
  Proof. unseal=> HP; split=> tr [??]. by apply HP. Qed.

  Lemma forall_intro {A} P (Ψ : A → tProp) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof. unseal; intros HPΨ; split=> n ? a; by apply HPΨ. Qed.
  Lemma forall_elim {A} {Ψ : A → tProp} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof. unseal; split=> n HP; apply HP. Qed.

  Lemma exist_intro {A} {Ψ : A → tProp} a : Ψ a ⊢ ∃ a, Ψ a.
  Proof. unseal; split=> n ?; by exists a. Qed.
  Lemma exist_elim {A} (Φ : A → tProp) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
  Proof. unseal; intros HΨ; split=> n [a ?]; by apply HΨ with a. Qed.

End primitive.
End ltl_primitive.

Import ltl_primitive.

Section ltl_constructors.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  (* LTL Operators *)
  Definition ltl_next_def (P : tProp) : tProp := λ tr, P (wf_tail tr).
  Definition ltl_next_aux : seal (@ltl_next_def).
  Proof. by eexists. Qed.
  Definition ltl_next := unseal ltl_next_aux.
  Definition ltl_next_unseal :
    @ltl_next = @ltl_next_def := seal_eq ltl_next_aux.

  Fixpoint ltl_next_iter (n : nat) (P : tProp) : tProp :=
    match n with
    | 0 => P
    | Datatypes.S n => ltl_next (ltl_next_iter n P)
    end.

  Definition ltl_always_def (P : tProp) : tProp := ltl_forall (λ n, ltl_next_iter n P)%I.
  Definition ltl_always_aux : seal (@ltl_always_def).
  Proof. by eexists. Qed.
  Definition ltl_always := unseal ltl_always_aux.
  Definition ltl_always_unseal :
    @ltl_always = @ltl_always_def := seal_eq ltl_always_aux.

End ltl_constructors.

Global Instance: Params (@ltl_next) 2 := {}.
Global Instance: Params (@ltl_always) 2 := {}.

Notation "○ P" := (ltl_next P%I) (at level 20, right associativity) : bi_scope.
Notation "○^ n P" := (ltl_next_iter n P%I) (at level 20, n at level 9, P at level 20, format "○^ n  P") : bi_scope.

Section ltl_axioms.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).
  Implicit Type P Q : tProp.

  Definition ltl_unseal :=
    (@ltl_pure_unseal S L Rel, @ltl_and_unseal S L Rel, @ltl_or_unseal S L Rel,
       @ltl_impl_unseal S L Rel, @ltl_forall_unseal S L Rel, @ltl_exist_unseal S L Rel,
         @ltl_always_unseal S L Rel, @ltl_next_unseal S L Rel).

  Ltac unseal := rewrite !ltl_unseal /=.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (ltl_entails P Q).
  Notation "'True'" := (ltl_pure True) : bi_scope.
  Notation "'False'" := (ltl_pure False) : bi_scope.
  Notation "'⌜' φ '⌝'" := (ltl_pure φ%type%stdpp) : bi_scope.
  Infix "∧" := ltl_and : bi_scope.
  Infix "∨" := ltl_or : bi_scope.
  Infix "→" := ltl_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (ltl_forall (λ x, .. (ltl_forall (λ y, P%I)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (ltl_exist (λ x, .. (ltl_exist (λ y, P%I)) ..)) : bi_scope.
  Notation "□ P" := (ltl_always P) : bi_scope.

  Lemma ltl_next_iter_sum n m (P : tProp) :
    (○^(n+m) P)%I ≡ (○^n (○^ m P))%I.
  Proof.
    revert m P.
    induction n; intros m P; [done|].
    replace (Datatypes.S n + m) with (n + (Datatypes.S m)) by lia.
    rewrite IHn.
    replace (Datatypes.S n) with (n + 1) by lia.
    rewrite IHn.
    clear IHn.
    done.
  Qed.

  Lemma ltl_next_iter_S n (P : tProp) :
    (○^(Datatypes.S n) P)%I ≡ (○^n (○ P))%I.
  Proof. replace (Datatypes.S n) with (n + 1) by lia.
         rewrite ltl_next_iter_sum. done. Qed.

  Instance ne_proper (f : tProp → tProp) `{!Proper ((≡) ==> (≡)) f} : NonExpansive f.
  Proof.
    constructor. intros.
    apply Proper0. done.
  Qed.

  Global Instance ltl_next_proper : Proper ((≡) ==> (≡)) (@ltl_next S L Rel).
  Proof.
    rewrite ltl_next_unseal.
    constructor.
    intros.
    destruct tr as [[[]|]]; split; intros; simplify_eq; simpl in *; by apply H.
  Qed.

  Lemma ltl_always_ne : NonExpansive (@ltl_always S L Rel).
  Proof.
    apply ne_proper. unseal. rewrite /ltl_always_def. unseal.
    constructor.
    intros.
    constructor.
    + intros Hx n.
      specialize (Hx n).
      revert x y H Hx.
      induction n; intros x y H Hx.
      { simpl. apply H. done. }
      apply ltl_next_iter_S.
      apply (IHn (○ x)%I (○ y)%I).
      { f_equiv. done. }
      apply ltl_next_iter_S.
      done.
    + intros Hx n.
      specialize (Hx n).
      revert x y H Hx.
      induction n; intros x y H Hx.
      { simpl. apply H. done. }
      apply ltl_next_iter_S.
      apply (IHn (○ x)%I (○ y)%I).
      { f_equiv. done. }
      apply ltl_next_iter_S.
      done.
  Qed.

  (* N○*)
  Lemma ltl_next_taut' (P : tProp) :
    (True ⊢ P) → (True ⊢ ○ P).
  Proof.
    unseal.
    intros [HP].
    constructor.
    intros tr _.
    destruct tr as [[[]|]]; intros; eapply HP; done.
  Qed.

  (* K○ *)
  Lemma ltl_next_mono_strong (P Q : tProp) :
    ○ (P → Q) ⊢ ○ P → ○ Q.
  Proof.
    unseal.
    constructor.
    intros tr HPQ HP.
    destruct tr as [[[]|]]; simpl in *; by apply HPQ.
  Qed.

  Lemma ltl_always_next_unfold P :
    (□ P = ∀ n, ○^n P)%I.
  Proof. rewrite ltl_always_unseal. unseal. rewrite /ltl_always_def. unseal. done. Qed.

  (* N□ *)
  Lemma ltl_always_taut P :
    (True ⊢ P) → (True ⊢ □ P).
  Proof.
    intros HP. rewrite ltl_always_next_unfold.
    apply forall_intro.
    intros n.
    induction n.
    { done. }
    simpl.
    apply ltl_next_taut'.
    done.
  Qed.

  Lemma ltl_next_mono_pre (P Q : tProp) :
    (P ⊢ Q) → (○ P ⊢ ○ Q).
  Proof.
    intros HPQ.
    etrans.
    { apply and_intro.
      - instantiate (1:= (True)%I).
        apply pure_intro. done.
      - exact.
    }
    apply impl_elim_l'. etrans; [|apply ltl_next_mono_strong].
    apply ltl_next_taut'.
    apply impl_intro_r. etrans; [|apply HPQ].
    apply and_elim_r.
  Qed.

  Lemma ltl_next_iter_mono_strong_pre n (P Q : tProp) :
    ○^n (P → Q) ⊢ ○^n P → ○^n Q.
  Proof.
    induction n.
    { done. }
    simpl.
    etrans; [|apply ltl_next_mono_strong].
    apply ltl_next_mono_pre.
    done.
  Qed.

  (* K□ *)
  Lemma ltl_always_mono_strong_pre (P Q : tProp) :
    □ (P → Q) ⊢ □ P → □ Q.
  Proof.
    rewrite !ltl_always_next_unfold.
    apply impl_intro_r.
    apply forall_intro=> n.
    etrans; [apply and_intro|].
    { etrans; [apply and_elim_l|]. apply (forall_elim n). }
    { etrans; [apply and_elim_r|]. apply (forall_elim n). }
    apply impl_elim_l'.
    apply ltl_next_iter_mono_strong_pre.
  Qed.

  Lemma ltl_next_forall_1 {A} (P : A → tProp) :
    (∀ x, ○ P x)%I ⊢ ○ ∀ x, P x.
  Proof.
    unseal.
    constructor. intros tr Hnext. destruct tr as [[[]|]].
    - simplify_eq. intros x. specialize (Hnext x).
      simplify_eq. done.
    - simplify_eq. intros x. specialize (Hnext x).
      simplify_eq. done.
    - simplify_eq. intros x. specialize (Hnext x).
      simplify_eq. done.
  Qed.

End ltl_axioms.

Section ltl_lemmas.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).
  Implicit Type P Q : tProp.

  (** The notations below are implicitly local due to the section, so we do not
  mind the overlap with the general BI notations. *)
  Notation "P ⊢ Q" := (ltl_entails P Q).
  Notation "'True'" := (ltl_pure True) : bi_scope.
  Notation "'False'" := (ltl_pure False) : bi_scope.
  Notation "'⌜' φ '⌝'" := (ltl_pure φ%type%stdpp) : bi_scope.
  Infix "∧" := ltl_and : bi_scope.
  Infix "∨" := ltl_or : bi_scope.
  Infix "→" := ltl_impl : bi_scope.
  Notation "∀ x .. y , P" :=
    (ltl_forall (λ x, .. (ltl_forall (λ y, P%I)) ..)) : bi_scope.
  Notation "∃ x .. y , P" :=
    (ltl_exist (λ x, .. (ltl_exist (λ y, P%I)) ..)) : bi_scope.
  Notation "□ P" := (ltl_always P) : bi_scope.

  (** Derived constructs *)

  Lemma ltl_always_unfold_pre_1 (P : tProp) :
    □ P ⊢ P ∧ ○ □ P.
  Proof.
    rewrite !ltl_always_next_unfold.
    apply and_intro.
    { etrans; [apply (forall_elim 0)|]. done. }
    etrans; [|apply ltl_next_forall_1].
    apply forall_intro=> n.
    etrans; [apply (forall_elim (Datatypes.S n))|].
    simpl. done.
  Qed.

  (* A5(?) - A5 ties until to its unfolding, consequently tying always to its unfolding *)
  Lemma ltl_always_unfold_pre_2 (P : tProp) :
    P ∧ ○ □ P ⊢ □ P.
  Proof.
    rewrite (ltl_always_next_unfold P).
    apply forall_intro=> n.
    destruct n.
    { apply and_elim_l. }
    simpl.
    etrans; [apply and_elim_r|].
    apply ltl_next_mono_pre.
    etrans; [apply (forall_elim n)|]. done.
  Qed.

  (* A4 *)
  Lemma ltl_always_intro_pre (P : tProp) :
    □ (P → ○ P) ⊢ P → □ P.
  Proof.
    rewrite (ltl_always_next_unfold P).
    apply impl_intro_r.
    apply forall_intro=> n.
    apply impl_elim_l'.
    induction n=> /=.
    { apply impl_intro_r, and_elim_r. }
    etrans; [apply ltl_always_unfold_pre_1|].
    apply impl_intro_r.
    etrans.
    { instantiate (1:= (○ □ (P → ○ P) ∧ ○ P)%I).
      apply and_intro.
      - etrans; [apply and_elim_l|]. apply and_elim_r.
      - apply impl_elim_l'. etrans; [apply and_elim_l|]. done.
    }
    apply impl_elim_l'.
    etrans; [|apply ltl_next_mono_strong].
    apply ltl_next_mono_pre.
    done.
  Qed.

  Lemma ltl_always_emp :
    True ⊢ (□ True) : tProp.
  Proof. apply ltl_always_taut. done. Qed.

  Lemma ltl_always_mono_pre (P Q : tProp) :
    (P ⊢ Q)%I → (□ P ⊢ □ Q)%I.
  Proof.
    intros HPQ.
    pose proof (ltl_always_mono_strong_pre P Q).
    apply impl_elim_l' in H.
    etrans; [|apply H].
    apply and_intro; [|done].
    trans (True : tProp)%I.
    { apply pure_intro. done. }
    apply ltl_always_taut.
    apply impl_intro_r.
    etrans; [apply and_elim_r|].
    done.
  Qed.

  Lemma ltl_always_and_pre (P Q : tProp) :
    (□ P) ∧ (□ Q) ⊢ □ (P ∧ Q).
  Proof.
    apply impl_elim_l'.
    etrans; [|apply ltl_always_mono_strong_pre].
    apply ltl_always_mono_pre.
    apply impl_intro_r.
    done.
  Qed.

  (* Axiom of IPM instantiation *)
  Lemma ltl_always_idemp_pre (P : tProp) :
    □ P ⊢ □ □ P.
  Proof.
    pose proof (ltl_always_intro_pre (□ P)) as Hintro.
    apply impl_elim_l' in Hintro.
    etrans; [|apply Hintro].
    apply and_intro; [|done].
    apply ltl_always_mono_pre.
    apply impl_intro_r.
    etrans; [apply and_elim_r|].
    etrans; [apply ltl_always_unfold_pre_1|].
    apply and_elim_r.
  Qed.

  (* Axiom of IPM instantiation *)
  Lemma ltl_always_affine (P Q : tProp) :
    (□ P) ∧ Q ⊢ (□ P).
  Proof. apply and_elim_l. Qed.

  (* Axiom of IPM instantiation *)
  Lemma ltl_always_sep_and (P Q : tProp) :
    (□ P) ∧ Q ⊢ P ∧ Q.
  Proof.
    apply and_intro.
    - etrans; [apply and_elim_l|].
      etrans; [apply ltl_always_unfold_pre_1|].
      apply and_elim_l.
    - apply and_elim_r.
  Qed.

End ltl_lemmas.

Section ltl_bi.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Definition ltl_emp : tProp := ltl_pure True.
  Definition ltl_sep (P Q : tProp) : tProp := ltl_and P Q.
  Definition ltl_wand (P Q : tProp) : tProp := ltl_impl P Q.
  Definition ltl_persistently (P : tProp) : tProp := ltl_always P.
  Definition ltl_later (P : tProp) : tProp := P.

  Local Existing Instance entails_po.

  Lemma ltl_bi_mixin :
    BiMixin
      ltl_entails ltl_emp ltl_pure ltl_and ltl_or ltl_impl
      (@ltl_forall S L Rel) (@ltl_exist S L Rel) ltl_sep ltl_wand.
  Proof.
    split.
    - exact: entails_po.
    - exact: equiv_entails.
    - exact: pure_ne.
    - exact: and_ne.
    - exact: or_ne.
    - exact: impl_ne.
    - exact: forall_ne.
    - exact: exist_ne.
    - exact: and_ne.
    - exact: impl_ne.
    - exact: pure_intro.
    - exact: pure_elim'.
    - exact: and_elim_l.
    - exact: and_elim_r.
    - exact: and_intro.
    - exact: or_intro_l.
    - exact: or_intro_r.
    - exact: or_elim.
    - exact: impl_intro_r.
    - exact: impl_elim_l'.
    - exact: @forall_intro.
    - exact: @forall_elim.
    - exact: @exist_intro.
    - exact: @exist_elim.
    - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *)
      intros P P' Q Q' H1 H2. apply and_intro.
      + by etrans; first apply and_elim_l.
      + by etrans; first apply and_elim_r.
    - (* P ⊢ emp ∗ P *)
      intros P. apply and_intro; last done. by apply pure_intro.
    - (* emp ∗ P ⊢ P *)
      intros P. apply and_elim_r.
    - (* P ∗ Q ⊢ Q ∗ P *)
      intros P Q. apply and_intro; [ apply and_elim_r | apply and_elim_l ].
    - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *)
      intros P Q R. repeat apply and_intro.
      + etrans; first apply and_elim_l. by apply and_elim_l.
      + etrans; first apply and_elim_l. by apply and_elim_r.
      + apply and_elim_r.
    - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *)
      apply impl_intro_r.
    - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *)
      apply impl_elim_l'.
  Qed.

  Lemma ltl_bi_persistently_mixin :
    BiPersistentlyMixin
      ltl_entails ltl_emp ltl_and
      ltl_sep ltl_persistently.
  Proof.
    split.
    - apply ltl_always_ne.
    - (* (P ⊢ Q) → <pers> P ⊢ <pers> Q *)
      apply ltl_always_mono_pre.
    - (* <pers> P ⊢ <pers> <pers> P *)
      apply ltl_always_idemp_pre.
    - (* emp ⊢ <pers> emp *)
      apply ltl_always_emp.
    - (* (<pers> P) ∧ (<pers> Q) ⊢ <pers> (P ∧ Q) *)
      apply ltl_always_and_pre.
    - (* <pers> P ∗ Q ⊢ <pers> P *)
      apply ltl_always_affine.
    - (* <pers> P ∧ Q ⊢ P ∗ Q *)
      apply ltl_always_sep_and.
  Qed.

  Lemma ltl_bi_later_mixin :
    BiLaterMixin
      ltl_entails ltl_pure ltl_or ltl_impl
      (@ltl_forall S L Rel) (@ltl_exist S L Rel) ltl_and ltl_persistently ltl_later.
  Proof.
    eapply bi_later_mixin_id; [done|];
      [done..|apply ltl_bi_mixin].
  Qed.

End ltl_bi.

Canonical Structure ltlI {S L : Type} {Rel} : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (tProp S L Rel);
    bi_bi_mixin := ltl_bi_mixin;
    bi_bi_persistently_mixin := ltl_bi_persistently_mixin;
    bi_bi_later_mixin := ltl_bi_later_mixin |}.

Section ltl_bi_typeclasses.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Global Instance ltl_pure_forall : BiPureForall (@ltlI S L Rel).
  Proof. exact: @pure_forall_2. Qed.

  Global Instance ltl_affine : BiAffine (@ltlI S L Rel) | 0.
  Proof. intros P. exact: pure_intro. Qed.
  (* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [BiAffine] as a premise. *)

End ltl_bi_typeclasses.

Global Hint Immediate ltl_affine : core.

(* OBS: This seems to be needed to avoid collision with FromImpl *)
Global Remove Hints class_instances.from_impl_impl : typeclass_instances.

(** extra BI instances *)

(** Re-state/export soundness lemmas *)

Module tProp.
Section restate.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  (** We restate the unsealing lemmas so that they also unfold the BI layer. The *)
(*   sealing lemmas are partially applied so that they also work under binders. *)
  Lemma ltl_emp_unseal : bi_emp = @ltl_pure_def S L Rel True.
  Proof. by rewrite -ltl_pure_unseal. Qed.
  Lemma ltl_pure_unseal : bi_pure = @ltl_pure_def S L Rel.
  Proof. by rewrite -ltl_pure_unseal. Qed.
  Lemma ltl_and_unseal : bi_and = @ltl_and_def S L Rel.
  Proof. by rewrite -ltl_and_unseal. Qed.
  Lemma ltl_or_unseal : bi_or = @ltl_or_def S L Rel.
  Proof. by rewrite -ltl_or_unseal. Qed.
  Lemma ltl_impl_unseal : bi_impl = @ltl_impl_def S L Rel.
  Proof. by rewrite -ltl_impl_unseal. Qed.
  Lemma ltl_forall_unseal : @bi_forall _ = @ltl_forall_def S L Rel.
  Proof. by rewrite -ltl_forall_unseal. Qed.
  Lemma ltl_exist_unseal : @bi_exist _ = @ltl_exist_def S L Rel.
  Proof. by rewrite -ltl_exist_unseal. Qed.
  Lemma ltl_persistently_unseal : bi_persistently = @ltl_persistently S L Rel.
  Proof. done. Qed.

  Definition ltl_unseal :=
    (ltl_emp_unseal, ltl_pure_unseal, ltl_and_unseal, ltl_or_unseal,
     ltl_impl_unseal, ltl_forall_unseal, ltl_exist_unseal,
     ltl_persistently_unseal).
End restate.

(** The final unseal tactic that also unfolds the BI layer. *)
Ltac unseal := rewrite !ltl_unseal /=.
End tProp.

Global Instance ltl_next_mono' {S L Rel} :
  Proper ((⊢) ==> (⊢)) (@ltl_next S L Rel).
Proof.
  rewrite ltl_next_unseal.
  constructor.
  intros. by apply H.
Qed.
Global Instance ltl_next_flip_mono' {S L Rel} :
  Proper (flip (⊢) ==> flip (⊢)) (@ltl_next S L Rel).
Proof.
  rewrite ltl_next_unseal.
  constructor. intros. by apply H.
Qed.

Section ltl_axioms.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  Definition ltl_unseal' :=
    (@ltl_pure_unseal S L, @ltl_and_unseal S L, @ltl_or_unseal S L,
       @ltl_impl_unseal S L, @ltl_forall_unseal S L, @ltl_exist_unseal S L,
         @ltl_next_unseal S L, @ltl_always_unseal S L).

  Ltac ltl_unseal := rewrite !ltl_unseal' /=.

  Import tProp.

  Lemma bi_intuitionistically_unseal (P : tProp) :
    @bi_intuitionistically (@ltlI S L Rel) P ≡ ltl_always P.
  Proof. rewrite /bi_intuitionistically.
         rewrite /bi_affinely.
         rewrite left_id. done.
  Qed.

  Lemma bi_intuitionistically_unseal' (P : tProp) tr :
    @bi_intuitionistically (@ltlI S L Rel) P tr ≡ ltl_always P tr.
  Proof.
    rewrite /bi_intuitionistically.
    rewrite /bi_affinely.
    unseal. simpl. rewrite /ltl_and_def /ltl_pure_def. simpl.
    rewrite left_id. done.
  Qed.

  Lemma impl_intro_l (P Q : tProp) :
    (⊢ P → Q) → (P ⊢ Q).
  Proof. iIntros (HPQ) "HP". by iApply HPQ. Qed.
  Lemma impl_intro_r (P Q : tProp) :
    (P ⊢ Q) → (⊢ P → Q).
  Proof. iIntros (HPQ) "HP". by rewrite HPQ. Qed.

  Lemma bi_sep_and (P Q : tProp) :
    P ∗ Q ⊣⊢ P ∧ Q.
  Proof. constructor. intros tr. unseal. done. Qed.
  Lemma bi_wand_impl (P Q : tProp) :
    (P -∗ Q) ⊣⊢ (P → Q).
  Proof. constructor. intros tr. unseal. done. Qed.

  Lemma ltl_dup (P : tProp) : P ⊢ P ∧ P.
  Proof. iIntros "H". iFrame. Qed.

  Lemma ltl_sep_and (P Q : tProp) :
    P ∗ Q ⊣⊢ P ∧ Q.
  Proof. done. Qed.

  Lemma ltl_wand_impl (P Q : tProp) :
    (P -∗ Q) ⊣⊢ (P → Q).
  Proof. done. Qed.

  (** AXIOMS *)

  (** ltl_next lemmas *)

  (* N○*)
  Lemma ltl_next_taut (P : tProp) :
    (⊢ P) → (⊢ ○ P).
  Proof. apply ltl_next_taut'. Qed.

  (* A2 *)
  Lemma ltl_next_not (P : tProp) :
    ¬ ○ P ⊣⊢ ○ (¬ P).
  Proof.
    split. intros tr. unseal. ltl_unseal.
    split.
    - intros. destruct tr as [[[]|]].
      + intros HP. eapply H. done.
      + intros HP. eapply H. done.
      + intros HP. eapply H. done.
    - intros. destruct tr as [[[]|]].
      + intros HP. apply H. apply HP.
      + intros HP. apply H. apply HP.
      + intros HP. apply H. apply HP.
  Qed.

  Lemma ltl_next_exists {A} (P : A → tProp) :
    (○ ∃ x, P x)%I ⊢ ∃ x, ○ P x.
  Proof.
    unseal. ltl_unseal.
    constructor. intros tr Hnext. inversion Hnext.
    eexists _. apply H.
  Qed.

  Lemma ltl_next_pure P :
    ○ ⌜P⌝ ⊣⊢@{tProp} ⌜P⌝.
  Proof. unseal. rewrite ltl_next_unseal. done. Qed.

  (** Next Iter *)

  Lemma ltl_next_iter_mono_strong n (P Q : tProp) :
    ○^n (P → Q) ⊢ ○^n P → ○^n Q.
  Proof. apply ltl_next_iter_mono_strong_pre. Qed.

  Lemma ltl_next_iter_taut n (P : tProp) :
    (⊢ P) → (⊢ ○^n P).
  Proof.
    intros HP.
    induction n; [done|].
    simpl. apply ltl_next_taut. done.
  Qed.

  Lemma ltl_next_iter_mono n (P Q : tProp) :
    (P ⊢ Q) → (○^n P ⊢ ○^n Q).
  Proof.
    iIntros (HPQ) "HPQ". iRevert "HPQ". iApply ltl_next_iter_mono_strong.
    iApply ltl_next_iter_taut. iIntros "HP". by iApply HPQ.
  Qed.

  Lemma ltl_iter_forall (P:tProp) :
    (∀ n, ○^n P)%I ⊢ ○ (∀ n, ○^n P).
  Proof.
    iIntros "HP". rewrite -ltl_next_forall_1. iIntros (n).
    iSpecialize ("HP" $! (Datatypes.S n)). done.
  Qed.

  (* TODO: Move *)
  Global Instance ltl_next_iter_proper n : Proper ((≡) ==> (≡)) (@ltl_next_iter S L Rel n).
  Proof.
    intros P Q Heq.
    induction n.
    { simpl. done. } 
    simpl. f_equiv. done.
  Qed.

  Lemma ltl_next_mono (P Q : tProp) :
    (P ⊢ Q) → (○ P ⊢ ○ Q).
  Proof. apply ltl_next_mono_pre. Qed.

  (** Restating ltl_always lemmas *)

  Lemma ltl_always_unfold (P : tProp) :
    □ P ⊣⊢ P ∧ ○ □ P.
  Proof. rewrite bi_intuitionistically_unseal.
    apply bi.equiv_entails_2.
    - apply ltl_always_unfold_pre_1.
    - apply ltl_always_unfold_pre_2.
  Qed.

  Lemma ltl_always_intro (P : tProp) :
    □ (P → ○ P) ⊢ P → □ P.
  Proof. rewrite !bi_intuitionistically_unseal. apply ltl_always_intro_pre. Qed.

  Lemma ltl_always_and (P Q : tProp) :
    (□ P) ∧ (□ Q) ⊢ □ (P ∧ Q).
  Proof. rewrite !bi_intuitionistically_unseal. apply ltl_always_and_pre. Qed.

  Lemma ltl_always_mono (P Q : tProp) :
    (P ⊢ Q)%I → (□ P ⊢ □ Q)%I.
  Proof. rewrite !bi_intuitionistically_unseal. apply ltl_always_mono_pre. Qed.

  Lemma ltl_always_elim (P : tProp) :
    □ P ⊢ P.
  Proof. rewrite ltl_always_unfold. iIntros "[$ _]". Qed.

  (* Actual A1 / K□ *)
  Lemma ltl_always_mono_strong (P Q : tProp) :
    □ (P → Q) ⊢ □ P → □ Q.
  Proof. rewrite !bi_intuitionistically_unseal. apply ltl_always_mono_strong_pre. Qed.

End ltl_axioms.

Section ltl_derived_rules.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  (** DERIVED RULES *)

  (* Next *)

  Lemma ltl_next_emp :
    True ⊢ ○ True : tProp.
  Proof. by apply ltl_next_taut. Qed.

  Lemma ltl_false_next :
    ○ False ⊢ False : tProp.
  Proof.
    iIntros "H".
    iDestruct (ltl_dup with "H") as "[H Hf]".
    iAssert (○ (False → False))%I with "[H]" as "H'".
    { iApply (ltl_next_mono_strong with "[] H"). iApply ltl_next_taut. eauto. }
    rewrite -ltl_next_not.
    iApply "H'". done.
  Qed.

  Lemma ltl_always_next (P : tProp) :
    □ P ⊢ ○ □ P.
  Proof. rewrite {1}ltl_always_unfold. apply bi.and_elim_r. Qed.

  Lemma ltl_next_and (P Q : tProp) : ○ P ∧ ○ Q ⊣⊢ ○ (P ∧ Q).
  Proof.
    apply (anti_symm _).
    - apply bi.impl_elim_l'.
      etrans; [|apply ltl_next_mono_strong].
      apply ltl_next_mono.
      apply bi.impl_intro_r.
      done.
    - apply bi.and_intro.
      + apply ltl_next_mono. apply bi.and_elim_l.
      + apply ltl_next_mono. apply bi.and_elim_r.
  Qed.

  Lemma ltl_next_or_2 (P Q : tProp) :
    ○ (P ∨ Q) ⊢ (○ P) ∨ (○ Q).
  Proof.
    iIntros "HPQ".
    iAssert (○ ∃ (b:bool), if b then P else Q)%I with "[HPQ]" as "H".
    { iApply (ltl_next_mono with "HPQ").
      iDestruct 1 as "[HP|HQ]"; [by iExists true|by iExists false]. }
    rewrite ltl_next_exists.
    iDestruct "H" as ([]) "H"; iFrame.
  Qed.

  Lemma ltl_next_or (P Q : tProp) :
    (○ P) ∨ (○ Q) ⊣⊢ ○ (P ∨ Q).
  Proof.
    apply bi.equiv_entails_2.
    - apply bi.or_elim.
      + apply ltl_next_mono. apply bi.or_intro_l.
      + apply ltl_next_mono. apply bi.or_intro_r.
    - apply ltl_next_or_2.
  Qed.

  Lemma ltl_always_next_comm_1 (P : tProp) :
    □ ○ P ⊢ ○ □ P.
  Proof.
    rewrite ltl_always_unfold.
    iIntros "H".
    rewrite ltl_next_and.
    iApply (ltl_next_mono with "H").
    iIntros "[HP #IH]".
    iApply ltl_always_intro; [|iFrame].
    iIntros "!> _". done.
  Qed.

  Lemma ltl_always_next_comm_2 (P : tProp) :
    ○ □ P ⊢ □ ○ P.
  Proof.
    rewrite (ltl_always_unfold (○ P)).
    iIntros "H".
    iSplit.
    - iApply (ltl_next_mono with "H"). eauto.
    - iApply (ltl_next_mono with "H"). rewrite -(bi.intuitionistically_idemp P).
      rewrite (ltl_always_next P). rewrite {1}(bi.intuitionistically_elim P). done.
  Qed.

  Lemma ltl_always_next_comm (P : tProp) :
    □ ○ P ⊣⊢ ○ □ P.
  Proof.
    iSplit.
    - iApply ltl_always_next_comm_1.
    - iApply ltl_always_next_comm_2.
  Qed.

  Lemma ltl_next_always_combine (P Q : tProp) :
    (□ P ∧ ○ Q) ⊢ (○ (Q ∧ □ P)).
  Proof. by rewrite bi.and_comm {1}ltl_always_next ltl_next_and. Qed.

  Lemma ltl_always_unseal' (P:tProp) : 
    (□ P)%I ≡ (∀ n, ○^n P)%I.
  Proof.   
    rewrite !bi_intuitionistically_unseal.
    rewrite ltl_always_unseal.
    done.
  Qed.

  Lemma ltl_always_idemp (P : tProp) :
    □ P ⊢ □ □ P.
  Proof.
    rewrite !bi_intuitionistically_unseal.
    apply ltl_always_idemp_pre.
  Qed.

  (* Override combine functionality that turns hyps into sep *)
  Global Instance ltl_and_combine (P Q : tProp) :
    CombineSepAs P Q (P ∧ Q) | 10.
  Proof. by rewrite /CombineSepAs bi_sep_and. Qed.

  Lemma ltl_always_coind (P Q : tProp) :
    □ (P → (Q ∧ ○ (P ∨ □ Q))) ⊢ P → □ Q.
  Proof.
    rewrite !ltl_always_unseal'.
    iIntros "H".
    iEval (rewrite !ltl_always_unseal').
    iIntros "HP" (n).
    iInduction n as [|n IHn] forall (P Q).
    { simpl. iSpecialize ("H" $! 0). iDestruct ("H" with "HP") as "[HQ _]". done. }
    replace (Datatypes.S n) with (1 + n) by lia.
    rewrite !ltl_next_iter_sum.
    iDestruct (ltl_dup with "H") as "[H H']".
    iSpecialize ("H" $! 0). simpl.
    iDestruct ("H" with "HP") as "[HQ H]".
    rewrite ltl_iter_forall.
    iCombine "H H'" as "H". rewrite ltl_next_and.
    iRevert "H". rewrite ltl_wand_impl. iApply ltl_next_mono_strong.
    iApply ltl_always_elim. iApply ltl_always_next_comm. iApply ltl_always_next.
    iIntros "!> [H H']".
    iDestruct "H" as "[HP|HQ]"; last first.
    { iDestruct (ltl_always_unseal' with "HQ") as "HQ". iApply "HQ". }
    iApply ("IHn" with "[H'] HP").
    iIntros (m).
    iApply "H'".
  Qed.

End ltl_derived_rules.

Section ltl_proofmode.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Notation tProp := (tProp S L Rel).

  (* Proofmode support for next modality *)

  Global Instance into_and_next (P Q1 Q2 : tProp) :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (○ P)%I (○ Q1)%I (○ Q2)%I.
  Proof.
    rewrite /IntoAnd. simpl.
    intros HPQ.
    rewrite ltl_next_and.
    by eapply ltl_next_mono.
  Qed.

  Global Instance into_sep_next (P Q1 Q2 : tProp) :
    IntoSep P Q1 Q2 →
    IntoSep (○ P)%I (○ Q1)%I (○ Q2)%I.
  Proof. apply into_and_next. Qed.

  Class IntoNext (p:bool) (P Q : tProp) :=
    into_next : □?p P ⊢ ○ Q.
  Global Arguments IntoNext _ _%I _%I : simpl never.
  Global Arguments into_next _ _%I _%I {_}.
  Global Hint Mode IntoNext ! ! - : typeclass_instances.

  Global Instance into_next_next p P :
    IntoNext p (○ P) P.
  Proof.
    rewrite /IntoNext.
    destruct p; simpl; by iIntros "HP".
  Qed.

  Global Instance into_next_and b (P1 P2 Q1 Q2 : tProp) :
    IntoNext b P1 P2 →
    IntoNext b Q1 Q2 →
    IntoNext b (P1 ∧ Q1) (P2 ∧ Q2).
  Proof.
    rewrite /IntoNext. intros HP HQ.
    destruct b; simpl.
    - rewrite -ltl_next_and. simpl in *.
      rewrite bi.intuitionistically_and.
      rewrite HP HQ. done.
    - rewrite -ltl_next_and. simpl in *.
      rewrite HP HQ. done.
  Qed.

  Global Instance into_next_sep b (P1 P2 Q1 Q2 : tProp) :
    IntoNext b P1 P2 →
    IntoNext b Q1 Q2 →
    IntoNext b (P1 ∗ Q1) (P2 ∗ Q2).
  Proof. apply into_next_and. Qed.

  Global Instance into_next_always p (P : tProp) :
    IntoNext p (□ P) (□ P) | 1.
  Proof.
    rewrite /IntoNext. destruct p.
    - simpl. rewrite -ltl_always_next. eauto.
    - apply ltl_always_next.
  Qed.

  Global Instance into_next_always_comm p (P Q : tProp) :
    IntoNext p P Q →
    IntoNext p (□ P) (□ Q) | 0.
  Proof.
    rewrite /IntoNext. intros HPQ. destruct p.
    - simpl. rewrite -ltl_always_next_comm. rewrite -HPQ. eauto.
    - simpl in *. rewrite HPQ. apply ltl_always_next_comm_1.
  Qed.

  Global Instance into_next_always_id (P : tProp) :
    IntoNext true P P | 10.
  Proof.
    rewrite /IntoNext. simpl. rewrite ltl_always_next.
    apply ltl_next_mono. eauto.
  Qed.

  Global Instance ltl_next_combine (P Q : tProp) :
    CombineSepAs (○ P) (○ Q) (○ (P ∧ Q)).
  Proof. by rewrite /CombineSepAs bi_sep_and ltl_next_and. Qed.

  Class FromNext (P Q : tProp) :=
    from_next : ○ P ⊢ Q.
  Global Arguments FromNext _%I _%I : simpl never.
  Global Arguments from_next _%I _%I {_}.
  Global Hint Mode FromNext - ! : typeclass_instances.

  Global Instance from_next_next (P : tProp) : FromNext P (○ P).
  Proof. done. Qed.

  Lemma modality_next_mixin : modality_mixin ltl_next
    (MIEnvTransform (IntoNext true)) (MIEnvTransform (IntoNext false)).
  Proof.
    split; simpl; eauto.
    - intros. split.
      + intros. rewrite -ltl_always_next_comm.
        iIntros "#HP !>". iStopProof.
        rewrite /IntoNext in H. apply H.
      + intros. by rewrite ltl_next_and.
    - by apply ltl_next_taut.
    - by apply ltl_next_mono.
    - iIntros (P Q) "[HP HQ]". iApply ltl_next_and. by iSplit.
    Unshelve. all: done.
  Qed.
  Definition modality_next := Modality ltl_next modality_next_mixin.
  Global Instance from_modal_next (P Q : tProp) :
    FromNext P Q → FromModal True modality_next Q Q P | 1.
  Proof. rewrite /FromModal /=. done. Qed.

  Global Instance into_wand_next p q (P Q R R' : tProp) :
    IntoNext p R R' →
    IntoWand p q R' P Q → IntoWand p q R (○ P)%I (○ Q)%I.
  Proof.
    rewrite /IntoWand /IntoNext.
    destruct p, q; simpl.
    - intros Hnext HR. iIntros "HR HP".
      rewrite ltl_always_idemp.
      rewrite Hnext.
      iModIntro. iApply (HR with "HR HP").
    - intros Hnext HR. iIntros "HR HP".
      rewrite ltl_always_idemp.
      rewrite Hnext.
      iModIntro. iApply (HR with "HR HP").
    - intros -> HR. iIntros "HR HP".
      iModIntro. by iApply (HR with "HR").
    - intros -> HR. iIntros "HR HP".
      iModIntro. by iApply (HR with "HR").
  Qed.

End ltl_proofmode.
