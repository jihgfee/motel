From ltl Require Import ltl ltl_fixpoints ltl_now ltl_adequacy classical.

Import tProp.

Section petri_nets.
  Context (place : Set).
  Context `{Countable place}.
  Context (transition : Set).
  Context `{Countable transition}.
  Context (input_arcs : gset (place * transition)).
  Context (output_arcs : gset (transition * place)).

  Definition enabled (t : transition) (s:gmap place nat) : Prop :=
    (∀ p, (p,t) ∈ input_arcs → ∃ x, s !! p = Some x ∧ x > 0).

  Inductive R : gmap place nat → transition → gmap place nat → Prop :=
  | fire s1 s2 t :
      enabled t s1 →
      (∀ p, (p,t) ∉ input_arcs → (t,p) ∉ output_arcs → s2 !! p = s1 !! p) →
      (∀ p x, (p,t) ∈ input_arcs → s1 !! p = Some x → s2 !! p = Some (x - 1)) →
      (∀ p x, (t,p) ∈ output_arcs → s1 !! p = Some x → s2 !! p = Some (x + 1)) →
      R s1 t s2.

  Notation tProp := (tProp (gmap place nat) (transition) R).

  Lemma petri_lbl_enabled t : ↓l t ⊢ ↓s' (enabled t) : tProp.
  Proof.
    iIntros "Hl".
    iDestruct (ltl_dup with "Hl") as "[Hl Hl']".
    iDestruct (ltl_st with "Hl'") as (s) "Hs".
    { intros [[]|]; eauto. naive_solver. }
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (trace_steps_label with "[$Hs' $Hl]") as (s' Hrel) "_".
    inversion Hrel.
    iApply (ltl_now_mono_state with "Hs").
    intros s'' <-. simplify_eq. naive_solver.
  Qed.

End petri_nets.

Arguments R {_ _ _ _ _ _} _ _ _.
Arguments enabled {_ _ _ _ _ _} _ _.

Section example.

  (*
    Model:
      t0 -> p0 ---> t1 ---> p1 ---> t3 ---> p3
      |                      ^
      -----> t2 ---> p2 ---> |

    Property: ◊ p3 > 0

    Fairness assumption: □ ◊ (↓s' enabled t) ⊢@{tProp} ◊ ↓l t
   *)

  Inductive place : Set := p0 | p1 | p2 | p3.
  Inductive transition : Set := t0 | t1 | t2 | t3.

  Instance place_dec : EqDecision place.
  Proof. intros [] []; unfold Decision; try naive_solver; right; naive_solver. Qed.
  Definition encode_place (p:place) : positive :=
    match p with
    | p0 => 1
    | p1 => 2
    | p2 => 3
    | p3 => 4
    end.
  Definition decode_place (p:positive) : option place :=
    match p with
    | 1%positive => Some p0
    | 2%positive => Some p1
    | 3%positive => Some p2
    | 4%positive => Some p3
    | _ => None
    end.
  Lemma decode_encode_place p :
    decode_place (encode_place p) = Some p.
  Proof. destruct p; done. Qed.
  Instance place_countable : Countable place :=
    { encode := encode_place;
      decode := decode_place;
      decode_encode := decode_encode_place }.

  Definition encode_transition (p:transition) : positive :=
    match p with
    | t0 => 1
    | t1 => 2
    | t2 => 3
    | t3 => 4
    end.
  Definition decode_transition (p:positive) : option transition :=
    match p with
    | 1%positive => Some t0
    | 2%positive => Some t1
    | 3%positive => Some t2
    | 4%positive => Some t3
    | _ => None
    end.
  Lemma decode_encode_transition p :
    decode_transition (encode_transition p) = Some p.
  Proof. destruct p; done. Qed.
  Instance transition_dec : EqDecision transition.
  Proof. intros [] []; unfold Decision; try naive_solver; right; naive_solver. Qed.
  Instance transition_countable : Countable transition :=
    { encode := encode_transition;
      decode := decode_transition;
      decode_encode := decode_encode_transition }.

  Definition input_arcs : gset (place * transition) :=
    {[ (p0,t1); (p0,t2); (p1,t3); (p2,t3) ]}.
  Definition output_arcs : gset (transition * place) :=
    {[ (t0,p0); (t1,p1); (t2,p2); (t3,p3) ]}.

  Notation tProp := (tProp (gmap place nat) transition (R input_arcs output_arcs)).

  Axiom fair : ∀ (t:transition),
    □ ◊ (↓s' enabled input_arcs t) ⊢@{tProp} ◊ ↓l t.

  Lemma always_reducible s :
    reducible (R input_arcs output_arcs) s.
  Proof.
    eexists _, _. apply (fire _ _ _ _ _ (<[p0 := (s : gmap place nat) !!! p0 + 1]>s) t0).
    - intros p Hp. destruct p; set_solver.
    - intros. destruct p; [set_solver|..]; by rewrite lookup_insert_ne.
    - intros. destruct p; set_solver.
    - intros. destruct p; try set_solver.
      rewrite lookup_insert. case_decide; [|done]. simplify_eq.
      rewrite lookup_total_alt. simpl. rewrite H0. done.
  Qed.

  Lemma t0_enabled : ∞ ⊢@{tProp} □ ↓s' (enabled input_arcs t0).
  Proof.
    iIntros "#Hinf !>".
    rewrite ltl_now_not.
    iApply (ltl_now_mono with "Hinf").
    intros [[]|]=> /=; try eauto.
    intros H p Hp.
    destruct p; set_solver.
  Qed.

  Lemma t0_fire n0 n1 n2 n3 :
    ↓l t0 ⊢@{tProp}
    ↓s {[p0 := n0;   p1 := n1;   p2 := n2; p3 := n3]} →
    ○ ↓s {[p0 := n0+1; p1 := n1;   p2 := n2; p3 := n3]}.
  Proof.
    iIntros "Hl Hs".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as (s' HRel) "H".
    iModIntro. inversion HRel.
    simplify_eq.
    iApply (ltl_now_mono_state with "H").
    intros s ->.
    assert (s !! p0 = Some (n0 + 1)).
    { apply H2; set_solver. }
    assert (s !! p1 = Some n1).
    { rewrite H0; set_solver. }
    assert (s !! p2 = Some n2).
    { rewrite H0; set_solver. }
    assert (s !! p3 = Some n3).
    { rewrite H0; set_solver. }
    clear HRel H H0 H1 H2.
    apply map_eq. intros i.
    destruct i; set_solver.
  Qed.

  Lemma t1_fire n0 n1 n2 n3 :
    ↓l t1 ⊢@{tProp}
            ↓s {[p0 := n0;   p1 := n1;   p2 := n2; p3 := n3]} →
            ○ ↓s {[p0 := n0-1; p1 := n1+1; p2 := n2; p3 := n3]}.
  Proof.
    iIntros "Hl Hs".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as (s' HRel) "H".
    iModIntro. inversion HRel.
    simplify_eq.
    iApply (ltl_now_mono_state with "H").
    intros s ->.
    assert (s !! p0 = Some $ n0 - 1).
    { apply H1; set_solver. }
    assert (s !! p1 = Some $ n1 + 1).
    { apply H2; set_solver. }
    assert (s !! p2 = Some n2).
    { rewrite H0; set_solver. }
    assert (s !! p3 = Some n3).
    { rewrite H0; set_solver. }
    clear HRel H H0 H1 H2.
    apply map_eq. intros i. destruct i; set_solver.
  Qed.

  Lemma t2_fire n0 n1 n2 n3 :
    ↓l t2 ⊢@{tProp}
            ↓s {[p0 := n0;   p1 := n1; p2 := n2;   p3 := n3]} →
            ○  ↓s {[p0 := n0-1; p1 := n1; p2 := n2+1; p3 := n3]}.
  Proof.
    iIntros "Hl Hs".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as (s' HRel) "H".
    iModIntro. inversion HRel.
    simplify_eq.
    iApply (ltl_now_mono_state with "H").
    intros s ->.
    assert (s !! p0 = Some $ n0 - 1).
    { apply H1; set_solver. }
    assert (s !! p1 = Some n1).
    { rewrite H0; set_solver. }
    assert (s !! p2 = Some $ n2 + 1).
    { apply H2; set_solver. }
    assert (s !! p3 = Some n3).
    { rewrite H0; set_solver. }
    clear HRel H H0 H1 H2.
    apply map_eq. intros i. destruct i; set_solver.
  Qed.

  Lemma t3_fire n0 n1 n2 n3 :
    ↓l t3 ⊢@{tProp}
            ↓s {[p0 := n0;   p1 := n1 ; p2 := n2;   p3 := n3 ]} →
            ○  ↓s {[p0 := n0; p1 := n1 - 1; p2 := n2 - 1; p3 := n3 + 1]}.
  Proof.
    iIntros "Hl Hs".
    iDestruct (trace_steps_label with "[$Hs $Hl]") as (s' HRel) "H".
    iModIntro. inversion HRel.
    simplify_eq.
    iApply (ltl_now_mono_state with "H").
    intros s ->.
    assert (s !! p0 = Some n0).
    { apply H0; set_solver. }
    assert (s !! p1 = Some $ n1 - 1).
    { apply H1; set_solver. }
    assert (s !! p2 = Some $ n2 - 1).
    { apply H1; set_solver. }
    assert (s !! p3 = Some $ n3 + 1).
    { apply H2; set_solver. }
    clear HRel H H0 H1 H2.
    apply map_eq. intros i. destruct i; set_solver.
  Qed.

  Lemma petri_st_lbl s : ↓s s ⊢ ∃ l, ↓l l : tProp.
  Proof.
    iIntros "Hs".
    iDestruct (trace_steps with "Hs") as (l s' Hrel) "[Hl Hs']".
    { apply always_reducible. }
    iFrame.
  Qed.

  Lemma safety_inv n0 n1 n2 n3:
    ↓s {[p0:=n0;p1:=n1;p2:=n2;p3:=n3]} ⊢@{tProp}
    □ ∃ n0 n1 n2 n3, ↓s {[p0:=n0;p1:=n1;p2:=n2;p3:=n3]}.
  Proof.
    iIntros "Hs".
    iAssert (∃ n0 n1 n2 n3 : nat, ↓s {[p0:=n0; p1:=n1; p2:=n2; p3:=n3]})%I
      with "[Hs]" as "Hs".
    { eauto. }
    iApply (ltl_always_intro with "[] Hs").
    iIntros "!> Hs".
    iDestruct "Hs" as (????) "Hs".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (petri_st_lbl with "Hs'") as (l) "Hl".
    destruct l.
    - iDestruct (t0_fire with "Hl Hs") as "Hs".
      iModIntro. iFrame.
    - iDestruct (t1_fire with "Hl Hs") as "Hs".
      iModIntro. iFrame.
    - iDestruct (t2_fire with "Hl Hs") as "Hs".
      iModIntro. iFrame.
    - iDestruct (t3_fire with "Hl Hs") as "Hs".
      iModIntro. iFrame.
  Qed.

  Lemma petri_inf :
    ↓s {[p0:=0;p1:=0;p2:=0;p3:=0]} ⊢@{tProp} ∞.
  Proof.
    iIntros "Hs".
    iAssert (∃ n0 n1 n2 n3 : nat, ↓s {[p0:=n0; p1:=n1; p2:=n2; p3:=n3]})%I
      with "[Hs]" as "Hs".
    { eauto. }
    iApply (ltl_always_coind with "[] Hs").
    iIntros "!> Hs". iSplit.
    { iIntros "Hl".
      iDestruct "Hs" as (????) "Hs".
      iCombine "Hs Hl" as "H".
      iDestruct (ltl_now_pure with "H") as %[[[]|] H];
        simpl in *; naive_solver.
    }
    iDestruct "Hs" as (????) "Hs".
    iDestruct (safety_inv with "Hs") as "#Hs'".
    iModIntro. iLeft. iFrame.
    done.
  Qed.

  Theorem petri_live :
    ↓s {[p0:=0;p1:=0;p2:=0;p3:=0]} ⊢@{tProp} ◊ ↓s' (λ s, (∃ x, s !! p3 = Some x ∧ x > 0)%type).
  Proof.
    iIntros "Hs".
    iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
    iDestruct (petri_inf with "Hs'") as "Hinf".
    iRevert "Hs".
    iDestruct (t0_enabled with "Hinf") as "#Ht0".
    iDestruct (fair with "[]") as "Ht0'".
    { do 2 iModIntro. done. }
    iIntros "Hs'".
    iDestruct (safety_inv with "Hs'") as "#Hs".
    iAssert (□ ◊ (↓s' (enabled input_arcs t1) ∧ ↓s' (enabled input_arcs t2)))%I with "[Hs]" as "#H".
    {
      iModIntro.
      iMod "Ht0'".
      iDestruct "Hs" as (????) "Hs".
      iDestruct (t0_fire n0 with "Ht0' Hs") as "H'".
      iEval (rewrite -ltl_next_eventually).
      do 2 iModIntro.
      iSplit.
      - iApply (ltl_now_mono_state with "H'").
        intros s <-.
        intros p Hp. repeat (destruct p; try set_solver).
        eexists _. split; [set_solver|lia].
      - iApply (ltl_now_mono_state with "H'").
        intros s <-.
        intros p Hp. repeat (destruct p; try set_solver).
        eexists _. split; [set_solver|lia].
    }
    rewrite ltl_eventually_and.
    iDestruct "H" as "[Ht1 Ht2]".
    iClear "Hs'".
    iDestruct (fair with "Ht1") as "Ht1'".
    iDestruct (fair with "Ht2") as "Ht2'".
    iAssert (□ ◊ (↓s' (enabled input_arcs t3)))%I as "#Ht3".
    {
      iAssert (◊ ↓s' (λ s, (∃ x, s !! p1 = Some x ∧ x > 0)%type))%I as "Hn1".
      {
        iMod "Ht1'".
        iDestruct "Hs" as (????) "Hs".
        iDestruct (t1_fire with "Ht1' Hs") as "Ht1'".
        iEval (rewrite -ltl_next_eventually).
        do 2 iModIntro.
        iApply (ltl_now_mono_state with "Ht1'").
        intros s <-.
        simplify_map_eq.
        eexists _. split; [done|lia].
      }
      iModIntro.
      iMod "Hn1".
      iRevert "Hn1".
      iApply (ltl_eventually_ind_strong with "[] Ht2'").
      iIntros "!> [Ht2''|H] Hn1".
      {
        iDestruct "Hs" as (????) "Hs".
        destruct n1.
        { iCombine "Hn1 Hs" as "Hs".
          iDestruct (ltl_now_pure with "Hs") as %[[[]|] H]; [|done].
          simpl in *.
          destruct H as [H1 H2].
          simplify_eq.
          destruct H1 as (x&HSome&Hx).
          simplify_map_eq. lia. }
        iDestruct (t2_fire with "Ht2'' Hs") as "Hs".
        iEval (rewrite -ltl_next_eventually).
        do 2 iModIntro.
        iApply (ltl_now_mono_state with "Hs").
        intros s <-.
        subst. intros p Hp.
        repeat (destruct p; try set_solver).
        - eexists _. split; [set_solver|lia].
        - eexists _. split; [set_solver|lia].
      }
      iDestruct "H" as "[H1 H2]".
      iDestruct "Hs" as (????) "Hs".
      destruct n2; last first.
      { iModIntro.
        (* TODO: Make a proper combine instance for ltl_now_state *)
        iCombine "Hs Hn1" as "Hs".
        iApply (ltl_now_mono with "Hs").
        intros [[]|]=> /=; intros H; simplify_eq; eauto.
        destruct H as [H1 H2]. simplify_eq.
        intros p Hp. destruct p; try set_solver.
        eexists _. split; [set_solver|lia].
      }
      iEval (rewrite -ltl_next_eventually).
      (* TODO: add destruct typeclass for next *)
      iAssert (○ ((↓s' λ s : gmap place nat, (∃ x, s !! p1 = Some x ∧ x > 0)%type) ∨
                 (↓s' enabled input_arcs t3)))%I with "[Hs Hn1]" as "H".
      { iDestruct (ltl_dup with "Hs") as "[Hs Hs']".
        iDestruct (petri_st_lbl with "Hs") as (l) "Hl".
        destruct n1.
        {
          iCombine "Hs' Hn1" as "Hs'".
          iDestruct (ltl_now_pure with "Hs'") as %[[[]|] H]; simpl in *; try done.
          destruct H as [H1 H2].
          subst.
          destruct H2 as (x&HSome&Hx).
          simplify_map_eq. lia.
        }
        destruct l.
        - iDestruct (t0_fire with "Hl Hs'") as "Hs'".
          iModIntro. iLeft.
          iApply (ltl_now_mono_state with "Hs'").
          intros s <-.
          eexists _. simplify_map_eq. split; [done|lia].
        - iDestruct (t1_fire with "Hl Hs'") as "Hs'".
          iModIntro. iLeft.
          iApply (ltl_now_mono_state with "Hs'").
          intros s <-.
          eexists _. simplify_map_eq. split; [done|lia].
        - iDestruct (t2_fire with "Hl Hs'") as "Hs'".
          iModIntro. iLeft.
          iApply (ltl_now_mono_state with "Hs'").
          intros s <-.
          eexists _. simplify_map_eq. split; [done|lia].
        -
          iDestruct (petri_lbl_enabled with "Hl") as "Hs".
          iCombine "Hs Hs'" as "Hs".
          iDestruct (ltl_now_pure with "Hs") as %[[[]|] H]; [|done].
          simpl in *.
          destruct H as [H1 H2].
          assert ((p2, t3) ∈ input_arcs) by set_solver.
          specialize (H1 p2 H).
          destruct H1 as (x&HSome&Hx).
          simplify_map_eq. lia.
      }
      iModIntro.
      iDestruct "H" as "[H'|H']".
      - by iApply "H2".
      - iModIntro. done.
    }
    iDestruct (fair with "Ht3") as "Ht3'".
    iMod "Ht3'".
    iDestruct "Hs" as (????) "Hs".
    iDestruct (t3_fire with "Ht3' Hs") as "Hs".
    iEval (rewrite -ltl_next_eventually).
    do 2 iModIntro.
    iApply (ltl_now_mono_state with "Hs").
    intros s <-.
    eexists _. split ; [set_solver|lia].
  Qed.

End example.
