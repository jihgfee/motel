From motel Require Import ltl ltl_fixpoints ltl_now.

Section increment_example.
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

End increment_example.
