From Stdlib.Arith Require Import PeanoNat.
From stdpp Require Import option.

Delimit Scope trace_scope with trace.

CoInductive trace_aux (S L : Type) :=
| tr_singl (s: S)
| tr_cons (s: S) (ℓ: L) (r: trace_aux S L).

Definition trace (S L : Type) := option $ trace_aux S L.

Arguments tr_singl {_} {_} _.
Arguments tr_cons {_} {_} _ _ _.

Bind Scope trace_scope with trace.

Arguments tr_singl {_} {_} _.
Arguments tr_cons {_} {_} _ _ _%trace.
Notation "⟨ ⟩" := (None) : trace_scope.
Notation "⟨ s ⟩" := (Some (tr_singl s)) : trace_scope.
Notation "s -[ ℓ ]->  r" := (Some (tr_cons s ℓ r)) (at level 33) : trace_scope.
Open Scope trace.

Section well_formed.
  Context {S L : Type}.
  Context (R : S → L → S → Prop).

  Definition head_trace_aux (tr : trace_aux S L) : S * option L :=
    match tr with
    | tr_singl s => (s, None)
    | tr_cons s ℓ tr => (s, Some ℓ)
    end.

  Definition tail_trace_aux (tr : trace_aux S L) : option (trace_aux S L) :=
    match tr with
    | tr_singl s => None
    | tr_cons s ℓ r => Some r
    end.

  Definition head_trace : trace S L → option (S * option L) :=
    fmap head_trace_aux.

  Definition tail_trace : trace S L → trace S L :=
    mbind tail_trace_aux.

  CoInductive trace_well_formed : trace S L → Prop :=
  | trace_well_formed_empty : trace_well_formed None
  | trace_well_formed_singleton c :
    (∀ oζ c', ¬ R c oζ c') → trace_well_formed (Some $ tr_singl c)
  | trace_well_formed_cons c l tr c' :
    fst <$> head_trace (Some tr) = Some c' →
    R c l c' →
    trace_well_formed (Some tr) →
    trace_well_formed (Some $ tr_cons c l tr).

  Lemma trace_well_formed_tail tr : trace_well_formed tr → trace_well_formed (tail_trace tr).
  Proof.
    intros Hwf.
    destruct tr as [[s|s l tr]|].
    - by constructor.
    - by inversion Hwf; simplify_eq.
    - by constructor.
  Qed.

End well_formed.

Record wf_trace S L R := Trace {
  tr_car : trace S L;
  tr_wf : trace_well_formed R tr_car;
}.

Arguments Trace {_ _ _} _ _.
Arguments tr_car {_ _ _} _.
Arguments tr_wf {_ _ _} _.
Arguments trace_well_formed_empty {_ _ _}.
Arguments trace_well_formed_singleton {_ _ _} _ _.
Arguments trace_well_formed_cons {_ _ _} _ _.

Notation "tr @ tr_wf" := (Trace tr tr_wf) (at level 100).

Section wf_after.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Definition wf_head (tr : wf_trace S L Rel) : option (S * option L) :=
    head_trace (tr_car tr).

  Definition wf_tail (tr : wf_trace S L Rel) : wf_trace S L Rel :=
    (tail_trace (tr_car tr)) @ (trace_well_formed_tail Rel (tr_car tr) (tr_wf tr)).

  Notation wf_after n t := (Nat.iter n wf_tail t).

  Lemma wf_after_wf_tail_comm n (tr : wf_trace S L Rel) :
    wf_after n (wf_tail tr) = wf_tail (wf_after n tr).
  Proof. induction n; [done|]. simpl. by rewrite IHn. Qed.

  Lemma wf_after_0 tr : wf_after 0 tr = tr.
  Proof. done. Qed.

  Lemma wf_after_sum n m tr : wf_after (n+m) tr = wf_after n (wf_after m tr).
  Proof. by rewrite Nat.iter_add. Qed.

  Lemma wf_tail_wf_after (tr : wf_trace S L Rel) : wf_tail tr = wf_after 1 tr.
  Proof. done. Qed.

End wf_after.

Notation wf_after n t := (Nat.iter n wf_tail t).
