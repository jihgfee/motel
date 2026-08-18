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

  Definition head_trace' (tr : trace_aux S L) : S * option L :=
    match tr with
    | tr_singl s => (s, None)
    | tr_cons s ℓ tr => (s, Some ℓ)
    end.

  Definition head_trace : trace S L → option (S * option L) :=
    fmap head_trace'.

  Definition tail_trace' (tr : trace_aux S L) : option (trace_aux S L) :=
    match tr with
    | tr_singl s => None
    | tr_cons s ℓ r => Some r
    end.

  Definition tail_trace : trace S L → trace S L :=
    mbind tail_trace'.

  CoInductive trace_maximal : trace S L → Prop :=
  | trace_maximal_empty : trace_maximal None
  | trace_maximal_singleton c :
    (∀ oζ c', ¬ R c oζ c') → trace_maximal (Some $ tr_singl c)
  | trace_maximal_cons c l tr c' :
    fst <$> head_trace (Some tr) = Some c' →
    R c l c' →
    trace_maximal (Some tr) →
    trace_maximal (Some $ tr_cons c l tr).

  Lemma trace_maximal_tail tr : trace_maximal tr → trace_maximal (tail_trace tr).
  Proof.
    intros wf.
    destruct tr as [[]|].
    - constructor.
    - simpl. inversion wf; simplify_eq. done.
    - simpl. constructor.
  Qed.

End well_formed.

Record wf_trace S L R := Trace {
  tr_car : trace S L;
  tr_wf : trace_maximal R tr_car;
}.

Arguments Trace {_ _ _} _ _.
Arguments tr_car {_ _ _} _.
Arguments tr_wf {_ _ _} _.
Arguments trace_maximal_empty {_ _ _}.
Arguments trace_maximal_singleton {_ _ _} _ _.

Notation "tr @ tr_wf" := (Trace tr tr_wf) (at level 100).

Section wf_after.
  Context {S L : Type}.
  Context {Rel : S → L → S → Prop}.

  Definition wf_head (tr : wf_trace S L Rel) : option (S * option L) :=
    head_trace (tr_car tr).

  Definition wf_tail : wf_trace S L Rel → wf_trace S L Rel :=
    λ tr, (tail_trace (tr_car tr)) @ (trace_maximal_tail Rel (tr_car tr) (tr_wf tr)).

  Notation wf_after n t := (Nat.iter n wf_tail t).

  Lemma wf_after_wf_tail_comm n (tr : wf_trace S L Rel) :
    wf_after n (wf_tail tr) = wf_tail (wf_after n tr).
  Proof. induction n; [done|]. simpl. by rewrite IHn. Qed.

  Lemma wf_after_0 tr : wf_after 0 tr = tr.
  Proof. by destruct tr. Qed.

  Lemma wf_after_sum n m tr : wf_after (n+m) tr = wf_after n (wf_after m tr).
  Proof. rewrite Nat.iter_add. done. Qed.

  Lemma wf_tail_wf_after (tr : wf_trace S L Rel) : wf_tail tr = wf_after 1 tr.
  Proof. done. Qed.

End wf_after.

Notation wf_after n t := (Nat.iter n wf_tail t).
