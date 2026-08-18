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

End well_formed.
