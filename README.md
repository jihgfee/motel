# MoTeL: Modal Temporal Logic Proofmode

MoTeL is a proofmode interface for working with modal temporal logic in Rocq, built on top of the MoSeL proofmode interface for separation logic, most notably used for the Iris logic: https://iris-project.org/

## Installation Instructions

### Dependencies

MoTeL has the following dependencies:

- opam: 2.5.1
- OCaml: 5.4.1
- Rocq: 9.2.0
- Iris: d6bbe37c

To install `opam` we refer to https://opam.ocaml.org/doc/Install.html

We recommend setting up an opam switch via

`opam switch create motel 5.4.1`

To install the Rocq and Iris dependencies, first add their repositories to opam with

`opam repo add rocq-released https://rocq-prover.github.io/opam/released/`

and

`opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git`

The dependencies can then be installed via

`make builddep [num CPU cores]`

### Building

Once the above dependencies have been installed, the development can be built using

`make [num CPU cores]`

### Installation 

After building the development it can be installed to the opam switch via

`make install`

## Overview of Development

The development defines a linear temporal logic closely resembling LTL, with higher-order impredicative quantification and fixpoints.

[./motel/trace.v](./motel/trace.v) defines the possibly-finite traces over which the temporal logic is defined.

[./motel/ltl.v](./motel/ltl.v) defines the temporal logic foundation, and MoSeL instantiation, giving definitions for the connectives required by MoSeL; entailment `⊢`, the propositional connectives `True`, `False`, `∧`, `∨`, `∀`, `∃`, `→`, and the persistent modality `□`.
The propositional connectives are defined as pointwise lifting of the corresponding Rocq connectives over traces.
The persistent modality is defined as the "globally" temporal modality, which we derive from the next modality `○ P ≜ λ tr, P (tail tr)` as `□ 𝑃  ≜ ∀ n, ○^n P`.

[./motel/ltl_fixpoints.v](./motel/ltl_fixpoints.v) defines the temporal logic until `∪` and eventually `◊` modalities.
The modalities are defined in terms of Knaster-Tarski fixpoints: `P ∪ Q ≜ μ X. Q ∨ (P ∧ ○ X)` and `◊ P ≜ True ∪ Q`.

[./motel/ltl_now.v](./motel/ltl_now.v) defines a point connective for assertions over the head of a trace `↓φ ≜ λ tr, ϕ (head tr)`, along with projection variants for asserting equality with exact states and labels.
It also includes lemmas for deriving logic-level assertions from a concrete model.

[./motel/ltl_adequacy.v](./motel/ltl_adequacy.v) defines the adequacy theorem of MoTeL for extracting meta-level assertions about traces from temporal logic-level proofs.

[./motel/ltl_classical.v](./motel/ltl_classical.v) axiomatise excluded middle, and derive a temporal logic level variant, along with consequential lemmas.

[./motel/examples/](./motel/examples/) contains a suite of examples using MoTeL.

## Overview of Proofmode

The proofmode interface can be instantiated by giving a labelled transition system (LTS) model by providing a notion of state (S), label (L), and transition relation (R).

The traces are possibly-finite, and come with `head` and `tail` functions:

```
  tr := ⟨ ⟩ | ⟨ s ⟩ | s -[l]-> tr
  tail (s -[l]-> tr) = tr , tail ⟨ s ⟩ = ⟨ ⟩, tail ⟨ ⟩ = ⟨ ⟩
  head (s -[l]-> tr) = (s,l) , head ⟨ s ⟩ = (s,⊥), head ⟨ ⟩ = ⊥
```

The `head` and `tail` functions are reflected in the logic as  `↓ p` (now) and `○ P` (next).
The remaining conventional primitives of LTL, such as `□ P` (globally), `◊ P` (eventually) and `P ∪ Q` (until) are derived from next.
We additionally have `↓s x` and `↓l x` variants of `↓ p` that asserts the current state and label, respectively.

The proofmode provides infrastructure for proving model-level axioms, that reflect the LTS transition relation in LTL.

To give an example, consider the following model (mechanised via MoTeL in [./motel/examples/fair_coin.v](./motel/examples/fair_coin.v)):

```
  S := bool
  L := bool
  R := b -[b]-> (¬ b) | b -[¬b]-> b
```

The relation yields the following axiom:

```
  ↓s b ⊢ (↓l b ∧ ○ ↓s (¬ b)) ∨ (↓l (¬ b) ∧ ○ ↓s b)
```

One can then express and prove properties about the model, such as fair progress:

```
  □ (◊ ↓l b) ∧ ◊ ↓s b ⊢ ○ ◊ ↓s ¬ b.
```

The proofmode comes with tactics inherited from [MoSeL](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md), allowing (1) managing the proof context of the temporal logic, and (2) eliminating and introducing modalities while updating the proof context soundly and conservatively.

For example, a proof of the above can be started via `iIntros "[#Hfair Hs]"`, yielding the proof context:

```
  "Hfair" : ◊ ↓l b
  --------------------------------------□
  "Hs" : ◊ ↓s b
  --------------------------------------∗
  ○ ◊ ↓s ¬ b
```

Similar to MoSeL, the `iMod "Hs"` tactic will eliminate the `◊` in `Hs`, which is sound in the current context:

```
  "Hfair" : ◊ ↓l b
  --------------------------------------□
  "Hs" : ↓s b
  --------------------------------------∗
  ○ ◊ ↓s ¬ b
```

The proofmode yields induction principles for `◊`, which can be used alongside `Hfair` to arrive at the time where `b` is scheduled, with an unchanged state:

```
  "Hfair" : ◊ ↓l b
  --------------------------------------□
  "Hs" : ↓s b
  "Hl" : ↓l b
  --------------------------------------∗
  ○ ◊ ↓s ¬ b
```

Given the above model-level axiom, we can use `"Hs"` and `"Hl"` to arrive at:

```
  "Hfair" : ◊ ↓l b
  --------------------------------------□
  "Hs" : ○ ↓s ¬ b
  --------------------------------------∗
  ○ ◊ ↓s ¬ b
```

The proofmode also inherits MoSeL's `iModIntro` tactic, that here introduce `○`, updating the non-persistent proof context accordingly by removing `○` from all hypotheses:

```
  "Hfair" : ◊ ↓l b
  --------------------------------------□
  "Hs" : ↓s ¬ b
  --------------------------------------∗
  ◊ ↓s ¬ b
```

We can finally introduce `◊` via `iModIntro`, concluding the proof.
