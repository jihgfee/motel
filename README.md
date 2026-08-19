# MoTeL: Extensible Modal Framework for Interactive Proofs in Linear Temporal Logic

MoTeL is a proofmode interface for working with linear temporal logic in Rocq, built on top of the MoSeL proofmode interface for separation logic, most notably used for the Iris logic: https://iris-project.org/ .

## Installation Instructions

### Dependencies

MoTeL has been installed with

- opam: 2.5.1
- OCaml: 5.4.1
- Rocq: 9.2.0
- Iris: 8e5e08bc (branch)

To install `opam` we refer to https://opam.ocaml.org/doc/Install.html .

We recommend setting up an opam switch via

`opam switch create motel 5.4.1`.

Rocq can be installed via

`opam install rocq-core.9.2.0`

The specific Iris version can be found here: https://gitlab.mpi-sws.org/iris/iris/-/tree/robbert/elim_modal_modality

It can be installed following the build instructions of Iris.

## Overview

The proofmode interface can be instantiated by giving a linear transition system (LTS) model by providing a notion of state (S), label (L), and transition relation (R).

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
For example, given a model:

```
  S := bool.
  L := bool.
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

The above proof can be found in
[./theories/examples.v](./theories/examples.v)
