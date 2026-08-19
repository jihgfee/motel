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

The traces are possibly-finite: `tr := ⟨ ⟩ | ⟨ s ⟩ | s -[l]-> tr`, where `tail ⟨ s ⟩ = ⟨ ⟩` and `tail ⟨ ⟩ = ⟨ ⟩`.

For example, given a model:

```
  S := bool.
  L := bool.
  R := b -[b]-> (¬ b) | b -[¬b]-> b
```

The proofmode provides infrastructure for proving model-level axioms, that reflect the LTS transition relation in LTL, for example, the above relation corresponds to:

```
↓s b ⊢ (↓l b ∧ ○ ↓s (negb b)) ∨ (↓l (negb b) ∧ ○ ↓s b)
```

Additionally, one can express and prove properties such as fair progress, as follows:

```
  □ (◊ ↓l b) ∧ ◊ ↓s b ⊢ ○ ◊ ↓s ¬ b.
```

The proofmode comes with tactics inherited from MoSeL, allowing (1) managing the proof context of the temporal logic, and (2) eliminating and introducing modalities while updating the proof context soundly and conservatively.

For example, a proof of the above can be started via `iIntros "[#Hfair Hs]"`, yielding:

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
