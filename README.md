# Kernel-proved specification synthesis for Lean 4

Given a program, this system produces formal specifications about it and proves
them. Every specification it emits has been checked by the Lean kernel; nothing
unproved is reported as a result.

It works on Lean 4 source directly and on Rust, by way of Charon and Aeneas,
which translate a Rust crate into a pure functional Lean model. Rust source
needs no annotation.

## What it does

```
Rust crate ──► Charon ──► Aeneas ──► Lean 4 definitions
                                          │
                                          ▼
                              candidate specifications
                                          │
                                   validation gates
                                          │
                                    proof search
                                          │
                                     refinement
                                          ▼
                          kernel-proved specification set
```

**Candidate generation.** Six strategies, selected by a complexity
classification of the target: direct prompting over seven property categories,
specification from observed input–output pairs, negative examples, joint
statement-and-proof generation, program slicing that specifies helpers before
their callers, and a behaviour-only strategy that hides the implementation.
Candidates are informed by Mathlib retrieval and by specifications proved in
earlier runs.

**Validation.** Candidates pass through progressively more expensive checks:
stored counterexamples from previous rejections, elaboration, concrete
evaluation, property-based testing, and a non-vacuity check that requires a
specification to *fail* on input-dependent wrong implementations. A
specification true of every implementation carries no information and is
rejected.

**Proof search.** Three layers, stopping at the first success. A curated tactic
portfolio derived from Mathlib's registered `hint` set, extended with
definitional and bitvector decision procedures. Then LeanHammer, which performs
neural premise selection over all of Mathlib rather than only the
`@[simp]`-tagged fragment. Then decomposition, in which the model proposes
intermediate lemmas, each is proved separately, and the recombined proof is
checked by the kernel as a single theorem.

**Refinement.** Program mutants are generated from an operator table and by
model rewriting, then classified by proof into equivalent, killed, survived or
unresolved — never by inference from a failed check. Surviving mutants are
concrete evidence that the specification set is too weak. A second tier searches
for an alternative implementation satisfying every proved specification while
differing from the original, which is a stronger form of the same evidence.

**Modularity.** For each function, the system checks whether its specification
follows from its callees' specifications alone, with callee implementations
abstracted away. Where it does not, it identifies which callee is underspecified
and whether the failure is a weak specification or an undischarged
precondition.

## Trust boundary

A status is never inferred from the absence of evidence. Every proved,
killed, survived or equivalent verdict rests on a proof confirmed in isolation.
A failed or timed-out check is reported as unresolved and excluded from the
denominator of any score.

No axioms are introduced. Function abstraction for the modularity check uses
universal quantification over a function variable rather than an assumed
constant, so the trust base remains the Lean kernel alone.

## What it reports

- proved specifications, with the layer and tactic that closed each one
- mutation score, with its denominator and the unresolved count shown separately
- surviving mutants and accepted adversarial implementations, as named
  weaknesses with the input that distinguishes them
- entailment-checked agreement with reference specifications, where a benchmark
  provides them
- contract-discharged calls and underspecified callees

## Requirements

Lean 4 with Mathlib. LeanHammer for the second proof layer. Python 3.11+ and an
Anthropic API key. For Rust targets, a project translated by Aeneas, with
Mathlib built.

## Running

```
python run.py --bench <name>                       # a Lean benchmark
python run.py --rust-project <path>                # every function in a crate
python run.py --rust-project <path> --bench <name> # one function
```

## Tests

```
python tests/run_all.py
```

Each test plants a case with a known answer — a deliberately weak specification
that must leave mutants alive, a strong one that must kill them, a callee
specification too weak to support its caller — and checks that the system
reaches the right verdict. They exist because several classes of defect in this
system are invisible in aggregate numbers and visible only against a known
answer.

## Status

Research code under active development. Interfaces change.
