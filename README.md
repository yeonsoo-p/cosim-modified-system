# Limits of non-iterative co-simulation: formal library and code

This repository accompanies the paper

> Y. Park, *Analysis of Non-Iterative Co-Simulation through Its Modified System: Limits on
> Accuracy, Energy and Damping*.

It contains the Lean 4 library in which the statements of the paper are formalised, the
correspondence between each statement of the paper and its Lean declarations, and the Python code
that computes the numbers and draws the figures of the paper.

## Contents

| Folder | What it is |
|---|---|
| `lean/` | The library `CoSimFoundations` (120 modules) and its axiom audit |
| `lean/CORRESPONDENCE.txt` | Statement of the paper → Lean declarations, with a status for each |
| `lean/SCOPE.txt` | The standard of the formalisation and the list of what is outside it |
| `python/figures/` | One script per figure of the paper |
| `python/numbers/` | Scripts that recompute the numbers of the examples, tables and text |

## The Lean library

- Lean 4 and Mathlib, both at release `v4.35.0` (`lean/lean-toolchain`, `lean/lake-manifest.json`).
- The library imports Mathlib and nothing else.
- It contains no `sorry`, and every audited theorem depends only on the three standard axioms of
  Lean: `propext`, `Classical.choice` and `Quot.sound`. The file `lean/CoSimFoundationsAudit.lean`
  runs `#print axioms` on 1,622 theorems by their fully qualified names; the build prints the result
  for each.
- Statements that the paper makes to leading order in the macro step are formalised at one macro
  step with an explicit bound on the remainder. `lean/SCOPE.txt` says in which form, and lists the
  statements of the paper that are not formalised.

To build:

```
cd lean
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib; without it Mathlib is compiled from source,
which takes hours. Each Lean process that imports Mathlib needs several gigabytes of memory, and
`lake build` runs several at once. On a machine with little memory build the modules one at a
time, for example `lake build CoSimFoundations.Setting`.

The headers of the modules name the statements of the paper by their labels (such as `thm:half`).
Where a header gives a statement number, it may be the number of an earlier draft;
`lean/CORRESPONDENCE.txt` has the numbers of the paper.

## The Python code

The scripts need Python 3 with `numpy`, `scipy` and `matplotlib`. `python/README.txt` lists each
script with what it computes and where the result stands in the paper.

## Licence

Apache License 2.0, see `LICENSE`.
