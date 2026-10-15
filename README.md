# Braids in Lean: Dehornoy's Subword Reversing Algorithm

This repository contains a Lean 4 formalization of Dehornoy's subword reversing method for the braid group word problem. Included are the algebraic definitions of braid groups and braid monoids, a basic theory of rectangular grid diagrams (a special case of van Kampen diagrams), and an executable algorithm for deciding whether two braid words represent the same braid group element, along with a formal proof of its correctness.

The repository accompanies a paper describing both the relevant mathematics and its formal verification in Lean.

## Repository organization

The easiest way to navigate the repository is to look through the associated paper and click the links on the righthand margins. As an overview,

- [`BraidProject/`](https://github.com/hannahfechtner/braids_better/tree/afm/BraidProject) contains all the Lean files.
- [`BraidProject/BraidGroup.lean`](https://github.com/hannahfechtner/braids_better/blob/afm/BraidProject/BraidGroup.lean) defines finite- and infinite-strand braid groups.
- [`BraidProject/Solver/GroupCorrectnessHardDirection.lean`](https://github.com/hannahfechtner/braids_better/blob/afm/BraidProject/Solver/GroupCorrectnessHardDirection.lean) contains the algorithm to solve the word problem in infinite braid groups, `braid_solver`, and its correctness theorem, `braid_solver_correct`.
- [`BraidProject/Solver/Solver_Fin.lean`](https://github.com/hannahfechtner/braids_better/blob/afm/BraidProject/Solver/Solver_Fin.lean) defines the solver for finite braid groups and proves its correctness theorem, `solver_fin_correct`
- [`BraidProject/Solver/Examples.lean`](https://github.com/hannahfechtner/braids_better/blob/afm/BraidProject/Solver/Examples.lean) shows a few examples of how to call the solvers

## Building the project

Install [Lean 4](https://lean-lang.org/install/) and Git. Then run:

```bash
git clone --branch afm https://github.com/hannahfechtner/braids_better.git
cd braids_better
lake exe cache get
lake build
```

Note that the Lean version for the frozen links in the paper is `4.29.0`, and the precise Mathlib SHA can be found in `lake-mainfest.json`.  

## Trying the solver

An example of the solver's input syntax is:

```lean
#eval braid_solver (σ 1 * (σ 2 * σ 1)^{-2}) (σ 2 * σ 1 * σ 2)^3
```

## Author

**Hannah Fechtner**