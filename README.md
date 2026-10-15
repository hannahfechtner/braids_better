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
git checkout 50c8de17ed3fe231596aea3ccb351195b2037cfa
lake exe cache get
lake build
```

The `git checkout` command selects the exact commit referenced by the links in the accompanying paper, ensuring that the source code and line numbers match. To build the latest version of the `afm` branch instead, omit this command.

The project uses Lean `v4.29.0-rc3`, as specified in `lean-toolchain`. The precise Mathlib version and other dependencies are recorded in `lake-manifest.json`.

## Trying the solver

An example of the solver's input syntax is:

```lean
#eval braid_solver (σ 1 * (σ 2 * σ 1)^{-2}) (σ 2 * σ 1 * σ 2)^3
```

## Author

**Hannah Fechtner**