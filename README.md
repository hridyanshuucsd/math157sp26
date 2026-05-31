# Formalizing Brouwer's Fixed Point Theorem via Sperner's Lemma

MATH 157 Final Project — Hridyanshu

## What This Project Does

This repository contains a Lean4/Mathlib formalization of Brouwer's Fixed Point Theorem in two dimensions, proved via Sperner's Lemma. The proof proceeds in two stages. First, given any continuous self-map of the standard 2-simplex that has no fixed point, we construct a valid Sperner labeling of the barycentric subdivision by assigning each vertex the index of a coordinate that the map strictly decreases at that point. Second, Sperner's Lemma guarantees an odd (hence positive) number of fully labeled triangles at every subdivision level, and a sequential compactness argument extracts a fixed point from the resulting sequence of triangles.

## Repository Contents

| File | Description |
|------|-------------|
| `SpernerBrouwer.lean` | Main Lean 4 source file |
| `MATH157_Essay.pdf` | Part 1 essay: precise statements, proof pathway, and what formalization reveals |
| `Week8_MATH157.pdf` | Scope adjustment report documenting changes made during the project |

## Compilation Status

The file compiles successfully with one `sorry`, in the final step of `brouwer_fixed_point_2d` (the sequential compactness limit argument). Every other definition and lemma compiles without warnings.

## Build Instructions

**Step 1.** Install Lean 4 and Lake following the instructions at https://leanprover.github.io/lean4/doc/setup.html

**Step 2.** From the repository root, fetch the precompiled Mathlib cache:
```
lake exe cache get
```

**Step 3.** Open `SpernerBrouwer.lean` in VSCode with the Lean 4 extension, or build from the command line:
```
lake build
```

Mathlib is the only dependency. No other packages are required.

## Project Structure

The file is organized into eight sections:

1. `stdSimplex2` — the standard 2-simplex as a subset of `Fin 3 → ℝ`, with a compactness proof
2. `TVertex` — barycentric subdivision vertices with a `Fintype` instance and coordinate map
3. `IsSpernerLabeling` — the four conditions a valid Sperner labeling must satisfy
4. `STriangle` / `IsFullyLabeled` — triangles in the subdivision and the full-labeling predicate
5. `distCount` — counting distinguished (label-0 to label-1) edges per triangle
6. `allTriangles` / `sperner_lemma` — the combinatorial statement, declared as an axiom
7. `labelFromMap` / `labelFromMap_is_sperner` — the central construction, fully proved
8. `brouwer_fixed_point_2d` — the topological conclusion, Step 1 proved and Step 2 sketched
