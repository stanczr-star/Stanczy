# Nonlocal Elliptic Equations in Lean 4 (Stańczy, 2001)

A Lean 4 formalization of the main constructions, boundary value problem equivalences, and existence theorems from the paper:
> **R. Stańczy**, *Nonlocal elliptic equations*, Nonlinear Analysis 47 (2001), 3579–3584.

## Overview
* **Main file:** [`Stanczy2001.lean`](./Stanczy2001.lean)
* **Toolchain:** Lean `v4.35.0-rc3`
* **Mathlib commit:** `8e30cac82f69c18f6cbe88799bdc3ebd74cc592d`
* **Proof status:** Zero `sorry` / `admit`. All analytical assertions, operator compactness results (via Arzelà–Ascoli), BVP equivalences, and cone properties are fully proved. Only the abstract Guo–Lakshmikantham cone compression/expansion fixed-point principle (`guo_lakshmikantham_fixed_point`) is assumed as an explicit axiom.

## Contents
1. **Abstract fixed-point theorem in a cone** (Theorem 2.1 & counterexample to the unrestricted trivial-cone formulation).
2. **One-dimensional case** (BVP (2)–(5), Green function, Harnack cone, complete continuity, Theorem 2.2, Examples 1–3).
3. **Radial problem in an annulus** (Equations (11)–(15), radial Green kernel, Theorem 3.1, Remarks 1–3).

## How to Verify

### Option 1: Instant verification in the browser (No installation)
1. Open [Lean 4 Web (live.lean-lang.org)](https://live.lean-lang.org/).
2. Load or paste the contents of `Stanczy2001.lean`.

### Option 2: Local / Codespaces build with Lake
```bash
lake exe cache get
lake env lean Stanczy2001.lean
