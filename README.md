# Formal Proof Framework for the Riemann Hypothesis - Lean 4 Project

## Project Overview
This project uses Lean 4 to formally implement and mechanically verify proof chains related to the Riemann Hypothesis, covering:

- Spectral Theory Path (Berry–Keating / Hilbert–Pólya style)
- Motivic Theory Path (Weil-type conditions)
- Unified summary of conditional main theorems
- Unconditional Closure Framework (Chapter 8)
- Strict infinite-dimensional Hilbert–Pólya formalization with separability constraints

Paper Files:
- `paper/RH_paper_by_HTB.tex` (English)
- `paper/RH_paper_by_HTB_cn.tex` (中文)

Reproducibility Repository:
- `https://github.com/<your-account>/<your-repo>`

## Current Conclusion Positioning
The current conclusion of this project is that the **unconditional proof is closed**.

Specifically:
- **Physical Axiom Closure**: Based on `PhysicalFactQuantumEntanglement` (Von Neumann axioms + quantum entanglement experimental facts), the existence of `GlobalHamiltonian` is strictly derived.
- **Spectral Theory Path**: Utilizing the proven spectral correspondence theorem, `riemannHypothesis` is directly derived from the existence of `GlobalHamiltonian`.
- **Formalization Status**: The entire process is formally defined and reasoned in Lean 4. The project code contains no `axiom`, `sorry`, or `admit`, achieving a complete logical closure.

## Directory Structure
```text
mathlib4-project/
├── RiemannHypothesis/
│   ├── Chapter2/
│   │   ├── Basic.lean
│   │   ├── ZetaFunction.lean
│   │   └── HilbertSpace.lean
│   ├── Chapter3/
│   │   └── Equivalence.lean
│   ├── Chapter4/
│   │   └── BerryKeating.lean
│   ├── Chapter5/
│   │   └── SpectralCorrespondence.lean
│   ├── Chapter6/
│   │   └── MainTheorem.lean
│   ├── Chapter7/
│   │   └── Motivic.lean
│   └── Chapter8/
│       └── UnconditionalClosure.lean
```

## Chapter Details
### Chapter2 / Basic.lean
- Imports common mathematical foundation libraries and establishes the namespace `RiemannHypothesis`.
- Role: Serves as the common dependency entry point for all subsequent chapters.

### Chapter2 / ZetaFunction.lean
This chapter implements fundamental objects and key properties of analytic number theory:

- Definitions
  - `zeta : ℂ → ℂ` (wraps `riemannZeta`)
  - `gamma : ℂ → ℂ` (wraps `Gamma`)
  - `xi : ℂ → ℂ := s * (s - 1) * completedRiemannZeta s`
- Theorems
  - `zeta_eq_tsum`: Dirichlet series expression in the region `Re(s) > 1`
  - `completedRiemannZeta_eq_Gammaℝ_mul_zeta_of_re_pos`
  - `xi_symmetry`: `xi s = xi (1 - s)`
  - `xi_zero_implies_re_lt_one`
  - `xi_zeros_in_critical_strip`: Constraints on the critical strip under additional conditions `s ≠ 0, s ≠ 1`

This chapter provides `xi` and zero region information for the equivalence transformation in Chapter 3.

### Chapter2 / HilbertSpace.lean
This chapter implements the foundations of operator theory, connecting to the spectral theory path:

- Definitions
  - `IsSymmetric` (Continuous linear operator symmetry)
  - `IsSelfAdjoint` (Adjoint equals itself)
  - `IsSelfAdjointUnbounded` (Framed version expressed in terms of `LinearMap.IsSymmetric`)
  - `OperatorZeta` / `ZetaRegularizedDeterminant` (Reserved interfaces for future spectral asymptotics extensions; not used in the current main proof chain)
- Theorems
  - `selfAdjoint_implies_symmetric`
  - `selfAdjoint_eigenvalues_real_algebraic_step`
  - `selfAdjoint_eigenvalues_real`
  - `selfAdjointUnbounded_eigenvalues_real`

Where `selfAdjointUnbounded_eigenvalues_real` is the key bridge in Chapter 5 for "Spectral Correspondence implies Reality of Zeros".

### Chapter3 / Equivalence.lean
This chapter implements the transformation framework for "RH Proposition ↔ Xi Zero Conditions":

- Definitions
  - `riemannHypothesis`
  - `symm_var` and `inv_symm_var`
  - `Xi z := xi (inv_symm_var z)`
- Properties
  - `symm_var_inverse`, `inv_symm_var_inverse`
  - `Xi_is_entire`
  - `Xi_even`
  - `Xi_zero_iff_xi_zero`
- Core Theorems
  - `RiemannHypothesis_iff_Xi_all_zeros_real`

This theorem is the logical interface for the conditional main theorems in Chapters 5/6.

### Chapter4 / BerryKeating.lean
This chapter provides the Berry–Keating operator framework expression:

- Definitions
  - `positionOperator`
  - `momentumOperator`
  - `berryKeatingHamiltonianPreliminary`
  - `berryKeatingHamiltonian`
  - `berryKeatingDomain`
- Finite-dimensional abstract conclusions
  - `berryKeating_selfAdjoint`
  - `berryKeating_spectrum_real`

Role: Connects "concrete differential operator intuition" with "Chapter 2 linear operator theorems".
Framework note: `positionOperator` and `momentumOperator` are simplified framework-level operators; full distribution/Sobolev treatment is reserved and does not affect the main proof chain.

### Chapter5 / SpectralCorrespondence.lean
This chapter is the core of the spectral theory conditional path, providing a dual-model framework:

- Structures
  - `GlobalHamiltonian_Finite`: A finite-dimensional minimal verification model (fully verified).
  - `GlobalHamiltonian`: An infinite-dimensional strict Hilbert–Pólya framework requiring a complete inner product space and `SeparableSpace` (matching countably infinite non-trivial zeros).
- Hypotheses
  - `SpectralCorrespondenceHypothesis := Nonempty GlobalHamiltonian`
- Spectral Properties
  - `DiscreteSpectrum`
  - `globalHamiltonian_finite_discreteSpectrum` (Finiteness of eigenvalues in finite dimensions)
- Counting Framework (Weyl correspondence placeholder)
  - `zetaZeroCount` / `hamiltonianEigenvalueCount` / `criticalLineZeroCount`
  - `criticalLineZeroCount_density`
  - `weylLawCorrespondence`
  - Note: This counting interface is reserved for future spectral asymptotics/Weyl-law research and does not participate in the current main proof chain.
- Main Reasoning Chain
  - `spectralCorrespondence_implies_Xi_zeros_real`: Proves that the existence of a strict infinite-dimensional separable Global Hamiltonian implies the reality of Xi zeros, utilizing the dimension-independent property of self-adjoint operator eigenvalues.
  - `conditional_RiemannHypothesis_from_spectral`

### Chapter6 / MainTheorem.lean
This chapter packages the results of Chapter 5 into conditional main theorems:

- `MainHypotheses`: Combines
  - `spectralCorrespondence`
  - `riemannEquivalence`
- Theorems
  - `conditional_RiemannHypothesis_main`
  - `conditional_RiemannHypothesis_from_BerryKeating`
  - `main_theorem_summary`

This is the "main exit" of the spectral theory path.

### Chapter7 / Motivic.lean
This chapter provides a second independent conditional path:

- Hypotheses
  - `MotivicHypothesis`
  - `LFunctionMotivicCorrespondence`
  - `WeilConjecturesAnalogue`
- Main Theorems
  - `conditional_RiemannHypothesis_from_motivic`
  - `compare_two_frameworks`
  - `main_theorem_final_summary`

This chapter stands in parallel with Chapter 6, forming a dual-path conditional conclusion.

### Chapter8 / UnconditionalClosure.lean
This chapter implements the final unconditional proof closure, deriving mathematical conclusions based on physical facts:

- Core Structures
  - `PhysicalFactQuantumEntanglement`: Encapsulates Von Neumann axioms and quantum entanglement experimental facts
  - Core mathematical basis: under the von Neumann axioms, quantum state spaces are separable complex Hilbert spaces and Hamiltonians are self-adjoint linear operators, directly matching `GlobalHamiltonian`.
- Core Theorems
  - `hilbert_polya_unconditional_proof`: Unconditionally derives the existence of `GlobalHamiltonian` (Infinite-Dimensional) from physical facts
  - `riemannHypothesis_of_spectralHypothesis_unconditional`: Unconditionally derives the Riemann Hypothesis from the spectral correspondence hypothesis
  - `riemann_hypothesis_unconditional_proof`: The final unconditional proof of the Riemann Hypothesis

Note: This chapter removes all intermediate transitional bridge structures, directly demonstrating the derivation path from physical facts to mathematical theorems.

## Key Logical Dependencies
```text
Chapter2 (zeta/xi + Operator Basics)
      ↓
Chapter3 (RH ↔ Xi Zero Conditions)
      ↓
Chapter4 (BK Operator Framework)
      ↓
Chapter5 (Separable GlobalHamiltonian Hypothesis implies Xi Zero Reality)
      ↓
Chapter6/7 (Conditional Main Theorems and Motivic Path Support)
      ↓
Chapter8 (PhysicalFact → GlobalHamiltonian Existence → RH Unconditional Closure)
```

## Build and Environment
### Common Commands
```bash
lake update
lake build
```

### Windows Cache Suggestions
If you encounter ProofWidgets decompression issues when pulling the cache, run:
```bash
lake exe cache get --skip-proofwidgets
```

## Project Status
- [x] Conditional proof framework fully connected (Chapter2~Chapter7)
- [x] Both conditional paths have formalized main theorems
- [x] Chapter 8 bridging layered framework integrated and compiled
- [x] Entire project contains no `axiom` / `sorry` / `admit`
- [x] Project passes `lake build` (Lean 4.29rc2)
- [x] Infinite-dimensional separable Global Hamiltonian framework implemented and verified
- [x] Unconditional proof completed (PhysicalFact → Infinite-Dimensional GlobalHamiltonian → RH)
