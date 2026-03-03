import RiemannHypothesis.Chapter2.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace RiemannHypothesis

open scoped Real
open Complex

/-
Chapter 2: Preliminaries and Core Fundamental Theorems
2.1 Analytic Foundations of Riemann Zeta and Xi Functions
-/

/- Definition 2.1.1: Riemann Zeta Function, using definition from Mathlib directly -/
noncomputable def zeta (s : ℂ) : ℂ := riemannZeta s

/- Theorem 2.1.1: When Re(s) > 1, ζ(s) is defined by series -/
theorem zeta_eq_tsum {s : ℂ} (hs : 1 < re s) :
    zeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

/- Definition 2.1.2: Gamma Function, using Gamma from Mathlib -/
noncomputable def gamma (s : ℂ) : ℂ := Gamma s

/- Definition 2.1.4: Riemann Xi Function (Entire Function) -/
/- Defined in the paper as ξ(s) = s(s-1) π^{-s/2} Γ(s/2) ζ(s) -/
/- Based directly on Mathlib's completedRiemannZeta definition -/
noncomputable def xi (s : ℂ) : ℂ :=
  s * (s - 1) * completedRiemannZeta s

theorem completedRiemannZeta_eq_Gammaℝ_mul_zeta_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * zeta s := by
  have h_re_ne : s.re ≠ 0 := ne_of_gt hs
  have hs0 : s ≠ 0 := by
    intro h
    exact h_re_ne (by simp [h])
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have h := riemannZeta_def_of_ne_zero (s := s) hs0
  have h' := congrArg (fun t => t * Gammaℝ s) h
  have h'' : riemannZeta s * Gammaℝ s = completedRiemannZeta s := by
    rw [h, div_mul_cancel₀ _ hGamma]
  rw [← h'', zeta]
  ring

/- Theorem 2.1.2: Core Properties of the Xi Function -/

/- Property 1: Symmetry of Xi Function ξ(s) = ξ(1-s), based on completedRiemannZeta property in Mathlib -/
theorem xi_symmetry (s : ℂ) : xi s = xi (1 - s) := by
  simp only [xi]
  have h1 : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  rw [h1]
  ring_nf

theorem xi_zero_implies_re_lt_one {s : ℂ} (hxi : xi s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s.re < 1 := by
  by_contra h_ge
  have h_ge' : 1 ≤ s.re := le_of_not_gt h_ge
  have h_re_pos : 0 < s.re := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h_ge'
  have h_completed : completedRiemannZeta s = Gammaℝ s * zeta s :=
    completedRiemannZeta_eq_Gammaℝ_mul_zeta_of_re_pos h_re_pos
  have h_zeta_ne : zeta s ≠ 0 := by
    have h : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h_ge'
    simpa [zeta] using h
  have h_gamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h_re_pos
  have h_completed_ne : completedRiemannZeta s ≠ 0 := by
    have h_mul : Gammaℝ s * zeta s ≠ 0 := mul_ne_zero h_gamma h_zeta_ne
    simpa [h_completed] using h_mul
  have h_factor_ne : s * (s - 1) ≠ 0 := by
    intro h
    have h' : s = 0 ∨ s - 1 = 0 := mul_eq_zero.mp h
    cases h' with
    | inl h0 => exact (hs0 h0).elim
    | inr h1 =>
        have : s = 1 := by
          exact sub_eq_zero.mp h1
        exact (hs1 this).elim
  have hxi_ne : xi s ≠ 0 := by
    have h_mul : s * (s - 1) * completedRiemannZeta s ≠ 0 := mul_ne_zero h_factor_ne h_completed_ne
    simpa [xi] using h_mul
  exact hxi_ne hxi

theorem xi_zeros_in_critical_strip {s : ℂ} (hxi : xi s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  have h_re_lt : s.re < 1 := xi_zero_implies_re_lt_one hxi hs0 hs1
  have hxi' : xi (1 - s) = 0 := by
    have hsymm : xi (1 - s) = xi s := by
      simpa using (xi_symmetry s).symm
    exact hsymm.trans hxi
  have hs0' : 1 - s ≠ 0 := by
    intro h
    have : s = 1 := by
      exact (sub_eq_zero.mp h).symm
    exact (hs1 this).elim
  have hs1' : 1 - s ≠ 1 := by
    intro h
    have h' : (1 : ℂ) + (0 : ℂ) = (1 : ℂ) + s := by
      simpa using (sub_eq_iff_eq_add.mp h).symm
    have : s = 0 := by
      exact (add_left_cancel h').symm
    exact (hs0 this).elim
  have h_re_lt_one' : (1 - s).re < 1 :=
    xi_zero_implies_re_lt_one (s := 1 - s) hxi' hs0' hs1'
  have h_re : (1 - s).re = 1 - s.re := by simp
  have h_re_gt : 0 < s.re := by
    linarith [h_re, h_re_lt_one']
  exact ⟨h_re_gt, h_re_lt⟩

end RiemannHypothesis
