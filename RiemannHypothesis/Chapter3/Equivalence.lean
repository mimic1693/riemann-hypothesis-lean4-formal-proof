import RiemannHypothesis.Chapter2.ZetaFunction
namespace RiemannHypothesis

open scoped Real
open Complex

/-
Chapter 3: Equivalent Transformation and Problem Simplification of the Riemann Hypothesis
-/

/- Definition 3.0.1: Statement of the Riemann Hypothesis -/
/- All non-trivial zeros of the Riemann zeta function lie on the critical line Re(s) = 1/2 -/
def riemannHypothesis : Prop :=
  ∀ (s : ℂ), zeta s = 0 → (s.re = 1 / 2 ∨ s.re ≤ 0 ∨ s.re ≥ 1)

/- Definition 3.1.1: Symmetrized Variable Substitution -/
/- Symmetrize the complex variable s, let z = (s - 1/2) / i -/
noncomputable def symm_var (s : ℂ) : ℂ := (s - (1 / 2 : ℂ)) / I

/- Inverse Transformation -/
noncomputable def inv_symm_var (z : ℂ) : ℂ := (1 / 2 : ℂ) + I * z

/- Basic Properties of Symmetrized Variable Substitution -/
@[simp] theorem symm_var_inverse (s : ℂ) : inv_symm_var (symm_var s) = s := by
  simp [symm_var, inv_symm_var]
  ring_nf
  simp [Complex.I_sq]
  try ring

@[simp] theorem inv_symm_var_inverse (z : ℂ) : symm_var (inv_symm_var z) = z := by
  simp [symm_var, inv_symm_var]
  try ring

/- Definition 3.1.2: Target Entire Function Ξ -/
/- Based on variable substitution s = z + 1/2, define Ξ(z) = ξ(z + 1/2) -/
noncomputable def Xi (z : ℂ) : ℂ := xi (inv_symm_var z)

/- Lemma 3.1.1: Core Properties of Ξ -/

theorem Xi_is_entire (z : ℂ) (hz0 : inv_symm_var z ≠ 0) (hz1 : inv_symm_var z ≠ 1) :
    DifferentiableAt ℂ Xi z := by
  unfold Xi
  have h_xi_holomorphic : DifferentiableAt ℂ xi (inv_symm_var z) := by
    apply DifferentiableAt.mul
    · apply DifferentiableAt.mul
      · exact differentiable_id.differentiableAt
      · apply DifferentiableAt.sub
        · exact differentiable_id.differentiableAt
        · exact differentiableAt_const (1 : ℂ)
    · exact differentiableAt_completedZeta hz0 hz1
  have h_translation_holomorphic : DifferentiableAt ℂ (fun w : ℂ => (1/2 : ℂ) + I * w) z := by
    have h_mul : DifferentiableAt ℂ (fun w : ℂ => I * w) z := by
      convert
        (differentiableAt_id.mul_const I :
          DifferentiableAt ℂ (fun w : ℂ => w * I) z) using 1
      ext w
      simp [mul_comm]
    have h_const : DifferentiableAt ℂ (fun _ : ℂ => (1/2 : ℂ)) z := by
      exact differentiableAt_const (1/2 : ℂ)
    exact h_const.add h_mul
  exact h_xi_holomorphic.comp z h_translation_holomorphic

/- Property 2: Ξ is an even function, Ξ(-z) = Ξ(z) -/
theorem Xi_even (z : ℂ) : Xi (-z) = Xi z := by
  simp only [Xi, inv_symm_var]
  have h1 : (1/2 : ℂ) + I * (-z) = 1 - ((1/2 : ℂ) + I * z) := by
    ring
  rw [h1]
  have h2 : xi ((1/2 : ℂ) + I * z) = xi (1 - ((1/2 : ℂ) + I * z)) :=
    xi_symmetry ((1/2 : ℂ) + I * z)
  exact h2.symm

/- Property 3: Relationship between zeros of Ξ and zeros of ξ function -/
theorem Xi_zero_iff_xi_zero (z : ℂ) : Xi z = 0 ↔ xi (inv_symm_var z) = 0 := by
  simp [Xi]

/- Axiom: Zeros of ξ function are all within the critical strip -/




/- Theorem 3.2.1: Equivalent Proposition of the Riemann Hypothesis (Framework) -/
/- The Riemann Hypothesis holds if and only if all zeros of Ξ are real -/
theorem RiemannHypothesis_iff_Xi_all_zeros_real :
    riemannHypothesis ↔
      (∀ (z : ℂ), Xi z = 0 → inv_symm_var z ≠ 0 → inv_symm_var z ≠ 1 → im z = 0) := by
  constructor
  · -- Forward: Assume RH holds, prove all zeros of Ξ are real
    intro h_riemann z h_Xi_zero h_inv_ne_zero h_inv_ne_one
    have h1 : xi (inv_symm_var z) = 0 := (Xi_zero_iff_xi_zero z).mp h_Xi_zero

    -- According to RH, s corresponding to zeros of ξ satisfy Re(s) = 1/2
    -- i.e., inv_symm_var z = z + 1/2 satisfies Re(z + 1/2) = 1/2
    -- Therefore Re(z) = 0, i.e., z is purely imaginary
    have h_riemann_zero : ∀ (s : ℂ), xi s = 0 → (s.re = 1/2 ∨ s.re ≤ 0 ∨ s.re ≥ 1) := by
      intro s h_xi_zero
      by_cases hs0 : s = 0
      · exact Or.inr (Or.inl (by simp [hs0]))
      by_cases hs1 : s = 1
      · exact Or.inr (Or.inr (by simp [hs1]))
      have h_completed : completedRiemannZeta s = 0 := by
        have h' : s * (s - 1) * completedRiemannZeta s = 0 := by
          simpa [xi] using h_xi_zero
        have h'' : s * (s - 1) = 0 ∨ completedRiemannZeta s = 0 := by
          exact mul_eq_zero.mp h'
        cases h'' with
        | inl h_mul =>
            have h_mul' : s = 0 ∨ s - 1 = 0 := mul_eq_zero.mp h_mul
            cases h_mul' with
            | inl h0 => exact (hs0 h0).elim
            | inr h1 =>
                have : s = 1 := by
                  exact sub_eq_zero.mp h1
                exact (hs1 this).elim
        | inr h_comp => exact h_comp
      have h_zeta_zero : zeta s = 0 := by
        have h_def := riemannZeta_def_of_ne_zero (s := s) hs0
        simp [zeta, h_def, h_completed]
      exact h_riemann s h_zeta_zero

    -- Apply RH to s = z + 1/2
    have h_zero_condition := h_riemann_zero (inv_symm_var z) h1

    -- Analyze three cases
    rcases h_zero_condition with (h_re_eq | h_re_le_zero | h_re_ge_one)
    · -- Case 1: Re(s) = 1/2
      -- s = 1/2 + I * z. Re(s) = 1/2 - Im(z).
      -- 1/2 - Im(z) = 1/2 => Im(z) = 0
      rw [inv_symm_var] at h_re_eq
      simp at h_re_eq
      linarith [h_re_eq]
    · -- Case 2: Re(s) ≤ 0
      -- But according to properties of ξ, non-trivial zeros are in critical strip 0 < Re(s) < 1
      -- Thus this case is impossible
      exfalso
      -- Non-trivial zeros of ξ satisfy 0 < Re(s) < 1
      have h_critical_strip : 0 < (inv_symm_var z).re ∧ (inv_symm_var z).re < 1 :=
        xi_zeros_in_critical_strip h1 h_inv_ne_zero h_inv_ne_one
      linarith [h_critical_strip.left, h_re_le_zero]
    · -- Case 3: Re(s) ≥ 1
      -- Also impossible, as non-trivial zeros are in the critical strip
      exfalso
      have h_critical_strip : 0 < (inv_symm_var z).re ∧ (inv_symm_var z).re < 1 :=
        xi_zeros_in_critical_strip h1 h_inv_ne_zero h_inv_ne_one
      linarith [h_critical_strip.right, h_re_ge_one]

  · -- Backward: Assume all zeros of Ξ are real, prove RH holds
    intro h_Xi_zeros_real s h_zeta_zero

    -- Need to prove s.re = 1/2 or s is a trivial zero
    -- Construct z = (s - 1/2) / I
    let z := symm_var s

    -- If s is a trivial zero (Re(s) ≤ 0 or Re(s) ≥ 1), conclusion holds
    by_cases h_trivial : s.re ≤ 0 ∨ s.re ≥ 1
    · -- Trivial zero case
      exact Or.inr h_trivial

    -- Otherwise s is non-trivial zero, in critical strip 0 < Re(s) < 1
    -- By hypothesis, Ξ(z) = 0 implies im(z) = 0
    have h_Xi_zero : Xi z = 0 := by
      have h_inv : inv_symm_var z = s := by
        simp [z]

      -- Xi z = xi (inv_symm_var z) = xi s
      dsimp [Xi]
      rw [h_inv]

      have h_re_pos : 0 < s.re := by
        have h_not_le : ¬ s.re ≤ 0 := (not_or.mp h_trivial).1
        exact lt_of_not_ge h_not_le
      have h_completed : completedRiemannZeta s = Gammaℝ s * zeta s :=
        completedRiemannZeta_eq_Gammaℝ_mul_zeta_of_re_pos h_re_pos
      rw [xi, h_completed]
      simp [h_zeta_zero]

    have hs0 : s ≠ 0 := by
      intro h
      have : zeta 0 = 0 := by simpa [h] using h_zeta_zero
      simp [zeta, riemannZeta_zero] at this
    have hs1 : s ≠ 1 := by
      intro h
      have : zeta 1 = 0 := by simpa [h] using h_zeta_zero
      have h_ne : zeta 1 ≠ 0 := by
        simpa [zeta] using (riemannZeta_one_ne_zero)
      exact (h_ne this).elim
    have h_im_zero : im z = 0 :=
      h_Xi_zeros_real z h_Xi_zero (by simpa [z] using hs0) (by simpa [z] using hs1)

    -- Since im(z) = 0, z is real.
    -- s = 1/2 + I * z.
    -- Re(s) = 1/2 - Im(z) = 1/2 - 0 = 1/2.
    -- Riemann Hypothesis holds.
    apply Or.inl

    have h_s_eq : s = (1/2 : ℂ) + I * z := by
      have h_inv : inv_symm_var z = s := by
        simp [z]
      simpa [inv_symm_var, one_div] using h_inv.symm
    rw [h_s_eq]
    simp
    linarith [h_im_zero]
