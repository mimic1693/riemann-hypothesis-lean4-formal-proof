import RiemannHypothesis.Chapter5.SpectralCorrespondence

namespace RiemannHypothesis

open scoped Real
open Complex

/-
Chapter 6: Conditional Main Theorem of the Riemann Hypothesis
-/

/- Definition 6.1.1: Main Set of Conditions -/
/- We combine all necessary hypotheses into a single condition -/
structure MainHypotheses : Prop where
  spectralCorrespondence : SpectralCorrespondenceHypothesis
  riemannEquivalence : riemannHypothesis ↔ (∀ (z : ℂ), Xi z = 0 → im z = 0)

/- Theorem 6.2.1: Conditional Main Theorem of the Riemann Hypothesis (First Form) -/
/- Under the condition that the spectral correspondence hypothesis and the equivalent proposition hold, the Riemann Hypothesis holds -/
theorem conditional_RiemannHypothesis_main (h : MainHypotheses) :
  riemannHypothesis := by
  have h1 : SpectralCorrespondenceHypothesis := h.spectralCorrespondence
  have h2 : riemannHypothesis ↔ (∀ (z : ℂ), Xi z = 0 → im z = 0) := h.riemannEquivalence
  exact conditional_RiemannHypothesis_from_spectral h1 h2

/- Definition 6.3.1: Berry-Keating Condition -/
/- Assume the Berry-Keating Hamiltonian is self-adjoint and its spectrum corresponds to the zeros of the Ξ function -/
def BerryKeatingCondition : Prop :=
  True ∧ SpectralCorrespondenceHypothesis

/- Theorem 6.3.1: Conditional Main Theorem of the Riemann Hypothesis (Second Form) -/
/- Under the Berry-Keating condition, the Riemann Hypothesis holds -/
theorem conditional_RiemannHypothesis_from_BerryKeating
  (h_bk : BerryKeatingCondition)
  (h_equiv : riemannHypothesis ↔ (∀ (z : ℂ), Xi z = 0 → im z = 0)) :
  riemannHypothesis := by
  have h_sc : SpectralCorrespondenceHypothesis := h_bk.right
  exact conditional_RiemannHypothesis_from_spectral h_sc h_equiv

/- Corollary 6.4.1: Summary of the Main Theorem (Framework) -/
/- Summarize our conditional proof framework -/
theorem main_theorem_summary :
  (BerryKeatingCondition ∧ (riemannHypothesis ↔ (∀ (z : ℂ), Xi z = 0 → im z = 0))) →
  riemannHypothesis := by
  intro h
  have h_bk : BerryKeatingCondition := h.1
  have h_equiv : riemannHypothesis ↔ (∀ (z : ℂ), Xi z = 0 → im z = 0) := h.2
  exact conditional_RiemannHypothesis_from_BerryKeating h_bk h_equiv

end RiemannHypothesis
