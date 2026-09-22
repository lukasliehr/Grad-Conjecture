import ANR41CoreGradientIntegral

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem collarProfile_zero (lower : ℝ) (test : ℝ → ℝ) (supported : tsupport test ⊆ Ioi lower)
    (radius : ℝ) (before : radius ≤ lower) : test radius = 0 ∧ deriv test radius = 0 := by
  have away : radius ∉ tsupport test := fun member => (not_lt_of_ge before) (supported member)
  exact ⟨image_eq_zero_of_notMem_tsupport away,
    image_eq_zero_of_notMem_tsupport (fun member => away (tsupport_deriv_subset member))⟩

theorem boundaryCharacter_gradient_collar_core (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (supported : tsupport test ⊆ Ioi lower) (field : ClosedJet 1) :
    inner ℂ (diskGradX (diskCoreInto (boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported))))
        (diskGradX (diskCoreInto field)) +
      inner ℂ (diskGradY (diskCoreInto (boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported))))
        (diskGradY (diskCoreInto field)) =
    (2 * Real.pi) • ∫ radius in lower..1,
      (radius * deriv test radius) • inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 1 radius) +
      (test radius * radialPotentialCurve lower positive mode radius) •
        inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 0 radius) := by
  let integrand : ℝ → ℂ := fun radius =>
    (radius * deriv test radius) • inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 1 radius) +
    (test radius * radialPotentialCurve lower positive mode radius) •
      inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 0 radius)
  have coefficients (radius : ℝ) : test radius * (mode : ℝ) ^ 2 / radius =
      test radius * radialPotentialCurve lower positive mode radius := by
    by_cases inside : lower ≤ radius
    · rw [radialPotentialCurve_literal lower positive mode radius inside]
      ring
    · rw [(collarProfile_zero lower test supported radius (le_of_not_ge inside)).1]
      simp
  have integralReplacement :
      (∫ radius in Icc (0 : ℝ) 1,
        (radius * deriv test radius) • inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 1 radius) +
        (test radius * (mode : ℝ) ^ 2 / radius) • inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 0 radius)) =
      ∫ radius in Icc (0 : ℝ) 1, integrand radius := by
    apply integral_congr_ae
    filter_upwards [] with radius
    exact congrArg (fun scalar : ℝ => (radius * deriv test radius) •
      inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 1 radius) +
      scalar • inner ℂ vector (radialCoefficientJet (originalPolarValue field) mode 0 radius)) (coefficients radius)
  have restriction : (∫ radius in Icc (0 : ℝ) 1, integrand radius) =
      ∫ radius in Icc lower 1, integrand radius := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      (Icc_subset_Icc positive.le le_rfl)
    intro radius outside
    have before : radius ≤ lower := le_of_not_gt (fun greater => outside.2 ⟨greater.le, outside.1.2⟩)
    obtain ⟨valueZero, derivativeZero⟩ := collarProfile_zero lower test supported radius before
    simp only [integrand, valueZero, derivativeZero, mul_zero, zero_mul, zero_smul, add_zero]
  have interval : (∫ radius in Icc lower 1, integrand radius) = ∫ radius in lower..1, integrand radius := by
    rw [intervalIntegral.integral_of_le bounded, integral_Icc_eq_integral_Ioc]
  exact (boundaryCharacter_gradient_polar mode vector test smooth (collarSupport_away lower positive test supported) field).trans
    (congrArg (fun value : ℂ => (2 * Real.pi) • value) (integralReplacement.trans (restriction.trans interval)))

end Grad.CircularHighRegularity
