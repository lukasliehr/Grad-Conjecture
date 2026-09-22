import ANR37PolarGradientPairing

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace

theorem radialTestLift_firstJets (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (radius angle : ℝ) (positive : 0 < radius) :
    radialField (radialTestLift mode vector test ∘ polarPlane) (radius, angle) =
      deriv test radius • (cellExponential mode angle • vector) ∧
    angularJet 1 (radialTestLift mode vector test ∘ polarPlane) (radius, angle) =
      test radius • (cellExponential mode angle • ((Complex.I * (mode : ℂ)) • vector)) := by
  have locally : radialTestLift mode vector test ∘ polarPlane =ᶠ[𝓝 (radius, angle)] polarTestModel mode vector test := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds positive] with point inside
    exact radialTestLift_model mode vector test point.1 inside point.2
  have first := congrArg (fun linear : (ℝ × ℝ) →L[ℝ] ComplexEuclidean 1 => linear (1, 0)) locally.fderiv_eq
  have second := congrArg (fun tensor : (ℝ × ℝ) [×1]→L[ℝ] ComplexEuclidean 1 => tensor (fun _ => (0, 1)))
    ((locally.iteratedFDeriv (𝕜 := ℝ) 1).eq_of_nhds)
  have radial : radialField (radialTestLift mode vector test ∘ polarPlane) (radius, angle) =
      radialField (polarTestModel mode vector test) (radius, angle) := first
  have angular : angularJet 1 (radialTestLift mode vector test ∘ polarPlane) (radius, angle) =
      angularJet 1 (polarTestModel mode vector test) (radius, angle) := second
  refine ⟨radial.trans ?_, angular.trans ?_⟩
  · rw [polarTestModel_radial mode vector test smooth]
    rfl
  · rw [polarTestModel_angular 1 mode vector test smooth, pow_one]
    rfl

private theorem mode_inner_square (mode : ℤ) (first second : ComplexEuclidean 1) :
    inner ℂ ((Complex.I * (mode : ℂ)) • first) ((Complex.I * (mode : ℂ)) • second) =
      ((mode : ℝ) ^ 2) • inner ℂ first second := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  have scalar : (starRingEnd ℂ) (Complex.I * (mode : ℂ)) * (Complex.I * (mode : ℂ)) =
      (((mode : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp only [map_mul, Complex.conj_I, map_intCast]
    push_cast
    linear_combination -(mode : ℂ) ^ 2 * Complex.I_sq
  rw [scalar]
  exact Complex.coe_smul _ _

theorem character_radial_gradient_integral (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (field : ClosedJet 1) (radius : ℝ) (positive : 0 < radius) :
    (∫ angle in Icc (-Real.pi) Real.pi,
      inner ℂ (radialField (radialTestLift mode vector test ∘ polarPlane) (radius, angle))
        (radialField (originalPolarValue field) (radius, angle))) =
      (2 * Real.pi) • (deriv test radius • inner ℂ vector
        (radialCoefficientJet (originalPolarValue field) mode 1 radius)) := by
  have integrands : (fun angle => inner ℂ (radialField (radialTestLift mode vector test ∘ polarPlane) (radius, angle))
      (radialField (originalPolarValue field) (radius, angle))) =
      (fun angle => deriv test radius • inner ℂ (cellExponential mode angle • vector)
        (radialField (originalPolarValue field) (radius, angle))) := by
    funext angle
    rw [(radialTestLift_firstJets mode vector test smooth radius angle positive).1, inner_smul_left_eq_smul]
  have coefficient := angular_inner_coefficient mode vector
    (fun angle => radialField (originalPolarValue field) (radius, angle))
    ((radialField_smooth _ (originalPolarValue_smooth field)).continuous.comp (continuous_const.prodMk continuous_id))
  rw [integrands, integral_smul, coefficient, smul_comm (deriv test radius) (2 * Real.pi)]
  rfl

theorem character_angular_gradient_integral (mode : ℤ) (vector : ComplexEuclidean 1) (test : ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ test) (field : ClosedJet 1) (radius : ℝ) (positive : 0 < radius) :
    (∫ angle in Icc (-Real.pi) Real.pi,
      inner ℂ (angularJet 1 (radialTestLift mode vector test ∘ polarPlane) (radius, angle))
        (angularJet 1 (originalPolarValue field) (radius, angle))) =
      (2 * Real.pi) • ((test radius * (mode : ℝ) ^ 2) • inner ℂ vector
        (radialCoefficientJet (originalPolarValue field) mode 0 radius)) := by
  have integrands : (fun angle => inner ℂ (angularJet 1 (radialTestLift mode vector test ∘ polarPlane) (radius, angle))
      (angularJet 1 (originalPolarValue field) (radius, angle))) =
      (fun angle => test radius • inner ℂ (cellExponential mode angle • ((Complex.I * (mode : ℂ)) • vector))
        (angularJet 1 (originalPolarValue field) (radius, angle))) := by
    funext angle
    rw [(radialTestLift_firstJets mode vector test smooth radius angle positive).2, inner_smul_left_eq_smul]
  have coefficient := angular_inner_coefficient mode ((Complex.I * (mode : ℂ)) • vector)
    (fun angle => angularJet 1 (originalPolarValue field) (radius, angle))
    ((angularJet_smooth 1 _ (originalPolarValue_smooth field)).continuous.comp (continuous_const.prodMk continuous_id))
  rw [integrands, integral_smul, coefficient,
    angularCoefficient_angularJet 1 _ (originalPolarValue_smooth field) (originalPolarValue_periodic field),
    pow_one, mode_inner_square, smul_comm (test radius) (2 * Real.pi), smul_smul]
  change (2 * Real.pi * test radius) • ((mode : ℝ) ^ 2 •
    inner ℂ vector (angularCoefficient (fun angle => originalPolarValue field (radius, angle)) mode)) =
    (2 * Real.pi) • ((test radius * (mode : ℝ) ^ 2) •
      inner ℂ vector (angularCoefficient (fun angle => originalPolarValue field (radius, angle)) mode))
  simp only [smul_smul, mul_assoc]

end Grad.CircularHighRegularity
