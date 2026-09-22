import ANT4HomogeneousElimination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianScalarElimination
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.NonlinearRange Grad.NonlinearDivision
open Grad.ActualAngularInverse Grad.CircularHighWeak Grad.CircularHighRegularity

/-- The accepted angular inverse composed with the actual R removes exactly
its constant mode. -/
theorem angularInverse_rotation (field : ClosedJet 1) :
    shiftInverseJet 0 (rotationJet field) = field - angularClosedJet 0 field := by
  have law : shiftInverseJet 0 (rotationJet field) = excludedAngularJet {0} field := by
    simpa only [shiftedRotationJet, Int.cast_zero, mul_zero, zero_smul, add_zero, neg_zero]
      using shiftInverse_left 0 field
  have projection : excludedAngularJet {0} field = field - angularClosedJet 0 field := by
    simpa only [neg_zero] using excluded_single_eq 0 field
  exact law.trans projection

theorem angularInverseSquare_rotationSquare (field : ClosedJet 1) :
    shiftInverseJet 0 (shiftInverseJet 0 (rotationJet (rotationJet field))) =
      field - angularClosedJet 0 field := by
  have first := angularInverse_rotation (rotationJet field)
  rw [angularClosedJet_rotation_zero, sub_zero] at first
  rw [first, angularInverse_rotation]

theorem rotationalPolynomial_mean_zero (field source : ClosedJet 1)
    (equation : rotationJet (rotationJet field) + (4 : ℂ) • field = rotationJet (rotationJet source)) :
    angularClosedJet 0 field = 0 := by
  have mean := congrArg (angularClosedJet 0) equation
  rw [angularClosedJet_add, angularClosedJet_smul, angularClosedJet_rotation_zero,
    angularClosedJet_rotation_zero, zero_add] at mean
  exact (smul_eq_zero.mp mean).resolve_left (by norm_num)

/-- Actual application of R^{-2}, with its constant mode accounted for.
The displayed multiplier is literally the defining formula of ANB fullBJet. -/
theorem rotationalPolynomial_resolved (field source : ClosedJet 1)
    (sourceMean : angularClosedJet 0 source = 0)
    (equation : rotationJet (rotationJet field) + (4 : ℂ) • field = rotationJet (rotationJet source)) :
    field + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 field) = source := by
  let inverseSquare := (shiftInverseLinear 1 0).comp (shiftInverseLinear 1 0)
  have transformed := congrArg inverseSquare equation
  rw [map_add, map_smul] at transformed
  change shiftInverseJet 0 (shiftInverseJet 0 (rotationJet (rotationJet field))) +
    (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 field) =
      shiftInverseJet 0 (shiftInverseJet 0 (rotationJet (rotationJet source))) at transformed
  rw [angularInverseSquare_rotationSquare, angularInverseSquare_rotationSquare,
    rotationalPolynomial_mean_zero field source equation, sourceMean, sub_zero, sub_zero] at transformed
  exact transformed

theorem homogeneous_div_angularInverse (theta : ClosedJet 1) (vector : ClosedJet 2)
    (mean : angularClosedJet 0 theta = 0)
    (equation : rotationJet vector + valueMapJet quarterValueMap vector =
      Grad.GaugeCoefficients.Physical.Compensated.gradientJet (rotationJet theta)) :
    vectorDivJet vector + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 (vectorDivJet vector)) = laplacianJet theta := by
  apply rotationalPolynomial_resolved _ _ _ (homogeneous_div_polynomial theta vector equation)
  rw [← laplacianJet_angular, mean]
  exact map_zero laplacianJetLinear

theorem homogeneous_radial_angularInverse (theta : ClosedJet 1) (vector : ClosedJet 2)
    (mean : angularClosedJet 0 theta = 0)
    (equation : rotationJet vector + valueMapJet quarterValueMap vector =
      Grad.GaugeCoefficients.Physical.Compensated.gradientJet (rotationJet theta)) :
    vectorRadialJet vector + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 (vectorRadialJet vector)) =
      eulerJet theta + (2 : ℂ) • theta := by
  apply rotationalPolynomial_resolved _ _ _ (homogeneous_radial_polynomial theta vector equation)
  rw [angularClosedJet_add, angularClosedJet_smul, angularClosedJet_euler, mean, smul_zero, add_zero]
  change (coordinateJetLinear 0) (partialJetLinear 1 0 0) +
    (coordinateJetLinear 1) (partialJetLinear 1 1 0) = 0
  simp only [map_zero, add_zero]

end Grad.CartesianScalarElimination
