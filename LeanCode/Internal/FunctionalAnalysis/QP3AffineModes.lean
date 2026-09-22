import QP2ModeAlgebra

noncomputable section

namespace Grad.QuotientProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.GaugeCoefficients.Radial Grad.AxisCore Grad.PhysicalFamily
open Grad.NonlinearQuotientBounds

/-- The mean is independent of angle even when the inserted cutoff is not radial. -/
theorem mean_value_polar {dimension : ℕ} (field : ClosedJet dimension)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    (angularClosedJet 0 field).value (polarClosedPoint radius bounded angle) =
      (angularClosedJet 0 field).value (axisClosedPoint radius bounded) := by
  change angularProjectionValue 0 (smoothClosedExtension field)
    (planeRotationEquiv angle (axisClosedPoint radius bounded).val) = _
  rw [← physicalRotation_eq_orthogonal, angularProjectionValue_rotation,
    angularCharacter_zero_mode, one_smul]
  rfl

theorem reflection_mean_jet {dimension : ℕ} (field : ClosedJet dimension) :
    orthogonalJet cartesianReflectionEquiv (angularClosedJet 0 field) =
      angularClosedJet 0 field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (angularClosedJet 0 field).value
    (orthogonalClosedPoint cartesianReflectionEquiv point) = _
  obtain ⟨angle, polar⟩ := closedPoint_has_polar_angle point
  rw [← polar, reflectedPoint_polar, mean_value_polar, mean_value_polar]

theorem reflection_coordinate_zbar {dimension : ℕ} (field : ClosedJet dimension) :
    orthogonalJet cartesianReflectionEquiv (coordinateMultiplyJet (-1) field) =
      coordinateMultiplyJet 1 (orthogonalJet cartesianReflectionEquiv field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (coordinateMultiplyJet (-1) field).value
    (orthogonalClosedPoint cartesianReflectionEquiv point) = _
  rw [coordinateMultiplyJet_value, coordinateMultiplyJet_value]
  congr 1
  simp [signedComplexCoordinate, orthogonalClosedPoint,
    cartesianReflectionEquiv, cartesianReflection]

/-- The actual scaled coordinate profiles give the literal z/bar(z) insertion. -/
theorem coordinate_profile {dimension : ℕ} (cell : ℤ)
    (value : ComplexEuclidean dimension) (sign : ℝ) :
    profileJetOne 0 cell value + (Complex.I * (sign : ℂ)) • profileJetOne 1 cell value =
      coordinateMultiplyJet sign (profileJetZero cell value) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [closedJet_value_add, closedJet_value_smul, coordinateMultiplyJet_value]
  apply PiLp.ext
  intro component
  change ((profileScalarOne 0 cell point.val : ℝ) : ℂ) * value component +
    (Complex.I * (sign : ℂ)) *
      (((profileScalarOne 1 cell point.val : ℝ) : ℂ) * value component) =
    signedComplexCoordinate sign point.val *
      (((profileScalarZero cell point.val : ℝ) : ℂ) * value component)
  simp only [profileScalarOne, profileScalarZero, coordinateLinear,
    signedComplexCoordinate]
  change (((point.val 0 * jetBump (cellFrequency cell • point.val) : ℝ) : ℂ) * value component +
    (Complex.I * (sign : ℂ)) *
      (((point.val 1 * jetBump (cellFrequency cell • point.val) : ℝ) : ℂ) * value component)) =
    ((point.val 0 : ℂ) + Complex.I * (sign : ℂ) * (point.val 1 : ℂ)) *
      ((jetBump (cellFrequency cell • point.val) : ℂ) * value component)
  push_cast
  ring

/-- N37's cancellation, established from the exact angular/reflection formulas. -/
theorem firstMode_affineInsertion (parameters : PhaseParameters)
    (family : AxisSmoothCore parameters 1) :
    firstMode parameters (affineInsertion parameters family) = 0 := by
  apply Subtype.ext
  funext cell
  change (1 / 2 : ℂ) •
    (angularClosedJet 1
      (Complex.I • (profileJetOne 0 cell (family.val cell) +
        Complex.I • profileJetOne 1 cell (family.val cell))) +
      orthogonalJet cartesianReflectionEquiv (angularClosedJet (-1)
        ((-Complex.I) • (profileJetOne 0 cell (family.val cell) -
          Complex.I • profileJetOne 1 cell (family.val cell))))) = 0
  have plus := coordinate_profile cell (family.val cell) 1
  have minus := coordinate_profile cell (family.val cell) (-1)
  simp only [Complex.ofReal_one, mul_one] at plus
  simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one,
    neg_smul, ← sub_eq_add_neg] at minus
  rw [plus, minus, angularClosedJet_smul, angularClosedJet_smul,
    angularClosedJet_z, angularClosedJet_zbar]
  norm_num only [Int.sub_self, neg_add_cancel]
  change (1 / 2 : ℂ) •
    (Complex.I • coordinateMultiplyJet 1 (angularClosedJet 0 (profileJetZero cell (family.val cell))) +
      (orthogonalJetLinear 1 cartesianReflectionEquiv)
        ((-Complex.I) • coordinateMultiplyJet (-1)
          (angularClosedJet 0 (profileJetZero cell (family.val cell))))) = 0
  rw [map_smul]
  change (1 / 2 : ℂ) •
    (Complex.I • coordinateMultiplyJet 1 (angularClosedJet 0 (profileJetZero cell (family.val cell))) +
      (-Complex.I) • orthogonalJet cartesianReflectionEquiv
        (coordinateMultiplyJet (-1) (angularClosedJet 0 (profileJetZero cell (family.val cell))))) = 0
  rw [reflection_coordinate_zbar, reflection_mean_jet, neg_smul, add_neg_cancel, smul_zero]

theorem modeProjection_affineInsertion (parameters : PhaseParameters)
    (family : AxisSmoothCore parameters 1) :
    modeProjection parameters (affineInsertion parameters family) = 0 := by
  rw [modeProjection_apply, firstMode_affineInsertion, map_zero]
  funext coordinate
  fin_cases coordinate <;> rfl

end Grad.QuotientProjection
