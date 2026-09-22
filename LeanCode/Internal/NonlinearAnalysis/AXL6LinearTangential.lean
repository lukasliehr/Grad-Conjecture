import AXL5ScalarGauge

noncomputable section

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.GaugeCoefficients.Radial

theorem angularClosedJet_coordinate_zero {dimension : ℕ} (mode : ℤ)
    (vector : ComplexEuclidean dimension) :
    angularClosedJet mode (coordinateJet 0 (constantValueJet vector)) =
      (1 / 2 : ℂ) • (coordinateMultiplyJet 1
        (if mode - 1 = 0 then constantValueJet vector else 0) +
        coordinateMultiplyJet (-1) (if mode + 1 = 0 then constantValueJet vector else 0)) := by
  rw [coordinateJet_eq_realCoordinateJet, Grad.Cor18.realCoordinateJet_zero_eq,
    angularClosedJet_smul, angularClosedJet_add, angularClosedJet_z, angularClosedJet_zbar,
    angularClosedJet_constant, angularClosedJet_constant]

theorem angularClosedJet_coordinate_one {dimension : ℕ} (mode : ℤ)
    (vector : ComplexEuclidean dimension) :
    angularClosedJet mode (coordinateJet 1 (constantValueJet vector)) =
      (-(Complex.I / 2)) • coordinateMultiplyJet 1
        (if mode - 1 = 0 then constantValueJet vector else 0) +
        (Complex.I / 2) • coordinateMultiplyJet (-1)
          (if mode + 1 = 0 then constantValueJet vector else 0) := by
  rw [coordinateJet_eq_realCoordinateJet, Grad.Cor18.realCoordinateJet_one_eq,
    angularClosedJet_add, angularClosedJet_smul, angularClosedJet_smul,
    angularClosedJet_z, angularClosedJet_zbar, angularClosedJet_constant, angularClosedJet_constant]

/-- A literal homogeneous linear plane field, with no symmetry assumption. -/
def linearColumnJet (first second : ComplexEuclidean 2) : ClosedJet 2 :=
  coordinateJet 0 (constantValueJet first) + coordinateJet 1 (constantValueJet second)

theorem linearColumnJet_value (first second : ComplexEuclidean 2) (point : ClosedDisk) :
    (linearColumnJet first second).value point = point.val 0 • first + point.val 1 • second := by
  rw [linearColumnJet, closedJet_value_add, ContinuousMap.add_apply,
    coordinateJet_value, coordinateJet_value, constantValueJet_value, constantValueJet_value]

theorem linearColumnJet_angular_positive (first second : ComplexEuclidean 2) (point : ClosedDisk) :
    (angularClosedJet 1 (linearColumnJet first second)).value point =
      (signedComplexCoordinate 1 point.val / 2) • first +
        (-(Complex.I * signedComplexCoordinate 1 point.val / 2)) • second := by
  rw [linearColumnJet, angularClosedJet_add, angularClosedJet_coordinate_zero, angularClosedJet_coordinate_one]
  norm_num only [show (1 : ℤ) - 1 = 0 by omega, show (1 : ℤ) + 1 ≠ 0 by omega,
    if_true, if_false, Grad.Cor18.coordinateMultiplyJet_zero_jet, add_zero, smul_zero]
  rw [closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul, closedJet_value_smul,
    ContinuousMap.smul_apply, ContinuousMap.smul_apply, coordinateMultiplyJet_value,
    coordinateMultiplyJet_value, constantValueJet_value, constantValueJet_value, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem linearColumnJet_angular_negative (first second : ComplexEuclidean 2) (point : ClosedDisk) :
    (angularClosedJet (-1) (linearColumnJet first second)).value point =
      (signedComplexCoordinate (-1) point.val / 2) • first +
        (Complex.I * signedComplexCoordinate (-1) point.val / 2) • second := by
  rw [linearColumnJet, angularClosedJet_add, angularClosedJet_coordinate_zero, angularClosedJet_coordinate_one]
  norm_num only [show (-1 : ℤ) - 1 ≠ 0 by omega, show (-1 : ℤ) + 1 = 0 by omega,
    if_true, if_false, Grad.Cor18.coordinateMultiplyJet_zero_jet, zero_add, smul_zero]
  rw [closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul, closedJet_value_smul,
    ContinuousMap.smul_apply, ContinuousMap.smul_apply, coordinateMultiplyJet_value,
    coordinateMultiplyJet_value, constantValueJet_value, constantValueJet_value, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem linearColumnJet_average_axis (first second : ComplexEuclidean 2)
    (radius : ℝ) (bounded : |radius| ≤ 1) :
    (equivariantAverageJet (linearColumnJet first second)).value (axisClosedPoint radius bounded) 1 =
      (radius : ℂ) / 2 * (first 1 - second 0) := by
  rw [equivariantAverageJet_value_helicity, linearColumnJet_angular_positive,
    linearColumnJet_angular_negative, positiveHelicity_apply, negativeHelicity_apply]
  simp [axisClosedPoint, signedComplexCoordinate]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Symmetric homogeneous linear fields have zero tangential gauge.
This is AL17's skew/symmetric cancellation on the entire closed disk. -/
theorem tangentialJet_linearColumn_zero (first second : ComplexEuclidean 2)
    (symmetric : first 1 = second 0) : tangentialJet (linearColumnJet first second) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  obtain ⟨angle, equality⟩ := closedPoint_has_polar_angle point
  rw [← equality, tangentialJet_polar_axis_value, linearColumnJet_average_axis, symmetric,
    sub_self, mul_zero, zero_smul, closedJet_value_zero]
  rfl

end Grad.ChartAxisLift
