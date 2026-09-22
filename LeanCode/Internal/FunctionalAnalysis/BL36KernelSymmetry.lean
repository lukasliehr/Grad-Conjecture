import BL35AngularSeries

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
open Grad.GaugeCoefficients.Radial

theorem boundaryFrequency_neg_fst (angular cell : ℤ) :
    boundaryFrequency (-angular, cell) = boundaryFrequency (angular, cell) := by
  simp only [boundaryFrequency]
  push_cast
  ring_nf

theorem boundaryFrequency_neg_snd (angular cell : ℤ) :
    boundaryFrequency (angular, -cell) = boundaryFrequency (angular, cell) := by
  simp only [boundaryFrequency]
  push_cast
  ring_nf

theorem boundaryKernel_neg_snd (angular cell : ℤ) (point : SpatialPlane) :
    boundaryKernel (angular, -cell) point = boundaryKernel (angular, cell) point := by
  simp only [boundaryKernel]
  rw [boundaryFrequency_neg_snd]

theorem unitComplexCoordinate_zero : unitComplexCoordinate 0 = 0 := by
  unfold unitComplexCoordinate
  have coordinateZero : signedComplexCoordinate 1 (0 : SpatialPlane) = 0 := by
    simp [signedComplexCoordinate]
  rw [coordinateZero, zero_div]

theorem unitComplexCoordinate_conj (point : SpatialPlane) :
    conj (unitComplexCoordinate point) = (unitComplexCoordinate point)⁻¹ := by
  by_cases zero : point = 0
  · subst zero
    rw [unitComplexCoordinate_zero, map_zero, inv_zero]
  · have norm1 : ‖unitComplexCoordinate point‖ = 1 := unitComplexCoordinate_norm point zero
    have square : unitComplexCoordinate point * conj (unitComplexCoordinate point) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm1]
      norm_num
    rw [mul_comm] at square
    exact eq_inv_of_mul_eq_one_left square

theorem unitComplexCoordinate_conj_zpow (point : SpatialPlane) (mode : ℤ) :
    conj (unitComplexCoordinate point ^ mode) = unitComplexCoordinate point ^ (-mode) := by
  rw [map_zpow₀, unitComplexCoordinate_conj, inv_zpow, ← zpow_neg]

theorem boundaryKernel_conj (angular cell : ℤ) (point : SpatialPlane) :
    conj (boundaryKernel (angular, cell) point) = boundaryKernel (-angular, cell) point := by
  simp only [boundaryKernel]
  rw [map_mul, Complex.conj_ofReal, unitComplexCoordinate_conj_zpow, boundaryFrequency_neg_fst]

theorem cellExponential_one_zpow (mode : ℤ) (angle : ℝ) :
    cellExponential 1 angle ^ mode = cellExponential mode angle := by
  unfold cellExponential
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem angularCharacter_neg_one_zpow (mode : ℤ) (angle : ℝ) :
    angularCharacter (-1) angle ^ mode = cellExponential mode angle := by
  have baseEquality : angularCharacter (-1) angle = cellExponential 1 angle := by
    unfold angularCharacter
    rw [neg_neg]
  rw [baseEquality, cellExponential_one_zpow]

theorem unitComplexCoordinate_rotated (angle : ℝ) (point : ClosedDisk) :
    unitComplexCoordinate (rotatedPoint angle point).val =
      angularCharacter (-1) angle * unitComplexCoordinate point.val := by
  unfold unitComplexCoordinate
  have normEquality : ‖(rotatedPoint angle point).val‖ = ‖point.val‖ :=
    planeRotation_norm angle point.val
  rw [complexCoordinate_rotated, normEquality, mul_div_assoc]

theorem boundaryKernel_rotated (angular cell : ℤ) (angle : ℝ) (point : ClosedDisk) :
    boundaryKernel (angular, cell) (rotatedPoint angle point).val =
      cellExponential angular angle * boundaryKernel (angular, cell) point.val := by
  simp only [boundaryKernel]
  have normEquality : ‖(rotatedPoint angle point).val‖ = ‖point.val‖ :=
    planeRotation_norm angle point.val
  rw [normEquality, unitComplexCoordinate_rotated, mul_zpow, angularCharacter_neg_one_zpow]
  ring

theorem boundaryFourier_norm (mode : ℤ) (angle : CellCircle) : ‖fourier mode angle‖ = 1 :=
  cellCharacter_apply_norm mode angle

end Grad.BoundaryLift
