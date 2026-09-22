import AXL9StoredPoloidal

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds

theorem angular_coordinateJet_zero {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (coordinateJet 0 field) =
      (1 / 2 : ℂ) • (coordinateMultiplyJet 1 (angularClosedJet (mode - 1) field) +
        coordinateMultiplyJet (-1) (angularClosedJet (mode + 1) field)) := by
  rw [coordinateJet_eq_realCoordinateJet, Grad.Cor18.realCoordinateJet_zero_eq,
    angularClosedJet_smul, angularClosedJet_add, angularClosedJet_z, angularClosedJet_zbar]

theorem angular_coordinateJet_one {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (coordinateJet 1 field) =
      (-(Complex.I / 2)) • coordinateMultiplyJet 1 (angularClosedJet (mode - 1) field) +
        (Complex.I / 2) • coordinateMultiplyJet (-1) (angularClosedJet (mode + 1) field) := by
  rw [coordinateJet_eq_realCoordinateJet, Grad.Cor18.realCoordinateJet_one_eq,
    angularClosedJet_add, angularClosedJet_smul, angularClosedJet_smul,
    angularClosedJet_z, angularClosedJet_zbar]

/-- The literal second angular moment: xy has zero average, while x² and
y² each average to half the original squared radius. -/
theorem angular_quadraticCoordinate_value {dimension : ℕ} (first second : Fin 2)
    (vector : ComplexEuclidean dimension) (point : ClosedDisk) :
    (angularClosedJet 0 (coordinateJet first (coordinateJet second (constantValueJet vector)))).value point =
      (if first = second then ((point.val 0 : ℂ)^2 + (point.val 1 : ℂ)^2) / 2 else 0) • vector := by
  have fourth : Complex.I ^ 4 = 1 := by
    calc Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  fin_cases first <;> fin_cases second
  all_goals first
    | (change (angularClosedJet 0 (coordinateJet 0 (coordinateJet 0 (constantValueJet vector)))).value point = _
       rw [angular_coordinateJet_zero, angularClosedJet_coordinate_zero, angularClosedJet_coordinate_zero])
    | (change (angularClosedJet 0 (coordinateJet 0 (coordinateJet 1 (constantValueJet vector)))).value point = _
       rw [angular_coordinateJet_zero, angularClosedJet_coordinate_one, angularClosedJet_coordinate_one])
    | (change (angularClosedJet 0 (coordinateJet 1 (coordinateJet 0 (constantValueJet vector)))).value point = _
       rw [angular_coordinateJet_one, angularClosedJet_coordinate_zero, angularClosedJet_coordinate_zero])
    | (change (angularClosedJet 0 (coordinateJet 1 (coordinateJet 1 (constantValueJet vector)))).value point = _
       rw [angular_coordinateJet_one, angularClosedJet_coordinate_one, angularClosedJet_coordinate_one])
  all_goals
    apply PiLp.ext
    intro coordinate
    norm_num [coordinateMultiplyJet_value, constantValueJet_value, signedComplexCoordinate,
      Grad.Cor18.coordinateMultiplyJet_zero_jet, closedJet_value_add, closedJet_value_smul]
    ring_nf <;> simp only [Complex.I_sq, fourth] <;> ring

/-- The original scalar quadratic form associated to a planar matrix. -/
def quadraticMatrixJet (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) : ClosedJet 1 :=
  ∑ first : Fin 2, ∑ second : Fin 2,
    Gauges.operatorEntry mapping first second •
      coordinateJet first (coordinateJet second (constantValueJet (EuclideanSpace.single 0 1)))

theorem quadraticMatrixJet_value (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (point : ClosedDisk) :
    (quadraticMatrixJet mapping).value point 0 =
      (point.val 0 : ℂ) * mapping (complexDiskPoint point) 0 +
        (point.val 1 : ℂ) * mapping (complexDiskPoint point) 1 := by
  simp only [quadraticMatrixJet, Fin.sum_univ_two, closedJet_value_add, closedJet_value_smul,
    ContinuousMap.add_apply, ContinuousMap.smul_apply, coordinateJet_value, constantValueJet_value,
    Gauges.operator_apply_coordinates]
  simp [complexDiskPoint]
  ring

theorem angular_quadraticMatrix_zero (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (trace : Gauges.operatorTrace mapping = 0) : angularClosedJet 0 (quadraticMatrixJet mapping) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [quadraticMatrixJet, Fin.sum_univ_two, angularClosedJet_add, angularClosedJet_smul,
    closedJet_value_add, closedJet_value_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    angular_quadraticCoordinate_value]
  norm_num [show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    closedJet_value_zero]
  rw [← add_smul, ← Gauges.operatorTrace, trace, zero_smul]

end Grad.ChartAxisLift
