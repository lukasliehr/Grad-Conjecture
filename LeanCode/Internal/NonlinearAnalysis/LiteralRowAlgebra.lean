import NonlinearQuotientInterface

noncomputable section

open Set

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily

theorem disk_basis_decomposition (point : Plane) :
    point = point 0 • diskBasis 0 + point 1 • diskBasis 1 := by
  ext coordinate
  fin_cases coordinate <;> simp [diskBasis]

theorem disk_quarterTurn_decomposition (point : Plane) :
    planeQuarterTurn point = (-point 1) • diskBasis 0 + point 0 • diskBasis 1 := by
  ext coordinate
  fin_cases coordinate <;> simp [diskBasis, planeQuarterTurn]

theorem disk_norm_sq (point : Plane) : ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem diskEuler_eq_coordinate_partials
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → ℝ → Target) (point : Plane) (time : ℝ) :
    diskEuler field point time =
      point 0 • fderiv ℝ (fun argument => field argument time) point (diskBasis 0) +
      point 1 • fderiv ℝ (fun argument => field argument time) point (diskBasis 1) := by
  unfold diskEuler
  conv_lhs => arg 2; rw [disk_basis_decomposition point]
  simp

theorem diskAngular_eq_coordinate_partials
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → ℝ → Target) (point : Plane) (time : ℝ) :
    diskAngular field point time =
      (-point 1) • fderiv ℝ (fun argument => field argument time) point (diskBasis 0) +
      point 0 • fderiv ℝ (fun argument => field argument time) point (diskBasis 1) := by
  unfold diskAngular
  rw [disk_quarterTurn_decomposition]
  simp

theorem complexDeterminant_eq (first second third : ComplexVec) :
    complexDeterminant first second third =
      first 0 * second 1 * third 2 - first 0 * second 2 * third 1 -
      first 1 * second 0 * third 2 + first 1 * second 2 * third 0 +
      first 2 * second 0 * third 1 - first 2 * second 1 * third 0 := by
  change Matrix.det !![first 0, second 0, third 0;
    first 1, second 1, third 1; first 2, second 2, third 2] = _
  rw [Matrix.det_fin_three]
  change first 0 * second 1 * third 2 - first 0 * third 1 * second 2 -
    second 0 * first 1 * third 2 + second 0 * third 1 * first 2 +
    third 0 * first 1 * second 2 - third 0 * second 1 * first 2 = _
  ring

theorem complexDeterminant_euler_angular (first second third : ComplexVec) (x y : ℝ) :
    complexDeterminant (x • first + y • second) ((-y) • first + x • second) third =
      (x ^ 2 + y ^ 2) • complexDeterminant first second third := by
  simp [complexDeterminant_eq]
  ring

/-- Literal O17: the determinant is multiplied by r² with the original sign. -/
theorem determinant_diskEuler_diskAngular
    (field : Plane → ℝ → ComplexVec) (point : Plane) (time : ℝ) (third : ComplexVec) :
    complexDeterminant (diskEuler field point time) (diskAngular field point time) third =
      (‖point‖ ^ 2) • complexDeterminant
        (fderiv ℝ (fun argument => field argument time) point (diskBasis 0))
        (fderiv ℝ (fun argument => field argument time) point (diskBasis 1)) third := by
  rw [diskEuler_eq_coordinate_partials, diskAngular_eq_coordinate_partials,
    complexDeterminant_euler_angular, disk_norm_sq]

@[simp] theorem diskEuler_zero
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → ℝ → Target) (time : ℝ) : diskEuler field 0 time = 0 := by
  simp [diskEuler]

@[simp] theorem diskAngular_zero
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → ℝ → Target) (time : ℝ) : diskAngular field 0 time = 0 := by
  have zeroTurn : planeQuarterTurn 0 = 0 := by
    ext coordinate
    fin_cases coordinate <;> simp [planeQuarterTurn]
  simp [diskAngular, zeroTurn]

end Grad.NonlinearQuotient
