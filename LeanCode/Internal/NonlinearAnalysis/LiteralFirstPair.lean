import LiteralRowAlgebra

noncomputable section

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily

@[simp] theorem complexDot_add_left (first second third : ComplexVec) :
    complexDot (first + second) third = complexDot first third + complexDot second third := by
  simp [complexDot, add_mul, Finset.sum_add_distrib]

@[simp] theorem complexDot_sub_left (first second third : ComplexVec) :
    complexDot (first - second) third = complexDot first third - complexDot second third := by
  simp [complexDot, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem complexDot_neg_left (first second : ComplexVec) :
    complexDot (-first) second = -complexDot first second := by
  simp [complexDot, Finset.sum_neg_distrib]

@[simp] theorem complexDot_smul_left (scalar : ℂ) (first second : ComplexVec) :
    complexDot (scalar • first) second = scalar * complexDot first second := by
  simp [complexDot, Finset.mul_sum, mul_assoc]

@[simp] theorem complexDot_real_smul_left (scalar : ℝ) (first second : ComplexVec) :
    complexDot (scalar • first) second = (scalar : ℂ) * complexDot first second := by
  simp [complexDot, Finset.mul_sum, mul_assoc]

theorem complexDiskCoordinate_eq (point : Plane) :
    complexDiskCoordinate point = (point 0 : ℂ) + Complex.I * (point 1 : ℂ) := by
  apply Complex.ext <;> simp [complexDiskCoordinate]

theorem plus_coordinate_algebra (x y : ℝ) (a b correction : ℂ)
    (first second angular : ComplexVec) :
    let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
    star z * (a + Complex.I * b - complexDot (first + Complex.I • second) angular +
      Complex.I * z + z * correction) =
      ((x : ℂ) * a + (y : ℂ) * b - complexDot (x • first + y • second) angular +
        ((x ^ 2 + y ^ 2 : ℝ) : ℂ) * correction) +
      Complex.I * (-(y : ℂ) * a + (x : ℂ) * b -
        complexDot ((-y) • first + x • second) angular + ((x ^ 2 + y ^ 2 : ℝ) : ℂ)) := by
  simp
  apply Complex.ext <;> simp [pow_two] <;> ring

theorem minus_coordinate_algebra (x y : ℝ) (a b correction : ℂ)
    (first second angular : ComplexVec) :
    let z : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
    z * (a - Complex.I * b - complexDot (first - Complex.I • second) angular -
      Complex.I * star z + star z * correction) =
      ((x : ℂ) * a + (y : ℂ) * b - complexDot (x • first + y • second) angular +
        ((x ^ 2 + y ^ 2 : ℝ) : ℂ) * correction) -
      Complex.I * (-(y : ℂ) * a + (x : ℂ) * b -
        complexDot ((-y) • first + x • second) angular + ((x ^ 2 + y ^ 2 : ℝ) : ℂ)) := by
  simp
  apply Complex.ext <;> simp [pow_two] <;> ring

theorem literal_plus_pointwise (mapping : Plane → ℝ → ComplexVec)
    (potential : Plane → ℝ → ℂ) (point : Plane) (time : ℝ) (correction : ℂ) :
    star (complexDiskCoordinate point) *
      (partialPlus (fun argument => potential argument time) point -
        complexDot (partialPlus (fun argument => mapping argument time) point)
          (diskAngular mapping point time) +
        Complex.I * complexDiskCoordinate point + complexDiskCoordinate point * correction) =
      (diskEuler potential point time -
        complexDot (diskEuler mapping point time) (diskAngular mapping point time) +
        (‖point‖ ^ 2 : ℝ) • correction) +
      Complex.I * (diskAngular potential point time -
        complexDot (diskAngular mapping point time) (diskAngular mapping point time) +
        (‖point‖ ^ 2 : ℝ)) := by
  have identity := plus_coordinate_algebra (point 0) (point 1)
    (fderiv ℝ (fun argument => potential argument time) point (diskBasis 0))
    (fderiv ℝ (fun argument => potential argument time) point (diskBasis 1)) correction
    (fderiv ℝ (fun argument => mapping argument time) point (diskBasis 0))
    (fderiv ℝ (fun argument => mapping argument time) point (diskBasis 1))
    (diskAngular mapping point time)
  simpa only [partialPlus, complexDiskCoordinate_eq, diskEuler_eq_coordinate_partials,
    diskAngular_eq_coordinate_partials, disk_norm_sq, Complex.real_smul,
    Complex.ofReal_neg, smul_eq_mul] using identity

theorem literal_minus_pointwise (mapping : Plane → ℝ → ComplexVec)
    (potential : Plane → ℝ → ℂ) (point : Plane) (time : ℝ) (correction : ℂ) :
    complexDiskCoordinate point *
      (partialMinus (fun argument => potential argument time) point -
        complexDot (partialMinus (fun argument => mapping argument time) point)
          (diskAngular mapping point time) -
        Complex.I * star (complexDiskCoordinate point) + star (complexDiskCoordinate point) * correction) =
      (diskEuler potential point time -
        complexDot (diskEuler mapping point time) (diskAngular mapping point time) +
        (‖point‖ ^ 2 : ℝ) • correction) -
      Complex.I * (diskAngular potential point time -
        complexDot (diskAngular mapping point time) (diskAngular mapping point time) +
        (‖point‖ ^ 2 : ℝ)) := by
  have identity := minus_coordinate_algebra (point 0) (point 1)
    (fderiv ℝ (fun argument => potential argument time) point (diskBasis 0))
    (fderiv ℝ (fun argument => potential argument time) point (diskBasis 1)) correction
    (fderiv ℝ (fun argument => mapping argument time) point (diskBasis 0))
    (fderiv ℝ (fun argument => mapping argument time) point (diskBasis 1))
    (diskAngular mapping point time)
  simpa only [partialMinus, complexDiskCoordinate_eq, diskEuler_eq_coordinate_partials,
    diskAngular_eq_coordinate_partials, disk_norm_sq, Complex.real_smul,
    Complex.ofReal_neg, smul_eq_mul] using identity

end Grad.NonlinearQuotient
