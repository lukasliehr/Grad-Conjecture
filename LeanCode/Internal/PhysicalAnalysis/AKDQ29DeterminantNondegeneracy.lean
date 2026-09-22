import AKDQ28DeterminantDirectionalDerivative

noncomputable section
set_option maxHeartbeats 1200000
open Set

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily

/-- Three vectors whose inner products determine every vector have a
nonzero literal column determinant. -/
theorem tripleDeterminant_ne_zero_of_separating (first second third : Vec)
    (separating : ∀ value : Vec, inner ℝ value first = 0 → inner ℝ value second = 0 →
      inner ℝ value third = 0 → value = 0) : tripleDeterminant first second third ≠ 0 := by
  let matrix : Matrix (Fin 3) (Fin 3) ℝ := fun row column => (![first, second, third] row) column
  have injective : Function.Injective matrix.mulVec := by
    intro one two equal
    let difference : Vec := WithLp.toLp 2 (one - two)
    have pairing (row : Fin 3) : inner ℝ difference (![first, second, third] row) = 0 := by
      have equation := congrFun equal row
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, matrix] at equation
      simp [PiLp.inner_apply, Fin.sum_univ_three, difference]
      nlinarith only [equation]
    have zero := separating difference (pairing 0) (pairing 1) (pairing 2)
    funext coordinate
    have equality := congrArg (fun point : Vec => point coordinate) zero
    change one coordinate - two coordinate = 0 at equality
    exact sub_eq_zero.mp equality
  have unit : IsUnit matrix := Matrix.mulVec_injective_iff_isUnit.mp injective
  have determinantUnit : IsUnit matrix.det := (Matrix.isUnit_iff_isUnit_det matrix).mp unit
  change matrix.transpose.det ≠ 0
  rw [Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mp determinantUnit

end Grad.PhysicalEquilibrium
