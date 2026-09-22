import AIT3HilbertOffDiagonalNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.Foundations

section CompleteFixedPoint
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Internal complete-space identity for the norm-convergent Neumann series. -/
theorem neumann_fixedPoint (operator : X →L[ℂ] X) (small : ‖operator‖ < 1) (known : X) :
    neumannInverse operator known = known + operator (neumannInverse operator known) := by
  have equation := congrArg (fun mapping : X →L[ℂ] X => mapping known)
    (neumannInverse_right operator small)
  change neumannInverse operator known - operator (neumannInverse operator known) = known at equation
  exact sub_eq_iff_eq_add.mp equation

theorem neumann_fixedPoint_unique (operator : X →L[ℂ] X) (small : ‖operator‖ < 1)
    (known candidate : X) (equation : candidate = known + operator candidate) :
    candidate = neumannInverse operator known := by
  have residual : (1 - operator) candidate = known := by
    change candidate - operator candidate = known
    exact sub_eq_iff_eq_add.mpr equation
  have inverse := congrArg (fun mapping : X →L[ℂ] X => mapping candidate)
    (neumannInverse_left operator small)
  change neumannInverse operator ((1 - operator) candidate) = candidate at inverse
  rw [residual] at inverse
  exact inverse.symm

omit [CompleteSpace X] in
theorem neumann_half_bound (operator : X →L[ℂ] X) (small : ‖operator‖ ≤ 1 / 2) :
    ‖neumannInverse operator‖ ≤ 2 := by
  have bound := neumannInverse_norm_of_le operator small (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at bound
  exact bound

/-- The fixed-point residual and the actual geometric series are mutual
continuous inverses; both laws act on arbitrary complete-space elements. -/
def neumannResidualEquiv (operator : X →L[ℂ] X) (small : ‖operator‖ < 1) : X ≃L[ℂ] X :=
  ContinuousLinearEquiv.equivOfInverse' (1 - operator) (neumannInverse operator)
    (neumannInverse_right operator small) (neumannInverse_left operator small)

theorem neumannResidualEquiv_forward (operator : X →L[ℂ] X) (small : ‖operator‖ < 1) :
    (neumannResidualEquiv operator small).toContinuousLinearMap = 1 - operator := rfl

theorem neumannResidualEquiv_inverse (operator : X →L[ℂ] X) (small : ‖operator‖ < 1) :
    (neumannResidualEquiv operator small).symm.toContinuousLinearMap = neumannInverse operator := rfl

end CompleteFixedPoint
end Grad.AnnularCoupledInverse
