import AIT9OneOriginalCoupledNeighborhood

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.Foundations Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (lower length compact : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
  (state : RetainedInverseState parameters length compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

/-- The literal BF20 operator for a state on the one BF21 neighborhood. -/
def coupledError : CoupledSpace lower length positive lengthPositive →L[ℂ] CoupledSpace lower length positive lengthPositive :=
  actualCoupledOffDiagonal parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state
    (coupledPrimitive_highSmall parameters length compact state small)

theorem coupledError_half :
    ‖coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small‖ ≤ 1 / 2 :=
  actualCoupledOffDiagonal_half parameters length compact state small lower lengthPositive positive lowerHalf widthHalf widthLength

/-- The actual norm-convergent Neumann series on the original complete Xalpha. -/
def actualCoupledInverse : CoupledSpace lower length positive lengthPositive →L[ℂ] CoupledSpace lower length positive lengthPositive :=
  neumannInverse (coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small)

theorem actualCoupledInverse_hasSum :
    HasSum (fun degree : ℕ => (coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small) ^ degree)
      (actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small) :=
  neumannInverse_hasSum _ ((coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).trans_lt (by norm_num))

theorem actualCoupledInverse_left :
    (actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).comp
      (1 - coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small) = 1 :=
  neumannInverse_left _ ((coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).trans_lt (by norm_num))

theorem actualCoupledInverse_right :
    (1 - coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).comp
      (actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small) = 1 :=
  neumannInverse_right _ ((coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).trans_lt (by norm_num))

theorem actualCoupledInverse_bound :
    ‖actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small‖ ≤ 2 :=
  neumann_half_bound _ (coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small)

theorem actualCoupledInverse_apply_bound (known : CoupledSpace lower length positive lengthPositive) :
    ‖actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known‖ ≤ 2 * ‖known‖ :=
  (ContinuousLinearMap.le_opNorm _ known).trans
    (mul_le_mul_of_nonneg_right (actualCoupledInverse_bound parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small) (norm_nonneg _))

theorem actualCoupledInverse_fixedPoint (known : CoupledSpace lower length positive lengthPositive) :
    actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known =
      known + coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small
        (actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known) :=
  neumann_fixedPoint _ ((coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).trans_lt (by norm_num)) known

theorem actualCoupledInverse_unique (known candidate : CoupledSpace lower length positive lengthPositive)
    (equation : candidate = known + coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small candidate) :
    candidate = actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small known :=
  neumann_fixedPoint_unique _ ((coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).trans_lt (by norm_num)) known candidate equation

/-- Both inverse laws packaged as the actual complete residual equivalence. -/
def actualCoupledResidualEquiv : CoupledSpace lower length positive lengthPositive ≃L[ℂ] CoupledSpace lower length positive lengthPositive :=
  neumannResidualEquiv _ ((coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).trans_lt (by norm_num))

theorem actualCoupledResidualEquiv_forward :
    (actualCoupledResidualEquiv parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).toContinuousLinearMap =
      1 - coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small := rfl

theorem actualCoupledResidualEquiv_inverse :
    (actualCoupledResidualEquiv parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).symm.toContinuousLinearMap =
      actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small := rfl

end Grad.AnnularCoupledInverse
