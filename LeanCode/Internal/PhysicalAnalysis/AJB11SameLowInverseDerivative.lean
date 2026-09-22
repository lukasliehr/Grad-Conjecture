import AJB8SameLowInverseOrbit
import AJA11GenericInverseDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularInverseCalculus

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
  (state : RetainedInverseState parameters length compact)

/-- The actual inverse derivative, retaining complex-linear physical operators
and differentiating the two real translation coordinates in operator norm. -/
def actualLowInverseDifferential (tau : OrbitParameter) :
    OrbitParameter →L[ℝ] (LowEnergyData lower →L[ℂ] lowEnergyGraph lower length positive) :=
  (inverseSandwich (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau)).comp
    (actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state tau)

variable (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
  lowCurrentNeighborhood parameters length compact)

include small in
/-- Genuine norm derivative of SAME AEI24, from the proved coefficient
derivative and both inverse laws; the original B8 ball is unchanged. -/
theorem actualLowInverseOrbit_hasFDerivAt (tau : OrbitParameter) :
    HasFDerivAt (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state)
      (actualLowInverseDifferential parameters length compact lower lengthPositive positive bounded state tau) tau := by
  apply sameInverse_hasFDerivAt
    (actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state)
    (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state)
  · intro sigma
    apply ContinuousLinearMap.ext
    intro data
    exact actualLowInverseOrbit_right parameters length compact lower lengthPositive positive bounded state small sigma data
  · intro sigma
    apply ContinuousLinearMap.ext
    intro field
    exact actualLowInverseOrbit_left parameters length compact lower lengthPositive positive bounded state small sigma field
  · exact actualLowDataOperatorOrbit_hasFDerivAt parameters length compact lower lengthPositive positive bounded state tau

theorem actualLowInverseDifferential_apply (tau direction : OrbitParameter) :
    actualLowInverseDifferential parameters length compact lower lengthPositive positive bounded state tau direction =
      -(actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau).comp
        ((actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state tau direction).comp
          (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau)) :=
  inverseSandwich_apply _ _

include small in
/-- At zero this is the derivative of the SAME original AEI24 inverse,
not a replacement inverse or a stronger-grade Neumann construction. -/
theorem originalLowInverseDifferential_apply (direction : OrbitParameter) :
    actualLowInverseDifferential parameters length compact lower lengthPositive positive bounded state 0 direction =
      -(lowCurrentInverse parameters length compact lower lengthPositive positive bounded state).comp
        ((actualLowDataOperatorDifferential parameters length compact lower lengthPositive positive bounded state 0 direction).comp
          (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state)) := by
  rw [actualLowInverseDifferential_apply, actualLowInverseOrbit_zero parameters length compact lower lengthPositive positive bounded state small]

end Grad.AnnularLowOrbit
