import AKDG3ActualOriginalSmoothInverse
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.FinitePhysicalJetLift Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization
open Grad.CartesianStartup
open Grad.NonlinearQuotientBounds

/-- One positive physical B10 radius, chosen before any state or source. -/
def actualOriginalInverseRadius (parameters : PhaseParameters) (compact : ℝ)
    (positive : 0 < parameters.length) (nonnegative : 0 ≤ compact) : ℝ :=
  min 1 (min (actualJetExhaustionRadius parameters parameters.length compact)
    (actualNativeAllOrderRadius parameters parameters.length compact positive nonnegative))

theorem actualOriginalInverseRadius_positive (parameters : PhaseParameters) (compact : ℝ)
    (positive : 0 < parameters.length) (nonnegative : 0 ≤ compact) :
    0 < actualOriginalInverseRadius parameters compact positive nonnegative :=
  lt_min zero_lt_one (lt_min (actualJetExhaustionRadius_positive parameters parameters.length compact positive)
    (actualNativeAllOrderRadius_positive parameters parameters.length compact positive nonnegative))

theorem actualOriginalInverseRadius_bounds (parameters : PhaseParameters) (compact : ℝ)
    (positive : 0 < parameters.length) (nonnegative : 0 ≤ compact) :
    actualOriginalInverseRadius parameters compact positive nonnegative ≤ 1 ∧
    actualOriginalInverseRadius parameters compact positive nonnegative ≤ actualJetExhaustionRadius parameters parameters.length compact ∧
    actualOriginalInverseRadius parameters compact positive nonnegative ≤ actualNativeAllOrderRadius parameters parameters.length compact positive nonnegative :=
  ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _)⟩

/-- The literal derivative is bijective on this one B10 neighborhood.
No high-order regularity or inverse is supplied as a premise. -/
theorem actualOriginalForward_bijective_onBall
    (parameters : PhaseParameters) (compact : ℝ) (positive : 0 < parameters.length)
    (widthHalf : parameters.gamma ≤ 1/2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (nonnegative : 0 ≤ compact) (alpha : |seed 1| ≤ compact)
    (delta : |seed 2| ≤ compact) (parameter : |seed 3| ≤ compact)
    (low : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 10 < actualOriginalInverseRadius parameters compact positive nonnegative) :
    Function.Bijective (literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis) := by
  have bounds := actualOriginalInverseRadius_bounds parameters compact positive nonnegative
  have small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 8 ≤ actualJetExhaustionRadius parameters parameters.length compact :=
    (physicalBudget_monotone parameters _ _ _ (by norm_num : 8 ≤ 10)).trans (low.le.trans bounds.2.1)
  exact actualOriginalForward_bijective parameters compact positive widthHalf widthLength reference insideR seed insideS base axis
    small nonnegative alpha delta parameter (low.trans_le bounds.2.2)

end Grad.OriginalCoreRealization
