import AKDG2ActualOriginalUniquePreimage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.FinitePhysicalJetLift Grad.OriginalKernelCovariantRecovery Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ActualPuncturedFamily
open Grad.ChartAxisProjections Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds

variable (parameters : PhaseParameters) (compact : ℝ)
  (lengthPositive : 0<parameters.length) (widthHalf : parameters.gamma≤1/2)
  (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
  (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain)
  (base : RealJointCore parameters reference insideR)
  (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
  (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (seed 0) base.1 8≤actualJetExhaustionRadius parameters parameters.length compact)
  (compactNonnegative : 0≤compact) (alphaSmall : |seed 1|≤compact)
  (deltaSmall : |seed 2|≤compact) (parameterSmall : |seed 3|≤compact)

open Grad.CartesianStartup Grad.OriginalCurrentInverseUniqueness

variable (low : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
  (seed 0) base.1 10 < actualNativeAllOrderRadius parameters parameters.length compact lengthPositive compactNonnegative)

include lengthPositive widthHalf widthLength small compactNonnegative alphaSmall deltaSmall parameterSmall low

/-- Bijectivity of the literal original real derivative, supplied by the
actual native core construction and the existing homogeneous uniqueness. -/
theorem actualOriginalForward_bijective : Function.Bijective
    (literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis) := by
  refine ⟨literalPhysicalSmoothForward_injective parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall,?_⟩
  intro source
  let result := actualOriginalSource_unique_preimage parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall
    1 zero_lt_one le_rfl source low
  exact ⟨result.choose,result.choose_spec.1⟩

/-- The actual original smooth inverse. Its two laws are proved on the
identical real constrained cores; no inverse operator is assumed. -/
def actualOriginalSmoothInverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference insideR :=
  (LinearEquiv.ofBijective
    (literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis)
    (actualOriginalForward_bijective parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall low)).symm.toLinearMap

theorem actualOriginalSmoothInverse_right (source : sourceSmoothRange parameters) :
    literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis
      (actualOriginalSmoothInverse parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall low source)=source :=
  (LinearEquiv.ofBijective
    (literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis)
    (actualOriginalForward_bijective parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall low)).apply_symm_apply source

theorem actualOriginalSmoothInverse_left (direction : stateSmoothRange parameters reference insideR) :
    actualOriginalSmoothInverse parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall low
      (literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis direction)=direction :=
  (LinearEquiv.ofBijective
    (literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis)
    (actualOriginalForward_bijective parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall low)).symm_apply_apply direction

end Grad.OriginalCoreRealization
