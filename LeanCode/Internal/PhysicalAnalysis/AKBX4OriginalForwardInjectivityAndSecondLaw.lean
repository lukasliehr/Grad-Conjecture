import AKBX3ActualFullSmoothForwardKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
namespace Grad.OriginalCurrentInverseUniqueness
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

include axis lengthPositive widthHalf widthLength small compactNonnegative alphaSmall deltaSmall parameterSmall

/-- Injectivity of the existing full original smooth forward map, at the
same actual current used by the finite-jet/exhaustion construction. -/
theorem literalPhysicalSmoothForward_injective : Function.Injective
    (literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis) := by
  intro first second equality
  apply sub_eq_zero.mp
  apply literalPhysicalSmoothForward_kernel_zero parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall
  rw [map_sub,equality,sub_self]

/-- The actual completed forward operator is faithful on its original
smooth-core realizations. This uses its checked literal core formula. -/
theorem actualPhysicalSmoothForward_smoothCore_injective
    (grade : ℕ) (large : 4≤grade) : Function.Injective
    (fun direction : stateSmoothRange parameters reference insideR =>
      actualPhysicalSmoothForward parameters parameters.length reference insideR seed grade large base
        (stateSmoothEmbedding parameters reference insideR (grade+6) (realHighLarge grade) direction)) := by
  intro first second equality
  apply literalPhysicalSmoothForward_injective parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall
  apply sourceSmoothEmbedding_injective parameters grade (Grad.SmoothForward.forwardLarge large)
  change sourceSmoothEmbedding parameters grade (Grad.SmoothForward.forwardLarge large)
      (literalPhysicalSmoothForwardValue parameters parameters.length reference insideR seed insideS base axis first)=
    sourceSmoothEmbedding parameters grade (Grad.SmoothForward.forwardLarge large)
      (literalPhysicalSmoothForwardValue parameters parameters.length reference insideR seed insideS base axis second)
  rw [←actualPhysicalSmoothForward_core_value parameters parameters.length reference insideR seed insideS grade large base axis first,
    ←actualPhysicalSmoothForward_core_value parameters parameters.length reference insideR seed insideS grade large base axis second]
  exact equality

/-- Once the same reconstructed state realizes the forward image of an
original direction, the second inverse law is forced on the original domain. -/
theorem sameRealizedCore_secondInverseLaw
    (grade : ℕ) (large : 4≤grade)
    (direction reconstructed : stateSmoothRange parameters reference insideR)
    (solved : actualPhysicalSmoothForward parameters parameters.length reference insideR seed grade large base
      (stateSmoothEmbedding parameters reference insideR (grade+6) (realHighLarge grade) reconstructed)=
      sourceSmoothEmbedding parameters grade (Grad.SmoothForward.forwardLarge large)
        (literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis direction)) :
    reconstructed=direction := by
  apply actualPhysicalSmoothForward_smoothCore_injective parameters compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall grade large
  dsimp only
  rw [actualPhysicalSmoothForward_core_value parameters parameters.length reference insideR seed insideS grade large base axis direction]
  exact solved

end Grad.OriginalCurrentInverseUniqueness
