import AKBX2SameActualCurrentKernelParameters

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

include lengthPositive widthHalf widthLength small compactNonnegative alphaSmall deltaSmall parameterSmall

/-- The full actual original smooth forward map has zero kernel. The free
axis is killed by the actual extraction identity before physical uniqueness;
there is no separate zero-axis or finite-jet kernel assumption. -/
theorem literalPhysicalSmoothForward_kernel_zero
    (direction : stateSmoothRange parameters reference insideR)
    (homogeneous : literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis direction=0) :
    direction=0 := by
  have flat : realChartKappa parameters reference insideR direction=0 := by
    rw [←realExtraction_forward parameters.length lengthPositive reference insideR seed insideS base axis direction,
      homogeneous,map_zero]
  let state := actualJetExhaustionState parameters parameters.length compact reference insideR seed insideS base small
    compactNonnegative alphaSmall deltaSmall parameterSmall
  have sameSeed : originalCoefficientSeed parameters compact state.val.val=seed :=
    actualJetExhaustionState_originalSeed parameters compact reference insideR seed insideS base small
      compactNonnegative alphaSmall deltaSmall parameterSmall
  have insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain := by
    rw [sameSeed]
    exact insideS
  let transferred := constrainedCoreTransfer parameters reference insideR seed insideS direction
  let vector := toPhysicalCore parameters transferred.val.2.1
  let scalar := transferred.val.2.2
  have physicalZero : quotientRowsDerivative parameters parameters.length 1
      (physicalReferenceState parameters reference insideR seed insideS
        (realJointCoreToJoint parameters reference insideR base)) ![(0,vector,scalar)]=0 := by
    have rows := congrArg Subtype.val homogeneous
    change literalPhysicalSmoothForwardRows parameters parameters.length reference insideR seed insideS base direction=0 at rows
    unfold literalPhysicalSmoothForwardRows at rows
    rw [originalFlatDirection_physical_first parameters reference insideR seed insideS base direction flat] at rows
    have inputs : (![(0,vector,scalar)] : Fin 1 → QuotientState parameters)=
        (fun _ => (0,toPhysicalCore parameters
          (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.1,
          (constrainedCoreTransfer parameters reference insideR seed insideS direction).val.2.2)) := by
      funext coordinate
      fin_cases coordinate
      rfl
    rw [inputs]
    exact rows
  have member : (0,toPhysicalCore parameters vector,scalar)∈
      stateSmoothRange parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed := by
    simpa only [sameSeed] using
      originalFlatDirection_physical_member parameters reference insideR seed insideS direction flat
  have pair := Grad.OriginalPhysicalKernelUniqueness.Consumer.originalSmoothDomain_physicalKernel_zero
    parameters compact lengthPositive widthHalf widthLength state
    (actualJetExhaustionState_coefficientSmall parameters compact reference insideR seed insideS base small
      compactNonnegative alphaSmall deltaSmall parameterSmall)
    (actualJetExhaustionState_primitiveSmall parameters compact reference insideR seed insideS base small
      compactNonnegative alphaSmall deltaSmall parameterSmall)
    insideSeed
    (physicalReferenceState parameters reference insideR seed insideS (realJointCoreToJoint parameters reference insideR base))
    (actualJetExhaustionState_samePhysicalBase parameters compact reference insideR seed insideS base small
      compactNonnegative alphaSmall deltaSmall parameterSmall)
    (actualJetExhaustionState_samePhysicalEpsilon parameters compact reference insideR seed insideS base small
      compactNonnegative alphaSmall deltaSmall parameterSmall)
    vector scalar physicalZero member
  have storedZero : transferred.val.2.1=0 := by
    have identity := congrArg (toPhysicalCore parameters) pair.1
    change toPhysicalCore parameters (toPhysicalCore parameters transferred.val.2.1)=toPhysicalCore parameters 0 at identity
    rwa [toPhysicalCore_involutive,map_zero] at identity
  have transferredZero : transferred=0 := by
    apply Subtype.ext
    apply Prod.ext
    · have formula := (constrainedCoreTransfer_coe parameters reference insideR seed insideS direction).trans
        (coreTransfer_apply parameters reference insideR seed insideS direction.val)
      exact (congrArg (fun value : Grad.SmoothingFamily.StateCore parameters => value.1) formula).trans
        (originalFlatDirection_axis_zero parameters reference insideR direction flat)
    · exact Prod.ext storedZero pair.2
  apply (coreTransferEquiv parameters reference insideR seed insideS).injective
  change transferred=constrainedCoreTransfer parameters reference insideR seed insideS 0
  rw [map_zero]
  exact transferredZero

end Grad.OriginalCurrentInverseUniqueness
