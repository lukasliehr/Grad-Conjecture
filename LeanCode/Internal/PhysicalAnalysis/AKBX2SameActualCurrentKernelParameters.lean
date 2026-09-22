import AKBX1SameFlatChartPhysicalVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.OriginalCurrentInverseUniqueness
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.FinitePhysicalJetLift Grad.OriginalKernelCovariantRecovery Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ActualPuncturedFamily
open Grad.ExhaustionSourceAllocation Grad.BoundaryKernelAction Grad.SourceCollar Grad.SourceCollarCoefficients

variable (parameters : PhaseParameters) (compact : ℝ)
  (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain)
  (base : RealJointCore parameters reference insideR)
  (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (seed 0) base.1 8≤actualJetExhaustionRadius parameters parameters.length compact)
  (compactNonnegative : 0≤compact) (alphaSmall : |seed 1|≤compact)
  (deltaSmall : |seed 2|≤compact) (parameterSmall : |seed 3|≤compact)

local notation "sameState" => actualJetExhaustionState parameters parameters.length compact reference insideR seed insideS base small compactNonnegative alphaSmall deltaSmall parameterSmall

theorem actualJetExhaustionState_originalSeed :
    originalCoefficientSeed parameters compact (sameState).val.val=seed := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem actualJetExhaustionState_coefficientSmall :
    physicalBudget parameters (sameState).val.val.field (sameState).val.val.rho (sameState).val.val.epsilon 8≤
      originalCoefficientLowRadius parameters parameters.length :=
  (actualJetExhaustion_exSmall parameters parameters.length compact reference insideR seed insideS base small).trans
    (min_le_right _ _)

theorem actualJetExhaustionState_primitiveSmall :
    physicalBudget parameters (sameState).val.val.field (sameState).val.val.rho (sameState).val.val.epsilon 8≤
      coupledPrimitiveRadius parameters parameters.length compact :=
  (actualJetExhaustion_exSmall parameters parameters.length compact reference insideR seed insideS base small).trans
    (min_le_left _ _)

theorem actualJetExhaustionState_samePhysicalBase :
    (physicalReferenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR base)).2.1=
      planarReferenceCore parameters+(sameState).val.val.field := by
  rw [actualFiniteCurrentState_eq]
  rfl

theorem actualJetExhaustionState_samePhysicalEpsilon :
    (physicalReferenceState parameters reference insideR seed insideS
      (realJointCoreToJoint parameters reference insideR base)).1=((sameState).val.val.epsilon:ℂ) := rfl

end Grad.OriginalCurrentInverseUniqueness
