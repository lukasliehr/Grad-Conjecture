import AKAI3ActualLinearJetReductionConsumer
import AKT13ActualCartesianCompatibleSolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 300000
namespace Grad.FinitePhysicalJetLift
open Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization
open Grad.ActualPuncturedFamily Grad.ActualCurrentPrimitives Grad.BoundaryKernelAction
open Grad.AnnularCoupledInverse Grad.AnnularReconstruction

/-- One fixed primitive B8 ball for the actual jet lift, mass inverse, and EX.
The independent B20 bound is kept separately, with unchanged analytic width. -/
def actualJetExhaustionRadius (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  min (originalCubicLowRadius parameters length)
    (min (actualMassInverseLowRadius parameters length compact)
      (originalExhaustionPrimitiveRadius parameters length compact))

theorem actualJetExhaustionRadius_positive (parameters : PhaseParameters) (length compact : ℝ)
    (positive : 0 < length) : 0 < actualJetExhaustionRadius parameters length compact :=
  lt_min (originalCubicLowRadius_positive parameters length)
    (lt_min (actualMassInverseLowRadius_positive parameters length compact)
      (originalExhaustionPrimitiveRadius_positive parameters length compact positive))

variable (parameters : PhaseParameters) (length compact : ℝ)
  (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
  (base : RealJointCore parameters reference insideR)
  (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (seed 0) base.1 8 ≤ actualJetExhaustionRadius parameters length compact)

include small in
theorem actualJetExhaustion_cubicSmall :
    physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 6 ≤ originalCubicLowRadius parameters length :=
  (physicalBudget_monotone parameters _ _ _ (by norm_num : 6 ≤ 8)).trans
    (small.trans (min_le_left _ _))

include small in
theorem actualJetExhaustion_massSmall :
    physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 7 ≤ actualMassInverseLowRadius parameters length compact :=
  (physicalBudget_monotone parameters _ _ _ (by norm_num : 7 ≤ 8)).trans
    (small.trans ((min_le_right _ _).trans (min_le_left _ _)))

include small in
theorem actualJetExhaustion_exSmall :
    physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 8 ≤ originalExhaustionPrimitiveRadius parameters length compact :=
  small.trans ((min_le_right _ _).trans (min_le_right _ _))

variable (compactNonnegative : 0 ≤ compact) (alphaSmall : |seed 1| ≤ compact)
  (deltaSmall : |seed 2| ≤ compact) (parameterSmall : |seed 3| ≤ compact)

/-- The retained primitive state uses the same actual Cartesian displacement,
seed coordinates and real scalar as the literal original jet residual. -/
def actualJetExhaustionState : RetainedInverseState parameters length compact :=
  let boundary := BoundaryReconstructionState.of (parameters := parameters) (L := length) (compactRadius := compact)
    (seed 0) (seed 1) (seed 2) (seed 3) base.1
    (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (actualJetExhaustion_massSmall parameters length compact reference insideR seed insideS base small)
    compactNonnegative alphaSmall deltaSmall parameterSmall
  coupledRetainedState parameters length compact boundary
    (originalExhaustionPrimitiveRadius_inverse parameters length compact (seed 0) base.1 _
      (actualJetExhaustion_exSmall parameters length compact reference insideR seed insideS base small))

theorem actualJetExhaustionState_same :
    (actualJetExhaustionState parameters length compact reference insideR seed insideS base small
      compactNonnegative alphaSmall deltaSmall parameterSmall).val.val.val =
      (seed 0,seed 1,seed 2,seed 3,base.1,actualFiniteCurrentField parameters reference insideR seed insideS base) := rfl

end Grad.FinitePhysicalJetLift
