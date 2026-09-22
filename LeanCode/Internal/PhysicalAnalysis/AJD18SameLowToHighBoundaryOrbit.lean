import AJD14SameCompleteHighCrossResponseOrbit
import AJD17ActualLowOuterInputTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit
open Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularKernelL2
open Grad.BoundaryKernelAction Grad.PhaseAlgebra Grad.BoundaryTrace Grad.ActualBoundaryPrimitives

/-- Every mixed full boundary kernel jet is smooth in its original completed operator norm. -/
theorem boundaryOrbitJetAction_contDiff {src tgt : ℕ} (parameters : PhaseParameters) (traceAngular traceCell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters src tgt) (angular cell : ℕ) :
    ContDiff ℝ ∞ (fun tau => boundaryOrbitJetAction parameters traceAngular traceCell kernel tau angular cell) :=
  orbitTower_contDiff _ (fun a b tau => boundaryOrbitJetAction_hasFDerivAt parameters traceAngular traceCell kernel tau a b) angular cell

variable (parameters : PhaseParameters) (L compact lower : ℝ) (lengthPositive : 0 < L)
  (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (state : RetainedInverseState parameters L compact)

def lowToHighBoundaryAmbientOrbit (tau : OrbitParameter) :
    lowEnergyGraph lower L positive →L[ℂ] NegativeTrace parameters 0 0 1 :=
  -((boundaryOrbitJetAction parameters 0 0 state.boundaryState.fullBoundaryDeviation tau 0 0).comp
    ((sevenSlotFlatten parameters 0 0).comp (lowOuterSevenTrace parameters lower L lengthPositive positive lowerHalf)))

theorem lowToHighBoundaryAmbientOrbit_contDiff :
    ContDiff ℝ ∞ (lowToHighBoundaryAmbientOrbit parameters L compact lower lengthPositive positive lowerHalf state) :=
  (complexOperatorComposition_contDiff _ _
    (boundaryOrbitJetAction_contDiff parameters 0 0 state.boundaryState.fullBoundaryDeviation 0 0) contDiff_const).neg

/-- The literal original boundary cross map, including the negative sign of BF16. -/
def lowToHighBoundaryOrbit (tau : OrbitParameter) :
    lowEnergyGraph lower L positive →L[ℂ] HighBoundaryPrimitive parameters 0 0 :=
  (highBoundaryTranslation parameters tau).comp
    ((lowToHighBoundaryCross parameters lower L compact lengthPositive positive lowerHalf state).comp
      (lowTranslation lower L positive (-tau)))

theorem lowToHighBoundaryOrbit_inclusion (tau : OrbitParameter) :
    (highAngularSubmodule parameters 0 0 1).subtypeL.comp
      (lowToHighBoundaryOrbit parameters L compact lower lengthPositive positive lowerHalf state tau) =
    lowToHighBoundaryAmbientOrbit parameters L compact lower lengthPositive positive lowerHalf state tau := by
  apply ContinuousLinearMap.ext
  intro field
  change orbitLpAction (ComplexEuclidean 1) tau
    (lowToHighBoundaryCross parameters lower L compact lengthPositive positive lowerHalf state
      (lowTranslation lower L positive (-tau) field)).val = _
  rw [lowToHighBoundaryCross_derivativeCoordinate]
  change orbitLpAction (ComplexEuclidean 1) tau
    (-(fullNegativeKernelAction parameters 0 0 state.boundaryState.fullBoundaryDeviation
      (sevenSlotFlatten parameters 0 0
        (lowOuterSevenTrace parameters lower L lengthPositive positive lowerHalf (lowTranslation lower L positive (-tau) field))))) =
    -(boundaryOrbitJetAction parameters 0 0 state.boundaryState.fullBoundaryDeviation tau 0 0
      (sevenSlotFlatten parameters 0 0 (lowOuterSevenTrace parameters lower L lengthPositive positive lowerHalf field)))
  rw [lowOuterSevenFlatten_translation, map_neg]
  unfold boundaryOrbitJetAction
  rw [kernelOrbitJet_zero, fullNegativeKernelAction_orbit]
  rfl

/-- Original high boundary membership is preserved; no independently prescribed boundary jet is assumed. -/
theorem lowToHighBoundaryOrbit_contDiff :
    ContDiff ℝ ∞ (lowToHighBoundaryOrbit parameters L compact lower lengthPositive positive lowerHalf state) := by
  apply graphOperator_contDiff_of_inclusion (highAngularSubmodule parameters 0 0 1) ∞
  have same := funext (lowToHighBoundaryOrbit_inclusion parameters L compact lower lengthPositive positive lowerHalf state)
  rw [same]
  exact lowToHighBoundaryAmbientOrbit_contDiff parameters L compact lower lengthPositive positive lowerHalf state

end Grad.AnnularCrossOrbit
