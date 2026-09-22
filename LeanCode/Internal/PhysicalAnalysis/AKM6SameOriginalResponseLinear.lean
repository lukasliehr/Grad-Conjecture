import AKM5OriginalFiveBlockWeakExtraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularStrongOrbit
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularHighGenerators
open Grad.AnnularCoupledOrbit Grad.AnnularCrossOrbit Grad.AnnularKernelOrbit
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularForwardDatum Grad.AnnularForwardTraces
open Grad.AnnularCurrentSource
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule
  traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

section Transport
variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

def transportedResponseLinear (input : X →L[ℝ] X) (output : F ≃ₗᵢ[ℂ] F)
    (operator : X →L[ℝ] F) : X →L[ℝ] F :=
  (output.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp (operator.comp input)

theorem transportedResponseLinear_apply (input : X →L[ℝ] X) (output : F ≃ₗᵢ[ℂ] F)
    (operator : X →L[ℝ] F) (response : X → F)
    (actual : ∀ source, operator (input source) = output (response source)) (source : X) :
    transportedResponseLinear input output operator source = response source := by
  change output.symm (operator (input source)) = response source
  rw [actual, output.symm_apply_apply]
end Transport

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

/-- The already constructed bounded transported operator is the SAME
shared response. No inverse or source action is reconstructed. -/
def sameSharedResponseLinear :
    StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 →L[ℝ]
      CoupledSpace lower length positive lengthPositive :=
  transportedResponseLinear
    (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 0)
    (coupledTranslationEquivalence lower length positive lengthPositive 0)
    (sharedStrongResponseOrbit parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small 0)

theorem sameSharedResponseLinear_apply
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    sameSharedResponseLinear parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data =
    sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data :=
  transportedResponseLinear_apply _ _ _ _
    (sharedStrongResponseOrbit_on_translation parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small 0) data

/-- Original BF5/BF6 changes of coordinates give the exact original response
as a bounded real linear map on the entire original datum. -/
def sameOriginalResponseLinear : OriginalStrongCarrier parameters lower 0 0 →L[ℝ]
    OriginalCoupledSpace lower length positive :=
  ((originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).symm.toContinuousLinearMap.restrictScalars ℝ).comp
    ((sameSharedResponseLinear parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small).comp
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).toContinuousLinearMap)

theorem sameOriginalResponseLinear_apply (data : OriginalStrongCarrier parameters lower 0 0) :
    sameOriginalResponseLinear parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data =
    originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data := by
  change (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).symm
    (sameSharedResponseLinear parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)) = _
  rw [sameSharedResponseLinear_apply]
  rfl

end Grad.AnnularWeakExhaustion
