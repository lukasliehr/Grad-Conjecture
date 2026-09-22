import AJF35SameSolutionGeneratorApplication

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open scoped ContDiff BigOperators
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.CartesianState Grad.AnnularKernelOrbit
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularCoupledOrbit Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCurrentSource Grad.AnnularStrongSolution
open Grad.AnnularCrossMaps Grad.AnnularFullSource Grad.AnnularCrossOrbit

section ContinuousTransport
variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]

theorem continuous_of_transported_operator (input : X →L[ℝ] X) (output : F ≃ₗᵢ[ℂ] F)
    (operator : X →L[ℝ] F) (response : X → F)
    (actual : ∀ source, operator (input source) = output (response source)) : Continuous response := by
  have smooth := output.symm.continuous.comp (operator.continuous.comp input.continuous)
  have same : (fun source => output.symm (operator (input source))) = response := by
    funext source
    rw [actual, output.symm_apply_apply]
  simpa only [Function.comp_def, same] using smooth
end ContinuousTransport

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

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)

/-- Continuity of the SAME original response follows from its actual
bounded transported operator; no source orbit regularity is assumed. -/
theorem sharedStrongResponse_continuous :
    Continuous (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) :=
  continuous_of_transported_operator
    (strongDataTranslation parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 0)
    (coupledTranslationEquivalence lower L positive lengthPositive 0)
    (sharedStrongResponseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small 0)
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (sharedStrongResponseOrbit_on_translation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small 0)

end Grad.AnnularHighGenerators
