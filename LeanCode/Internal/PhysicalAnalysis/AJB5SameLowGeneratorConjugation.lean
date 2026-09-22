import AJB4ActualLowCharacterCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
  (state : RetainedInverseState parameters length compact)

theorem lowBulkTranslation_inverse (tau : OrbitParameter) (field : LowEnergyBulk lower) :
    lowBulkTranslation lower tau (lowBulkTranslation lower (-tau) field) = field := by
  apply lp.ext
  funext index
  rw [lowBulkTranslation_apply, lowBulkTranslation_apply, smul_smul, orbitCharacter_inverse, one_smul]

/-- The translated completed coefficients give the literal physical response
conjugation after all seven-input and three-output normalizations. -/
theorem actualLowResponseOrbit_conjugation (tau : OrbitParameter) :
    actualLowResponseOrbit parameters length compact lower lengthPositive positive bounded state tau =
      (lowBulkTranslation lower tau).comp
        ((lowPhysicalResponse parameters length compact lower lengthPositive positive bounded state).comp
          (lowBulkTranslation lower (-tau))) := by
  apply ContinuousLinearMap.ext
  intro field
  unfold actualLowResponseOrbit lowPhysicalResponse
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_add, actualLowRowOrbit_conjugation,
    ← lowNormalizedSevenInput_translation, lowFirstOutput_translation, lowCellOutput_translation,
    lowAngularOutput_translation]

/-- The SAME AEI21 generator, including its original fixed diagonal. -/
theorem actualLowGeneratorOrbit_conjugation (tau : OrbitParameter) :
    actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded state tau =
      (lowBulkTranslation lower tau).comp
        ((lowCurrentBulk parameters length compact lower lengthPositive positive bounded state).comp
          (lowBulkTranslation lower (-tau))) := by
  rw [actualLowGeneratorOrbit, actualLowResponseOrbit_conjugation]
  apply ContinuousLinearMap.ext
  intro field
  change lowCommonDiagonal parameters length lower lengthPositive positive field + _ =
    lowBulkTranslation lower tau
      (lowCommonDiagonal parameters length lower lengthPositive positive (lowBulkTranslation lower (-tau) field) + _)
  rw [map_add, lowCommonDiagonal_translation, lowBulkTranslation_inverse]
  rfl

/-- Covariance on the actual original low bulk, avoiding a translated-state
premise and preserving the original analytic width and B8 neighborhood. -/
theorem actualLowGeneratorOrbit_translation (tau : OrbitParameter) (field : LowEnergyBulk lower) :
    actualLowGeneratorOrbit parameters length compact lower lengthPositive positive bounded state tau
      (lowBulkTranslation lower tau field) =
        lowBulkTranslation lower tau
          (lowCurrentBulk parameters length compact lower lengthPositive positive bounded state field) := by
  rw [actualLowGeneratorOrbit_conjugation]
  change lowBulkTranslation lower tau
    (lowCurrentBulk parameters length compact lower lengthPositive positive bounded state
      (lowBulkTranslation lower (-tau) (lowBulkTranslation lower tau field))) = _
  have inverse := lowBulkTranslation_inverse lower (-tau) field
  rw [neg_neg] at inverse
  rw [inverse]

end Grad.AnnularLowOrbit
