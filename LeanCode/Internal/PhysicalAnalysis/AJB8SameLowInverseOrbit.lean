import AJB7ActualLowDataOperatorOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularLowVolterra Grad.GaugeCoefficients.Physical.Allocation

private theorem unitaryTransportBound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (input : E ≃ₗᵢ[ℂ] E) (output : F ≃ₗᵢ[ℂ] F) (operator : E →L[ℂ] F) (constant : ℝ)
    (bound : ‖operator‖ ≤ constant) :
    ‖output.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (operator.comp input.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ ≤ constant := by
  apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg operator).trans bound)
  intro field
  change ‖output (operator (input.symm field))‖ ≤ constant * ‖field‖
  rw [output.norm_map]
  exact (operator.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right bound (norm_nonneg _)).trans_eq
      (congrArg (fun value : ℝ => constant * value) (input.symm.norm_map field)))

variable (parameters : PhaseParameters) (length compact lower : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
  (state : RetainedInverseState parameters length compact)

/-- The SAME accepted AEI24 inverse transported by genuine graph/data
translations, with original rho, original width, and no new smallness premise. -/
def actualLowInverseOrbit (tau : OrbitParameter) :
    LowEnergyData lower →L[ℂ] lowEnergyGraph lower length positive :=
  (lowTranslationEquivalence lower length positive tau).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lowCurrentInverse parameters length compact lower lengthPositive positive bounded state).comp
      (lowDataTranslationEquivalence lower tau).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem actualLowInverseOrbit_apply (tau : OrbitParameter) (data : LowEnergyData lower) :
    actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau data =
      lowTranslation lower length positive tau
        (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state
          (lowDataTranslationEquivalence lower (-tau) data)) := rfl

variable (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
  lowCurrentNeighborhood parameters length compact)

include small

/-- The original B8 ball suffices for every translated inverse's right law. -/
theorem actualLowInverseOrbit_right (tau : OrbitParameter) (data : LowEnergyData lower) :
    actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state tau
      (actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau data) = data := by
  rw [actualLowInverseOrbit_apply, actualLowDataOperatorOrbit_translation,
    lowCurrentDataOperator_inverse parameters length compact lower lengthPositive positive bounded state small]
  exact (lowDataTranslationEquivalence lower tau).apply_symm_apply data

/-- The original B8 ball suffices for every translated inverse's left law. -/
theorem actualLowInverseOrbit_left (tau : OrbitParameter) (field : lowEnergyGraph lower length positive) :
    actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau
      (actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state tau field) = field := by
  rw [actualLowDataOperatorOrbit_conjugation]
  change lowTranslationEquivalence lower length positive tau
    (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state
      ((lowDataTranslationEquivalence lower tau).symm
        (lowDataTranslationEquivalence lower tau
          (lowCurrentDataOperator parameters length compact lower lengthPositive positive bounded state
            ((lowTranslationEquivalence lower length positive tau).symm field))))) = field
  rw [(lowDataTranslationEquivalence lower tau).symm_apply_apply,
    lowCurrentInverse_dataOperator parameters length compact lower lengthPositive positive bounded state small]
  exact (lowTranslationEquivalence lower length positive tau).apply_symm_apply field

/-- The SAME radius-independent inverse bound, on the unchanged B8 neighborhood. -/
theorem actualLowInverseOrbit_bound (tau : OrbitParameter) :
    ‖actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau‖ ≤
      2 * Real.sqrt (lowReferenceGraphConstant parameters length) :=
  unitaryTransportBound (lowDataTranslationEquivalence lower tau)
    (lowTranslationEquivalence lower length positive tau)
    (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state)
    (2 * Real.sqrt (lowReferenceGraphConstant parameters length))
    (lowCurrentInverse_bound parameters length compact lower lengthPositive positive bounded state small)

theorem actualLowInverseOrbit_zero :
    actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state 0 =
      lowCurrentInverse parameters length compact lower lengthPositive positive bounded state := by
  apply ContinuousLinearMap.ext
  intro data
  have right := actualLowInverseOrbit_right parameters length compact lower lengthPositive positive bounded state small 0 data
  rw [actualLowDataOperatorOrbit_zero] at right
  have inverse := congrArg (lowCurrentInverse parameters length compact lower lengthPositive positive bounded state) right
  rw [lowCurrentInverse_dataOperator parameters length compact lower lengthPositive positive bounded state small] at inverse
  exact inverse

/-- Actual inverse uniqueness at each translated original physical operator. -/
theorem actualLowInverseOrbit_unique (tau : OrbitParameter)
    (candidate : LowEnergyData lower →L[ℂ] lowEnergyGraph lower length positive)
    (right : ∀ data, actualLowDataOperatorOrbit parameters length compact lower lengthPositive positive bounded state tau
      (candidate data) = data) :
    candidate = actualLowInverseOrbit parameters length compact lower lengthPositive positive bounded state tau := by
  apply ContinuousLinearMap.ext
  intro data
  have inverse := actualLowInverseOrbit_left parameters length compact lower lengthPositive positive bounded state small tau (candidate data)
  rw [right data] at inverse
  exact inverse.symm

end Grad.AnnularLowOrbit
