import AIW9ActualToAJFourierMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.AnnularCurrentGreen Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularFluxTrace Grad.AnnularReconstruction

def originalLowToAJBulkMap (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1) (slot : Fin 3) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  originalLowScalarFamily lower
    (fun index => ![originalLowToAJValueCurve parameters lower length positive index,
      originalLowToAJCorrectionCurve parameters lower length positive index,
      originalLowToAJSlopeCurve parameters lower length positive index] slot)
    (originalLowToAJConstant parameters length * lower⁻¹)
    (mul_nonneg (zero_le_one.trans (originalLowToAJConstant_dominates parameters length lengthPositive).2.2.2)
      (inv_nonneg.mpr positive.le))
    (fun index radius inside => by
      have bounds := originalLowToAJ_curves_bound parameters lower length positive lengthPositive bounded index radius inside
      fin_cases slot
      · exact bounds.1
      · exact bounds.2.1
      · exact bounds.2.2)

def originalLowToAJAmbient (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1) :
    LowEnergyAmbient lower →L[ℂ] LowEnergyAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => LowEnergyBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (originalLowToAJBulkMap parameters lower length positive lengthPositive bounded 0).comp (PiLp.proj 2 _ 0),
      (originalLowToAJBulkMap parameters lower length positive lengthPositive bounded 1).comp (PiLp.proj 2 _ 0) +
        (originalLowToAJBulkMap parameters lower length positive lengthPositive bounded 2).comp (PiLp.proj 2 _ 1)])

theorem originalLowToAJAmbient_value (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    originalLowToAJAmbient parameters lower length positive lengthPositive bounded field.val 0 index =
      lowEnergyToAJComponentValue parameters lower length positive index field := by
  change collarScalar 1 lower (originalLowRatio parameters lower length positive index * lowStorageInverse lower positive)
    (field.val 0 index) = _
  rw [← collarScalar_mul_apply]
  rfl

theorem originalLowToAJAmbient_slope (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    originalLowToAJAmbient parameters lower length positive lengthPositive bounded field.val 1 index =
      lowEnergyToAJComponentSlope parameters lower length positive index field := by
  change collarScalar 1 lower ((cellFrequency index.2.val.2)⁻¹ •
      (originalLowRatioSlope parameters lower length positive index * lowStorageInverse lower positive)) (field.val 0 index) +
    collarScalar 1 lower ((cellFrequency index.2.val.2)⁻¹ •
      (originalLowRatio parameters lower length positive index * lowMuCurve lower length positive index.2.val.2 *
        lowStorageInverse lower positive)) (field.val 1 index) = _
  rw [collarScalar_real_multiple, collarScalar_real_multiple, ← smul_add,
    ← collarScalar_mul_apply, ← collarScalar_mul_apply, ← collarScalar_mul_apply]
  rfl

def originalLowUnweight (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1) :
    lowEnergyGraph lower length positive →L[ℂ] originalLowGraph lower :=
  ((originalLowToAJAmbient parameters lower length positive lengthPositive bounded).comp
    (lowEnergyGraph lower length positive).subtypeL).codRestrict (originalLowGraph lower) (fun field => by
      intro index
      change CollarWeakDerivative lower
        (originalLowToAJAmbient parameters lower length positive lengthPositive bounded field.val 0 index)
        ((cellFrequency index.2.val.2 : ℂ) •
          originalLowToAJAmbient parameters lower length positive lengthPositive bounded field.val 1 index)
      rw [originalLowToAJAmbient_value, originalLowToAJAmbient_slope]
      exact lowEnergyToAJComponent_weak parameters lower length positive lengthPositive index field)

theorem originalLowUnweight_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : lowEnergyGraph lower length positive) :
    ‖originalLowUnweight parameters lower length positive lengthPositive bounded field‖ ≤
      (3 * originalLowToAJConstant parameters length) * lower⁻¹ * ‖field‖ := by
  let B := originalLowToAJConstant parameters length * lower⁻¹
  have Bnonnegative : 0 ≤ B :=
    mul_nonneg (zero_le_one.trans (originalLowToAJConstant_dominates parameters length lengthPositive).2.2.2)
      (inv_nonneg.mpr positive.le)
  have input := lowEnergyGraph_norm_sq lower length positive field
  have firstInput : ‖field.val 0‖ ≤ ‖field‖ := by nlinarith [norm_nonneg field, sq_nonneg ‖field.val 1‖]
  have secondInput : ‖field.val 1‖ ≤ ‖field‖ := by nlinarith [norm_nonneg field, sq_nonneg ‖field.val 0‖]
  have bulkBound (slot : Fin 3) (value : LowEnergyBulk lower) :
      ‖originalLowToAJBulkMap parameters lower length positive lengthPositive bounded slot value‖ ≤ B * ‖value‖ :=
    originalLowScalarFamily_bound _ _ _ _ _ value
  let output := originalLowUnweight parameters lower length positive lengthPositive bounded field
  have firstOutput : ‖output.val 0‖ ≤ B * ‖field‖ :=
    (bulkBound 0 (field.val 0)).trans (mul_le_mul_of_nonneg_left firstInput Bnonnegative)
  have secondOutput : ‖output.val 1‖ ≤ 2 * B * ‖field‖ := by
    change ‖originalLowToAJBulkMap parameters lower length positive lengthPositive bounded 1 (field.val 0) +
      originalLowToAJBulkMap parameters lower length positive lengthPositive bounded 2 (field.val 1)‖ ≤ _
    exact (norm_add_le _ _).trans ((add_le_add
      ((bulkBound 1 (field.val 0)).trans (mul_le_mul_of_nonneg_left firstInput Bnonnegative))
      ((bulkBound 2 (field.val 1)).trans (mul_le_mul_of_nonneg_left secondInput Bnonnegative))).trans_eq (by ring))
  have outputNorm := originalLowGraph_norm_sq lower output
  have triangle : ‖output‖ ≤ ‖output.val 0‖ + ‖output.val 1‖ := by
    nlinarith [norm_nonneg output, norm_nonneg (output.val 0), norm_nonneg (output.val 1),
      mul_nonneg (norm_nonneg (output.val 0)) (norm_nonneg (output.val 1))]
  change ‖output‖ ≤ _
  calc
    ‖output‖ ≤ ‖output.val 0‖ + ‖output.val 1‖ := triangle
    _ ≤ B * ‖field‖ + 2 * B * ‖field‖ := add_le_add firstOutput secondOutput
    _ = _ := by dsimp [B]; ring

end Grad.AnnularOriginalLow
