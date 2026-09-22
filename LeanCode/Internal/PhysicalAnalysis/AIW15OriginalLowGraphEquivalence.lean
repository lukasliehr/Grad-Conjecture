import AIW14ActualOriginalLowWeightGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.AnnularFourSource Grad.GaugeCoefficients.Physical.WeightedTrace

theorem originalLowUnweight_weight (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : originalLowGraph lower) :
    originalLowUnweight parameters lower length positive lengthPositive bounded
      (originalLowWeight parameters lower length positive lengthPositive bounded field) = field := by
  apply originalLowGraph_value_injective lower
  apply lp.ext
  funext index
  change collarScalar 1 lower (originalLowToAJValueCurve parameters lower length positive index)
    (collarScalar 1 lower (originalLowFromAJValueCurve parameters lower length positive lengthPositive index) (field.val 0 index)) = _
  exact collarScalar_inverse_apply lower _ _ (fun radius => by
    rw [mul_comm]
    exact (originalLowTriangular_inverse parameters lower length positive lengthPositive index radius).1) _

theorem originalLowWeight_unweight (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : lowEnergyGraph lower length positive) :
    originalLowWeight parameters lower length positive lengthPositive bounded
      (originalLowUnweight parameters lower length positive lengthPositive bounded field) = field := by
  apply lowEnergyGraph_value_injective lower length positive
  apply lp.ext
  funext index
  change collarScalar 1 lower (originalLowFromAJValueCurve parameters lower length positive lengthPositive index)
    (collarScalar 1 lower (originalLowToAJValueCurve parameters lower length positive index) (field.val 0 index)) = _
  exact collarScalar_inverse_apply lower _ _ (fun radius =>
    (originalLowTriangular_inverse parameters lower length positive lengthPositive index radius).1) _

/-- Actual BF6 low isomorphism from independently specified AJ8 to BE18. -/
def originalLowGraphEquivalence (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1) :
    originalLowGraph lower ≃L[ℂ] lowEnergyGraph lower length positive where
  toLinearEquiv :=
    { toLinearMap := (originalLowWeight parameters lower length positive lengthPositive bounded).toLinearMap
      invFun := originalLowUnweight parameters lower length positive lengthPositive bounded
      left_inv := originalLowUnweight_weight parameters lower length positive lengthPositive bounded
      right_inv := originalLowWeight_unweight parameters lower length positive lengthPositive bounded }
  continuous_toFun := (originalLowWeight parameters lower length positive lengthPositive bounded).continuous
  continuous_invFun := (originalLowUnweight parameters lower length positive lengthPositive bounded).continuous

theorem originalLowWeight_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : originalLowGraph lower) :
    ‖originalLowWeight parameters lower length positive lengthPositive bounded field‖ ≤
      (3 * originalLowFromAJConstant parameters length) * lower ^ (-(15 / 4 : ℝ)) * ‖field‖ := by
  let B := originalLowFromAJConstant parameters length * lower ^ (-(15 / 4 : ℝ))
  have Bnonnegative : 0 ≤ B :=
    mul_nonneg (zero_le_one.trans (originalLowFromAJConstant_dominates parameters length lengthPositive).2.2.2)
      (Real.rpow_pos_of_pos positive _).le
  have input := originalLowGraph_norm_sq lower field
  have firstInput : ‖field.val 0‖ ≤ ‖field‖ := by nlinarith [norm_nonneg field, sq_nonneg ‖field.val 1‖]
  have secondInput : ‖field.val 1‖ ≤ ‖field‖ := by nlinarith [norm_nonneg field, sq_nonneg ‖field.val 0‖]
  have bulkBound (slot : Fin 3) (value : LowEnergyBulk lower) :
      ‖originalLowFromAJBulkMap parameters lower length positive lengthPositive bounded slot value‖ ≤ B * ‖value‖ :=
    originalLowScalarFamily_bound _ _ _ _ _ value
  let output := originalLowWeight parameters lower length positive lengthPositive bounded field
  have firstOutput : ‖output.val 0‖ ≤ B * ‖field‖ :=
    (bulkBound 0 (field.val 0)).trans (mul_le_mul_of_nonneg_left firstInput Bnonnegative)
  have secondOutput : ‖output.val 1‖ ≤ 2 * B * ‖field‖ := by
    change ‖originalLowFromAJBulkMap parameters lower length positive lengthPositive bounded 1 (field.val 0) +
      originalLowFromAJBulkMap parameters lower length positive lengthPositive bounded 2 (field.val 1)‖ ≤ _
    exact (norm_add_le _ _).trans ((add_le_add
      ((bulkBound 1 (field.val 0)).trans (mul_le_mul_of_nonneg_left firstInput Bnonnegative))
      ((bulkBound 2 (field.val 1)).trans (mul_le_mul_of_nonneg_left secondInput Bnonnegative))).trans_eq (by ring))
  have outputNorm := lowEnergyGraph_norm_sq lower length positive output
  have triangle : ‖output‖ ≤ ‖output.val 0‖ + ‖output.val 1‖ := by
    nlinarith [norm_nonneg output, norm_nonneg (output.val 0), norm_nonneg (output.val 1),
      mul_nonneg (norm_nonneg (output.val 0)) (norm_nonneg (output.val 1))]
  change ‖output‖ ≤ _
  calc
    ‖output‖ ≤ ‖output.val 0‖ + ‖output.val 1‖ := triangle
    _ ≤ B * ‖field‖ + 2 * B * ‖field‖ := add_le_add firstOutput secondOutput
    _ = _ := by dsimp [B]; ring

theorem originalLowGraphEquivalence_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : originalLowGraph lower) :
    ‖originalLowGraphEquivalence parameters lower length positive lengthPositive bounded field‖ ≤
      (3 * originalLowFromAJConstant parameters length) * lower ^ (-(15 / 4 : ℝ)) * ‖field‖ :=
  originalLowWeight_bound parameters lower length positive lengthPositive bounded field

theorem originalLowGraphEquivalence_inverse_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : lowEnergyGraph lower length positive) :
    ‖(originalLowGraphEquivalence parameters lower length positive lengthPositive bounded).symm field‖ ≤
      (3 * originalLowToAJConstant parameters length) * lower⁻¹ * ‖field‖ :=
  originalLowUnweight_bound parameters lower length positive lengthPositive bounded field

end Grad.AnnularOriginalLow
