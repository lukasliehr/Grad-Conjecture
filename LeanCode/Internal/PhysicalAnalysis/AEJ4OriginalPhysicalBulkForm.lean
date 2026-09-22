import AEJ3ContinuousActualBulkForms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact) (power : ℕ)

/-- The actual eliminated weak form in the original all-mode r dr pairing,
with the reciprocal physical dual test and the same reconstructed (x,c,rV). -/
theorem currentHighBulkFormValue_originalPhysical
    (field test : annularEnergySpace lower L positive) :
    currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test =
      -(∑' mode : ℤ × ℤ, ∫ radius, (radius : ℂ) *
        inner ℂ (highDualTestCoefficient parameters power lower
          (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test) radius mode)
          (highTiltedRowCoefficient parameters power lower
            (eliminatedBulkAction parameters L compact lower positive bounded state power
              (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field)) radius mode)
        ∂volume.restrict (Icc lower 1)) := by
  unfold currentHighBulkFormValue
  rw [highBulk_originalPhysicalPairing parameters power lower positive]

theorem currentHighBulkFormValue_add_field
    (first second test : annularEnergySpace lower L positive) :
    currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power (first + second) test =
      currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power first test +
      currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power second test := by
  simp only [currentHighBulkFormValue, map_add, inner_add_right, neg_add_rev]
  abel

theorem currentHighBulkFormValue_smul_field (scalar : ℂ)
    (field test : annularEnergySpace lower L positive) :
    currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power (scalar • field) test =
      scalar * currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test := by
  simp only [currentHighBulkFormValue, map_smul, inner_smul_right, mul_neg]

theorem currentHighBulkFormValue_add_test
    (field first second : annularEnergySpace lower L positive) :
    currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field (first + second) =
      currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field first +
      currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field second := by
  simp only [currentHighBulkFormValue, map_add, inner_add_left, neg_add_rev]
  abel

theorem currentHighBulkFormValue_smul_test (scalar : ℂ)
    (field test : annularEnergySpace lower L positive) :
    currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field (scalar • test) =
      starRingEnd ℂ scalar * currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test := by
  simp only [currentHighBulkFormValue, map_smul, inner_smul_left, mul_neg]

/-- Base bulk action uses no extra tangential conjugation; its B7 error
is bounded by the same physical B8 used by the boundary contribution. -/
theorem highBulkErrorFormValue_base_bound
    (field test : annularEnergySpace lower L positive) :
    ‖highBulkErrorFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state 0 field test‖ ≤
      highBulkErrorConstant parameters L compact 0 * state.val.errorBudget 1 * ‖field‖ * ‖test‖ := by
  have budget : state.val.errorBudget 0 ≤ state.val.errorBudget 1 :=
    Grad.GaugeCoefficients.Physical.Allocation.physicalBudget_monotone parameters
      state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num)
  exact (highBulkErrorFormValue_bound parameters L compact lower positive bounded lengthPositive widthHalf widthLength state 0 field test).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left budget (highBulkErrorConstant_nonnegative parameters L compact 0))
      (norm_nonneg field)) (norm_nonneg test))

/-- The base physical B8 perturbation constant is independent of the positive
inner radius and is attached to the SAME current-minus-circle form. -/
theorem currentHighBulkFormValue_difference_B8 (parameters : PhaseParameters) (L compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
      (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
      (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
      (state : RetainedInverseState parameters L compact)
      (field test : annularEnergySpace lower L positive),
    ‖currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state 0 field test -
      circularHighBulkFormValue parameters L lower positive bounded lengthPositive widthHalf widthLength 0 field test‖ ≤
      constant * Grad.GaugeCoefficients.Physical.Allocation.physicalBudget parameters
        state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ * ‖test‖ := by
  refine ⟨highBulkErrorConstant parameters L compact 0,
    highBulkErrorConstant_nonnegative parameters L compact 0, ?_⟩
  intro lower positive bounded lengthPositive widthHalf widthLength state field test
  rw [← highBulkErrorFormValue_eq_sub]
  exact highBulkErrorFormValue_base_bound parameters L compact lower positive bounded lengthPositive widthHalf widthLength state field test

end Grad.AnnularCurrentEnergy
