import MultiplierPhase

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Grad.Constraints.Multipliers

open Grad.ClosedJets Grad.CartesianState Grad.AnalyticWeights
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

theorem closedValueL2_pointwise_domination {dimension : ℕ}
    (first second : C(ClosedDisk, ComplexEuclidean dimension))
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ point : ClosedDisk, ‖first point‖ ≤ constant * ‖second point‖) :
    ‖closedContinuousToDiskL2 first‖ ≤ constant * ‖closedContinuousToDiskL2 second‖ := by
  calc
    _ ≤ ‖constant • closedContinuousToDiskL2 second‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [closedContinuousToDiskL2_ae first, closedContinuousToDiskL2_ae second,
        Lp.coeFn_smul constant (closedContinuousToDiskL2 second),
        ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point firstAt secondAt scaledAt pointIn
      rw [firstAt, scaledAt, Pi.smul_apply, secondAt, norm_smul, Real.norm_of_nonneg nonnegative]
      simpa only [closedDiskLift, openDiskMembershipClosed point pointIn, dite_true] using
        bound ⟨point, openDiskMembershipClosed point pointIn⟩
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg nonnegative]

theorem shifted_ratio_weight (parameters : PhaseParameters) (input shift : ℤ)
    (point : SpatialPlane) :
    weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input point *
      cartesianWeight parameters input point = cartesianWeight parameters (input + shift) point := by
  change (physicalWeight _ _ _ _ point * (physicalWeight _ _ _ input point)⁻¹) *
    physicalWeight _ _ _ input point = physicalWeight _ _ _ _ point
  rw [mul_assoc, inv_mul_cancel₀, mul_one]
  exact ne_of_gt (cartesianWeight_pos parameters input point)

theorem shifted_weighted_restriction {dimension : ℕ} (parameters : PhaseParameters)
    (input shift : ℤ) (field : ClosedJet dimension) :
    globalClosedJet
      (fun point => weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input point •
        smoothClosedExtension (phaseWeightedJet parameters input field) point)
      ((weightRatio_contDiff _ _ _ _ _).smul (smoothClosedExtension_smooth _)) =
      phaseWeightedJet parameters (input + shift) field := by
  apply globalClosedJet_eq_of_restriction
  intro point
  rw [smoothClosedExtension_value, phaseWeightedJet_spec, phaseWeightedJet_spec,
    smul_smul, shifted_ratio_weight]

def shiftedDerivativeTerm {dimension rank : ℕ} (parameters : PhaseParameters)
    (input shift : ℤ) (field : ClosedJet dimension) (word : CartesianWord rank)
    (selected : Finset (Fin rank)) : C(ClosedDisk, ComplexEuclidean dimension) where
  toFun point :=
    selectedDerivative word selected
      (weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input) point.val •
    closedDerivative (phaseWeightedJet parameters input field) selectedᶜ.card
      (subword word selectedᶜ) point
  continuous_toFun := by
    have tensorsContinuous : Continuous (fun point : ClosedDisk =>
        iteratedFDeriv ℝ selected.card
          (weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input) point.val) :=
      ((weightRatio_contDiff parameters.sigma0 parameters.gamma 1
      (input + shift) input).continuous_iteratedFDeriv
      (m := selected.card) (by exact_mod_cast le_top)).comp continuous_subtype_val
    have fieldContinuous := (closedDerivative (phaseWeightedJet parameters input field)
      selectedᶜ.card (subword word selectedᶜ)).continuous
    dsimp [selectedDerivative, orderedDerivative]
    fun_prop

theorem shifted_weighted_derivative {dimension rank : ℕ} (parameters : PhaseParameters)
    (input shift : ℤ) (field : ClosedJet dimension) (word : CartesianWord rank) :
    closedDerivative (phaseWeightedJet parameters (input + shift) field) rank word =
      ∑ selected : Finset (Fin rank), shiftedDerivativeTerm parameters input shift field word selected := by
  apply ContinuousMap.ext
  intro point
  rw [← shifted_weighted_restriction parameters input shift field, globalClosedJet_derivative,
    Grad.GaugeCoefficients.Radial.continuousMap_sum_apply]
  change orderedDerivative rank word
    (fun source => weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input source •
      smoothClosedExtension (phaseWeightedJet parameters input field) source) point.val = _
  have expansion := ordered_bilinear_at
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ComplexEuclidean dimension →L[ℝ] ComplexEuclidean dimension)
    (weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input)
    (smoothClosedExtension (phaseWeightedJet parameters input field)) point.val
    (weightRatio_contDiff _ _ _ _ _).contDiffAt
    (smoothClosedExtension_smooth _).contDiffAt rank word
  change orderedDerivative rank word
    (fun source => weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input source •
      smoothClosedExtension (phaseWeightedJet parameters input field) source) point.val =
      ∑ selected : Finset (Fin rank),
        selectedDerivative word selected (weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input) point.val •
        selectedDerivative word selectedᶜ (smoothClosedExtension (phaseWeightedJet parameters input field)) point.val at expansion
  rw [expansion]
  apply Finset.sum_congr rfl
  intro selected _
  change selectedDerivative word selected
    (weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input) point.val •
    cartesianDerivative selectedᶜ.card (subword word selectedᶜ)
      (smoothClosedExtension (phaseWeightedJet parameters input field)) point.val = _
  rw [smoothClosedExtension_derivative]
  rfl

theorem shiftedDerivativeTerm_L2_bound {dimension rank : ℕ} (parameters : PhaseParameters)
    (input shift : ℤ) (field : ClosedJet dimension) (word : CartesianWord rank)
    (selected : Finset (Fin rank)) :
    ‖closedContinuousToDiskL2 (shiftedDerivativeTerm parameters input shift field word selected)‖ ≤
      (ratioDerivativeConstant selected.card parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) *
        cellPolynomialWeight shift ^ selected.card * cellFrequency input ^ selected.card) *
      ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters input field)
        selectedᶜ.card (subword word selectedᶜ))‖ := by
  apply closedValueL2_pointwise_domination
  · exact mul_nonneg (mul_nonneg (mul_nonneg
      (ratioDerivativeConstant_nonnegative _ _ parameters.gamma_pos.le) (Real.exp_pos _).le)
      (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le shift)).le _))
      (pow_nonneg (cellFrequency_pos input).le _)
  · intro point
    change ‖selectedDerivative word selected
      (weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input) point.val •
      closedDerivative (phaseWeightedJet parameters input field) selectedᶜ.card
        (subword word selectedᶜ) point‖ ≤ _
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (orderedDerivative_norm_le selected.card (subword word selected) _ point.val).trans
      (shifted_ratio_derivative_le parameters input shift selected.card point)

end Grad.Constraints.Multipliers
