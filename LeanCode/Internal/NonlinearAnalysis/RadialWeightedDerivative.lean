import RadialDilationPhase
import RadialDilationL2
import AW3Leibniz

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.AnalyticWeights.Higher

theorem dilationMultiplier_weight (parameters : PhaseParameters) (cell : ℤ) (scale : ℝ)
    (point : SpatialPlane) :
    dilationMultiplier parameters cell scale point * cartesianWeight parameters cell (scale • point) =
      cartesianWeight parameters cell point := by
  rw [dilationMultiplier, cartesianWeight_exp, cartesianWeight_exp, ← Real.exp_add]
  congr 1
  unfold dilationPhaseDefect
  ring

def weightedDilationSmooth {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (scale : ℝ) (field : ClosedJet dimension) (point : SpatialPlane) : ComplexEuclidean dimension :=
  dilationMultiplier parameters cell scale point •
    smoothClosedExtension (phaseWeightedJet parameters cell field) (scale • point)

theorem weightedDilationSmooth_smooth {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (scale : ℝ) (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (weightedDilationSmooth parameters cell scale field) :=
  (dilationMultiplier_smooth parameters cell scale).smul
    ((smoothClosedExtension_smooth _).comp (dilationLinear scale).contDiff)

theorem weightedDilationSmooth_restricts {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension) :
    globalClosedJet (weightedDilationSmooth parameters cell scale field)
        (weightedDilationSmooth_smooth parameters cell scale field) =
      phaseWeightedJet parameters cell (dilationJet scale field) := by
  apply globalClosedJet_eq_of_restriction
  intro point
  change dilationMultiplier parameters cell scale point.val •
    smoothClosedExtension (phaseWeightedJet parameters cell field)
      (dilationPoint scale nonnegative bounded point).val = _
  rw [smoothClosedExtension_value, phaseWeightedJet_spec, phaseWeightedJet_spec,
    dilationJet_value_closed nonnegative bounded, smul_smul]
  exact congrArg (fun value => value • field.value (dilationPoint scale nonnegative bounded point))
    (dilationMultiplier_weight parameters cell scale point.val)

theorem weightedDilation_derivative {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (word : CartesianWord rank) (point : ClosedDisk) :
    closedDerivative (phaseWeightedJet parameters cell (dilationJet scale field)) rank word point =
      ∑ selected : Finset (Fin rank),
        selectedDerivative word selected (dilationMultiplier parameters cell scale) point.val •
          (scale ^ selectedᶜ.card • closedDerivative (phaseWeightedJet parameters cell field)
            selectedᶜ.card (subword word selectedᶜ) (dilationPoint scale nonnegative bounded point)) := by
  rw [← weightedDilationSmooth_restricts parameters cell nonnegative bounded field,
    globalClosedJet_derivative]
  change orderedDerivative rank word (weightedDilationSmooth parameters cell scale field) point.val = _
  have expansion := ordered_bilinear_at
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ComplexEuclidean dimension →L[ℝ] ComplexEuclidean dimension)
    (dilationMultiplier parameters cell scale)
    (fun source => smoothClosedExtension (phaseWeightedJet parameters cell field) (scale • source))
    point.val (dilationMultiplier_smooth parameters cell scale).contDiffAt
    (((smoothClosedExtension_smooth _).comp (dilationLinear scale).contDiff).contDiffAt) rank word
  change orderedDerivative rank word (weightedDilationSmooth parameters cell scale field) point.val =
    ∑ selected : Finset (Fin rank),
      selectedDerivative word selected (dilationMultiplier parameters cell scale) point.val •
        selectedDerivative word selectedᶜ
          (fun source => smoothClosedExtension (phaseWeightedJet parameters cell field) (scale • source)) point.val at expansion
  rw [expansion]
  apply Finset.sum_congr rfl
  intro selected _
  congr 1
  change cartesianDerivative selectedᶜ.card (subword word selectedᶜ)
    (fun source => smoothClosedExtension (phaseWeightedJet parameters cell field) (scale • source)) point.val = _
  rw [cartesianDerivative_dilation scale _ (smoothClosedExtension_smooth _)]
  exact congrArg (fun value => scale ^ selectedᶜ.card • value)
    (smoothClosedExtension_derivative _ _ (dilationPoint scale nonnegative bounded point))

theorem weightedDilation_point_bound {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (word : CartesianWord rank) (point : ClosedDisk) :
    ‖closedDerivative (phaseWeightedJet parameters cell (dilationJet scale field)) rank word point‖ ≤
      ∑ selected : Finset (Fin rank),
        (dilationDerivativeConstant selected.card * cellFrequency cell ^ selected.card) *
          ‖closedDerivative (phaseWeightedJet parameters cell field)
            selectedᶜ.card (subword word selectedᶜ) (dilationPoint scale nonnegative bounded point)‖ := by
  rw [weightedDilation_derivative parameters cell nonnegative bounded]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro selected _
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg nonnegative _)]
  apply mul_le_mul
  · exact (orderedDerivative_norm_le selected.card (subword word selected) _ point.val).trans
      (dilationMultiplier_iterated_bound parameters cell nonnegative bounded selected.card point.val)
  · exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ nonnegative bounded)
  · exact mul_nonneg (pow_nonneg nonnegative _) (norm_nonneg _)
  · exact mul_nonneg (dilationDerivativeConstant_nonnegative _) (pow_nonneg (cellFrequency_pos _).le _)

theorem weightedDilation_L2_bound {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    {scale : ℝ} (positive : 0 < scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2
      (closedDerivative (phaseWeightedJet parameters cell (dilationJet scale field)) rank word)‖ ≤
      ∑ selected : Finset (Fin rank),
        (dilationDerivativeConstant selected.card * cellFrequency cell ^ selected.card) *
          (scale⁻¹ * ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell field)
            selectedᶜ.card (subword word selectedᶜ))‖) := by
  apply (closedDiskL2_norm_le_finite_majorant _
    (fun selected : Finset (Fin rank) =>
      (closedDerivative (phaseWeightedJet parameters cell field) selectedᶜ.card
        (subword word selectedᶜ)).comp (dilationClosedMap scale positive.le bounded))
    (fun selected => dilationDerivativeConstant selected.card * cellFrequency cell ^ selected.card)
    (fun selected => mul_nonneg (dilationDerivativeConstant_nonnegative _) (pow_nonneg (cellFrequency_pos _).le _))
    (weightedDilation_point_bound parameters cell positive.le bounded field word)).trans
  exact Finset.sum_le_sum (fun selected _ => mul_le_mul_of_nonneg_left
    (closedValueL2_dilation_bound positive bounded _)
    (mul_nonneg (dilationDerivativeConstant_nonnegative _) (pow_nonneg (cellFrequency_pos _).le _)))

end Grad.NonlinearRadial
