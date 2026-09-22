import ASX4OriginalDilationPhase

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.ActualExceptionalInverse

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus Grad.NonlinearRadial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope

theorem originalDilationMultiplier_weight (sigma gamma ell : ℝ) (cell : ℤ) (scale : ℝ)
    (point : SpatialPlane) :
    originalDilationMultiplier sigma gamma ell cell scale point * physicalWeight sigma gamma ell cell (scale • point) =
      physicalWeight sigma gamma ell cell point := by
  rw [originalDilationMultiplier, physicalWeight_exp, physicalWeight_exp, ← Real.exp_add]
  congr 1
  unfold originalDilationDefect
  ring

def originalWeightedDilationSmooth {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (scale : ℝ) (field : ClosedJet dimension) (point : SpatialPlane) : ComplexEuclidean dimension :=
  originalDilationMultiplier sigma gamma ell cell scale point •
    smoothClosedExtension (apWeightedJet sigma gamma ell cell field) (scale • point)

theorem originalWeightedDilationSmooth_smooth {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (scale : ℝ) (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (originalWeightedDilationSmooth sigma gamma ell cell scale field) :=
  (originalDilationMultiplier_smooth sigma gamma ell cell scale).smul
    ((smoothClosedExtension_smooth _).comp (dilationLinear scale).contDiff)

theorem originalWeightedDilationSmooth_restricts {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension) :
    globalClosedJet (originalWeightedDilationSmooth sigma gamma ell cell scale field)
        (originalWeightedDilationSmooth_smooth sigma gamma ell cell scale field) =
      apWeightedJet sigma gamma ell cell (dilationJet scale field) := by
  apply globalClosedJet_eq_of_restriction
  intro point
  change originalDilationMultiplier sigma gamma ell cell scale point.val •
    smoothClosedExtension (apWeightedJet sigma gamma ell cell field)
      (dilationPoint scale nonnegative bounded point).val = _
  rw [smoothClosedExtension_value, apWeightedJet_value, apWeightedJet_value,
    dilationJet_value_closed nonnegative bounded, smul_smul]
  exact congrArg (fun value => value • field.value (dilationPoint scale nonnegative bounded point))
    (originalDilationMultiplier_weight sigma gamma ell cell scale point.val)

theorem originalWeightedDilation_derivative {dimension rank : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (word : CartesianWord rank) (point : ClosedDisk) :
    closedDerivative (apWeightedJet sigma gamma ell cell (dilationJet scale field)) rank word point =
      ∑ selected : Finset (Fin rank),
        selectedDerivative word selected (originalDilationMultiplier sigma gamma ell cell scale) point.val •
          (scale ^ selectedᶜ.card • closedDerivative (apWeightedJet sigma gamma ell cell field)
            selectedᶜ.card (subword word selectedᶜ) (dilationPoint scale nonnegative bounded point)) := by
  rw [← originalWeightedDilationSmooth_restricts sigma gamma ell cell nonnegative bounded field,
    globalClosedJet_derivative]
  change orderedDerivative rank word (originalWeightedDilationSmooth sigma gamma ell cell scale field) point.val = _
  have expansion := ordered_bilinear_at
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ComplexEuclidean dimension →L[ℝ] ComplexEuclidean dimension)
    (originalDilationMultiplier sigma gamma ell cell scale)
    (fun source => smoothClosedExtension (apWeightedJet sigma gamma ell cell field) (scale • source))
    point.val (originalDilationMultiplier_smooth sigma gamma ell cell scale).contDiffAt
    (((smoothClosedExtension_smooth _).comp (dilationLinear scale).contDiff).contDiffAt) rank word
  change orderedDerivative rank word (originalWeightedDilationSmooth sigma gamma ell cell scale field) point.val =
    ∑ selected : Finset (Fin rank),
      selectedDerivative word selected (originalDilationMultiplier sigma gamma ell cell scale) point.val •
        selectedDerivative word selectedᶜ
          (fun source => smoothClosedExtension (apWeightedJet sigma gamma ell cell field) (scale • source)) point.val at expansion
  rw [expansion]
  apply Finset.sum_congr rfl
  intro selected _
  congr 1
  change cartesianDerivative selectedᶜ.card (subword word selectedᶜ)
    (fun source => smoothClosedExtension (apWeightedJet sigma gamma ell cell field) (scale • source)) point.val = _
  rw [cartesianDerivative_dilation scale _ (smoothClosedExtension_smooth _)]
  exact congrArg (fun value => scale ^ selectedᶜ.card • value)
    (smoothClosedExtension_derivative _ _ (dilationPoint scale nonnegative bounded point))

theorem originalWeightedDilation_point_bound {dimension rank : ℕ} {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (cell : ℤ)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (word : CartesianWord rank) (point : ClosedDisk) :
    ‖closedDerivative (apWeightedJet sigma gamma ell cell (dilationJet scale field)) rank word point‖ ≤
      ∑ selected : Finset (Fin rank),
        (originalDilationConstant L gamma selected.card * scaledCellWeight L ell cell ^ selected.card) *
          ‖closedDerivative (apWeightedJet sigma gamma ell cell field)
            selectedᶜ.card (subword word selectedᶜ) (dilationPoint scale nonnegative bounded point)‖ := by
  rw [originalWeightedDilation_derivative sigma gamma ell cell nonnegative bounded]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro selected _
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg nonnegative _)]
  apply mul_le_mul
  · exact (orderedDerivative_norm_le selected.card (subword word selected) _ point.val).trans
      (originalDilationMultiplier_iterated_bound admissible cell nonnegative bounded selected.card point.val)
  · exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ nonnegative bounded)
  · exact mul_nonneg (pow_nonneg nonnegative _) (norm_nonneg _)
  · exact mul_nonneg (originalDilationConstant_nonnegative admissible _) (pow_nonneg (scaledCellWeight_nonnegative L ell _) _)

theorem originalWeightedDilation_L2_bound {dimension rank : ℕ} {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (cell : ℤ)
    {scale : ℝ} (positive : 0 < scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2
      (closedDerivative (apWeightedJet sigma gamma ell cell (dilationJet scale field)) rank word)‖ ≤
      ∑ selected : Finset (Fin rank),
        (originalDilationConstant L gamma selected.card * scaledCellWeight L ell cell ^ selected.card) *
          (scale⁻¹ * ‖closedContinuousToDiskL2 (closedDerivative (apWeightedJet sigma gamma ell cell field)
            selectedᶜ.card (subword word selectedᶜ))‖) := by
  apply (closedDiskL2_norm_le_finite_majorant _
    (fun selected : Finset (Fin rank) =>
      (closedDerivative (apWeightedJet sigma gamma ell cell field) selectedᶜ.card
        (subword word selectedᶜ)).comp (dilationClosedMap scale positive.le bounded))
    (fun selected => originalDilationConstant L gamma selected.card * scaledCellWeight L ell cell ^ selected.card)
    (fun selected => mul_nonneg (originalDilationConstant_nonnegative admissible _) (pow_nonneg (scaledCellWeight_nonnegative L ell _) _))
    (originalWeightedDilation_point_bound admissible cell positive.le bounded field word)).trans
  exact Finset.sum_le_sum (fun selected _ => mul_le_mul_of_nonneg_left
    (closedValueL2_dilation_bound positive bounded _)
    (mul_nonneg (originalDilationConstant_nonnegative admissible _) (pow_nonneg (scaledCellWeight_nonnegative L ell _) _)))

end Grad.ActualExceptionalInverse
