import GC12PowerSlots

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra

/-- The slot which carries the full AP8 weight of a fixed Cartesian
derivative coordinate. -/
def topRegularitySlot {grade : ℕ} (index : DerivativeIndex grade) :
    RegularitySlot grade := by
  have orderLe : derivativeOrder index ≤ grade := index.2
  exact ⟨index.1.1, index.1.2,
    ⟨grade - derivativeOrder index, by omega⟩, by
      change derivativeOrder index + (grade - derivativeOrder index) ≤ grade
      omega⟩

@[simp] theorem slotDerivativeIndex_top {grade : ℕ}
    (index : DerivativeIndex grade) :
    slotDerivativeIndex (topRegularitySlot index) = index := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

@[simp] theorem slotOrder_top {grade : ℕ} (index : DerivativeIndex grade) :
    slotOrder (topRegularitySlot index) = grade := by
  have orderLe : derivativeOrder index ≤ grade := index.2
  change derivativeOrder index + (grade - derivativeOrder index) = grade
  omega

@[simp] theorem slotGap_top {grade : ℕ} (index : DerivativeIndex grade) :
    slotGap (topRegularitySlot index) = 0 := by
  simp [slotGap]

theorem slotCoordinate_top {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (index : DerivativeIndex grade) (cell : ℤ) :
    slotCoordinate coefficient (topRegularitySlot index) cell =
      weightedDerivative coefficient cell index := by
  unfold slotCoordinate
  rw [slotGap_top, slotDerivativeIndex_top]
  simp

theorem slotNorm_top {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    slotNorm coefficient (topRegularitySlot index) =
      ∑' cell : ℤ, ‖weightedDerivative coefficient cell index‖ := by
  unfold slotNorm
  simp_rw [slotCoordinate_top]

theorem coefficient_norm_eq_sum_topSlots {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension) :
    ‖coefficient‖ = ∑ index : DerivativeIndex grade,
      slotNorm coefficient (topRegularitySlot index) := by
  rw [coefficient_norm_formula]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro index _membership
    exact (slotNorm_top coefficient index).symm
  · intro index _membership
    exact coordinate_norm_summable coefficient.1 index

theorem gradedCoefficientPower_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1) :
    Summable (fun power =>
      ‖gradedCoefficientPower admissible gradedCoefficient power‖) := by
  have slotSumSummable : Summable (fun power =>
      ∑ index : DerivativeIndex grade,
        slotNorm (gradedCoefficientPower admissible gradedCoefficient power)
          (topRegularitySlot index)) := by
    apply summable_sum
    intro index _membership
    exact gradedCoefficientPower_slotNorm_summable admissible positive
      baseCoefficient gradedCoefficient theta realizes normBound thetaLt
      (topRegularitySlot index)
  exact slotSumSummable.congr fun power =>
    (coefficient_norm_eq_sum_topSlots
      (gradedCoefficientPower admissible gradedCoefficient power)).symm

theorem gradedCoefficientPower_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (positive : 0 < dimension)
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (theta : ℝ)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient)
    (normBound : ‖baseCoefficient‖ ≤ theta) (thetaLt : theta < 1) :
    Summable (gradedCoefficientPower admissible gradedCoefficient) :=
  (gradedCoefficientPower_norm_summable admissible positive baseCoefficient
    gradedCoefficient theta realizes normBound thetaLt).of_norm

end Grad.GaugeCoefficients.Neumann.Regularity
