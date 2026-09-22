import RadialIntegralJet
import RadialLogIntegral
import RadialDilationCore

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.AnalyticWeights.Higher

def radialWordCellBound {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord rank) : ℝ :=
  ∑ selected : Finset (Fin rank),
    (dilationDerivativeConstant selected.card * cellFrequency cell ^ selected.card) *
      ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell field)
        selectedᶜ.card (subword word selectedᶜ))‖

theorem radialWordCellBound_nonnegative {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord rank) :
    0 ≤ radialWordCellBound parameters cell field word :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg
    (mul_nonneg (dilationDerivativeConstant_nonnegative _) (pow_nonneg (cellFrequency_pos cell).le _))
    (norm_nonneg _))

theorem weightedDilationDerivativeFamily_L2_bound {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord rank) {scale : ℝ}
    (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) :
    ‖closedContinuousToDiskL2 (weightedDilationDerivativeFamily parameters cell field word scale)‖ ≤
      (-Real.log scale) * radialWordCellBound parameters cell field word := by
  rw [weightedDilationDerivativeFamily, closedValueL2_real_smul, norm_smul]
  by_cases zeroScale : scale = 0
  · simp [zeroScale, Real.negMulLog]
  · have positive : 0 < scale := lt_of_le_of_ne nonnegative (Ne.symm zeroScale)
    rw [Real.norm_of_nonneg (Real.negMulLog_nonneg nonnegative bounded)]
    apply (mul_le_mul_of_nonneg_left (weightedDilation_L2_bound parameters cell positive bounded field word)
      (Real.negMulLog_nonneg nonnegative bounded)).trans_eq
    have sumEquality :
        (∑ selected : Finset (Fin rank),
          (dilationDerivativeConstant selected.card * cellFrequency cell ^ selected.card) *
            (scale⁻¹ * ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell field)
              selectedᶜ.card (subword word selectedᶜ))‖)) =
        scale⁻¹ * radialWordCellBound parameters cell field word := by
      rw [radialWordCellBound, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro selected _
      ring
    rw [sumEquality, ← mul_assoc, negMulLog_mul_inverse]

theorem radialIntervalJet_L2_bound {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    {lower upper : ℝ} (lowerNonnegative : 0 ≤ lower) (upperBounded : upper ≤ 1)
    (field : ClosedJet dimension) (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2 (closedDerivative
      (phaseWeightedJet parameters cell (radialIntervalJet lower upper field)) rank word)‖ ≤
      logarithmicMass lower upper * radialWordCellBound parameters cell field word := by
  have familyContinuous := weightedDilationDerivativeFamily_continuous parameters cell field word
  have imageContinuous := (closedValueL2Continuous dimension).continuous.comp familyContinuous
  rw [radialIntervalJet_weighted_derivative_map,
    closedValueL2_integral familyContinuous.continuousOn.integrableOn_Icc]
  calc
    _ ≤ ∫ scale in Icc lower upper,
        ‖closedContinuousToDiskL2 (weightedDilationDerivativeFamily parameters cell field word scale)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ scale in Icc lower upper,
        (-Real.log scale) * radialWordCellBound parameters cell field word := by
      apply integral_mono_ae imageContinuous.norm.continuousOn.integrableOn_Icc
        ((negativeLog_integrable lower upper).mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with scale scaleIn
      exact weightedDilationDerivativeFamily_L2_bound parameters cell field word
        (lowerNonnegative.trans scaleIn.1) (scaleIn.2.trans upperBounded)
    _ = _ := by rw [integral_mul_const]; rfl

end Grad.NonlinearRadial
