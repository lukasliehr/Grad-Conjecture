import ASX6OriginalPowerIntegral

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.AnalyticWeights.Higher Grad.ActualCenterVolterra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra

def originalWordCellBound {dimension rank : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) (word : CartesianWord rank) : ℝ :=
  ∑ selected : Finset (Fin rank),
    (originalDilationConstant L gamma selected.card * scaledCellWeight L ell cell ^ selected.card) *
      ‖closedContinuousToDiskL2 (closedDerivative (apWeightedJet sigma gamma ell cell field)
        selectedᶜ.card (subword word selectedᶜ))‖

theorem originalWordCellBound_nonnegative {dimension rank : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (field : ClosedJet dimension) (word : CartesianWord rank) :
    0 ≤ originalWordCellBound L sigma gamma ell cell field word :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg
    (mul_nonneg (originalDilationConstant_nonnegative admissible _) (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _))
    (norm_nonneg _))

theorem originalPowerDerivativeFamily_L2_bound {dimension rank : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (power : ℕ)
    (field : ClosedJet dimension) (word : CartesianWord rank) {scale : ℝ}
    (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) :
    ‖closedContinuousToDiskL2 (originalPowerDerivativeFamily sigma gamma ell cell (power + 1) field word scale)‖ ≤
      originalWordCellBound L sigma gamma ell cell field word := by
  rw [originalPowerDerivativeFamily, closedValueL2_real_smul, norm_smul]
  by_cases zeroScale : scale = 0
  · simp only [zeroScale, zero_pow (by omega : power + 1 ≠ 0), norm_zero, zero_mul]
    exact originalWordCellBound_nonnegative admissible cell field word
  · have positive : 0 < scale := lt_of_le_of_ne nonnegative (Ne.symm zeroScale)
    rw [Real.norm_of_nonneg (pow_nonneg nonnegative _)]
    apply (mul_le_mul_of_nonneg_left (originalWeightedDilation_L2_bound admissible cell positive bounded field word)
      (pow_nonneg nonnegative (power + 1))).trans
    have sumEquality :
        (∑ selected : Finset (Fin rank),
          (originalDilationConstant L gamma selected.card * scaledCellWeight L ell cell ^ selected.card) *
            (scale⁻¹ * ‖closedContinuousToDiskL2 (closedDerivative (apWeightedJet sigma gamma ell cell field)
              selectedᶜ.card (subword word selectedᶜ))‖)) =
        scale⁻¹ * originalWordCellBound L sigma gamma ell cell field word := by
      rw [originalWordCellBound, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro selected _
      ring
    rw [sumEquality, ← mul_assoc]
    have coefficient : scale ^ (power + 1) * scale⁻¹ = scale ^ power := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ zeroScale, mul_one]
    rw [coefficient]
    exact mul_le_of_le_one_left (originalWordCellBound_nonnegative admissible cell field word)
      (pow_le_one₀ nonnegative bounded)

theorem originalPower_L2_bound {dimension rank : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (power : ℕ)
    (field : ClosedJet dimension) (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2 (closedDerivative
      (apWeightedJet sigma gamma ell cell (powerDilationJet (power + 1) field)) rank word)‖ ≤
      originalWordCellBound L sigma gamma ell cell field word := by
  have familyContinuous := originalPowerDerivativeFamily_continuous sigma gamma ell cell (power + 1) field word
  have imageContinuous := (closedValueL2Continuous dimension).continuous.comp familyContinuous
  rw [originalPower_weighted_derivative_map,
    closedValueL2_integral familyContinuous.continuousOn.integrableOn_Icc]
  calc
    _ ≤ ∫ scale in Icc (0 : ℝ) 1,
        ‖closedContinuousToDiskL2 (originalPowerDerivativeFamily sigma gamma ell cell (power + 1) field word scale)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _scale in Icc (0 : ℝ) 1, originalWordCellBound L sigma gamma ell cell field word := by
      apply integral_mono_ae imageContinuous.norm.continuousOn.integrableOn_Icc
        continuous_const.continuousOn.integrableOn_Icc
      filter_upwards [ae_restrict_mem measurableSet_Icc] with scale scaleIn
      exact originalPowerDerivativeFamily_L2_bound admissible cell power field word scaleIn.1 scaleIn.2
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_const]
      simp

def originalDilationWordConstant (L gamma : ℝ) (rank : ℕ) : ℝ :=
  ∑ selected : Finset (Fin rank), originalDilationConstant L gamma selected.card

theorem originalDilationWordConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) : 0 ≤ originalDilationWordConstant L gamma rank :=
  Finset.sum_nonneg (fun _ _ => originalDilationConstant_nonnegative admissible _)

theorem originalWordCellBound_scaled {dimension rank grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (field : ClosedJet dimension)
    (word : CartesianWord rank) (rankBound : rank ≤ grade) :
    scaledCellWeight L ell cell ^ (grade - rank) * originalWordCellBound L sigma gamma ell cell field word ≤
      originalDilationWordConstant L gamma rank * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  rw [originalWordCellBound, originalDilationWordConstant, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro selected _
  have complement : selected.card + selectedᶜ.card = rank := by
    have equality := selected.card_add_card_compl
    simpa only [Fintype.card_fin] using equality
  have cardBound : selectedᶜ.card ≤ grade := by omega
  have power : grade - selectedᶜ.card = grade - rank + selected.card := by omega
  have term := mul_le_mul_of_nonneg_left
    (apWeighted_word_bound L sigma gamma ell cell field cardBound (subword word selectedᶜ))
    (originalDilationConstant_nonnegative admissible selected.card)
  rw [power, pow_add] at term
  convert term using 1
  ring

def originalPowerRowConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (DerivativeIndex grade)) *
    ∑ index : DerivativeIndex grade, originalDilationWordConstant L gamma (derivativeOrder index)

theorem originalPowerRow_bound {dimension grade : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (cell : ℤ) (power : ℕ) (field : ClosedJet dimension) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (powerDilationJet (power + 1) field)‖ ≤
      originalPowerRowConstant L gamma grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have nonnegative (index : DerivativeIndex grade) : 0 ≤ originalDilationWordConstant L gamma (derivativeOrder index) :=
    originalDilationWordConstant_nonnegative admissible _
  have bound := apRow_norm_bound_of_coordinates
    (apRowLinear (grade := grade) L sigma gamma ell cell (powerDilationJet (power + 1) field))
    ((∑ index : DerivativeIndex grade, originalDilationWordConstant L gamma (derivativeOrder index)) *
      ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖)
    (mul_nonneg (Finset.sum_nonneg (fun index _ => nonnegative index)) (norm_nonneg _))
  have coordinateBound : ∀ index : DerivativeIndex grade,
      ‖apRowLinear (grade := grade) L sigma gamma ell cell (powerDilationJet (power + 1) field) index‖ ≤
        (∑ index : DerivativeIndex grade, originalDilationWordConstant L gamma (derivativeOrder index)) *
          ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
    intro index
    rw [apRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (scaledCellWeight_nonnegative L ell cell)]
    change scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
      ‖closedContinuousToDiskL2 (closedMultiDerivative _ (derivativeMultiIndex index))‖ ≤ _
    have integral := originalPower_L2_bound admissible cell power field (apIndexWord index)
    have scaled := (mul_le_mul_of_nonneg_left integral (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _)).trans
      (originalWordCellBound_scaled admissible cell field (apIndexWord index) index.property)
    apply scaled.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Finset.single_le_sum (fun other _ => nonnegative other) (Finset.mem_univ index)
  apply (bound coordinateBound).trans_eq
  unfold originalPowerRowConstant
  ring

end Grad.ActualExceptionalInverse
