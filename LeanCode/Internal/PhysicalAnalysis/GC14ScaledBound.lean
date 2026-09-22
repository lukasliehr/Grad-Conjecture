import GC14ScaledJet

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set
open scoped BigOperators ContDiff Topology

namespace Grad.GaugeCoefficients.Physical

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

theorem originalEnvelope_scaledDerivative_bound
    {dimension inputDimension outputDimension : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ClosedJet dimension) (cell : ℤ) (index : CartesianMultiIndex) (point : ClosedDisk) :
    originalEnvelope parameters.sigma0 parameters.gamma ell cell point.val *
        ‖smoothOperatorDerivative (scaledOriginalJet ell mapping field) index point‖ ≤
      ‖mapping‖ * ‖phaseOutsideClosedDerivative parameters cell field
        (cartesianOrder index) (cartesianMultiIndexWord index)‖ := by
  have ellPositive := admissible.2.2.2.1
  have ellLe : ell ≤ 1 := admissible.2.2.2.2.trans (min_le_left _ _)
  have envelopePositive : 0 ≤ originalEnvelope parameters.sigma0 parameters.gamma ell
      cell point.val := (Real.exp_pos _).le
  have weightPositive := cartesianWeight_pos parameters cell (radialPoint ell point).val
  have envelopeLe := (envelopeGoal L parameters.sigma0 parameters.gamma ell admissible
    cell point.val (by simpa [closedDisk, closedUnitDisk, Metric.mem_closedBall, dist_zero_right]
      using point.property)).2.1
  rw [originalWeight_scaledPoint ellPositive.le ellLe] at envelopeLe
  rw [scaledOriginalJet_derivative ellPositive.le ellLe,
    norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ellPositive.le]
  calc
    _ ≤ originalEnvelope parameters.sigma0 parameters.gamma ell cell point.val *
        (1 * (‖mapping‖ * ‖closedMultiDerivative field index (radialPoint ell point)‖)) := by
      apply mul_le_mul_of_nonneg_left _ envelopePositive
      exact mul_le_mul (pow_le_one₀ ellPositive.le ellLe)
        (mapping.le_opNorm _) (norm_nonneg _) zero_le_one
    _ ≤ cartesianWeight parameters cell (radialPoint ell point).val *
        (‖mapping‖ * ‖closedMultiDerivative field index (radialPoint ell point)‖) := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right envelopeLe
        (mul_nonneg (norm_nonneg mapping) (norm_nonneg
          (closedMultiDerivative field index (radialPoint ell point))))
    _ = ‖mapping‖ * ‖phaseOutsideClosedDerivative parameters cell field
        (cartesianOrder index) (cartesianMultiIndexWord index) (radialPoint ell point)‖ := by
      change _ = ‖mapping‖ * ‖cartesianWeight parameters cell (radialPoint ell point).val •
        closedMultiDerivative field index (radialPoint ell point)‖
      rw [norm_smul, Real.norm_of_nonneg weightPositive.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _)
      (norm_nonneg mapping)

theorem scaledOriginalJet_weightedDerivative_bound
    {dimension inputDimension outputDimension grade : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ClosedJet dimension) (cell : ℤ) (index : DerivativeIndex grade) :
    ‖weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell grade cell
        (scaledOriginalJet ell mapping field) index‖ ≤
      ‖mapping‖ * (cellFrequency cell ^ (grade - derivativeOrder index) *
        ‖phaseOutsideClosedDerivative parameters cell field (derivativeOrder index)
          (derivativeWord index)‖) := by
  have frequencyNonnegative := (cellFrequency_pos cell).le
  have scaleNonnegative : 0 ≤ scaledCellWeight L ell cell := Real.sqrt_nonneg _
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro point
  change ‖(coefficientScale L parameters.sigma0 parameters.gamma ell grade cell index point : ℂ) •
    smoothOperatorDerivative (scaledOriginalJet ell mapping field)
      (derivativeMultiIndex index) point‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg
    (coefficientScale_pos L parameters.sigma0 parameters.gamma ell grade cell index point).le]
  unfold coefficientScale
  calc
    _ = scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
        (originalEnvelope parameters.sigma0 parameters.gamma ell cell point.val *
          ‖smoothOperatorDerivative (scaledOriginalJet ell mapping field)
            (derivativeMultiIndex index) point‖) := by ring
    _ ≤ cellFrequency cell ^ (grade - derivativeOrder index) *
        (‖mapping‖ * ‖phaseOutsideClosedDerivative parameters cell field
          (derivativeOrder index) (derivativeWord index)‖) := by
      apply mul_le_mul
        (pow_le_pow_left₀ scaleNonnegative (scaledCellWeight_le_frequency admissible cell) _)
        (originalEnvelope_scaledDerivative_bound parameters admissible mapping field
          cell (derivativeMultiIndex index) point)
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        (pow_nonneg frequencyNonnegative _)
    _ = _ := by ring

theorem scaledOriginalJet_weightedDerivative_summable
    {dimension inputDimension outputDimension grade : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (index : DerivativeIndex grade) :
    Summable (fun cell : ℤ => ‖weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell
      grade cell (scaledOriginalJet ell mapping (field.1 cell)) index‖) := by
  apply Summable.of_nonneg_of_le
    (fun cell => norm_nonneg (weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell
      grade cell (scaledOriginalJet ell mapping (field.1 cell)) index))
    (fun cell => scaledOriginalJet_weightedDerivative_bound parameters admissible mapping
      (field.1 cell) cell index)
  exact (phaseOutsideClosedDerivative_frequency_summable parameters field
    (derivativeWord index) (grade - derivativeOrder index)).mul_left ‖mapping‖

theorem scaledOriginalJet_weightedDerivative_tsum_bound
    {dimension inputDimension outputDimension grade : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : GradeCore parameters dimension (grade + 3)) (index : DerivativeIndex grade) :
    ∑' cell : ℤ, ‖weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell
        grade cell (scaledOriginalJet ell mapping (field.toCore.1 cell)) index‖ ≤
      ‖mapping‖ * (originalDerivativeSumConstant parameters (derivativeOrder index) * ‖field‖) := by
  calc
    _ ≤ ∑' cell : ℤ, ‖mapping‖ *
        (cellFrequency cell ^ (grade - derivativeOrder index) *
          ‖phaseOutsideClosedDerivative parameters cell (field.toCore.1 cell)
            (derivativeOrder index) (derivativeWord index)‖) :=
      (scaledOriginalJet_weightedDerivative_summable parameters admissible mapping
        field.toCore index).tsum_le_tsum
          (fun cell => scaledOriginalJet_weightedDerivative_bound parameters admissible
            mapping (field.toCore.1 cell) cell index)
          ((phaseOutsideClosedDerivative_frequency_summable parameters field.toCore
            (derivativeWord index) (grade - derivativeOrder index)).mul_left ‖mapping‖)
    _ = ‖mapping‖ * ∑' cell : ℤ,
        cellFrequency cell ^ (grade - derivativeOrder index) *
          ‖phaseOutsideClosedDerivative parameters cell (field.toCore.1 cell)
            (derivativeOrder index) (derivativeWord index)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (phaseOutsideClosedDerivative_frequency_tsum_bound parameters field
        (derivativeWord index) (grade - derivativeOrder index)
        (by have indexLe : derivativeOrder index ≤ grade := index.2
            change derivativeOrder index + (grade - derivativeOrder index) ≤ grade
            omega)) (norm_nonneg mapping)

end Grad.GaugeCoefficients.Physical
