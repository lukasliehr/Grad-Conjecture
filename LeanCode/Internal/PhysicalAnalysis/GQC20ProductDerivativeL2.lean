import GQC19PhaseGradient

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

theorem apProductJet_derivativeL2 {input output grade : ℕ}
    (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) (index : DerivativeIndex grade) :
    closedDerivativeL2 (derivativeMultiIndex index) (apProductJet coefficient field) =
      ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℂ) •
        closedOperatorL2 (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)))
          (closedDerivativeL2 (derivativeMultiIndex (upperDerivativeIndex index split)) field) := by
  let term (split : DerivativeSplit index) : C(ClosedDisk, ComplexEuclidean output) :=
    ⟨fun point => (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)) point)
      (closedMultiDerivative field (derivativeMultiIndex (upperDerivativeIndex index split)) point),
      (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split))).continuous.clm_apply
        (closedMultiDerivative field (derivativeMultiIndex (upperDerivativeIndex index split))).continuous⟩
  have identity : closedMultiDerivative (apProductJet coefficient field) (derivativeMultiIndex index) =
      ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℂ) • term split := by
    apply ContinuousMap.ext
    intro point
    rw [apProductJet_derivative, continuousMap_sum_apply]
    rfl
  change (closedValueL2Continuous output) (closedMultiDerivative (apProductJet coefficient field) (derivativeMultiIndex index)) = _
  rw [identity, map_sum]
  apply Finset.sum_congr rfl
  intro split _
  rw [map_smul]
  congr 1
  exact (closedOperatorL2_closed
    (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)))
    (closedMultiDerivative field (derivativeMultiIndex (upperDerivativeIndex index split)))).symm

theorem apProductJet_derivativeL2_bound {input output grade : ℕ}
    (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) (index : DerivativeIndex grade) :
    ‖closedDerivativeL2 (derivativeMultiIndex index) (apProductJet coefficient field)‖ ≤
      ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ) *
        ‖smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split))‖ *
          ‖closedDerivativeL2 (derivativeMultiIndex (upperDerivativeIndex index split)) field‖ := by
  rw [apProductJet_derivativeL2]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro split _
  rw [norm_smul, Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left (closedOperatorL2_apply_norm_le _ _) (Nat.cast_nonneg _)).trans_eq
    (mul_assoc _ _ _).symm

theorem phaseOperatorDerivative_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (cell : ℤ) (coordinate : Fin 2) (index : CartesianMultiIndex) :
    ‖smoothOperatorDerivative (apScalarOperatorJet dimension (phaseDirectional sigma gamma ell cell coordinate)
      (phaseDirectional_smooth sigma gamma ell cell coordinate)) index‖ ≤
      phaseDirectionalConstant L gamma (cartesianOrder index) * scaledCellWeight L ell cell ^ (cartesianOrder index + 1) := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (phaseDirectionalConstant_nonnegative admissible _)
    (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _))).mpr
  intro point
  rw [apScalarOperatorJet_derivative, norm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_id_le)).trans
    (phaseDirectional_ordered_bound admissible cell coordinate _ _ point.val)

end Grad.GaugeCoefficients.Physical.Compensated
