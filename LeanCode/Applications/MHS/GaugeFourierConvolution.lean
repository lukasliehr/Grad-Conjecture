import GaugeSeed

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra

theorem operatorVectorConvolution_fourier {sourceDimension targetDimension : ℕ}
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (values : ℤ → ComplexEuclidean sourceDimension)
    (coefficientSummable : Summable (fun cell => ‖coefficients cell‖))
    (valueSummable : Summable (fun cell => ‖values cell‖)) (angle : ℝ) :
    (∑' cell : ℤ, fourierPhase cell angle •
      ∑' shift : ℤ, coefficients shift (values (cell - shift))) =
      (∑' shift : ℤ, fourierPhase shift angle • coefficients shift)
        (∑' cell : ℤ, fourierPhase cell angle • values cell) := by
  let pairTerm (pair : ℤ × ℤ) :=
    (fourierPhase pair.1 angle • coefficients pair.1)
      (fourierPhase pair.2 angle • values pair.2)
  have pairMajorant : Summable (fun pair : ℤ × ℤ => ‖coefficients pair.1‖ * ‖values pair.2‖) :=
    coefficientSummable.mul_of_nonneg valueSummable (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have pairNorm : Summable (fun pair => ‖pairTerm pair‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ pairMajorant
    intro pair
    simpa only [pairTerm, norm_smul, fourierPhase_norm, one_mul] using
      (fourierPhase pair.1 angle • coefficients pair.1).le_opNorm
        (fourierPhase pair.2 angle • values pair.2)
  have pairSum : Summable pairTerm := pairNorm.of_norm
  have reindexed : Summable (fun pair : ℤ × ℤ => pairTerm (cellConvolutionEquiv pair)) :=
    cellConvolutionEquiv.summable_iff.mpr pairSum
  have literal (cell shift : ℤ) :
      fourierPhase cell angle • coefficients shift (values (cell - shift)) =
        pairTerm (cellConvolutionEquiv (cell, shift)) := by
    change _ = (fourierPhase shift angle • coefficients shift)
      (fourierPhase (cell - shift) angle • values (cell - shift))
    simp only [smul_apply, map_smul, smul_smul]
    rw [← fourierPhase_add, sub_add_cancel]
  have coefficientPhaseNorm : Summable (fun cell => ‖fourierPhase cell angle • coefficients cell‖) := by
    simpa only [norm_smul, fourierPhase_norm, one_mul] using coefficientSummable
  have valuePhaseNorm : Summable (fun cell => ‖fourierPhase cell angle • values cell‖) := by
    simpa only [norm_smul, fourierPhase_norm, one_mul] using valueSummable
  calc
    _ = ∑' cell : ℤ, ∑' shift : ℤ, pairTerm (cellConvolutionEquiv (cell, shift)) := by
      apply tsum_congr
      intro cell
      rw [← tsum_const_smul'']
      exact tsum_congr (literal cell)
    _ = ∑' pair : ℤ × ℤ, pairTerm (cellConvolutionEquiv pair) := reindexed.tsum_prod.symm
    _ = ∑' pair : ℤ × ℤ, pairTerm pair := cellConvolutionEquiv.tsum_eq pairTerm
    _ = ∑' shift : ℤ, ∑' cell : ℤ, pairTerm (shift, cell) := pairSum.tsum_prod
    _ = ∑' shift : ℤ, (fourierPhase shift angle • coefficients shift)
        (∑' cell : ℤ, fourierPhase cell angle • values cell) := by
      apply tsum_congr
      intro shift
      exact ((fourierPhase shift angle • coefficients shift).map_tsum valuePhaseNorm.of_norm).symm
    _ = _ := ((ContinuousLinearMap.apply ℂ (ComplexEuclidean targetDimension)
      (∑' cell : ℤ, fourierPhase cell angle • values cell)).map_tsum coefficientPhaseNorm.of_norm).symm

end Grad.Constraints.Gauges
