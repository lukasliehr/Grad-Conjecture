import AKBZ13SharpCoefficientDisplacement

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

def sharpPhaseDenominator (L ell : ℝ) (rank : ℕ) (input shift : ℤ) : ℝ :=
  ∑ displacement ∈ Finset.Icc 1 rank,
    scaledCellWeight L ell shift^displacement*scaledCellWeight L ell input^(rank-displacement)

theorem sharpPhaseDenominator_pos (L ell : ℝ) (rank : ℕ) (positive : 0<rank) (input shift : ℤ) :
    0<sharpPhaseDenominator L ell rank input shift := by
  unfold sharpPhaseDenominator
  apply Finset.sum_pos'
  · intro displacement membership
    exact mul_nonneg (pow_nonneg (scaledCellWeight_nonnegative L ell shift) _)
      (pow_nonneg (scaledCellWeight_nonnegative L ell input) _)
  · refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl,positive⟩, ?_⟩
    exact mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell shift)) _)
      (pow_pos (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input)) _)

/-- Actual phase derivative divided among its displacement orders. After
reserving a-d input frequencies each summand has coefficient order b+d. -/
def sharpAllocatedCoefficient {L sigma gamma ell : ℝ} {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (rank displacement : ℕ) (word : Fin rank → Fin 2) (index : CartesianMultiIndex)
    (input shift : ℤ) : C(ClosedDisk, OperatorValue inputDimension outputDimension) where
  toFun point :=
    (((apRatioDerivative sigma gamma ell rank word input shift point*
      scaledCellWeight L ell shift^displacement/sharpPhaseDenominator L ell rank input shift : ℝ) : ℂ) •
      rawFamilyDerivative family shift index point)
  continuous_toFun := (Complex.continuous_ofReal.comp
    (((apRatioDerivative sigma gamma ell rank word input shift).continuous.mul_const _).div_const _)).smul
      (coefficientDerivative (family (cartesianOrder index)) shift (multiIndexAtOrder index)).continuous

theorem sharpAllocatedCoefficient_exact {L sigma gamma ell : ℝ} {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (rank : ℕ) (positive : 0<rank) (word : Fin rank → Fin 2) (index : CartesianMultiIndex)
    (input shift : ℤ) (point : ClosedDisk) :
    ∑ displacement ∈ Finset.Icc 1 rank,
      ((scaledCellWeight L ell input^(rank-displacement) : ℝ) : ℂ) •
        sharpAllocatedCoefficient family rank displacement word index input shift point =
    ((apRatioDerivative sigma gamma ell rank word input shift point : ℝ) : ℂ) •
      rawFamilyDerivative family shift index point := by
  have denominator := ne_of_gt (sharpPhaseDenominator_pos L ell rank positive input shift)
  change (∑ displacement ∈ Finset.Icc 1 rank,
    ((scaledCellWeight L ell input^(rank-displacement) : ℝ) : ℂ) •
      (((apRatioDerivative sigma gamma ell rank word input shift point*
        scaledCellWeight L ell shift^displacement/sharpPhaseDenominator L ell rank input shift : ℝ) : ℂ) •
          rawFamilyDerivative family shift index point)) = _
  simp only [smul_smul, ← Finset.sum_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 2
  calc
    _ = apRatioDerivative sigma gamma ell rank word input shift point/sharpPhaseDenominator L ell rank input shift*
      sharpPhaseDenominator L ell rank input shift := by
        unfold sharpPhaseDenominator
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro displacement membership
        ring
    _ = _ := div_mul_cancel₀ _ denominator

end Grad.OriginalCartesianTameEstimate
