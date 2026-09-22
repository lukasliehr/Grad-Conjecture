import AKDX8CanonicalPolarWordEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity

theorem tensorAngular_energy_le_words {dimension order : ℕ}
    (tensor : ℝ → (ℝ × ℝ) [×order]→L[ℝ] ComplexEuclidean dimension)
    (continuousTensor : Continuous tensor) :
    (∫ angle in -Real.pi..Real.pi,‖tensor angle‖^2) ≤
      productWordCoefficientSum order * ∑ word : CartesianWord order,
        ‖productWordCoefficient word‖ * ∫ angle in -Real.pi..Real.pi,
          ‖tensor angle (fun position => productBasis (word position))‖^2 := by
  have wordContinuous (word : CartesianWord order) : Continuous (fun angle : ℝ =>
      ‖tensor angle (fun position => productBasis (word position))‖ ^ 2) :=
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => ℝ × ℝ)
      (ComplexEuclidean dimension) (fun position => productBasis (word position))).continuous.comp
        continuousTensor).norm.pow 2
  have weightedContinuous : Continuous (fun angle : ℝ => productWordCoefficientSum order *
      ∑ word : CartesianWord order, ‖productWordCoefficient word‖ *
        ‖tensor angle (fun position => productBasis (word position))‖ ^ 2) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro word _
    exact continuous_const.mul (wordContinuous word)
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (neg_le_self Real.pi_pos.le)
    ((continuousTensor.norm.pow 2).intervalIntegrable _ _)
    (weightedContinuous.intervalIntegrable _ _)
    (fun angle _ => productTensor_squared_bound (tensor angle))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum] at comparison
  · simpa only [intervalIntegral.integral_const_mul,Pi.pow_apply] using comparison
  · intro word _
    exact (continuous_const.mul (wordContinuous word)).intervalIntegrable _ _

/-- Full genuine polar tensors are controlled by the SAME canonical radial
curves, after summing an arbitrary finite axial support before Parseval. -/
theorem canonicalPolarTensor_energy {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (core : ACore parameters dimension)
    (order : ℕ) (radius : ℝ) (inside : radius∈Icc lower 1) (cells : Finset ℤ) :
    (∑ cell∈cells,∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (originalPolarValue (phaseWeightedJet parameters cell (core.val cell)))
        (radius,angle)‖^2)≤
      productWordCoefficientSum order * ∑ word : CartesianWord order,
        ‖productWordCoefficient word‖ * ((2*Real.pi)*
          ‖cartesianWeightedRadialCurve parameters lower positive bounded core
            (polarWordCount word 1) (polarWordCount word 0) radius‖^2) := by
  calc
    _ ≤ ∑ cell∈cells,productWordCoefficientSum order * ∑ word : CartesianWord order,
        ‖productWordCoefficient word‖ * ∫ angle in -Real.pi..Real.pi,
          ‖polarWordField (originalPolarValue (phaseWeightedJet parameters cell (core.val cell)))
            word (radius,angle)‖^2 := by
      apply Finset.sum_le_sum
      intro cell _
      exact tensorAngular_energy_le_words _
        (((originalPolarValue_smooth _).continuous_iteratedFDeriv
          (by exact_mod_cast (le_top : (order : ℕ∞)≤⊤))).comp
            (continuous_const.prodMk continuous_id))
    _ = productWordCoefficientSum order * ∑ word : CartesianWord order,
        ‖productWordCoefficient word‖ * ∑ cell∈cells,∫ angle in -Real.pi..Real.pi,
          ‖polarWordField (originalPolarValue (phaseWeightedJet parameters cell (core.val cell)))
            word (radius,angle)‖^2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (productWordCoefficientSum_nonnegative order)
      apply Finset.sum_le_sum
      intro word _
      exact mul_le_mul_of_nonneg_left
        (canonicalPolarWord_energy parameters lower positive bounded core order word radius inside cells)
        (norm_nonneg _)

end Grad.OriginalCollarNorm
