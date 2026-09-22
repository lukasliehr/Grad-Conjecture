import BL15FiniteParseval

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem tensorWord_continuous {dimension order : ℕ} (field : ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (word : CartesianWord order) :
    Continuous (fun point => iteratedFDeriv ℝ order field point (fun position => productBasis (word position))) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => ℝ × ℝ) (ComplexEuclidean dimension)
    (fun position => productBasis (word position))).continuous.comp
      (smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)))

theorem finitePolarField_tensor_integral {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (order : ℕ) (time : ℝ) :
    (∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (finitePolarField parameters cell modes values) (time, angle)‖ ^ 2) ≤
      ((2 * Real.pi) * productWordCoefficientSum order ^ 2) * ∑ mode ∈ modes,
        ‖iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)‖ ^ 2 := by
  let field := finitePolarField parameters cell modes values
  have smooth : ContDiff ℝ ∞ field := finitePolarField_smooth parameters cell modes values
  have tensorContinuous : Continuous (fun angle : ℝ => ‖iteratedFDeriv ℝ order field (time, angle)‖ ^ 2) :=
    (((smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).comp
      (continuous_const.prodMk continuous_id)).norm).pow 2
  have wordContinuous (word : CartesianWord order) : Continuous (fun angle : ℝ =>
      ‖iteratedFDeriv ℝ order field (time, angle) (fun position => productBasis (word position))‖ ^ 2) :=
    (((tensorWord_continuous field smooth word).comp (continuous_const.prodMk continuous_id)).norm).pow 2
  have weightedContinuous : Continuous (fun angle : ℝ => productWordCoefficientSum order *
      ∑ word : CartesianWord order, ‖productWordCoefficient word‖ *
        ‖iteratedFDeriv ℝ order field (time, angle) (fun position => productBasis (word position))‖ ^ 2) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro word _
    exact continuous_const.mul (wordContinuous word)
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (neg_le_self Real.pi_pos.le)
    (tensorContinuous.intervalIntegrable _ _) (weightedContinuous.intervalIntegrable _ _)
    (fun angle _ => productTensor_squared_bound (iteratedFDeriv ℝ order field (time, angle)))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum] at comparison
  · have termIdentity (word : CartesianWord order) :
        (∫ angle in -Real.pi..Real.pi, ‖productWordCoefficient word‖ *
          ‖iteratedFDeriv ℝ order field (time, angle) (fun position => productBasis (word position))‖ ^ 2) =
        ‖productWordCoefficient word‖ * ((2 * Real.pi) * ∑ mode ∈ modes,
          ‖iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)
            (fun position => productBasis (word position))‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
      rw [finitePolarField_word_integral parameters cell modes values word time]
    simp_rw [termIdentity] at comparison
    apply comparison.trans
    have wordBound (word : CartesianWord order) :
        (∑ mode ∈ modes,
          ‖iteratedFDeriv ℝ order (polarModeField parameters (mode, cell) (values mode)) (time, 0)
            (fun position => productBasis (word position))‖ ^ 2) ≤
          ∑ mode ∈ modes, ‖iteratedFDeriv ℝ order
            (polarModeField parameters (mode, cell) (values mode)) (time, 0)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro mode _
      exact pow_le_pow_left₀ (norm_nonneg _) (productTensor_word_bound _ word) 2
    calc
      _ ≤ productWordCoefficientSum order *
          ∑ word : CartesianWord order, ‖productWordCoefficient word‖ * ((2 * Real.pi) *
            ∑ mode ∈ modes, ‖iteratedFDeriv ℝ order
              (polarModeField parameters (mode, cell) (values mode)) (time, 0)‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (productWordCoefficientSum_nonnegative order)
        apply Finset.sum_le_sum
        intro word _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (wordBound word) (by positivity)) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; unfold productWordCoefficientSum; ring
  · intro word _
    exact (continuous_const.mul (wordContinuous word)).intervalIntegrable _ _

end Grad.BoundaryLift
