import ARC4ArbitraryPolarFamily
import BL16AngularTensor

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

/-- Finite Parseval for each coordinate row, before taking the tensor operator norm.
The row amplitudes are arbitrary, and the constant is independent of the mode set. -/
theorem finiteTensorRows_integral {dimension order : ℕ}
    (tensor : ℝ → (ℝ × ℝ) [×order]→L[ℝ] ComplexEuclidean dimension)
    (continuousTensor : Continuous tensor) (modes : Finset ℤ)
    (rows : CartesianWord order → ℤ → ComplexEuclidean dimension)
    (expansion : ∀ angle word, tensor angle (fun position => productBasis (word position)) =
      ∑ mode ∈ modes, fourier mode (angle : CellCircle) • rows word mode) :
    (∫ angle in -Real.pi..Real.pi, ‖tensor angle‖ ^ 2) ≤
      (2 * Real.pi) * productWordCoefficientSum order *
        ∑ word : CartesianWord order, ‖productWordCoefficient word‖ *
          ∑ mode ∈ modes, ‖rows word mode‖ ^ 2 := by
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
  · have termIdentity (word : CartesianWord order) :
        (∫ angle in -Real.pi..Real.pi, ‖productWordCoefficient word‖ *
          ‖tensor angle (fun position => productBasis (word position))‖ ^ 2) =
        ‖productWordCoefficient word‖ * ((2 * Real.pi) * ∑ mode ∈ modes, ‖rows word mode‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
      simp_rw [expansion]
      rw [finiteFourier_integral_norm_sq]
    simp_rw [termIdentity] at comparison
    apply comparison.trans_eq
    calc
      _ = productWordCoefficientSum order * ((2 * Real.pi) *
          ∑ word : CartesianWord order, ‖productWordCoefficient word‖ *
            ∑ mode ∈ modes, ‖rows word mode‖ ^ 2) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro word _
        ring
      _ = _ := by ring
  · intro word _
    exact (continuous_const.mul (wordContinuous word)).intervalIntegrable _ _

def finiteProfileRowDensity {dimension : ℕ} (modes : Finset ℤ)
    (profiles : ℤ → ℝ → ComplexEuclidean dimension) (order : ℕ) (time : ℝ) : ℝ :=
  productWordCoefficientSum order * ∑ word : CartesianWord order,
    ‖productWordCoefficient word‖ * ∑ mode ∈ modes,
      ‖iteratedFDeriv ℝ order (profileMode mode (profiles mode)) (time, 0)
        (fun position => productBasis (word position))‖ ^ 2

theorem finiteProfileField_tensor_integral {dimension : ℕ} (modes : Finset ℤ)
    (profiles : ℤ → ℝ → ComplexEuclidean dimension) (smooth : ∀ mode, ContDiff ℝ ∞ (profiles mode))
    (order : ℕ) (time : ℝ) :
    (∫ angle in -Real.pi..Real.pi,
      ‖iteratedFDeriv ℝ order (finiteProfileField modes profiles) (time, angle)‖ ^ 2) ≤
      (2 * Real.pi) * finiteProfileRowDensity modes profiles order time := by
  have comparison := finiteTensorRows_integral
    (fun angle => iteratedFDeriv ℝ order (finiteProfileField modes profiles) (time, angle))
    (((finiteProfileField_smooth modes profiles smooth).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).comp
      (continuous_const.prodMk continuous_id)) modes
    (fun word mode => iteratedFDeriv ℝ order (profileMode mode (profiles mode)) (time, 0)
      (fun position => productBasis (word position)))
    (fun angle word => finiteProfileField_word_expansion modes profiles smooth word time angle)
  exact comparison.trans_eq (by unfold finiteProfileRowDensity; ring)

end Grad.CollarCartesian
