import ANL3NormalPolarEnergy

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.CollarCartesian

def normalProfiles {dimension : ℕ} (values : ℤ → ComplexEuclidean dimension)
    (mode : ℤ) (time : ℝ) : ComplexEuclidean dimension := normalProfile mode time • values mode

theorem normalProfiles_smooth {dimension : ℕ} (values : ℤ → ComplexEuclidean dimension) (mode : ℤ) :
    ContDiff ℝ ∞ (normalProfiles values mode) := (normalProfile_smooth mode).smul contDiff_const

def normalFiniteBoundaryEnergy {dimension : ℕ} (grade : ℕ) (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) : ℝ :=
  ∑ mode ∈ modes, boundaryFrequency (mode, 0) ^ (2 * grade - 3) * ‖values mode‖ ^ 2

theorem normalFiniteBoundaryEnergy_nonnegative {dimension : ℕ} (grade : ℕ) (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) : 0 ≤ normalFiniteBoundaryEnergy grade modes values :=
  Finset.sum_nonneg (fun mode _ => mul_nonneg (pow_nonneg (boundaryFrequency_pos (mode, 0)).le _) (sq_nonneg _))

theorem normalRowsDensity_bound {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (order : ℕ) (time : ℝ) :
    finiteProfileRowDensity modes (normalProfiles values) order time ≤
      productWordCoefficientSum order ^ 2 * ∑ mode ∈ modes,
        ‖iteratedFDeriv ℝ order (normalPolar mode (values mode)) (time, 0)‖ ^ 2 := by
  unfold finiteProfileRowDensity normalProfiles
  simp_rw [← normalPolar_profileMode]
  have words : (∑ word : CartesianWord order, ‖productWordCoefficient word‖ *
      ∑ mode ∈ modes, ‖iteratedFDeriv ℝ order (normalPolar mode (values mode)) (time, 0)
        (fun position => productBasis (word position))‖ ^ 2) ≤
      ∑ word : CartesianWord order, ‖productWordCoefficient word‖ *
        ∑ mode ∈ modes, ‖iteratedFDeriv ℝ order (normalPolar mode (values mode)) (time, 0)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro word _
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro mode _
    exact pow_le_pow_left₀ (norm_nonneg _) (productTensor_word_bound _ word) 2
  apply (mul_le_mul_of_nonneg_left words (productWordCoefficientSum_nonnegative order)).trans_eq
  rw [← Finset.sum_mul]
  unfold productWordCoefficientSum
  ring

theorem normalRowsDensity_integral {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (grade order : ℕ)
    (gradeBound : 2 ≤ grade) (orderBound : order ≤ grade) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), finiteProfileRowDensity modes (normalProfiles values) order time) ≤
      (productWordCoefficientSum order ^ 2 * normalPolarConstant order ^ 2) *
        normalFiniteBoundaryEnergy grade modes values := by
  have modeContinuous (mode : ℤ) : Continuous (fun time : ℝ =>
      ‖iteratedFDeriv ℝ order (normalPolar mode (values mode)) (time, 0)‖ ^ 2) :=
    ((((normalPolar_smooth mode (values mode)).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).comp
        (continuous_id.prodMk continuous_const)).norm).pow 2
  have rightContinuous : Continuous (fun time : ℝ => productWordCoefficientSum order ^ 2 *
      ∑ mode ∈ modes, ‖iteratedFDeriv ℝ order (normalPolar mode (values mode)) (time, 0)‖ ^ 2) :=
    continuous_const.mul (continuous_finsetSum modes (fun mode _ => modeContinuous mode))
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    ((finiteProfileRowDensity_continuous modes (normalProfiles values) (normalProfiles_smooth values) order).intervalIntegrable _ _)
    (rightContinuous.intervalIntegrable _ _) (fun time _ => normalRowsDensity_bound modes values order time)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun mode _ => (modeContinuous mode).intervalIntegrable _ _)] at comparison
  have integrated := Finset.sum_le_sum (fun mode (_ : mode ∈ modes) =>
    normalPolar_grade_energy mode (values mode) grade order gradeBound orderBound)
  apply (comparison.trans (mul_le_mul_of_nonneg_left integrated (sq_nonneg (productWordCoefficientSum order)))).trans_eq
  simp only [normalFiniteBoundaryEnergy, mul_assoc, Finset.mul_sum]

def normalFinitePolarConstant (order : ℕ) : ℝ :=
  (2 * Real.pi) * ∑ index ∈ Finset.range (order + 1),
    productWordCoefficientSum index ^ 2 * normalPolarConstant index ^ 2

theorem normalFinitePolarConstant_nonnegative (order : ℕ) : 0 ≤ normalFinitePolarConstant order :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun index _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem normalFiniteProfileEnergy_bound {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (grade order : ℕ)
    (gradeBound : 2 ≤ grade) (orderBound : order ≤ grade) :
    finiteProfileEnergy modes (normalProfiles values) order ≤
      normalFinitePolarConstant order * normalFiniteBoundaryEnergy grade modes values := by
  unfold finiteProfileEnergy normalFinitePolarConstant
  have summed := Finset.sum_le_sum (s := Finset.range (order + 1)) (fun index inside =>
    normalRowsDensity_integral modes values grade index gradeBound
      (by have := Finset.mem_range.mp inside; omega))
  have scaled := mul_le_mul_of_nonneg_left summed (show 0 ≤ 2 * Real.pi by positivity)
  apply scaled.trans_eq
  rw [← Finset.sum_mul]
  ring

end Grad.CircularNormalLift
