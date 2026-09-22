import ANL2NormalProfileEnergy

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.CollarCartesian

theorem normalRadial_iterated_bound (mode : ℤ)
    (order : ℕ) (point : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ order (fun source : ℝ × ℝ => normalProfile mode source.1) point‖ ≤
      ‖iteratedDeriv order (normalProfile mode) point.1‖ := by
  have representation : (fun source : ℝ × ℝ => normalProfile mode source.1) =
      normalProfile mode ∘ ContinuousLinearMap.fst ℝ ℝ ℝ := rfl
  rw [representation, (ContinuousLinearMap.fst ℝ ℝ ℝ).iteratedFDeriv_comp_right
    (normalProfile_smooth mode) point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  have bound := (iteratedFDeriv ℝ order (normalProfile mode) point.1).norm_compContinuousLinearMap_le
    (fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ)
  rw [show (ContinuousLinearMap.fst ℝ ℝ ℝ) point = point.1 from rfl]
  simpa only [ContinuousLinearMap.norm_fst, Finset.prod_const_one, mul_one,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] using bound

def normalPolar {dimension : ℕ} (mode : ℤ) (value : ComplexEuclidean dimension)
    (point : ℝ × ℝ) : ComplexEuclidean dimension :=
  normalProfile mode point.1 • (cellExponential mode point.2 • value)

theorem normalPolar_smooth {dimension : ℕ} (mode : ℤ) (value : ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (normalPolar mode value) :=
  ((normalProfile_smooth mode).comp contDiff_fst).smul
    ((angularExponential_smooth mode).smul contDiff_const)

theorem normalPolar_profileMode {dimension : ℕ} (mode : ℤ) (value : ComplexEuclidean dimension) :
    normalPolar mode value = profileMode mode (fun time => normalProfile mode time • value) := by
  funext point
  exact smul_comm _ _ _

theorem normalPolar_iterated_bound {dimension : ℕ} (mode : ℤ)
    (value : ComplexEuclidean dimension) (order : ℕ) (point : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ order (normalPolar mode value) point‖ ≤
      ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
        ‖iteratedDeriv index (normalProfile mode) point.1‖ *
          |(mode : ℝ)| ^ (order - index) * ‖value‖ := by
  have product := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
    (f := fun source : ℝ × ℝ => normalProfile mode source.1)
    (g := fun source : ℝ × ℝ => cellExponential mode source.2 • value)
    ((normalProfile_smooth mode).comp contDiff_fst)
    ((angularExponential_smooth mode).smul contDiff_const) point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ order (normalPolar mode value) point‖ ≤ _ at product
  apply product.trans
  apply Finset.sum_le_sum
  intro index _
  have radial := normalRadial_iterated_bound mode index point
  have angular := angularExponential_vector_iterated_bound mode value (order - index) point
  calc
    _ ≤ (order.choose index : ℝ) * ‖iteratedDeriv index (normalProfile mode) point.1‖ *
        (|(mode : ℝ)| ^ (order - index) * ‖value‖) := by gcongr
    _ = _ := by ring


def normalPolarConstant (order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * (2 * normalProfileConstant index)

theorem normalPolarConstant_nonnegative (order : ℕ) : 0 ≤ normalPolarConstant order :=
  Finset.sum_nonneg (fun index _ => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (by norm_num) (normalProfileConstant_nonnegative _)))

theorem normalPolar_decay {dimension : ℕ} (mode : ℤ) (value : ComplexEuclidean dimension)
    (order : ℕ) (point : ℝ × ℝ) (inside : point.1 ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedFDeriv ℝ order (normalPolar mode value) point‖ ≤
      normalPolarConstant order * boundaryFrequency (mode, 0) ^ order /
        boundaryFrequency (mode, 0) * Real.exp (-boundaryFrequency (mode, 0) * point.1 / 2) * ‖value‖ := by
  apply (normalPolar_iterated_bound mode value order point).trans
  simp only [normalPolarConstant, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_le_sum
  intro index indexIn
  have indexBound : index ≤ order := by have := Finset.mem_range.mp indexIn; omega
  have radial := normalProfile_decay_bound mode index point.1 inside
  have frequencyBound : boundaryFrequency (mode, 0) ^ index * |(mode : ℝ)| ^ (order - index) ≤
      boundaryFrequency (mode, 0) ^ order := by
    calc
      _ ≤ boundaryFrequency (mode, 0) ^ index * boundaryFrequency (mode, 0) ^ (order - index) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (angularFrequency_le_boundaryFrequency (mode, 0)) _)
          (pow_nonneg (boundaryFrequency_pos (mode, 0)).le _)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le indexBound]
  calc
    _ ≤ (order.choose index : ℝ) *
        ((2 * normalProfileConstant index) * boundaryFrequency (mode, 0) ^ index /
          boundaryFrequency (mode, 0) * Real.exp (-boundaryFrequency (mode, 0) * point.1 / 2)) *
        |(mode : ℝ)| ^ (order - index) * ‖value‖ := by gcongr
    _ = ((order.choose index : ℝ) * (2 * normalProfileConstant index) /
        boundaryFrequency (mode, 0) * Real.exp (-boundaryFrequency (mode, 0) * point.1 / 2) * ‖value‖) *
        (boundaryFrequency (mode, 0) ^ index * |(mode : ℝ)| ^ (order - index)) := by ring
    _ ≤ ((order.choose index : ℝ) * (2 * normalProfileConstant index) /
        boundaryFrequency (mode, 0) * Real.exp (-boundaryFrequency (mode, 0) * point.1 / 2) * ‖value‖) *
        boundaryFrequency (mode, 0) ^ order := by
      apply mul_le_mul_of_nonneg_left frequencyBound
      exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (normalProfileConstant_nonnegative index)))
          (boundaryFrequency_pos (mode, 0)).le) (Real.exp_pos _).le) (norm_nonneg _)
    _ = _ := by ring

theorem normalPolar_squared {dimension : ℕ} (mode : ℤ) (value : ComplexEuclidean dimension)
    (order : ℕ) (point : ℝ × ℝ) (inside : point.1 ∈ Icc (0 : ℝ) (1 / 2)) :
    ‖iteratedFDeriv ℝ order (normalPolar mode value) point‖ ^ 2 ≤
      (normalPolarConstant order ^ 2 * boundaryFrequency (mode, 0) ^ (2 * order) /
        boundaryFrequency (mode, 0) ^ 2 * ‖value‖ ^ 2) * Real.exp (-boundaryFrequency (mode, 0) * point.1) := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (normalPolar_decay mode value order point inside) 2).trans_eq
  simp only [mul_pow, div_pow, ← pow_mul]
  rw [show Real.exp (-boundaryFrequency (mode, 0) * point.1 / 2) ^ 2 =
      Real.exp (-boundaryFrequency (mode, 0) * point.1) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  ring

theorem normalPolar_integral {dimension : ℕ} (mode : ℤ) (value : ComplexEuclidean dimension) (order : ℕ) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖iteratedFDeriv ℝ order (normalPolar mode value) (time, 0)‖ ^ 2) ≤
      normalPolarConstant order ^ 2 * boundaryFrequency (mode, 0) ^ (2 * order) /
        boundaryFrequency (mode, 0) ^ 3 * ‖value‖ ^ 2 := by
  have normContinuous : Continuous (fun time : ℝ =>
      ‖iteratedFDeriv ℝ order (normalPolar mode value) (time, 0)‖ ^ 2) :=
    ((((normalPolar_smooth mode value).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).comp
        (continuous_id.prodMk continuous_const)).norm).pow 2
  have exponentialContinuous : Continuous (fun time : ℝ =>
      (normalPolarConstant order ^ 2 * boundaryFrequency (mode, 0) ^ (2 * order) /
        boundaryFrequency (mode, 0) ^ 2 * ‖value‖ ^ 2) * Real.exp (-boundaryFrequency (mode, 0) * time)) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (normContinuous.intervalIntegrable _ _) (exponentialContinuous.intervalIntegrable _ _)
    (fun time inside => normalPolar_squared mode value order (time, 0) inside)
  rw [intervalIntegral.integral_const_mul] at comparison
  have integrated := mul_le_mul_of_nonneg_left
    (exponential_decay_integral_le (boundaryFrequency (mode, 0)) (1 / 2) (boundaryFrequency_pos (mode, 0)) (by norm_num))
    (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg (normalPolarConstant order))
      (pow_nonneg (boundaryFrequency_pos (mode, 0)).le (2 * order)))
        (sq_nonneg (boundaryFrequency (mode, 0)))) (sq_nonneg ‖value‖))
  apply (comparison.trans integrated).trans_eq
  ring

theorem normalPolar_grade_energy {dimension : ℕ} (mode : ℤ) (value : ComplexEuclidean dimension)
    (grade order : ℕ) (gradeBound : 2 ≤ grade) (orderBound : order ≤ grade) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖iteratedFDeriv ℝ order (normalPolar mode value) (time, 0)‖ ^ 2) ≤
      normalPolarConstant order ^ 2 * boundaryFrequency (mode, 0) ^ (2 * grade - 3) * ‖value‖ ^ 2 := by
  have powers : boundaryFrequency (mode, 0) ^ (2 * order) ≤ boundaryFrequency (mode, 0) ^ (2 * grade) :=
    pow_le_pow_right₀ (boundaryFrequency_one_le (mode, 0)) (by omega)
  have comparison := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left powers (sq_nonneg (normalPolarConstant order)))
    (pow_nonneg (boundaryFrequency_pos (mode, 0)).le 3)
  have scaled := mul_le_mul_of_nonneg_right comparison (sq_nonneg ‖value‖)
  apply ((normalPolar_integral mode value order).trans scaled).trans_eq
  have factor : boundaryFrequency (mode, 0) ^ (2 * grade - 3) * boundaryFrequency (mode, 0) ^ 3 =
      boundaryFrequency (mode, 0) ^ (2 * grade) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← factor]
  field_simp [(boundaryFrequency_pos (mode, 0)).ne']

end Grad.CircularNormalLift
