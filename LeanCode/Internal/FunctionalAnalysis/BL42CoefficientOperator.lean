import BL41WeightRatios

noncomputable section

open scoped BigOperators ENNReal

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

def cellPairTranslation (shift : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun mode := (mode.1, mode.2 - shift)
  invFun mode := (mode.1, mode.2 + shift)
  left_inv mode := by simp
  right_inv mode := by simp

@[simp] theorem cellPairTranslation_apply (shift : ℤ) (mode : ℤ × ℤ) :
    cellPairTranslation shift mode = (mode.1, mode.2 - shift) := rfl

def angularPairTranslation (shift : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun mode := (mode.1 - shift, mode.2)
  invFun mode := (mode.1 + shift, mode.2)
  left_inv mode := by simp
  right_inv mode := by simp

@[simp] theorem angularPairTranslation_apply (shift : ℤ) (mode : ℤ × ℤ) :
    angularPairTranslation shift mode = (mode.1 - shift, mode.2) := rfl

theorem boundaryGrade_norm_sq_raw {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : BoundaryGrade parameters (ComplexEuclidean dimension) grade) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]

theorem boundaryGrade_sq_summable {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : BoundaryGrade parameters (ComplexEuclidean dimension) grade) :
    Summable (fun mode : ℤ × ℤ => ‖field mode‖ ^ 2) := by
  have member := lp.memℓp field
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)] at member
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using member

variable {sourceDimension targetDimension : ℕ}

/-- One coefficientwise reindexed operator entry family applied to a field. -/
def entryReindexFun (parameters : PhaseParameters) (grade : ℕ) (reindex : ℤ × ℤ ≃ ℤ × ℤ)
    (entry : ℤ × ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade) (mode : ℤ × ℤ) :
    ComplexEuclidean targetDimension :=
  entry mode (field (reindex mode))

theorem entryReindexFun_sq_bound (parameters : PhaseParameters) (grade : ℕ)
    (reindex : ℤ × ℤ ≃ ℤ × ℤ)
    (entry : ℤ × ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    {bound : ℝ} (entryBound : ∀ mode, ‖entry mode‖ ≤ bound)
    (field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade) (mode : ℤ × ℤ) :
    ‖entryReindexFun parameters grade reindex entry field mode‖ ^ 2 ≤
      bound ^ 2 * ‖field (reindex mode)‖ ^ 2 := by
  have termBound : ‖entryReindexFun parameters grade reindex entry field mode‖ ≤
      bound * ‖field (reindex mode)‖ :=
    ((entry mode).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (entryBound mode) (norm_nonneg _))
  calc ‖entryReindexFun parameters grade reindex entry field mode‖ ^ 2 ≤
      (bound * ‖field (reindex mode)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) termBound 2
    _ = bound ^ 2 * ‖field (reindex mode)‖ ^ 2 := mul_pow _ _ _

theorem entryReindexFun_memlp (parameters : PhaseParameters) (grade : ℕ)
    (reindex : ℤ × ℤ ≃ ℤ × ℤ)
    (entry : ℤ × ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    {bound : ℝ} (entryBound : ∀ mode, ‖entry mode‖ ≤ bound)
    (field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade) :
    Memℓp (entryReindexFun parameters grade reindex entry field) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  have reindexedSummable : Summable (fun mode : ℤ × ℤ => ‖field (reindex mode)‖ ^ 2) :=
    reindex.summable_iff.mpr (boundaryGrade_sq_summable parameters grade field)
  exact Summable.of_nonneg_of_le (fun mode => sq_nonneg _)
    (fun mode => entryReindexFun_sq_bound parameters grade reindex entry entryBound field mode)
    (reindexedSummable.mul_left (bound ^ 2))

def entryReindexLinear (parameters : PhaseParameters) (grade : ℕ) (reindex : ℤ × ℤ ≃ ℤ × ℤ)
    (entry : ℤ × ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    {bound : ℝ} (entryBound : ∀ mode, ‖entry mode‖ ≤ bound) :
    BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade →ₗ[ℂ]
      BoundaryGrade parameters (ComplexEuclidean targetDimension) grade where
  toFun field := ⟨entryReindexFun parameters grade reindex entry field,
    entryReindexFun_memlp parameters grade reindex entry entryBound field⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact map_add (entry mode) (first (reindex mode)) (second (reindex mode))
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    exact map_smul (entry mode) scalar (field (reindex mode))

theorem entryReindexLinear_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (reindex : ℤ × ℤ ≃ ℤ × ℤ)
    (entry : ℤ × ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    {bound : ℝ} (boundNonneg : 0 ≤ bound) (entryBound : ∀ mode, ‖entry mode‖ ≤ bound)
    (field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade) :
    ‖entryReindexLinear parameters grade reindex entry entryBound field‖ ≤ bound * ‖field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg boundNonneg (norm_nonneg _))).mp
  rw [boundaryGrade_norm_sq_raw, mul_pow, boundaryGrade_norm_sq_raw]
  have reindexedSummable : Summable (fun mode : ℤ × ℤ => ‖field (reindex mode)‖ ^ 2) :=
    reindex.summable_iff.mpr (boundaryGrade_sq_summable parameters grade field)
  have termSummable := boundaryGrade_sq_summable parameters grade
    (entryReindexLinear parameters grade reindex entry entryBound field)
  calc ∑' mode : ℤ × ℤ, ‖entryReindexLinear parameters grade reindex entry entryBound field mode‖ ^ 2
      ≤ ∑' mode : ℤ × ℤ, bound ^ 2 * ‖field (reindex mode)‖ ^ 2 :=
        termSummable.tsum_le_tsum
          (fun mode => entryReindexFun_sq_bound parameters grade reindex entry entryBound field mode)
          (reindexedSummable.mul_left (bound ^ 2))
    _ = bound ^ 2 * ∑' mode : ℤ × ℤ, ‖field (reindex mode)‖ ^ 2 := tsum_mul_left
    _ = bound ^ 2 * ∑' mode : ℤ × ℤ, ‖field mode‖ ^ 2 := by
        rw [reindex.tsum_eq (fun mode => ‖field mode‖ ^ 2)]

/-- The bounded coefficientwise reindexed operator between boundary grades. -/
def coefficientOperator (parameters : PhaseParameters) (grade : ℕ) (reindex : ℤ × ℤ ≃ ℤ × ℤ)
    (entry : ℤ × ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    {bound : ℝ} (boundNonneg : 0 ≤ bound) (entryBound : ∀ mode, ‖entry mode‖ ≤ bound) :
    BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade →L[ℂ]
      BoundaryGrade parameters (ComplexEuclidean targetDimension) grade :=
  LinearMap.mkContinuous (entryReindexLinear parameters grade reindex entry entryBound) bound
    (entryReindexLinear_norm_le parameters grade reindex entry boundNonneg entryBound)

theorem coefficientOperator_apply (parameters : PhaseParameters) (grade : ℕ)
    (reindex : ℤ × ℤ ≃ ℤ × ℤ)
    (entry : ℤ × ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    {bound : ℝ} (boundNonneg : 0 ≤ bound) (entryBound : ∀ mode, ‖entry mode‖ ≤ bound)
    (field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade) (mode : ℤ × ℤ) :
    coefficientOperator parameters grade reindex entry boundNonneg entryBound field mode =
      entry mode (field (reindex mode)) := rfl

theorem coefficientOperator_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (reindex : ℤ × ℤ ≃ ℤ × ℤ)
    (entry : ℤ × ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    {bound : ℝ} (boundNonneg : 0 ≤ bound) (entryBound : ∀ mode, ‖entry mode‖ ≤ bound) :
    ‖coefficientOperator parameters grade reindex entry boundNonneg entryBound‖ ≤ bound :=
  LinearMap.mkContinuous_norm_le _ boundNonneg _

end Grad.BoundaryLift
