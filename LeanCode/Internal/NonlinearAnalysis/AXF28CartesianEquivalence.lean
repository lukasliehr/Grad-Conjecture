import AXF27FixedRadialProfile

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.QuotientProjection Grad.NonlinearProduct

variable {parameters : PhaseParameters}

abbrev CartesianSourceCore (parameters : PhaseParameters) :=
  ACore parameters 2 × ACore parameters 1 × ACore parameters 1

def cartesianToSpin : CartesianSourceCore parameters →ₗ[ℂ] SmoothQuotient parameters where
  toFun source := ![spinCore 1 source.1, spinCore (-1) source.1, source.2.1, source.2.2]
  map_add' first second := by
    funext index
    fin_cases index <;> simp [map_add]
  map_smul' scalar source := by
    funext index
    fin_cases index <;> simp [map_smul]

def spinToCartesian : SmoothQuotient parameters →ₗ[ℂ] CartesianSourceCore parameters :=
  cartesianSourceLinear.prod ((LinearMap.proj 2).prod (LinearMap.proj 3))

theorem cartesianSourceVector_cartesianToSpin (source : CartesianSourceCore parameters) :
    cartesianSourceVector (cartesianToSpin source) = source.1 := by
  apply spinCore_joint_injective
  · rw [spinCore_cartesianSource_plus]
    rfl
  · rw [spinCore_cartesianSource_minus]
    rfl

def spinCartesianEquiv : SmoothQuotient parameters ≃ₗ[ℂ] CartesianSourceCore parameters where
  toLinearMap := spinToCartesian
  invFun := cartesianToSpin
  left_inv source := by
    funext index
    fin_cases index
    · exact spinCore_cartesianSource_plus source
    · exact spinCore_cartesianSource_minus source
    · rfl
    · rfl
  right_inv source := by
    apply Prod.ext
    · exact cartesianSourceVector_cartesianToSpin source
    · rfl

/-- The exact BS3 norm, using the original A^q vector and scalar norms. -/
def cartesianSourceNorm (grade : ℕ) (source : CartesianSourceCore parameters) : ℝ :=
  Real.sqrt (2 * originalGradeNorm grade source.1 ^ 2 +
    originalGradeNorm grade source.2.1 ^ 2 + originalGradeNorm grade source.2.2 ^ 2)

theorem spinCartesianEquiv_norm (grade : ℕ) (source : SmoothQuotient parameters) :
    cartesianSourceNorm grade (spinCartesianEquiv source) = quotientNorm parameters grade source := by
  change Real.sqrt (2 * originalGradeNorm grade (cartesianSourceVector source) ^ 2 +
    originalGradeNorm grade (source 2) ^ 2 + originalGradeNorm grade (source 3) ^ 2) = _
  rw [← originalSpin_cartesian_vector_norm parameters grade source]
  exact Real.sqrt_sq (norm_nonneg (quotientEta parameters grade source))

theorem cartesianToSpin_norm (grade : ℕ) (source : CartesianSourceCore parameters) :
    quotientNorm parameters grade (cartesianToSpin source) = cartesianSourceNorm grade source := by
  rw [← spinCartesianEquiv_norm]
  change cartesianSourceNorm grade (spinCartesianEquiv (spinCartesianEquiv.symm source)) = _
  rw [LinearEquiv.apply_symm_apply]

def cartesianFlatProjection : CartesianSourceCore parameters →ₗ[ℂ] CartesianSourceCore parameters :=
  spinToCartesian.comp (flatSourceProjection.comp cartesianToSpin)

theorem cartesianFlatProjection_idempotent (source : CartesianSourceCore parameters) :
    cartesianFlatProjection (cartesianFlatProjection source) = cartesianFlatProjection source := by
  change spinCartesianEquiv (flatSourceProjection (spinCartesianEquiv.symm
    (spinCartesianEquiv (flatSourceProjection (spinCartesianEquiv.symm source))))) = _
  rw [LinearEquiv.symm_apply_apply, flatSourceProjection_idempotent]
  rfl

theorem cartesianFlatProjection_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ source : CartesianSourceCore parameters,
      cartesianSourceNorm grade (cartesianFlatProjection source) ≤ constant * cartesianSourceNorm grade source := by
  obtain ⟨constant, nonnegative, bound⟩ := flatSourceProjection_bound parameters grade large
  refine ⟨constant, nonnegative, fun source => ?_⟩
  change cartesianSourceNorm grade (spinCartesianEquiv
    (flatSourceProjection (cartesianToSpin source))) ≤ _
  rw [spinCartesianEquiv_norm, ← cartesianToSpin_norm]
  exact bound (cartesianToSpin source)

end Grad.FlatSourceProjection
