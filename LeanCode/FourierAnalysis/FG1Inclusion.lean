import FG1Grade

noncomputable section

open scoped BigOperators ENNReal

universe valueUniverse

namespace Grad.FourierGrade

def diagonalLinearMap {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (factor : FourierMode → ℂ) (factorBound : ∀ mode, ‖factor mode‖ ≤ 1) :
    lp (fun _ : FourierMode => Value) 2 →ₗ[ℂ] lp (fun _ : FourierMode => Value) 2 where
  toFun field := ⟨fun mode => factor mode • field mode,
    Memℓp.mono' field.property (fun mode => by
      rw [norm_smul]
      simpa using mul_le_mul_of_nonneg_right (factorBound mode) (norm_nonneg (field mode)))⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact smul_add (factor mode) (first mode) (second mode)
  map_smul' scalar field := by
    apply Subtype.ext
    change (fun mode => factor mode • (scalar • field mode)) =
      (fun mode => scalar • (factor mode • field mode))
    funext mode
    rw [smul_smul, smul_smul, mul_comm]

def diagonal {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (factor : FourierMode → ℂ) (factorBound : ∀ mode, ‖factor mode‖ ≤ 1) :
    lp (fun _ : FourierMode => Value) 2 →L[ℂ] lp (fun _ : FourierMode => Value) 2 :=
  (diagonalLinearMap factor factorBound).mkContinuous 1 (fun field => by
    simpa using lp.norm_mono (p := 2) (by norm_num) (x := diagonalLinearMap factor factorBound field)
      (y := field) (fun mode => by
        change ‖factor mode • field mode‖ ≤ ‖field mode‖
        rw [norm_smul]
        simpa using mul_le_mul_of_nonneg_right (factorBound mode) (norm_nonneg (field mode))))

def inclusionFactor (source target : ℕ) (mode : FourierMode) : ℂ :=
  ((frequencyWeight mode : ℂ)⁻¹) ^ (source - target)

theorem inclusionFactor_norm_le_one (source target : ℕ) (mode : FourierMode) :
    ‖inclusionFactor source target mode‖ ≤ 1 := by
  rw [inclusionFactor, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (frequencyWeight_pos mode)]
  exact pow_le_one₀ (inv_nonneg.mpr (frequencyWeight_pos mode).le)
    (inv_le_one_of_one_le₀ (frequencyWeight_one_le mode))

/-- The canonical coefficient-preserving contraction from grade `source` to grade `target`. -/
def inclusion {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (source target : ℕ) (_ordered : target ≤ source) : JGrade Value source →L[ℂ] JGrade Value target :=
  diagonal (inclusionFactor source target) (inclusionFactor_norm_le_one source target)

theorem inclusion_apply {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (source target : ℕ) (ordered : target ≤ source)
    (field : JGrade Value source) (mode : FourierMode) :
    inclusion source target ordered field mode = inclusionFactor source target mode • field mode := rfl

set_option maxHeartbeats 800000 in
theorem inclusion_norm_le_one {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (source target : ℕ) (ordered : target ≤ source) :
    ‖inclusion (Value := Value) source target ordered‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound
    (f := inclusion (Value := Value) source target ordered) (by norm_num) ?_
  intro field
  change ‖diagonalLinearMap (inclusionFactor source target)
    (inclusionFactor_norm_le_one source target) field‖ ≤ 1 * ‖field‖
  simpa using lp.norm_mono (p := 2) (by norm_num)
    (x := diagonalLinearMap (inclusionFactor source target)
      (inclusionFactor_norm_le_one source target) field)
    (y := field) (fun mode => by
      change ‖inclusionFactor source target mode • field mode‖ ≤ ‖field mode‖
      rw [norm_smul]
      simpa using mul_le_mul_of_nonneg_right (inclusionFactor_norm_le_one source target mode)
        (norm_nonneg (field mode)))

theorem inclusion_coefficient {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (source target : ℕ) (ordered : target ≤ source)
    (field : JGrade Value source) (mode : FourierMode) :
    coefficient target (inclusion source target ordered field) mode = coefficient source field mode := by
  simp only [coefficient, inclusion_apply, inclusionFactor, smul_smul]
  congr 1
  have nonzero : (frequencyWeight mode : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (frequencyWeight_ne_zero mode)
  rw [← inv_pow, inv_pow_sub₀ nonzero ordered,
    mul_comm ((frequencyWeight mode : ℂ) ^ source)⁻¹
      ((frequencyWeight mode : ℂ) ^ target),
    ← mul_assoc, ← mul_pow, inv_mul_cancel₀ nonzero, one_pow, one_mul]

theorem inclusion_injective {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (source target : ℕ) (ordered : target ≤ source) :
    Function.Injective (inclusion (Value := Value) source target ordered) := by
  intro first second equality
  apply ext_coefficients
  intro mode
  rw [← inclusion_coefficient source target ordered first mode,
    ← inclusion_coefficient source target ordered second mode, equality]

theorem inclusion_self {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) :
    inclusion (Value := Value) grade grade le_rfl = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro field
  apply ext_coefficients
  intro mode
  rw [inclusion_coefficient]
  rfl

theorem inclusion_comp {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (high middle low : ℕ)
    (middleHigh : middle ≤ high) (lowMiddle : low ≤ middle) :
    (inclusion (Value := Value) middle low lowMiddle).comp
      (inclusion high middle middleHigh) = inclusion high low (lowMiddle.trans middleHigh) := by
  apply ContinuousLinearMap.ext
  intro field
  apply ext_coefficients
  intro mode
  simp only [ContinuousLinearMap.comp_apply, inclusion_coefficient]

end Grad.FourierGrade
