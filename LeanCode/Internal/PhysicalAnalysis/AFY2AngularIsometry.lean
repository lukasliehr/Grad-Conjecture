import AFY1StrongMatchingSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- A private coordinate construction used for the actual angular phase below. -/
def highUnitaryLinear (L sigma gamma ell : ℝ) (grade : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (unit : ∀ mode, ‖multiplier mode‖ = 1) :
    HighBoundaryGrade L sigma gamma ell grade →ₗ[ℂ] HighBoundaryGrade L sigma gamma ell grade where
  toFun field := ⟨⟨fun mode => multiplier mode • field.val mode,
    field.val.property.mono' (fun mode => by rw [norm_smul, unit, one_mul])⟩, by
      apply (highBoundary_mem L sigma gamma ell grade _).mpr
      apply Subtype.ext
      funext mode
      change (if 3 ≤ |mode.1| then multiplier mode • field.val mode else 0) =
        multiplier mode • field.val mode
      split_ifs with high
      · rfl
      · rw [highBoundary_low L sigma gamma ell grade field mode high, smul_zero]⟩
  map_add' first second := by
    apply Subtype.ext
    apply Subtype.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply Subtype.ext
    apply Subtype.ext
    funext mode
    change multiplier mode • (scalar • field.val mode) = scalar • (multiplier mode • field.val mode)
    exact smul_comm _ _ _

theorem highUnitaryLinear_coordinate (L sigma gamma ell : ℝ) (grade : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (unit : ∀ mode, ‖multiplier mode‖ = 1)
    (field : HighBoundaryGrade L sigma gamma ell grade) (mode : ℤ × ℤ) :
    (highUnitaryLinear L sigma gamma ell grade multiplier unit field).val mode =
      multiplier mode • field.val mode := rfl

theorem highUnitaryLinear_norm (L sigma gamma ell : ℝ) (grade : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (unit : ∀ mode, ‖multiplier mode‖ = 1)
    (field : HighBoundaryGrade L sigma gamma ell grade) :
    ‖highUnitaryLinear L sigma gamma ell grade multiplier unit field‖ = ‖field‖ := by
  have point : ∀ mode,
      ‖(highUnitaryLinear L sigma gamma ell grade multiplier unit field).val mode‖ = ‖field.val mode‖ := by
    intro mode
    rw [highUnitaryLinear_coordinate, norm_smul, unit, one_mul]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun mode => (point mode).le))
    (lp.norm_mono (by norm_num) (fun mode => (point mode).ge))

def highUnitaryEquiv (L sigma gamma ell : ℝ) (grade : ℕ)
    (multiplier : ℤ × ℤ → ℂ) (unit : ∀ mode, ‖multiplier mode‖ = 1) :
    HighBoundaryGrade L sigma gamma ell grade ≃ₗᵢ[ℂ] HighBoundaryGrade L sigma gamma ell grade where
  toLinearEquiv :=
    { highUnitaryLinear L sigma gamma ell grade multiplier unit with
      invFun := highUnitaryLinear L sigma gamma ell grade (fun mode => (multiplier mode)⁻¹)
        (fun mode => by rw [norm_inv, unit, inv_one])
      left_inv := by
        intro field
        apply Subtype.ext
        apply Subtype.ext
        funext mode
        change (multiplier mode)⁻¹ • (multiplier mode • field.val mode) = field.val mode
        exact inv_smul_smul₀ (by intro zero; simpa [zero] using unit mode) _
      right_inv := by
        intro field
        apply Subtype.ext
        apply Subtype.ext
        funext mode
        change multiplier mode • ((multiplier mode)⁻¹ • field.val mode) = field.val mode
        exact smul_inv_smul₀ (by intro zero; simpa [zero] using unit mode) _ }
  norm_map' := highUnitaryLinear_norm L sigma gamma ell grade multiplier unit

/-- Normalized coordinates of the genuine im angular multiplier. -/
def strongAngularPhase (mode : ℤ × ℤ) : ℂ :=
  if 3 ≤ |mode.1| then Complex.I * (mode.1 : ℂ) / ((|(mode.1 : ℝ)| : ℝ) : ℂ) else 1

theorem strongAngularPhase_norm (mode : ℤ × ℤ) : ‖strongAngularPhase mode‖ = 1 := by
  unfold strongAngularPhase
  split_ifs with high
  · rw [norm_div, norm_mul, Complex.norm_I, one_mul]
    have castNorm : ‖(mode.1 : ℂ)‖ = |(mode.1 : ℝ)| := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    rw [castNorm, Complex.norm_real, Real.norm_eq_abs, abs_abs,
      div_self (highAngularAbs_pos mode high).ne']
  · exact norm_one

/-- AY1: R from Q T^(q+1/2) onto C^(q-1/2), with its exact inverse. -/
def highAngularIsometry (L sigma gamma ell : ℝ) (q : ℕ) :
    HighBoundaryGrade L sigma gamma ell (q + 1) ≃ₗᵢ[ℂ] StrongMatchingGrade L sigma gamma ell q :=
  highUnitaryEquiv L sigma gamma ell (q + 1) strongAngularPhase strongAngularPhase_norm

theorem highAngularIsometry_coordinate (L sigma gamma ell : ℝ) (q : ℕ)
    (field : HighBoundaryGrade L sigma gamma ell (q + 1)) (mode : ℤ × ℤ) :
    (highAngularIsometry L sigma gamma ell q field).val mode = strongAngularPhase mode • field.val mode := rfl

theorem highAngularIsometry_coefficient (L sigma gamma ell : ℝ) (q : ℕ)
    (field : HighBoundaryGrade L sigma gamma ell (q + 1)) (mode : ℤ × ℤ) :
    strongMatchingCoefficient L sigma gamma ell q (highAngularIsometry L sigma gamma ell q field) mode =
      (Complex.I * (mode.1 : ℂ)) • apBoundaryCoefficient L sigma gamma ell (q + 1) field.val mode := by
  by_cases high : 3 ≤ |mode.1|
  · change ((strongMatchingWeight L sigma gamma ell q mode : ℂ)⁻¹) •
      (strongAngularPhase mode • field.val mode) =
        (Complex.I * (mode.1 : ℂ)) • (((apBoundaryWeight L sigma gamma ell (q + 1) mode : ℂ)⁻¹) • field.val mode)
    rw [smul_smul, smul_smul, strongMatchingWeight, strongAngularPhase]
    simp only [if_pos high]
    push_cast
    congr 1
    have nonzero : ((|(mode.1 : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (highAngularAbs_pos mode high).ne'
    field_simp
  · rw [strongMatchingCoefficient_low L sigma gamma ell q _ mode high]
    unfold apBoundaryCoefficient
    rw [highBoundary_low L sigma gamma ell (q + 1) field mode high, smul_zero, smul_zero]

theorem highAngularIsometry_inverse_coefficient (L sigma gamma ell : ℝ) (q : ℕ)
    (field : StrongMatchingGrade L sigma gamma ell q) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell (q + 1)
      ((highAngularIsometry L sigma gamma ell q).symm field).val mode =
      (Complex.I * (mode.1 : ℂ))⁻¹ • strongMatchingCoefficient L sigma gamma ell q field mode := by
  by_cases high : 3 ≤ |mode.1|
  · have identity := highAngularIsometry_coefficient L sigma gamma ell q
      ((highAngularIsometry L sigma gamma ell q).symm field) mode
    rw [LinearIsometryEquiv.apply_symm_apply] at identity
    rw [identity]
    exact (inv_smul_smul₀ (mul_ne_zero Complex.I_ne_zero (by
      intro zero
      have integerZero : mode.1 = 0 := by exact_mod_cast zero
      simp [integerZero] at high)) _).symm
  · unfold apBoundaryCoefficient
    rw [highBoundary_low L sigma gamma ell (q + 1) _ mode high,
      strongMatchingCoefficient_low L sigma gamma ell q field mode high, smul_zero, smul_zero]

end Grad.GaugeCoefficients.Physical.Compensated
