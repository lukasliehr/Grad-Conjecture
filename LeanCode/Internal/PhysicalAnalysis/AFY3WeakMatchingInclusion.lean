import AFY2AngularIsometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace

def strongWeakMultiplier (L ell : ℝ) (mode : ℤ × ℤ) : ℂ :=
  (|(mode.1 : ℝ)| / apBoundaryFrequency L ell mode : ℝ)

theorem strongWeakMultiplier_bound (L ell : ℝ) (mode : ℤ × ℤ) :
    ‖strongWeakMultiplier L ell mode‖ ≤ 1 := by
  rw [strongWeakMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (apBoundaryFrequency_pos L ell mode).le)]
  exact (div_le_one (apBoundaryFrequency_pos L ell mode)).mpr (matchingAngularFrequency_le L ell mode)

def strongMatchingWeakLinear (L sigma gamma ell : ℝ) (q : ℕ) :
    StrongMatchingGrade L sigma gamma ell q →ₗ[ℂ] APBoundaryGrade L sigma gamma ell 1 q where
  toFun field := ⟨fun mode => strongWeakMultiplier L ell mode • field.val mode,
    field.val.property.mono' (fun mode => by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (strongWeakMultiplier_bound L ell mode)
        (norm_nonneg (field.val mode))).trans_eq (one_mul _))⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply Subtype.ext
    funext mode
    change strongWeakMultiplier L ell mode • (scalar • field.val mode) =
      scalar • (strongWeakMultiplier L ell mode • field.val mode)
    exact smul_comm _ _ _

/-- AY1's continuous inclusion C^(q-1/2) into the ordinary trace grade. -/
def strongMatchingWeak (L sigma gamma ell : ℝ) (q : ℕ) :
    StrongMatchingGrade L sigma gamma ell q →L[ℂ] APBoundaryGrade L sigma gamma ell 1 q :=
  (strongMatchingWeakLinear L sigma gamma ell q).mkContinuous 1 (fun field => by
    rw [one_mul]
    apply lp.norm_mono (by norm_num)
    intro mode
    change ‖strongWeakMultiplier L ell mode • field.val mode‖ ≤ ‖field.val mode‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (strongWeakMultiplier_bound L ell mode)
      (norm_nonneg (field.val mode))).trans_eq (one_mul _))

theorem strongMatchingWeak_bound (L sigma gamma ell : ℝ) (q : ℕ)
    (field : StrongMatchingGrade L sigma gamma ell q) :
    ‖strongMatchingWeak L sigma gamma ell q field‖ ≤ ‖field‖ := by
  apply lp.norm_mono (by norm_num)
  intro mode
  change ‖strongWeakMultiplier L ell mode • field.val mode‖ ≤ ‖field.val mode‖
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (strongWeakMultiplier_bound L ell mode)
    (norm_nonneg (field.val mode))).trans_eq (one_mul _)

theorem strongMatchingWeak_coefficient (L sigma gamma ell : ℝ) (q : ℕ) (positive : 1 ≤ q)
    (field : StrongMatchingGrade L sigma gamma ell q) (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell q (strongMatchingWeak L sigma gamma ell q field) mode =
      strongMatchingCoefficient L sigma gamma ell q field mode := by
  by_cases high : 3 ≤ |mode.1|
  · change ((apBoundaryWeight L sigma gamma ell q mode : ℂ)⁻¹) •
      (strongWeakMultiplier L ell mode • field.val mode) =
        ((strongMatchingWeight L sigma gamma ell q mode : ℂ)⁻¹) • field.val mode
    rw [smul_smul, strongMatchingWeight, if_pos high, strongWeakMultiplier,
      matchingBoundaryWeight_succ L sigma gamma ell q positive]
    push_cast
    congr 1
    field_simp
  · change ((apBoundaryWeight L sigma gamma ell q mode : ℂ)⁻¹) •
      (strongWeakMultiplier L ell mode • field.val mode) = _
    rw [highBoundary_low L sigma gamma ell (q + 1) field mode high,
      strongMatchingCoefficient_low L sigma gamma ell q field mode high, smul_zero, smul_zero]

/-- The stronger target realizes the SAME actual high angular trace. -/
theorem strongMatchingWeak_angular (L sigma gamma ell : ℝ) (q : ℕ)
    (field : APBoundaryGrade L sigma gamma ell 1 (q + 1)) :
    strongMatchingWeak L sigma gamma ell q
      (highAngularIsometry L sigma gamma ell q (highBoundaryProjection L sigma gamma ell (q + 1) field)) =
      apHighProjection L sigma gamma ell q (matchingAngular L sigma gamma ell q field) := by
  apply Subtype.ext
  funext mode
  change strongWeakMultiplier L ell mode •
      (strongAngularPhase mode • (if 3 ≤ |mode.1| then field mode else 0)) =
        if 3 ≤ |mode.1| then matchingAngularMultiplier L ell mode • field mode else 0
  by_cases high : 3 ≤ |mode.1|
  · simp only [if_pos high]
    rw [smul_smul, strongWeakMultiplier, strongAngularPhase, if_pos high, matchingAngularMultiplier]
    push_cast
    congr 1
    have nonzero : ((|(mode.1 : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (highAngularAbs_pos mode high).ne'
    field_simp
  · simp only [if_neg high, smul_zero]

end Grad.GaugeCoefficients.Physical.Compensated
