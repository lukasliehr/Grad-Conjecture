import AIY5OriginalBulkWeightEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularCurrentSource Grad.AnnularVariational

/-- A norm-one symbol converting the genuine angular derivative to |m|g. -/
def angularRecoverySymbol (mode : ℤ × ℤ) : ℂ :=
  if 0 ≤ mode.1 then -Complex.I else Complex.I

theorem angularRecoverySymbol_norm (mode : ℤ × ℤ) : ‖angularRecoverySymbol mode‖ = 1 := by
  unfold angularRecoverySymbol
  split_ifs <;> simp

def angularRecoveryMap (lower : ℝ) : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  complexLpTwoMap
    (fun mode => angularRecoverySymbol mode • ContinuousLinearMap.id ℂ (RadialL2 1 lower))
    1 zero_le_one (fun mode field => by
      change ‖angularRecoverySymbol mode • field‖ ≤ 1 * ‖field‖
      rw [norm_smul, angularRecoverySymbol_norm])

theorem angularRecoveryMap_bound (lower : ℝ) (field : DivisionRow 1 lower) :
    ‖angularRecoveryMap lower field‖ ≤ ‖field‖ := by
  simpa only [angularRecoveryMap, one_mul] using complexLpTwoMap_bound
    (fun mode : ℤ × ℤ => angularRecoverySymbol mode • ContinuousLinearMap.id ℂ (RadialL2 1 lower))
    1 zero_le_one (fun mode field => by
      change ‖angularRecoverySymbol mode • field‖ ≤ 1 * ‖field‖
      rw [norm_smul, angularRecoverySymbol_norm]) field

def strengthenedG (lower : ℝ) (g rg : DivisionRow 1 lower) : DivisionRow 1 lower :=
  g + angularRecoveryMap lower rg

theorem strengthenedG_bound (lower : ℝ) (g rg : DivisionRow 1 lower) :
    ‖strengthenedG lower g rg‖ ≤ ‖g‖ + ‖rg‖ :=
  (norm_add_le _ _).trans (add_le_add le_rfl (angularRecoveryMap_bound lower rg))

theorem angularRecoverySymbol_product (mode : ℤ × ℤ) :
    angularRecoverySymbol mode * (Complex.I * (mode.1 : ℂ)) = (|(mode.1 : ℝ)| : ℝ) := by
  unfold angularRecoverySymbol
  split_ifs with nonnegative
  · have positiveReal : 0 ≤ (mode.1 : ℝ) := by exact_mod_cast nonnegative
    rw [abs_of_nonneg positiveReal]
    push_cast
    linear_combination -(mode.1 : ℂ) * Complex.I_sq
  · have negativeReal : (mode.1 : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge nonnegative)
    rw [abs_of_neg negativeReal]
    push_cast
    linear_combination (mode.1 : ℂ) * Complex.I_sq

/-- The original strengthened angular normalization is exactly (1+|m|)g,
with no radial derivative and no loss of an inserted tangential grade. -/
theorem strengthenedG_mode (lower : ℝ) (g rg : DivisionRow 1 lower)
    (relation : ∀ mode : ℤ × ℤ, rg mode = (Complex.I * (mode.1 : ℂ)) • g mode)
    (mode : ℤ × ℤ) :
    strengthenedG lower g rg mode = ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • g mode := by
  change g mode + angularRecoverySymbol mode • rg mode = _
  rw [relation, smul_smul, angularRecoverySymbol_product]
  simp only [Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]

def originalAngularDecode (lower : ℝ) : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  complexLpTwoMap
    (fun mode : ℤ × ℤ => (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) •
      ContinuousLinearMap.id ℂ (RadialL2 1 lower))
    1 zero_le_one (fun mode field => by
      change ‖(((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • field‖ ≤ 1 * ‖field‖
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
      exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg (mode.1 : ℝ)]))

theorem originalAngularDecode_bound (lower : ℝ) (field : DivisionRow 1 lower) :
    ‖originalAngularDecode lower field‖ ≤ ‖field‖ := by
  simpa only [originalAngularDecode, one_mul] using complexLpTwoMap_bound
    (fun mode : ℤ × ℤ => (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) •
      ContinuousLinearMap.id ℂ (RadialL2 1 lower))
    1 zero_le_one (fun mode field => by
      change ‖(((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • field‖ ≤ 1 * ‖field‖
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
      exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg (mode.1 : ℝ)])) field

theorem strengthenedG_decode (lower : ℝ) (g rg : DivisionRow 1 lower)
    (relation : ∀ mode : ℤ × ℤ, rg mode = (Complex.I * (mode.1 : ℂ)) • g mode) :
    originalAngularDecode lower (strengthenedG lower g rg) = g ∧
    sourceAngularBulk lower (strengthenedG lower g rg) = rg := by
  have weightNonzero (mode : ℤ × ℤ) : ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + |(mode.1 : ℝ)| by positivity))
  constructor
  · apply lp.ext
    funext mode
    change (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • strengthenedG lower g rg mode = g mode
    rw [strengthenedG_mode lower g rg relation, smul_smul, Complex.ofReal_inv,
      inv_mul_cancel₀ (weightNonzero mode), one_smul]
  · apply lp.ext
    funext mode
    rw [sourceAngularBulk_mode, strengthenedG_mode lower g rg relation, relation, smul_smul]
    congr 1
    unfold sourceAngularRatio
    exact div_mul_cancel₀ _ (weightNonzero mode)

theorem strengthenedG_component_bounds (lower : ℝ) (g rg : DivisionRow 1 lower)
    (relation : ∀ mode : ℤ × ℤ, rg mode = (Complex.I * (mode.1 : ℂ)) • g mode) :
    ‖g‖ ≤ ‖strengthenedG lower g rg‖ ∧ ‖rg‖ ≤ ‖strengthenedG lower g rg‖ := by
  obtain ⟨first,second⟩ := strengthenedG_decode lower g rg relation
  constructor
  · have bound := originalAngularDecode_bound lower (strengthenedG lower g rg)
    rw [first] at bound
    exact bound
  · have bound := sourceAngularBulk_bound lower (strengthenedG lower g rg)
    rw [second] at bound
    exact bound

end Grad.AnnularStrongData
