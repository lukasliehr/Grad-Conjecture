import AAR1ActualBulkRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational Grad.CircularHighWeak

def annularDSymbol (mode : HighAnnularMode) : ℂ :=
  Complex.I * (((mode.val.1 : ℝ) * highMultiplier mode.val.1 : ℝ) : ℂ)

def annularAngularWeight (mode : HighAnnularMode) : ℝ := 1 + |(mode.val.1 : ℝ)|

theorem annularDSymbol_norm (mode : HighAnnularMode) :
    ‖annularDSymbol mode‖ = |(mode.val.1 : ℝ)| * highMultiplier mode.val.1 := by
  rw [annularDSymbol, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (highMultiplier_nonnegative _)]

theorem annularDSymbol_ne_zero (mode : HighAnnularMode) : annularDSymbol mode ≠ 0 := by
  have modeBound : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  have multiplier := (highMultiplier_bounds mode.val.1 (Grad.ActualReferenceAssembly.highMode_not_low _ mode.property)).1
  apply norm_pos_iff.mp
  rw [annularDSymbol_norm]
  exact mul_pos (by linarith) (by linarith)

/-- AG1's sharp angular gain for the actual high D symbol. -/
theorem annularDSymbol_inverse_weighted_bound (mode : HighAnnularMode) :
    annularAngularWeight mode * ‖-(annularDSymbol mode)⁻¹‖ ≤ 12 / 5 := by
  have modeBound : (3 : ℝ) ≤ |(mode.val.1 : ℝ)| := by exact_mod_cast mode.property
  have multiplier := (highMultiplier_bounds mode.val.1 (Grad.ActualReferenceAssembly.highMode_not_low _ mode.property)).1
  have modePositive : 0 < |(mode.val.1 : ℝ)| := by linarith
  have multiplierPositive : 0 < highMultiplier mode.val.1 := by linarith
  rw [norm_neg, norm_inv, annularDSymbol_norm, ← div_eq_mul_inv]
  apply (div_le_iff₀ (mul_pos modePositive multiplierPositive)).2
  unfold annularAngularWeight
  nlinarith [mul_nonneg (abs_nonneg (mode.val.1 : ℝ)) (sub_nonneg.mpr multiplier)]

theorem annularDSymbol_inverse_bound (mode : HighAnnularMode) :
    ‖-(annularDSymbol mode)⁻¹‖ ≤ 12 / 5 := by
  have enlarged : ‖-(annularDSymbol mode)⁻¹‖ ≤
      annularAngularWeight mode * ‖-(annularDSymbol mode)⁻¹‖ := by
    unfold annularAngularWeight
    nlinarith [norm_nonneg (-(annularDSymbol mode)⁻¹), abs_nonneg (mode.val.1 : ℝ)]
  exact enlarged.trans (annularDSymbol_inverse_weighted_bound mode)

def annularPMode (lower : ℝ) (mode : HighAnnularMode) :
    RadialL2 1 lower →L[ℂ] RadialL2 1 lower :=
  (-(annularDSymbol mode)⁻¹) • ContinuousLinearMap.id ℂ (RadialL2 1 lower)

theorem annularPMode_bound (lower : ℝ) (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    ‖annularPMode lower mode field‖ ≤ (12 / 5 : ℝ) * ‖field‖ := by
  change ‖(-(annularDSymbol mode)⁻¹) • field‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (annularDSymbol_inverse_bound mode) (norm_nonneg _)

def annularAngularPMode (lower : ℝ) (mode : HighAnnularMode) :
    RadialL2 1 lower →L[ℂ] RadialL2 1 lower :=
  (annularAngularWeight mode : ℂ) • annularPMode lower mode

theorem annularAngularPMode_bound (lower : ℝ) (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    ‖annularAngularPMode lower mode field‖ ≤ (12 / 5 : ℝ) * ‖field‖ := by
  have nonnegative : 0 ≤ annularAngularWeight mode := by unfold annularAngularWeight; positivity
  change ‖(annularAngularWeight mode : ℂ) • ((-(annularDSymbol mode)⁻¹) • field)‖ ≤ _
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg nonnegative,
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (annularDSymbol_inverse_weighted_bound mode) (norm_nonneg _)

def annularPMap (lower : ℝ) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  complexLpTwoMap (annularPMode lower) (12 / 5) (by norm_num) (annularPMode_bound lower)

/-- The normalized angular grade-one p coordinate, with its exact weight. -/
def annularAngularPMap (lower : ℝ) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  complexLpTwoMap (annularAngularPMode lower) (12 / 5) (by norm_num) (annularAngularPMode_bound lower)

theorem annularPMap_apply (lower : ℝ) (field : AnnularBulk lower) (mode : HighAnnularMode) :
    annularPMap lower field mode = (-(annularDSymbol mode)⁻¹) • field mode := rfl

theorem annularAngularPMap_apply (lower : ℝ) (field : AnnularBulk lower) (mode : HighAnnularMode) :
    annularAngularPMap lower field mode =
      (annularAngularWeight mode : ℂ) • annularPMap lower field mode := rfl

theorem annularAngularPMap_bound (lower : ℝ) (field : AnnularBulk lower) :
    ‖annularAngularPMap lower field‖ ≤ (12 / 5 : ℝ) * ‖field‖ :=
  complexLpTwoMap_bound _ _ _ _ field

theorem annularPMap_D (lower : ℝ) (field : AnnularBulk lower) (mode : HighAnnularMode) :
    annularDSymbol mode • annularPMap lower field mode = -field mode := by
  rw [annularPMap_apply, smul_smul, mul_neg,
    mul_inv_cancel₀ (annularDSymbol_ne_zero mode), neg_one_smul]

end Grad.AnnularReconstruction
