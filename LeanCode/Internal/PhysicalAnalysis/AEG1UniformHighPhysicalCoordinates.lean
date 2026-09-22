import AED9ActualPhysicalWeakRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighWeak Grad.ActualReferenceAssembly

/-- The literal R/r symbol relative to the stored potential coordinate. -/
def highAngularRadiusRatio (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => ((mode.val.1 : ℝ) / max lower radius) /
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius,
    (continuous_const.div (continuous_const.max continuous_id)
      (fun _ => (positive.trans_le (le_max_left _ _)).ne')).div
      (annularPotentialWeight lower length positive mode.val.1 mode.val.2).continuous
      (fun radius => (annularPotentialWeight_pos lower length positive mode radius).ne')⟩

theorem highAngularRadiusRatio_bound (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |highAngularRadiusRatio lower length positive mode radius| ≤ 1 := by
  have rootPositive := annularPotentialWeight_pos lower length positive mode radius
  have rootSquare := annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside.1
  have dominated : ((mode.val.1 : ℝ) / radius) ^ 2 ≤
      annularPotential length radius mode.val.1 mode.val.2 := by
    rw [div_pow]
    exact le_add_of_nonneg_right (div_nonneg
      (mul_nonneg (highMultiplier_nonnegative _) (sq_nonneg _)) (sq_nonneg _))
  change |((mode.val.1 : ℝ) / max lower radius) /
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius| ≤ 1
  rw [max_eq_right inside.1, abs_div, abs_of_pos rootPositive]
  apply (div_le_one rootPositive).mpr
  nlinarith [sq_abs ((mode.val.1 : ℝ) / radius), abs_nonneg ((mode.val.1 : ℝ) / radius)]

def highEnergyAngularRadius (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  Complex.I • (annularScalarFamily lower (highAngularRadiusRatio lower length positive)
    1 (by norm_num) (highAngularRadiusRatio_bound lower length positive)).comp
      (annularEnergyMass lower length positive)

theorem highEnergyAngularRadius_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖highEnergyAngularRadius lower length positive field‖ ≤ ‖field‖ := by
  change ‖Complex.I • annularScalarFamily lower (highAngularRadiusRatio lower length positive)
    1 (by norm_num) (highAngularRadiusRatio_bound lower length positive)
      (annularEnergyMass lower length positive field)‖ ≤ _
  rw [norm_smul, Complex.norm_I, one_mul]
  exact (annularScalarFamily_bound _ _ _ _ _ _).trans (by
    simpa only [one_mul] using annularEnergyMass_bound lower length positive field)

/-- Physical scalar divided by radius, with the original factor 2 removed. -/
def highEnergyRadius (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (1 / 2 : ℂ) • annularEnergyRadial lower length positive

theorem highEnergyRadius_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖highEnergyRadius lower length positive field‖ ≤ (1 / 3 : ℝ) * ‖field‖ := by
  change ‖(1 / 2 : ℂ) • annularEnergyRadial lower length positive field‖ ≤ _
  rw [norm_smul]
  have half : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [half]
  linarith [annularEnergyRadial_bound lower length positive field]

theorem highInverseB_bound (mode : HighAnnularMode) :
    |(highMultiplier mode.val.1)⁻¹| ≤ 2 := by
  rw [abs_of_pos (inv_pos.mpr (highMultiplier_positive mode)), inv_eq_one_div]
  apply (div_le_iff₀ (highMultiplier_positive mode)).mpr
  have bound := (highMultiplier_bounds mode.val.1 (highMode_not_low mode.val.1 mode.property)).1
  linarith

/-- Literal cell derivative divided by L, undoing the b_m in AAG's test map. -/
def highEnergyCell (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (realLpDiagonal (fun mode : HighAnnularMode => (highMultiplier mode.val.1)⁻¹)
    2 (by norm_num) highInverseB_bound).comp (annularEnergyCell lower length positive)

theorem highEnergyCell_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖highEnergyCell lower length positive field‖ ≤ 2 * ‖field‖ :=
  (realLpDiagonal_bound (fun mode : HighAnnularMode => (highMultiplier mode.val.1)⁻¹)
    2 (by norm_num) highInverseB_bound (annularEnergyCell lower length positive field)).trans
    (mul_le_mul_of_nonneg_left (annularEnergyCell_bound lower length positive field) (by norm_num))

theorem physicalEnergyDecode_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖bEnergyDecode lower length positive field‖ ≤ ‖field‖ := by
  simpa only [bEnergyDecode, one_mul] using annularEnergyDiagonal_bound lower length positive
    (fun mode => Real.sqrt (highMultiplier mode.val.1)) 1 (by norm_num) bEnergyDecode_bound field

end Grad.AnnularCurrentEnergy
