import TRM11PublicBoundary

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.SourceCollarBulk

open Grad.SourceCollarDivision Grad.SourceCollarAngular

/-- The exact diagonal multiplier which turns a stored `nu^(p+1)` angular
row into the stored `nu^p` row of its angular derivative. -/
def annularAngularRatio (mode : ℤ × ℤ) : ℂ :=
  (Complex.I * (mode.1 : ℂ)) / (annularFrequency mode.1 mode.2 : ℂ)

theorem annularAngularRatio_norm_le_one (mode : ℤ × ℤ) :
    ‖annularAngularRatio mode‖ ≤ 1 := by
  rw [annularAngularRatio, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (annularFrequency_pos mode.1 mode.2).le]
  have modeNorm : ‖(mode.1 : ℂ)‖ = |(mode.1 : ℝ)| := by norm_cast
  rw [modeNorm, div_le_one (annularFrequency_pos mode.1 mode.2)]
  unfold annularFrequency
  linarith [abs_nonneg (mode.2 : ℝ)]

def annularAngularRowValue {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) : DivisionRow dimension lower :=
  ⟨fun mode => annularAngularRatio mode • field mode, by
    let comparison := (1 : ℂ) • field
    apply (lp.memℓp comparison).mono'
    intro mode
    change ‖annularAngularRatio mode • field mode‖ ≤ ‖(1 : ℂ) • field mode‖
    rw [norm_smul, norm_smul, norm_one, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (annularAngularRatio_norm_le_one mode)⟩

theorem annularAngularRowValue_norm_le {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) :
    ‖annularAngularRowValue lower field‖ ≤ ‖field‖ := by
  calc
    _ ≤ ‖(1 : ℂ) • field‖ := by
      apply lp.norm_mono (by norm_num)
      intro mode
      change ‖annularAngularRatio mode • field mode‖ ≤ ‖(1 : ℂ) • field mode‖
      rw [norm_smul, norm_smul, norm_one, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (annularAngularRatio_norm_le_one mode)
    _ = _ := by simp only [one_smul]

def annularAngularRowLinear {dimension : ℕ} (lower : ℝ) :
    DivisionRow dimension lower →ₗ[ℂ] DivisionRow dimension lower where
  toFun := annularAngularRowValue lower
  map_add' first second := by
    apply lp.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    exact smul_comm (annularAngularRatio mode) scalar (field mode)

def annularAngularRow {dimension : ℕ} (lower : ℝ) :
    DivisionRow dimension lower →L[ℂ] DivisionRow dimension lower :=
  LinearMap.mkContinuous (annularAngularRowLinear lower) 1
    (fun field => by
      change ‖annularAngularRowValue lower field‖ ≤ 1 * ‖field‖
      simpa only [one_mul] using annularAngularRowValue_norm_le lower field)

@[simp] theorem annularAngularRow_apply {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) (mode : ℤ × ℤ) :
    annularAngularRow lower field mode = annularAngularRatio mode • field mode := rfl

theorem annularAngularRow_norm_le {dimension : ℕ} (lower : ℝ) :
    ‖annularAngularRow (dimension := dimension) lower‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def annularAngularArrayLinear {dimension radial : ℕ} (lower : ℝ) :
    DivisionJetArray dimension lower radial →ₗ[ℂ]
      DivisionJetArray dimension lower radial where
  toFun field := WithLp.toLp 1 (fun index => annularAngularRow lower (field index))
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact map_add (annularAngularRow lower) (first index) (second index)
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact map_smul (annularAngularRow lower) scalar (field index)

theorem annularAngularArrayLinear_norm_le {dimension radial : ℕ} (lower : ℝ)
    (field : DivisionJetArray dimension lower radial) :
    ‖annularAngularArrayLinear lower field‖ ≤ ‖field‖ := by
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  exact Finset.sum_le_sum (fun index _ => annularAngularRowValue_norm_le lower (field index))

def annularAngularArray {dimension radial : ℕ} (lower : ℝ) :
    DivisionJetArray dimension lower radial →L[ℂ]
      DivisionJetArray dimension lower radial :=
  LinearMap.mkContinuous (annularAngularArrayLinear lower) 1
    (fun field => by simpa only [one_mul] using annularAngularArrayLinear_norm_le lower field)

theorem annularAngularArray_mem_graph {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial) :
    annularAngularArray lower field.val ∈
      annularDerivativeGraph dimension lower positive radial := by
  apply (annularDerivativeGraph_mem_iff lower positive radial _).mpr
  intro index mode
  change HasWeakRadialDerivative lower positive
    (annularAngularRatio mode • field.val index.castSucc mode)
    (annularAngularRatio mode • field.val index.succ mode)
  exact ((annularDerivativeGraph_mem_iff lower positive radial field.val).mp field.property
    index mode).smul _

/-- Genuine angular differentiation on every coordinate of the closed weak
radial graph. The input is stored with one additional `nu` weight. -/
def annularAngularDerivative {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) :
    annularDerivativeGraph dimension lower positive radial →L[ℂ]
      annularDerivativeGraph dimension lower positive radial :=
  ((annularAngularArray lower).comp
    (annularDerivativeGraph dimension lower positive radial).subtypeL).codRestrict
      (annularDerivativeGraph dimension lower positive radial)
      (annularAngularArray_mem_graph lower positive)

@[simp] theorem annularAngularDerivative_apply {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularAngularDerivative lower positive field).val index mode =
      annularAngularRatio mode • field.val index mode := rfl

theorem annularAngularDerivative_apply_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial) :
    ‖annularAngularDerivative lower positive field‖ ≤ ‖field‖ :=
  annularAngularArrayLinear_norm_le lower field.val

theorem annularAngularDerivative_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) :
    ‖annularAngularDerivative (dimension := dimension) (radial := radial)
      lower positive‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using annularAngularDerivative_apply_norm_le lower positive field

theorem annularAngularRatio_weight (power : ℕ) (mode : ℤ × ℤ) :
    annularAngularRatio mode * (annularFrequency mode.1 mode.2 : ℂ) ^ (power + 1) =
      (Complex.I * (mode.1 : ℂ)) *
        (annularFrequency mode.1 mode.2 : ℂ) ^ power := by
  have nonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 := by
    exact_mod_cast (annularFrequency_pos mode.1 mode.2).ne'
  unfold annularAngularRatio
  rw [pow_succ, div_eq_mul_inv]
  field_simp

end Grad.SourceCollarBulk
