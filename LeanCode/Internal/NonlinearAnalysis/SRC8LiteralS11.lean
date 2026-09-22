import SRC7LiteralAHGraph

noncomputable section

namespace Grad.SourceCollarBulk

open Grad.SourceCollarDivision Grad.SourceCollarAngular
open Grad.CartesianState Grad.AxisCore

/-- Exact ratio converting strong `nu^(t+1)` storage into the original
AH multiplier `(1+|m|)nu^t`. -/
def annularS11Ratio (mode : ℤ × ℤ) : ℂ :=
  ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) /
    (annularFrequency mode.1 mode.2 : ℂ)

theorem annularS11Ratio_norm_le_one (mode : ℤ × ℤ) :
    ‖annularS11Ratio mode‖ ≤ 1 := by
  have comparison : 1 + |(mode.1 : ℝ)| ≤ annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.2 : ℝ)]
  rw [annularS11Ratio, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1 + |(mode.1 : ℝ)|),
    Real.norm_of_nonneg (annularFrequency_pos mode.1 mode.2).le,
    div_le_one (annularFrequency_pos mode.1 mode.2)]
  exact comparison

def annularS11RowValue {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) : DivisionRow dimension lower :=
  ⟨fun mode => annularS11Ratio mode • field mode, by
    let comparison := (1 : ℂ) • field
    apply (lp.memℓp comparison).mono'
    intro mode
    change ‖annularS11Ratio mode • field mode‖ ≤ ‖(1 : ℂ) • field mode‖
    rw [norm_smul, norm_smul, norm_one, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (annularS11Ratio_norm_le_one mode)⟩

theorem annularS11RowValue_norm_le {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) :
    ‖annularS11RowValue lower field‖ ≤ ‖field‖ := by
  calc
    _ ≤ ‖(1 : ℂ) • field‖ := by
      apply lp.norm_mono (by norm_num)
      intro mode
      change ‖annularS11Ratio mode • field mode‖ ≤ ‖(1 : ℂ) • field mode‖
      rw [norm_smul, norm_smul, norm_one, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (annularS11Ratio_norm_le_one mode)
    _ = _ := by simp only [one_smul]

def annularS11RowLinear {dimension : ℕ} (lower : ℝ) :
    DivisionRow dimension lower →ₗ[ℂ] DivisionRow dimension lower where
  toFun := annularS11RowValue lower
  map_add' first second := by
    apply lp.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    exact smul_comm (annularS11Ratio mode) scalar (field mode)

def annularS11ArrayLinear {dimension radial : ℕ} (lower : ℝ) :
    DivisionJetArray dimension lower radial →ₗ[ℂ]
      DivisionJetArray dimension lower radial where
  toFun field := WithLp.toLp 1 (fun index => annularS11RowLinear lower (field index))
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact map_add (annularS11RowLinear lower) (first index) (second index)
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact map_smul (annularS11RowLinear lower) scalar (field index)

theorem annularS11ArrayLinear_norm_le {dimension radial : ℕ} (lower : ℝ)
    (field : DivisionJetArray dimension lower radial) :
    ‖annularS11ArrayLinear lower field‖ ≤ ‖field‖ := by
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  exact Finset.sum_le_sum (fun index _ => annularS11RowValue_norm_le lower (field index))

def annularS11Array {dimension radial : ℕ} (lower : ℝ) :
    DivisionJetArray dimension lower radial →L[ℂ]
      DivisionJetArray dimension lower radial :=
  LinearMap.mkContinuous (annularS11ArrayLinear lower) 1
    (fun field => by simpa only [one_mul] using annularS11ArrayLinear_norm_le lower field)

theorem annularS11Array_mem_graph {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial) :
    annularS11Array lower field.val ∈
      annularDerivativeGraph dimension lower positive radial := by
  apply (annularDerivativeGraph_mem_iff lower positive radial _).mpr
  intro index mode
  change HasWeakRadialDerivative lower positive
    (annularS11Ratio mode • field.val index.castSucc mode)
    (annularS11Ratio mode • field.val index.succ mode)
  exact ((annularDerivativeGraph_mem_iff lower positive radial field.val).mp field.property
    index mode).smul _

/-- The literal completed AH `S^(1;1)` graph with
`(1+|m|)nu^t` on both `W F0` and its weak radial derivative. -/
def annularS11 {dimension radial : ℕ} (lower : ℝ) (positive : 0 < lower) :
    annularDerivativeGraph dimension lower positive radial →L[ℂ]
      annularDerivativeGraph dimension lower positive radial :=
  ((annularS11Array lower).comp
    (annularDerivativeGraph dimension lower positive radial).subtypeL).codRestrict
      (annularDerivativeGraph dimension lower positive radial)
      (annularS11Array_mem_graph lower positive)

@[simp] theorem annularS11_apply {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularS11 lower positive field).val index mode =
      annularS11Ratio mode • field.val index mode := rfl

theorem annularS11_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial) :
    ‖annularS11 lower positive field‖ ≤ ‖field‖ :=
  annularS11ArrayLinear_norm_le lower field.val

theorem annularS11Ratio_weight (power : ℕ) (mode : ℤ × ℤ) :
    annularS11Ratio mode *
        (annularFrequency mode.1 mode.2 : ℂ) ^ (power + 1) =
      ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) *
        (annularFrequency mode.1 mode.2 : ℂ) ^ power := by
  have nonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 := by
    exact_mod_cast (annularFrequency_pos mode.1 mode.2).ne'
  unfold annularS11Ratio
  rw [pow_succ]
  field_simp

def completedForceS11 (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ) :
    ZAmbient parameters (tangential + 2) →L[ℂ]
      annularDerivativeGraph 1 lower positive 1 :=
  (annularS11 lower positive).comp
    (completedForceTangential lower positive bounded parameters tangential)

@[simp] theorem completedForceS11_row
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2))
    (index : Fin 2) (mode : ℤ × ℤ) :
    (completedForceS11 lower positive bounded parameters tangential source).val index mode =
      annularS11Ratio mode •
        (completedForceTangential lower positive bounded parameters tangential source).val index mode := rfl

theorem completedForceS11_bound
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2)) :
    ‖completedForceS11 lower positive bounded parameters tangential source‖ ≤
      planarBulkConstant tangential * ‖source‖ :=
  (annularS11_norm_le lower positive _).trans
    (completedForceTangential_bound lower positive bounded parameters tangential source)

end Grad.SourceCollarBulk
