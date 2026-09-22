import SRC6PublicBoundary

noncomputable section

namespace Grad.SourceCollarBulk

open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarAngular
open Grad.CartesianState Grad.AxisCore

/-- The exact multiplier lowering `nu^(t+1)` strong storage to the literal
`nu^t` AH row. -/
def annularWeightLoweringRatio (mode : ℤ × ℤ) : ℂ :=
  (annularFrequency mode.1 mode.2 : ℂ)⁻¹

theorem annularWeightLoweringRatio_norm_le_one (mode : ℤ × ℤ) :
    ‖annularWeightLoweringRatio mode‖ ≤ 1 := by
  have frequencyOne : 1 ≤ annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]
  rw [annularWeightLoweringRatio, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (annularFrequency_pos mode.1 mode.2).le]
  exact (inv_le_one₀ (annularFrequency_pos mode.1 mode.2)).mpr frequencyOne

def annularWeightLoweringRowValue {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) : DivisionRow dimension lower :=
  ⟨fun mode => annularWeightLoweringRatio mode • field mode, by
    let comparison := (1 : ℂ) • field
    apply (lp.memℓp comparison).mono'
    intro mode
    change ‖annularWeightLoweringRatio mode • field mode‖ ≤ ‖(1 : ℂ) • field mode‖
    rw [norm_smul, norm_smul, norm_one, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (annularWeightLoweringRatio_norm_le_one mode)⟩

theorem annularWeightLoweringRowValue_norm_le {dimension : ℕ} (lower : ℝ)
    (field : DivisionRow dimension lower) :
    ‖annularWeightLoweringRowValue lower field‖ ≤ ‖field‖ := by
  calc
    _ ≤ ‖(1 : ℂ) • field‖ := by
      apply lp.norm_mono (by norm_num)
      intro mode
      change ‖annularWeightLoweringRatio mode • field mode‖ ≤ ‖(1 : ℂ) • field mode‖
      rw [norm_smul, norm_smul, norm_one, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (annularWeightLoweringRatio_norm_le_one mode)
    _ = _ := by simp only [one_smul]

def annularWeightLoweringRowLinear {dimension : ℕ} (lower : ℝ) :
    DivisionRow dimension lower →ₗ[ℂ] DivisionRow dimension lower where
  toFun := annularWeightLoweringRowValue lower
  map_add' first second := by
    apply lp.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    exact smul_comm (annularWeightLoweringRatio mode) scalar (field mode)

def annularWeightLoweringArrayLinear {dimension radial : ℕ} (lower : ℝ) :
    DivisionJetArray dimension lower radial →ₗ[ℂ]
      DivisionJetArray dimension lower radial where
  toFun field := WithLp.toLp 1
    (fun index => annularWeightLoweringRowLinear lower (field index))
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact map_add (annularWeightLoweringRowLinear lower) (first index) (second index)
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact map_smul (annularWeightLoweringRowLinear lower) scalar (field index)

theorem annularWeightLoweringArrayLinear_norm_le {dimension radial : ℕ}
    (lower : ℝ) (field : DivisionJetArray dimension lower radial) :
    ‖annularWeightLoweringArrayLinear lower field‖ ≤ ‖field‖ := by
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  exact Finset.sum_le_sum
    (fun index _ => annularWeightLoweringRowValue_norm_le lower (field index))

def annularWeightLoweringArray {dimension radial : ℕ} (lower : ℝ) :
    DivisionJetArray dimension lower radial →L[ℂ]
      DivisionJetArray dimension lower radial :=
  LinearMap.mkContinuous (annularWeightLoweringArrayLinear lower) 1
    (fun field => by
      simpa only [one_mul] using annularWeightLoweringArrayLinear_norm_le lower field)

theorem annularWeightLoweringArray_mem_graph {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial) :
    annularWeightLoweringArray lower field.val ∈
      annularDerivativeGraph dimension lower positive radial := by
  apply (annularDerivativeGraph_mem_iff lower positive radial _).mpr
  intro index mode
  change HasWeakRadialDerivative lower positive
    (annularWeightLoweringRatio mode • field.val index.castSucc mode)
    (annularWeightLoweringRatio mode • field.val index.succ mode)
  exact ((annularDerivativeGraph_mem_iff lower positive radial field.val).mp field.property
    index mode).smul _

/-- Bounded lowering from the strong `nu^(t+1)` graph to the literal
`nu^t` value-and-radial-derivative graph. -/
def annularWeightLowering {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower) :
    annularDerivativeGraph dimension lower positive radial →L[ℂ]
      annularDerivativeGraph dimension lower positive radial :=
  ((annularWeightLoweringArray lower).comp
    (annularDerivativeGraph dimension lower positive radial).subtypeL).codRestrict
      (annularDerivativeGraph dimension lower positive radial)
      (annularWeightLoweringArray_mem_graph lower positive)

@[simp] theorem annularWeightLowering_apply {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial)
    (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    (annularWeightLowering lower positive field).val index mode =
      annularWeightLoweringRatio mode • field.val index mode := rfl

theorem annularWeightLowering_norm_le {dimension radial : ℕ}
    (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive radial) :
    ‖annularWeightLowering lower positive field‖ ≤ ‖field‖ :=
  annularWeightLoweringArrayLinear_norm_le lower field.val

theorem annularWeightLoweringRatio_weight (power : ℕ) (mode : ℤ × ℤ) :
    annularWeightLoweringRatio mode *
        (annularFrequency mode.1 mode.2 : ℂ) ^ (power + 1) =
      (annularFrequency mode.1 mode.2 : ℂ) ^ power := by
  have nonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 := by
    exact_mod_cast (annularFrequency_pos mode.1 mode.2).ne'
  unfold annularWeightLoweringRatio
  rw [pow_succ]
  field_simp

theorem annularWeightLowering_restrictionModeLp {dimension : ℕ}
    (lower : ℝ) (power radial : ℕ) (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    annularWeightLoweringRatio mode •
        restrictionModeLp lower (power + 1) radial parameters field mode =
      restrictionModeLp lower power radial parameters field mode := by
  unfold restrictionModeLp
  rw [smul_smul, annularWeightLoweringRatio_weight]

/-- Literal AH value graph for `F0`, with `nu^t` rather than the stronger
`nu^(t+1)` storage used in the restriction estimate. -/
def completedForceTangentialAH (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ) :
    ZAmbient parameters (tangential + 2) →L[ℂ]
      annularDerivativeGraph 1 lower positive 1 :=
  (annularWeightLowering lower positive).comp
    (completedForceTangential lower positive bounded parameters tangential)

@[simp] theorem completedForceTangentialAH_row
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2))
    (index : Fin 2) (mode : ℤ × ℤ) :
    (completedForceTangentialAH lower positive bounded parameters tangential source).val index mode =
      annularWeightLoweringRatio mode •
        (completedForceTangential lower positive bounded parameters tangential source).val index mode := rfl

theorem completedForceTangentialAH_bound
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2)) :
    ‖completedForceTangentialAH lower positive bounded parameters tangential source‖ ≤
      planarBulkConstant tangential * ‖source‖ :=
  (annularWeightLowering_norm_le lower positive _).trans
    (completedForceTangential_bound lower positive bounded parameters tangential source)

end Grad.SourceCollarBulk
