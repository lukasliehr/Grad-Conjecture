import AJF5OriginalHighInsertedGraphGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Filter
open scoped Topology BigOperators ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularGrades Grad.AnnularOrbitGenerators

def energyCut (lower length : ℝ) (positive : 0 < lower) (support : Finset HighAnnularMode) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  annularEnergyDiagonal lower length positive (fun mode => if mode ∈ support then 1 else 0)
    1 (by norm_num) (fun mode => by split_ifs <;> norm_num)

theorem energyCut_val (lower length : ℝ) (positive : 0 < lower) (support : Finset HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    (energyCut lower length positive support field).val = originalLpCut support field.val := by
  apply lp.ext
  funext index
  rw [energyCut, annularEnergyDiagonal_apply, originalLpCut_apply]
  by_cases inside : index ∈ support <;> simp [inside]

theorem energyCut_norm (lower length : ℝ) (positive : 0 < lower) (support : Finset HighAnnularMode)
    (field : annularEnergySpace lower length positive) :
    ‖energyCut lower length positive support field‖ ≤ ‖field‖ := by
  change ‖(energyCut lower length positive support field).val‖ ≤ ‖field.val‖
  rw [energyCut_val]
  exact originalLpCut_norm support field.val

theorem energyCut_tendsto (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    Tendsto (fun support : Finset HighAnnularMode => energyCut lower length positive support field) atTop (𝓝 field) := by
  rw [tendsto_subtype_rng]
  simpa only [energyCut_val] using originalLpCut_tendsto field.val

theorem energyCut_weighted (lower length : ℝ) (positive : 0 < lower) (support : Finset HighAnnularMode)
    (field weighted : annularEnergySpace lower length positive) (coefficient : HighAnnularMode → ℂ)
    (actual : ∀ index, weighted.val index = coefficient index • field.val index) (index : HighAnnularMode) :
    (energyCut lower length positive support weighted).val index =
      coefficient index • (energyCut lower length positive support field).val index := by
  rw [energyCut_val, energyCut_val]
  exact originalLpCut_weighted support field.val weighted.val coefficient actual index

def fluxCut (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (support : Finset HighAnnularMode) :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ]
      annularOmegaGraph lower length positive lengthPositive :=
  annularOmegaGraphDiagonal lower length positive lengthPositive (fun mode => if mode ∈ support then 1 else 0)
    1 (by norm_num) (fun mode => by split_ifs <;> norm_num)

theorem fluxCut_row (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (support : Finset HighAnnularMode) (field : annularOmegaGraph lower length positive lengthPositive)
    (coordinate : Fin 2) :
    (fluxCut lower length positive lengthPositive support field).val coordinate = originalLpCut support (field.val coordinate) := by
  have diagonal : (fluxCut lower length positive lengthPositive support field).val coordinate =
      realLpDiagonal (fun mode => if mode ∈ support then 1 else 0) 1 (by norm_num)
        (fun mode => by split_ifs <;> norm_num) (field.val coordinate) := by
    fin_cases coordinate
    · exact annularOmegaGraphDiagonal_value lower length positive lengthPositive _ _ _ _ field
    · exact annularOmegaGraphDiagonal_slope lower length positive lengthPositive _ _ _ _ field
  rw [diagonal]
  apply lp.ext
  funext index
  rw [realLpDiagonal_apply, originalLpCut_apply]
  by_cases inside : index ∈ support <;> simp [inside]

theorem fluxCut_norm (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (support : Finset HighAnnularMode) (field : annularOmegaGraph lower length positive lengthPositive) :
    ‖fluxCut lower length positive lengthPositive support field‖ ≤ ‖field‖ := by
  have first := pow_le_pow_left₀ (norm_nonneg _) (originalLpCut_norm support (field.val 0)) 2
  have second := pow_le_pow_left₀ (norm_nonneg _) (originalLpCut_norm support (field.val 1)) 2
  have output := annularOmegaGraph_norm_sq lower length positive lengthPositive
    (fluxCut lower length positive lengthPositive support field)
  have input := annularOmegaGraph_norm_sq lower length positive lengthPositive field
  rw [fluxCut_row, fluxCut_row] at output
  nlinarith only [first, second, output, input, norm_nonneg field,
    norm_nonneg (fluxCut lower length positive lengthPositive support field)]

theorem fluxCut_tendsto (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    Tendsto (fun support : Finset HighAnnularMode => fluxCut lower length positive lengthPositive support field)
      atTop (𝓝 field) := by
  rw [tendsto_subtype_rng]
  have rows : Tendsto (fun support : Finset HighAnnularMode =>
      fun coordinate : Fin 2 => originalLpCut support (field.val coordinate)) atTop (𝓝 field.val.ofLp) :=
    tendsto_pi_nhds.mpr (fun coordinate => originalLpCut_tendsto (field.val coordinate))
  have output := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => AnnularBulk lower)).symm.continuous.tendsto
    field.val.ofLp).comp rows
  have actual (support : Finset HighAnnularMode) :
      (fluxCut lower length positive lengthPositive support field).val =
        WithLp.toLp 2 (fun coordinate : Fin 2 => originalLpCut support (field.val coordinate)) := by
    apply PiLp.ext
    intro coordinate
    exact fluxCut_row lower length positive lengthPositive support field coordinate
  change Tendsto (fun support : Finset HighAnnularMode =>
    WithLp.toLp 2 (fun coordinate : Fin 2 => originalLpCut support (field.val coordinate))) atTop (𝓝 field.val) at output
  simpa only [actual] using output

theorem fluxCut_weighted (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (support : Finset HighAnnularMode) (field weighted : annularOmegaGraph lower length positive lengthPositive)
    (coefficient : HighAnnularMode → ℂ)
    (actual : ∀ (coordinate : Fin 2) index, weighted.val coordinate index = coefficient index • field.val coordinate index)
    (coordinate : Fin 2) (index : HighAnnularMode) :
    (fluxCut lower length positive lengthPositive support weighted).val coordinate index =
      coefficient index • (fluxCut lower length positive lengthPositive support field).val coordinate index := by
  rw [fluxCut_row, fluxCut_row]
  exact originalLpCut_weighted support (field.val coordinate) (weighted.val coordinate) coefficient (actual coordinate) index

end Grad.AnnularHighGenerators
