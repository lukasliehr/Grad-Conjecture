import AJF6ActualHighFiniteGraphApproximation
import AJB25CompleteLpFatou

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Filter
open scoped Topology
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularOrbitGenerators

/-- Uniform weighted bounds for genuine energy approximants pass to the
same original energy graph by coefficient limits and its proved closure. -/
theorem energy_weighted_of_bounded_approximation {κ : Type*} (source : Filter κ) [NeBot source]
    (lower length : ℝ) (positive : 0 < lower)
    (approximation weightedApproximation : κ → annularEnergySpace lower length positive)
    (field : annularEnergySpace lower length positive) (coefficient : HighAnnularMode → ℂ)
    (converges : Tendsto approximation source (𝓝 field))
    (actual : ∀ stage index, (weightedApproximation stage).val index = coefficient index • (approximation stage).val index)
    (bound : ℝ) (nonnegative : 0 ≤ bound) (bounded : ∀ stage, ‖weightedApproximation stage‖ ≤ bound) :
    ∃ weighted : annularEnergySpace lower length positive,
      (∀ index, weighted.val index = coefficient index • field.val index) ∧ ‖weighted‖ ≤ bound := by
  obtain ⟨result, resultActual, resultBound⟩ := lp_of_bounded_coordinate_limit source
    (fun stage => (weightedApproximation stage).val) (fun index => coefficient index • field.val index)
    (fun index => by
      have coordinateConverges := (((lp.evalCLM ℂ (fun _ : HighAnnularMode => AnnularModeEnergyAmbient lower) 2 index).comp
        (annularEnergySpace lower length positive).subtypeL).continuous.tendsto field).comp converges
      have weightedConverges := coordinateConverges.const_smul (coefficient index)
      change Tendsto (fun stage => coefficient index • (approximation stage).val index) source
        (𝓝 (coefficient index • field.val index)) at weightedConverges
      simpa only [← actual] using weightedConverges)
    bound nonnegative bounded
  have membership := closedLpGraph_weighted (annularEnergySpace lower length positive)
    (LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure
    (fun value index => by
      rw [← energySingle_apply lower length positive index value]
      exact (energySingle lower length positive index value).property)
    field result coefficient resultActual
  exact ⟨⟨result, membership⟩, resultActual, resultBound⟩

/-- Both original Domega coordinates survive the finite-data limit with
the same weak derivative constraint, rather than an independent slope. -/
theorem flux_weighted_of_bounded_approximation {κ : Type*} (source : Filter κ) [NeBot source]
    (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (approximation weightedApproximation : κ → annularOmegaGraph lower length positive lengthPositive)
    (field : annularOmegaGraph lower length positive lengthPositive) (coefficient : HighAnnularMode → ℂ)
    (converges : Tendsto approximation source (𝓝 field))
    (actual : ∀ stage (coordinate : Fin 2) index,
      (weightedApproximation stage).val coordinate index = coefficient index • (approximation stage).val coordinate index)
    (bound : ℝ) (nonnegative : 0 ≤ bound) (bounded : ∀ stage, ‖weightedApproximation stage‖ ≤ bound) :
    ∃ weighted : annularOmegaGraph lower length positive lengthPositive,
      (∀ (coordinate : Fin 2) index, weighted.val coordinate index = coefficient index • field.val coordinate index) ∧
      ‖weighted‖ ≤ 2 * bound := by
  have limits (coordinate : Fin 2) : ∃ result : AnnularBulk lower,
      (∀ index, result index = coefficient index • field.val coordinate index) ∧ ‖result‖ ≤ bound := by
    refine lp_of_bounded_coordinate_limit source (fun stage => (weightedApproximation stage).val coordinate)
      (fun index => coefficient index • field.val coordinate index) ?_ bound nonnegative ?_
    · intro index
      have coordinateConverges := (((lp.evalCLM ℂ _ 2 index).comp
        (fluxStoredCoordinate lower length positive lengthPositive coordinate)).continuous.tendsto field).comp converges
      have weightedConverges := coordinateConverges.const_smul (coefficient index)
      change Tendsto (fun stage => coefficient index • (approximation stage).val coordinate index) source
        (𝓝 (coefficient index • field.val coordinate index)) at weightedConverges
      simpa only [← actual] using weightedConverges
    · intro stage
      exact (fluxStoredCoordinate_bound lower length positive lengthPositive coordinate (weightedApproximation stage)).trans (bounded stage)
  let result := fun coordinate => (limits coordinate).choose
  have resultActual (coordinate : Fin 2) (index : HighAnnularMode) :
      result coordinate index = coefficient index • field.val coordinate index := (limits coordinate).choose_spec.1 index
  have membership (coordinate : Fin 2) : Memℓp (fun index => coefficient index • field.val coordinate index) 2 := by
    have same : (fun index => coefficient index • field.val coordinate index) = fun index => result coordinate index :=
      funext (fun index => (resultActual coordinate index).symm)
    rw [same]
    exact (result coordinate).property
  let weighted := fluxSummableMultiplier lower length positive lengthPositive field coefficient membership
  refine ⟨weighted, fun _ _ => rfl, ?_⟩
  have coordinateBound (coordinate : Fin 2) : ‖weighted.val coordinate‖ ≤ bound := by
    have same : weighted.val coordinate = result coordinate := by
      apply lp.ext
      funext index
      exact (resultActual coordinate index).symm
    rw [same]
    exact (limits coordinate).choose_spec.2
  have squared := annularOmegaGraph_norm_sq lower length positive lengthPositive weighted
  have first := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 0) 2
  have second := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 1) 2
  nlinarith only [squared, first, second, nonnegative, norm_nonneg weighted, sq_nonneg bound]

end Grad.AnnularHighGenerators
