import AJB18OriginalLowGradeMembership
import AJB25CompleteLpFatou

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularLowEnergy Grad.AnnularOrbitGenerators

/-- Uniform bounds for actual weighted approximants pass to a genuine
weighted element of the original weak radial graph. Both stored coordinates
are passed through the actual lp coefficient limits. -/
theorem lowGraph_weighted_of_bounded_approximation {κ : Type*} (source : Filter κ) [NeBot source]
    (lower length : ℝ) (positive : 0 < lower)
    (approximation weightedApproximation : κ → lowEnergyGraph lower length positive)
    (field : lowEnergyGraph lower length positive) (coefficient : LowAnnularIndex → ℂ)
    (converges : Tendsto approximation source (𝓝 field))
    (actual : ∀ stage (coordinate : Fin 2) (index : LowAnnularIndex),
      (weightedApproximation stage).val coordinate index = coefficient index • (approximation stage).val coordinate index)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (bounded : ∀ stage, ‖weightedApproximation stage‖ ≤ bound) :
    ∃ weighted : lowEnergyGraph lower length positive,
      (∀ (coordinate : Fin 2) (index : LowAnnularIndex), weighted.val coordinate index = coefficient index • field.val coordinate index) ∧
      ‖weighted‖ ≤ 2 * bound := by
  have limits (coordinate : Fin 2) : ∃ result : LowEnergyBulk lower,
      (∀ index, result index = coefficient index • field.val coordinate index) ∧ ‖result‖ ≤ bound := by
    refine lp_of_bounded_coordinate_limit source (fun stage => (weightedApproximation stage).val coordinate)
      (fun index => coefficient index • field.val coordinate index) ?_ bound boundNonnegative ?_
    · intro index
      have coordinateConverges := (((lowEnergyCoordinate lower coordinate index).comp
        (lowEnergyGraph lower length positive).subtypeL).continuous.tendsto field).comp converges
      have weightedConverges := coordinateConverges.const_smul (coefficient index)
      change Tendsto (fun stage => coefficient index • (approximation stage).val coordinate index) source
        (𝓝 (coefficient index • field.val coordinate index)) at weightedConverges
      simpa only [← actual] using weightedConverges
    · intro stage
      exact (lowStoredCoordinate_bound lower length positive coordinate (weightedApproximation stage)).trans (bounded stage)
  let result := fun coordinate => (limits coordinate).choose
  have resultActual (coordinate : Fin 2) (index : LowAnnularIndex) :
      result coordinate index = coefficient index • field.val coordinate index := (limits coordinate).choose_spec.1 index
  have membership (coordinate : Fin 2) : Memℓp (fun index => coefficient index • field.val coordinate index) 2 := by
    have same : (fun index => coefficient index • field.val coordinate index) = fun index => result coordinate index :=
      funext (fun index => (resultActual coordinate index).symm)
    rw [same]
    exact (result coordinate).property
  let weighted := lowSummableGraphMultiplier lower length positive field coefficient membership
  refine ⟨weighted, fun _ _ => rfl, ?_⟩
  have coordinateBound (coordinate : Fin 2) : ‖weighted.val coordinate‖ ≤ bound := by
    have same : weighted.val coordinate = result coordinate := by
      apply lp.ext
      funext index
      exact (resultActual coordinate index).symm
    rw [same]
    exact (limits coordinate).choose_spec.2
  have squared := lowEnergyGraph_norm_sq lower length positive weighted
  have first := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 0) 2
  have second := pow_le_pow_left₀ (norm_nonneg _) (coordinateBound 1) 2
  nlinarith only [squared, first, second, boundNonnegative, norm_nonneg weighted, sq_nonneg bound]

end Grad.AnnularLowOrbit
